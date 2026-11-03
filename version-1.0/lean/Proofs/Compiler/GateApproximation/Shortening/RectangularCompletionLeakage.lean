import Proofs.Compiler.GateApproximation.Shortening.RectangularCompletionSampler
import Proofs.Compiler.GateApproximation.Shortening.RectangularPhysicalStochastic



/-!
# Exact conditional leakage from the completion sampler's internal tape

The conditional answer distribution below is derived from the concrete independent-entry rejection sampler. It retains every rejected proposal. Its dependence on the local inputs `U,A` is explicit, and no independence from those inputs is assumed.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators Classical

namespace CircuitCompiler.Rectangular.CompletionSampler

open Refresh MatrixRefresh Sampling Sampling.Unbounded

noncomputable section

variable {F B : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype B]

/-- Conditional finite answer distribution given the returned matrix. The rejected prefix depends on the local input `(U,A)` but not on the selected completion. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; u ∈ U(F, (n + t)); a ∈ U(F, n); f ∈ InternalTape(m = n + t, a) → B; H ∈ Completion(u, a), define

leftTapeDistribution(u, a, f, H) := toFinite((((p ↦ f(reconstruct(u, a, p, H))))_*rejectedDistribution(u, a))) .
-/
def leftTapeDistribution {n t : ℕ} (u : U F (n+t)) (a : U F n)
    (f : InternalTape (m := n+t) a → B) (H : Completion u a) : FiniteDistribution B :=
  toFinite ((rejectedDistribution u a).map (fun p => f (reconstruct u a p H)))

/-- Observe the actual matrix and any finite-valued function of all internal rejected and accepted field-entry proposals. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; u ∈ U(F, (n + t)); a ∈ U(F, n); f ∈ InternalTape(m = n + t, a) → B, define

observedJoint(u, a, f) := toFinite((((tape ↦ (returned(u, a, ((tape)₂)₂), f(tape))))_*tapeDistribution(u, a))).
-/
def observedJoint {n t : ℕ} (u : U F (n+t)) (a : U F n)
    (f : InternalTape (m := n+t) a → B) : FiniteDistribution (Completion u a × B) :=
  toFinite ((tapeDistribution u a).map (fun tape => (returned u a tape.2.2,f tape)))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X,Y a set; P ∈ 𝒟(X); Q ∈ X → 𝒟(Y), assume X is finite; Y is finite. Then

P.joint(Q) = bind(P, ((x ↦ (((y ↦ (x, y)))_*Q(x))))).
-/
private theorem joint_eq_bind_map {X Y : Type*} [Fintype X] [Fintype Y]
    (P : FiniteDistribution X) (Q : X → FiniteDistribution Y) :
    P.joint Q = P.bind (fun x => (Q x).map (fun y => (x,y))) := by
  classical
  ext ⟨x,y⟩
  simp [FiniteDistribution.joint,FiniteDistribution.bind,FiniteDistribution.map,FiniteDistribution.pure,ite_and,mul_ite]

/-- Exact implementation-to-conditional-distribution connection. The finite observation of the complete internal sampling tape can be generated after the uniform completion, with its correct input-dependent local conditional distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): The joint distribution of the final full-rank completion H and any finite observation of its internal rejection tape equals: sample H uniformly from all completions, then sample the observation from its conditional reconstructed-tape distribution. Thus this disintegration retains the full dependence of leakage on H. -/
theorem observedJoint_eq_uniform_joint {n t : ℕ} (u : U F (n+t)) (a : U F n)
    (f : InternalTape (m := n+t) a → B) :
    letI := completion_nonempty u a
    observedJoint u a f = (FiniteDistribution.uniform : FiniteDistribution (Completion u a)).joint (leftTapeDistribution u a f) := by
  letI := completion_nonempty u a
  unfold observedJoint
  rw [tapeDistribution_eq_reconstructed,PMF.map_bind]
  simp_rw [PMF.map_comp,Function.comp_def,returned_reconstruct]
  change toFinite ((rejectedDistribution u a).bind (fun p =>
    (toPMF (FiniteDistribution.uniform : FiniteDistribution (Completion u a))).bind (fun H =>
      PMF.pure (H,f (reconstruct u a p H))))) = _
  rw [PMF.bind_comm,toFinite_bind,toFinite_toPMF,joint_eq_bind_map]
  congr 1
  funext H
  change toFinite ((rejectedDistribution u a).map (fun p => (H,f (reconstruct u a p H)))) = _
  rw [leftTapeDistribution,← toFinite_map,PMF.map_comp]
  rfl

/-- Marginalizing the returned matrix recovers the same actual internal-tape answer distribution. This is suitable for stochastic observations of outer attempts. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For any finite observation f of the completion sampler's internal tape,

Pr[f = b] = 𝔼_(H ← Completion(u,a)) [Pr[f = b | H]],

where H is uniform and the conditional distribution is obtained by reconstructing its rejected prefix.
-/
theorem observedAnswer_eq_mixture {n t : ℕ} (u : U F (n+t)) (a : U F n)
    (f : InternalTape (m := n+t) a → B) :
    letI := completion_nonempty u a
    toFinite ((tapeDistribution u a).map f) =
      (FiniteDistribution.uniform : FiniteDistribution (Completion u a)).bind (leftTapeDistribution u a f) := by
  letI := completion_nonempty u a
  have h := congrArg (fun Q : FiniteDistribution (Completion u a × B) => Q.map Prod.snd)
    (observedJoint_eq_uniform_joint u a f)
  rw [observedJoint,← toFinite_map,PMF.map_comp] at h
  rw [joint_eq_bind_map,FiniteDistribution.map_bind] at h
  simp only [FiniteDistribution.map_map,Function.comp_def] at h
  have hid (Q : FiniteDistribution B) : Q.map (fun x => x) = Q := by
    ext b
    simp [FiniteDistribution.map,FiniteDistribution.bind,FiniteDistribution.pure]
  simpa only [hid] using h

end

end CircuitCompiler.Rectangular.CompletionSampler
