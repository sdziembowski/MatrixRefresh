import Proofs.Compiler.LocalComparisons.Framework.TopologicalExecution



/-!
# Canonical coupling only on reachable, correctly typed prefixes
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler.Composition

open Refresh

/-- Zero-weight points impose no condition on an expectation bound. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X a set; P ∈ 𝒟(X); f ∈ X → ℝ; bound ∈ ℝ, assume X is finite; ∀ x, (P(x) ≠ 0) ⇒ f(x) ≤ bound. Then

𝔼_(u ← P) [f(u)] ≤ bound.
-/
theorem expect_le_on_support {X : Type*} [Fintype X]
    (P : FiniteDistribution X) (f : X → ℝ) (bound : ℝ)
    (h : ∀ x, P.weight x ≠ 0 → f x ≤ bound) : P.expect f ≤ bound := by
  calc
    _ ≤ ∑ x, P.weight x * bound := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : P.weight x = 0
      · simp [hx]
      · exact mul_le_mul_of_nonneg_left (h x hx) (P.nonneg x)
    _ = bound := by rw [← Finset.sum_mul, P.total, one_mul]

/-- Conditional errors need only be controlled on the canonical source distribution's support. Arbitrary malformed encodings outside that support are irrelevant. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X,Y a set; P, Q ∈ 𝒟(X); real, canonical ∈ X → 𝒟(Y); error ∈ ℝ, assume X is finite; Y is finite; ∀ x, (Q(x) ≠ 0) ⇒ δ(real(x), canonical(x)) ≤ error. Then

δ(bind(P, real), bind(Q, canonical)) ≤ δ(P, Q) + error.
-/
theorem statisticalDistance_transition_supported {X Y : Type*} [Fintype X] [Fintype Y]
    (P Q : FiniteDistribution X) (real canonical : X → FiniteDistribution Y) (error : ℝ)
    (hstep : ∀ x, Q.weight x ≠ 0 → statisticalDistance (real x) (canonical x) ≤ error) :
    statisticalDistance (P.bind real) (Q.bind canonical) ≤ statisticalDistance P Q + error := by
  have hmap (transition : X → FiniteDistribution Y) : (Q.joint transition).map Prod.snd = Q.bind transition := by
    classical
    ext y
    simp [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.joint, FiniteDistribution.pure, Fintype.sum_prod_type]
  have hjoint : statisticalDistance (Q.joint real) (Q.joint canonical) =
      Q.expect (fun x => statisticalDistance (real x) (canonical x)) :=
    statisticalDistance_joint_mixture Q real canonical
  have hconditional := statisticalDistance_map_le (Q.joint real) (Q.joint canonical) Prod.snd
  rw [hmap, hmap, hjoint] at hconditional
  have hbound := hconditional.trans (expect_le_on_support Q _ error hstep)
  exact (statisticalDistance_triangle _ (Q.bind real) _).trans
    (add_le_add (statisticalDistance_bind_le P Q real) hbound)

namespace TopologicalExecution

universe u v

variable {E : Type u} {A : Type v} [Fintype E] [Fintype A] {inputs T : ℕ}

/-- Each local gate coupling is required only when its prefix can actually occur in the canonical execution. -/
/- Mathematical definition (normal notation): Corresponding actual and canonical gate transitions are within statistical distance ε on every prior state having positive probability under the canonical execution. No local comparison is required on unreachable canonical prefixes. -/
def Runner.CoupledOn (initial : FiniteDistribution (Fin inputs → E)) (error : ℝ) :
    {T : ℕ} → Runner E A inputs T → Runner E A inputs T → Prop
  | 0, .nil, .nil => True
  | _ + 1, .snoc real realGate, .snoc canonical canonicalGate =>
      real.CoupledOn initial error canonical ∧ ∀ state,
        (canonical.execute initial).weight state ≠ 0 →
          statisticalDistance (realGate state) (canonicalGate state) ≤ error

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For initial ∈ 𝒟(({0,…,inputs-1} → E)); real, canonical ∈ Runner(E, A, inputs, T); error ∈ ℝ, assume real.CoupledOn(initial, error, canonical). Then

δ(real.execute(initial), canonical.execute(initial)) ≤ T · error.
-/
theorem Runner.execute_distance_on_support (initial : FiniteDistribution (Fin inputs → E))
    (real canonical : Runner E A inputs T) (error : ℝ)
    (h : real.CoupledOn initial error canonical) :
    statisticalDistance (real.execute initial) (canonical.execute initial) ≤ (T : ℝ) * error := by
  induction real with
  | nil => cases canonical; simp [Runner.execute]
  | @snoc T real realGate ih =>
      cases canonical with
      | snoc canonical canonicalGate =>
          rcases h with ⟨hprior, hgate⟩
          rw [Runner.execute_snoc, Runner.execute_snoc]
          have hstep (state : RunState E A inputs T) (hs : (canonical.execute initial).weight state ≠ 0) :
              statisticalDistance
                ((realGate state).map (fun pair => appendEquiv (state, pair)))
                ((canonicalGate state).map (fun pair => appendEquiv (state, pair))) ≤ error :=
            (statisticalDistance_map_le _ _ _).trans (hgate state hs)
          have hbound := statisticalDistance_transition_supported
            (real.execute initial) (canonical.execute initial) _ _ error hstep
          have hprev := ih canonical hprior
          push_cast
          nlinarith

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; initial ∈ 𝒟(({0,…,inputs-1} → E)); real, canonical ∈ Runner(E, A, inputs, T); error ∈ ℝ; observe ∈ RunState(E, A, inputs, T) → V, assume V is finite; real.CoupledOn(initial, error, canonical). Then

δ((observe_*real.execute(initial)), (observe_*canonical.execute(initial))) ≤ T · error.
-/
theorem Runner.execute_observed_distance_on_support {V : Type*} [Fintype V]
    (initial : FiniteDistribution (Fin inputs → E))
    (real canonical : Runner E A inputs T) (error : ℝ)
    (h : real.CoupledOn initial error canonical) (observe : RunState E A inputs T → V) :
    statisticalDistance ((real.execute initial).map observe) ((canonical.execute initial).map observe) ≤
      (T : ℝ) * error :=
  (statisticalDistance_map_le _ _ _).trans (real.execute_distance_on_support initial canonical error h)

/-- Every wire in a reachable canonical prefix lies in the support of its own independent encoding distribution. Adaptivity of the answers does not affect this. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For initial ∈ {0,…,inputs-1} → 𝒟(E); canonical ∈ Canonical(E, A, inputs, T), we have

Supports(canonical.runner.execute(independentDistribution(initial)))(((state ↦ ∀ w, canonical.wireDistributions(initial, w)((state)₁(w)) ≠ 0))) .
-/
theorem Canonical.execute_support_wireDistributions (initial : Fin inputs → FiniteDistribution E)
    (canonical : Canonical E A inputs T) :
    (canonical.runner.execute (independentDistribution initial)).Supports (fun state =>
      ∀ w, (canonical.wireDistributions initial w).weight (state.1 w) ≠ 0) := by
  intro state hstate
  rw [canonical.execute_weight] at hstate
  have hprod : (∏ w, (canonical.wireDistributions initial w).weight (state.1 w)) ≠ 0 :=
    (mul_ne_zero_iff.mp hstate).1
  intro w
  exact (Finset.prod_ne_zero_iff.mp hprod) w (Finset.mem_univ w)

/-- Correctly typed per-wire distributions imply a correctly typed canonical prefix, which is exactly the hypothesis needed by the physical gate coupling. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For initial ∈ {0,…,inputs-1} → 𝒟(E); canonical ∈ Canonical(E, A, inputs, T); valid ∈ {0,…,(inputs + T)-1} → E → Prop, assume ∀ w, Supports(canonical.wireDistributions(initial, w))(valid(w)). Then

Supports(canonical.runner.execute(independentDistribution(initial)))(((state ↦ ∀ w, valid(w, (state)₁(w))))).
-/
theorem Canonical.execute_support (initial : Fin inputs → FiniteDistribution E)
    (canonical : Canonical E A inputs T) (valid : Fin (inputs + T) → E → Prop)
    (hvalid : ∀ w, (canonical.wireDistributions initial w).Supports (valid w)) :
    (canonical.runner.execute (independentDistribution initial)).Supports (fun state => ∀ w, valid w (state.1 w)) := by
  intro state hstate w
  exact hvalid w (state.1 w) (canonical.execute_support_wireDistributions initial state hstate w)

end TopologicalExecution

end CircuitCompiler.Composition
