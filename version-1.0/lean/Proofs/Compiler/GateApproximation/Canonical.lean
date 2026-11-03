import Proofs.Compiler.GateApproximation.MatrixPhase.Disintegration
import Proofs.Compiler.Construction.Parameters

set_option autoImplicit false

/-!
# Exact canonical answers from the full physical transition

For a joint output-and-answer distribution P, the conditional answer p(z ∣ o) is obtained by conditioning P on its output encoding o. The identity P(o,z) = μ(o) p(z ∣ o) is exact when μ is the output marginal. Thus exact freshness gives an exact canonical experiment even when the answer can inspect every rejected shortening proposal.
-/

noncomputable section
open scoped BigOperators

namespace CompilerProof.Canonical

open Refresh CircuitCompiler CircuitCompiler.Composition
  CircuitCompiler.Composition.TopologicalExecution

/-- Conditioning the actual joint distribution P on its first coordinate gives a normalized answer distribution. Conditions of probability zero receive the construction's arbitrary normalized fallback. -/
def answer {E A : Type*} [Fintype E] [DecidableEq E] [Fintype A]
    (P : FiniteDistribution (E × A)) (output : E) : FiniteDistribution A :=
  (conditional P Prod.fst output).map Prod.snd

/-- Disintegration preserves the complete joint distribution: P = (P.map fst).joint answer(P). It makes no independence claim between an output encoding and its leakage. -/
theorem disintegration {E A : Type*} [Fintype E] [DecidableEq E] [Fintype A]
    (P : FiniteDistribution (E × A)) :
    (P.map Prod.fst).joint (answer P) = P := by
  have h := observed_joint_conditional P Prod.fst Prod.snd
  have hm : P.map (fun x : E × A => (x.1,x.2)) = P := by
    classical
    ext x
    simp [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.pure]
  exact h.trans hm

/-- At every positive-mass output o, the normalized conditional weight is exactly P(o,z)/μ(o). -/
theorem answer_weight {E A : Type*} [Fintype E] [DecidableEq E] [Fintype A]
    (P : FiniteDistribution (E × A)) (output : E) (z : A)
    (houtput : 0 < (P.map Prod.fst).weight output) :
    (answer P output).weight z = P.weight (output,z) / (P.map Prod.fst).weight output := by
  have h := congrArg (fun Q : FiniteDistribution (E × A) => Q.weight (output,z))
    (disintegration P)
  change (P.map Prod.fst).weight output * (answer P output).weight z = P.weight (output,z) at h
  exact (eq_div_iff (ne_of_gt houtput)).2 (by simpa only [mul_comm] using h)

/-- An injective change of output coordinates preserves the probability of every original atom. -/
theorem map_injective_weight {X Y : Type*} [Fintype X] [Fintype Y]
    (P : FiniteDistribution X) (f : X → Y) (hf : Function.Injective f) (x : X) :
    (P.map f).weight (f x) = P.weight x := by
  classical
  simp [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.pure, hf.eq_iff]

/-- Conditioning on an output is unchanged by an injective representation of that output, such as inclusion of a secret fiber into the common wire-state space. -/
theorem answer_map_injective {E D A : Type*}
    [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D] [Fintype A]
    (P : FiniteDistribution (E × A)) (f : E → D) (hf : Function.Injective f)
    (output : E) (houtput : 0 < (P.map Prod.fst).weight output) :
    answer (P.map (fun z => (f z.1,z.2))) (f output) = answer P output := by
  classical
  have hpair : Function.Injective (fun z : E × A => (f z.1,z.2)) := by
    intro x y h
    have hh := Prod.mk.inj h
    exact Prod.ext (hf hh.1) hh.2
  have hm : ((P.map (fun z => (f z.1,z.2))).map Prod.fst).weight (f output) =
      (P.map Prod.fst).weight output := by
    rw [FiniteDistribution.map_map]
    have h := map_injective_weight (P.map Prod.fst) f hf output
    simpa only [FiniteDistribution.map_map, Function.comp_def] using h
  ext z
  rw [answer_weight _ _ _ (by rw [hm]; exact houtput), answer_weight P output z houtput,
    hm, map_injective_weight P _ hpair (output,z)]

/-- Replacing the analytic answer field by the actual conditional distribution leaves the physical transition unchanged. -/
def protocol {F E A : Type*} [Fintype E] [DecidableEq E] [Fintype A] {inputs : ℕ}
    (physical : GateProtocol F E A inputs) : GateProtocol F E A inputs where
  real := physical.real
  answer i gate history left right := answer (physical.real i gate history left right)

/-- The chronological real runner reads only the physical transition, so adding its exact conditional answer does not alter any execution. -/
theorem realRunner_eq {F E A : Type*} [Mul F] [Sub F]
    [Fintype E] [DecidableEq E] [Fintype A] {inputs T : ℕ}
    (physical : GateProtocol F E A inputs) (program : Program F inputs T) :
    (protocol physical).realRunner program = physical.realRunner program := by
  induction program with
  | nil => rfl
  | snoc prior gate ih =>
    simp only [GateProtocol.realRunner, ih]
    rfl

/-- Exact output freshness immediately identifies a physical gate with the joint fresh-encoding and actual-conditional-answer transition. -/
theorem gate_eq_joint {F E A : Type*} [Fintype E] [DecidableEq E] [Fintype A]
    {inputs : ℕ} (physical : GateProtocol F E A inputs) (i : ℕ)
    (gate : Gate F (inputs + i)) (history : Fin i → A) (left right : E)
    (μ : FiniteDistribution E)
    (hfresh : (physical.real i gate history left right).map Prod.fst = μ) :
    physical.real i gate history left right =
      μ.joint ((protocol physical).answer i gate history left right) := by
  rw [← hfresh]
  exact (disintegration _).symm

/-- Zero statistical distance identifies the entire finite distribution, including every retained observation. -/
theorem eq_of_distance_nonpos {X : Type*} [Fintype X]
    (P Q : FiniteDistribution X) (h : statisticalDistance P Q ≤ 0) : P = Q := by
  classical
  have hs : variationNorm (fun x => P.weight x - Q.weight x) ≤ 0 := by
    unfold statisticalDistance at h
    linarith
  ext x
  have hx : |P.weight x - Q.weight x| ≤ variationNorm (fun y => P.weight y - Q.weight y) := by
    change |P.weight x - Q.weight x| ≤ ∑ y, |P.weight y - Q.weight y|
    exact Finset.single_le_sum (fun y _ => abs_nonneg (P.weight y - Q.weight y)) (Finset.mem_univ x)
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (hx.trans hs) (abs_nonneg _)))

end CompilerProof.Canonical
