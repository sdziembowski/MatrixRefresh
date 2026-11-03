import Proofs.Compiler.GateApproximation.MatrixPhase.RejectionSampling
import Proofs.Compiler.Construction.Parameters



/-!
# Exact conditioning of a finite randomized execution

This supplies the conditional randomness behind a gate's leakage distribution. Conditioning on the produced encoding and then sampling the remaining tape is exactly the original joint experiment. Zero-probability conditions receive an arbitrary normalized distribution and never affect that equality.
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler

open Refresh Sampling

variable {Ω Y Z : Type*} [Fintype Ω] [Fintype Y] [Fintype Z] [DecidableEq Y]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(Ω); value ∈ Ω → Y; y ∈ Y, we have

(value_*P)(y) = acceptance(P, ((ω ↦ decide((value(ω) = y))))).
-/
theorem output_mass_eq_acceptance (P : FiniteDistribution Ω) (value : Ω → Y) (y : Y) :
    (P.map value).weight y = acceptance P (fun ω => decide (value ω = y)) := by
  classical
  simp [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.pure, acceptance, eq_comm]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(Ω); value ∈ Ω → Y; y ∈ Y; ω ∈ Ω, we have

(value_*P)(y) · conditional(P, value, y)(ω) = { P(ω) if value(ω) = y,; 0 otherwise }.
-/
theorem conditional_weight_identity (P : FiniteDistribution Ω) (value : Ω → Y) (y : Y) (ω : Ω) :
    (P.map value).weight y * (conditional P value y).weight ω =
      if value ω = y then P.weight ω else 0 := by
  rw [output_mass_eq_acceptance]
  unfold conditional
  by_cases hp : 0 < acceptance P (fun ω => decide (value ω = y))
  · rw [dif_pos hp]
    dsimp [accepted]
    simp only [decide_eq_true_eq]
    rw [mul_div_cancel₀ _ (ne_of_gt hp)]
  · rw [dif_neg hp]
    have hm : acceptance P (fun ω => decide (value ω = y)) = 0 :=
      le_antisymm (le_of_not_gt hp) (acceptance_nonneg _ _)
    rw [hm, zero_mul]
    by_cases hω : value ω = y
    · rw [if_pos hω]
      have hle : P.weight ω ≤ acceptance P (fun ω => decide (value ω = y)) := by
        unfold acceptance
        convert Finset.single_le_sum
          (fun a _ => show 0 ≤ (if decide (value a = y) then P.weight a else 0) from
            by split_ifs; exact P.nonneg a; rfl) (Finset.mem_univ ω) using 1
        simp [hω]
      linarith [P.nonneg ω]
    · rw [if_neg hω]

/-- Revealing an output and then conditionally sampling the tape preserves the entire joint distribution, including the original random sample. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(Ω); value ∈ Ω → Y, we have

joint((value_*P))(conditional(P, value)) = (((ω ↦ (value(ω), ω)))_*P).
-/
theorem joint_conditional (P : FiniteDistribution Ω) (value : Ω → Y) :
    (P.map value).joint (conditional P value) = P.map (fun ω => (value ω, ω)) := by
  classical
  ext ⟨y, ω⟩
  change (P.map value).weight y * (conditional P value y).weight ω = _
  rw [conditional_weight_identity]
  simp only [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.pure, Prod.mk.injEq,
    ite_and, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single ω]
  · simp [eq_comm]
  · intro b _hb hne
    simp [Ne.symm hne]
  · simp

/-- Consequently every leakage observation can be sampled after the produced encoding, from a conditional distribution that preserves all tape dependence. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(Ω); value ∈ Ω → Y; answer ∈ Ω → Z, we have

joint((value_*P))(((y ↦ (answer_*conditional(P, value, y))))) = (((ω ↦ (value(ω), answer(ω))))_*P).
-/
theorem observed_joint_conditional (P : FiniteDistribution Ω) (value : Ω → Y)
    (answer : Ω → Z) :
    (P.map value).joint (fun y => (conditional P value y).map answer) =
      P.map (fun ω => (value ω, answer ω)) := by
  classical
  ext ⟨y, z⟩
  change (P.map value).weight y *
    (∑ ω, (conditional P value y).weight ω * (FiniteDistribution.pure (answer ω)).weight z) = _
  rw [Finset.mul_sum]
  simp_rw [← mul_assoc, conditional_weight_identity]
  simp only [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.pure, Prod.mk.injEq,
    ite_and, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hv : value ω = y
  · subst y
    by_cases ha : answer ω = z
    · subst z; simp
    · simp [Ne.symm ha]
  · simp [hv, Ne.symm hv]

/-- The answer can itself be sampled by an answer distribution conditioned on the tape. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(Ω); value ∈ Ω → Y; answer ∈ Ω → 𝒟(Z), we have

joint((value_*P))(((y ↦ bind(conditional(P, value, y), answer)))) = (((pair ↦ (value((pair)₁), (pair)₂)))_*P.joint(answer)) .
-/
theorem answer_joint_conditional (P : FiniteDistribution Ω) (value : Ω → Y)
    (answer : Ω → FiniteDistribution Z) :
    (P.map value).joint (fun y => (conditional P value y).bind answer) =
      (P.joint answer).map (fun pair => (value pair.1, pair.2)) := by
  classical
  ext ⟨y, z⟩
  change (P.map value).weight y *
    (∑ ω, (conditional P value y).weight ω * (answer ω).weight z) = _
  rw [Finset.mul_sum]
  simp_rw [← mul_assoc, conditional_weight_identity]
  simp only [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.pure, FiniteDistribution.joint,
    Fintype.sum_prod_type, Prod.mk.injEq, ite_and, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : value ω = y
  · simp [hω]
  · simp [hω, Ne.symm hω]

end CircuitCompiler
