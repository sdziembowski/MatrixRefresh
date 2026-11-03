import Proofs.Compiler.GateApproximation.MatrixPhase.CommonTruncation



/-!
# Probability and local error facts for a common gate mask
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler.CommonTruncation

open Refresh

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] {rank : ℕ}

/-- The retained real answer table is pointwise nonnegative. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ Z → X → {0,…,rank-1} → ℝ; b ∈ Z → Y → {0,…,rank-1} → ℝ; B ∈ ℝ; k ∈ Z → X → Y → ℝ; z ∈ Z; x ∈ X; y ∈ Y, assume ∀ z, x, y, 0 ≤ k(z, x, y). Then

0 ≤ cut(a, b, B, k(z), x, y).
-/
theorem cut_nonneg
    (a : Z → X → Fin rank → ℝ) (b : Z → Y → Fin rank → ℝ) (B : ℝ)
    (k : Z → X → Y → ℝ) (hnonneg : ∀ z x y, 0 ≤ k z x y) (z : Z) (x : X) (y : Y) :
    0 ≤ cut a b B (k z) x y := by
  unfold cut
  split_ifs
  · exact hnonneg z x y
  · exact le_refl 0

/-- Keeping the same zero-one mask for every answer yields a subprobability table, including at off-support outer port tuples. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ Z → X → {0,…,rank-1} → ℝ; b ∈ Z → Y → {0,…,rank-1} → ℝ; B ∈ ℝ; k ∈ Z → X → Y → ℝ; x ∈ X; y ∈ Y, assume ∀ x, y, (∑_z (k(z, x, y))) = 1. Then

(∑_z (cut(a, b, B, k(z), x, y))) ≤ 1.
-/
theorem cut_total_le
    (a : Z → X → Fin rank → ℝ) (b : Z → Y → Fin rank → ℝ) (B : ℝ)
    (k : Z → X → Y → ℝ) (htotal : ∀ x y, (∑ z, k z x y) = 1) (x : X) (y : Y) :
    (∑ z, cut a b B (k z) x y) ≤ 1 := by
  classical
  by_cases h : energy a x ≤ B ∧ energy b y ≤ B
  · simp only [cut, if_pos h, htotal, le_refl]
  · simp only [cut, if_neg h, Finset.sum_const_zero, zero_le_one]

/-- Each fixed answer loses at most the probability of the common bad mask. No answer-alphabet factor is lost in this local estimate. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ Z → X → {0,…,rank-1} → ℝ; b ∈ Z → Y → {0,…,rank-1} → ℝ; B ∈ ℝ; k ∈ Z → X → Y → ℝ; P ∈ 𝒟((X × Y)); z ∈ Z, assume ∀ z, x, y, 0 ≤ k(z, x, y); ∀ x, y, (∑_z (k(z, x, y))) = 1. Then

𝔼_(xy ← P) [|k(z, (xy)₁, (xy)₂) - cut(a, b, B, k(z), (xy)₁, (xy)₂)|] ≤ 𝔼_(xy ← P) [{ 0 if energy(a, (xy)₁) ≤ B ∧ energy(b, (xy)₂) ≤ B,; 1 otherwise }].
-/
theorem cut_original_answer_error_le_bad
    (a : Z → X → Fin rank → ℝ) (b : Z → Y → Fin rank → ℝ) (B : ℝ)
    (k : Z → X → Y → ℝ) (hnonneg : ∀ z x y, 0 ≤ k z x y)
    (htotal : ∀ x y, (∑ z, k z x y) = 1) (P : FiniteDistribution (X × Y)) (z : Z) :
    P.expect (fun xy => |k z xy.1 xy.2 - cut a b B (k z) xy.1 xy.2|) ≤
      P.expect (fun xy => if energy a xy.1 ≤ B ∧ energy b xy.2 ≤ B then 0 else 1) := by
  classical
  apply P.expect_mono
  intro xy
  by_cases h : energy a xy.1 ≤ B ∧ energy b xy.2 ≤ B
  · simp [cut, h]
  · simp only [cut, if_neg h, sub_zero, abs_of_nonneg (hnonneg z xy.1 xy.2)]
    rw [← htotal xy.1 xy.2]
    exact Finset.single_le_sum (fun z' _ => hnonneg z' xy.1 xy.2) (Finset.mem_univ z)

/-- A fixed-answer approximation after truncation is bounded by the original sum of local answer errors. This is the input used at a forced query. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ Z → X → {0,…,rank-1} → ℝ; b ∈ Z → Y → {0,…,rank-1} → ℝ; B ∈ ℝ; k, G ∈ Z → X → Y → ℝ; P ∈ 𝒟((X × Y)); z ∈ Z, we have

𝔼_(xy ← P) [|cut(a, b, B, G(z), (xy)₁, (xy)₂) - cut(a, b, B, k(z), (xy)₁, (xy)₂)|] ≤ ∑_(z') (𝔼_(xy ← P) [|k(z', (xy)₁, (xy)₂) - G(z', (xy)₁, (xy)₂)|]).
-/
theorem cut_fixed_answer_error_le
    (a : Z → X → Fin rank → ℝ) (b : Z → Y → Fin rank → ℝ) (B : ℝ)
    (k G : Z → X → Y → ℝ) (P : FiniteDistribution (X × Y)) (z : Z) :
    P.expect (fun xy => |cut a b B (G z) xy.1 xy.2 - cut a b B (k z) xy.1 xy.2|) ≤
      ∑ z', P.expect (fun xy => |k z' xy.1 xy.2 - G z' xy.1 xy.2|) := by
  calc
    _ = P.expect (fun xy => |cut a b B (k z) xy.1 xy.2 - cut a b B (G z) xy.1 xy.2|) := by
      congr 1
      funext xy
      exact abs_sub_comm _ _
    _ ≤ ∑ z', P.expect (fun xy =>
        |cut a b B (k z') xy.1 xy.2 - cut a b B (G z') xy.1 xy.2|) :=
      Finset.single_le_sum (fun z' _ => P.expect_nonneg
        (fun xy => |cut a b B (k z') xy.1 xy.2 - cut a b B (G z') xy.1 xy.2|)
        (fun xy => abs_nonneg _))
        (Finset.mem_univ z)
    _ ≤ _ := cut_error_le a b B k G P

end CircuitCompiler.CommonTruncation
