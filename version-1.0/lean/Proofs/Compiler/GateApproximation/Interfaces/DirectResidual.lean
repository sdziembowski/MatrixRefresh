import Proofs.Compiler.GateApproximation.Interfaces.AnswerPairing
import Proofs.Compiler.GateApproximation.Interfaces.Consistency
import Proofs.Compiler.GateApproximation.Interfaces.ResidualBootstrap



/-!
# Geometry of the actual strict-truncation residual
-/
set_option autoImplicit false

set_option maxHeartbeats 1500000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.AnswerApproximation

open Refresh MatrixRefresh TableAnalysis RefreshAnalysis SingularTruncation

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

/-
Mathematical definition (normal notation): For a real table A, define its strict-truncation residual by

Δ := A-2 · project(A^(>β)).

If A vanishes on invalid pairs, this also equals project(A-2 · A^(>β)).
-/
def approximationResidual (valid : I → I → Prop) [DecidableRel valid]
    (A : Matrix I I ℝ) (β : ℝ) : Matrix I I ℝ :=
  A - (2 : ℝ) • project valid (strictTruncation A β)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For valid ∈ I → I → Prop; A ∈ ℝ^(I × I); β ∈ ℝ; i, j ∈ I, assume DecidableRel(valid); ∀ i, j, ¬ (valid(i, j)) → A(i, j) = 0; ¬ (valid(i, j)). Then

approximationResidual(valid, A, β, i, j) = 0.
-/
theorem approximationResidual_supported (valid : I → I → Prop) [DecidableRel valid]
    (A : Matrix I I ℝ) (β : ℝ) (hA : ∀ i j, ¬valid i j → A i j = 0)
    (i j : I) (hij : ¬valid i j) : approximationResidual valid A β i j = 0 := by
  simp [approximationResidual, project, hij, hA i j hij]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; i, j ∈ I, assume 0 < β; ∀ i, j, |A(i, j)| ≤ 1. Then

|strictTruncation(A, β, i, j)| ≤ 1 / β.
-/
theorem strictPart_entry (A : Matrix I I ℝ) (β : ℝ) (hβ : 0 < β)
    (hA : ∀ i j, |A i j| ≤ 1) (i j : I) :
    |strictTruncation A β i j| ≤ 1 / β := by
  rw [strictTruncation_factorization]
  have hl := truncationLeftFactor_energy A β hβ hA i
  have hr := truncationRightFactor_energy A β hβ hA j
  have h := abs_real_inner_le_norm (truncationLeftFactor A β i) (truncationRightFactor A β j)
  have hh : ‖truncationLeftFactor A β i‖ * ‖truncationRightFactor A β j‖ ≤ 1 / β := by
    nlinarith [sq_nonneg (‖truncationLeftFactor A β i‖ - ‖truncationRightFactor A β j‖)]
  exact h.trans hh

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For valid ∈ I → I → Prop; A ∈ ℝ^(I × I); β ∈ ℝ; i, j ∈ I, assume DecidableRel(valid); 0 < β; β ≤ 1; ∀ i, j, |A(i, j)| ≤ 1. Then

|approximationResidual(valid, A, β, i, j)| ≤ 3 / β.
-/
theorem approximationResidual_entry (valid : I → I → Prop) [DecidableRel valid]
    (A : Matrix I I ℝ) (β : ℝ) (hβ : 0 < β) (hβone : β ≤ 1)
    (hA : ∀ i j, |A i j| ≤ 1) (i j : I) :
    |approximationResidual valid A β i j| ≤ 3 / β := by
  have hH := strictPart_entry A β hβ hA i j
  have hmask : |project valid (strictTruncation A β) i j| ≤ 1 / β := by
    unfold project
    split_ifs
    · exact hH
    · simp; positivity
  change |A i j - 2 * project valid (strictTruncation A β) i j| ≤ _
  have h := (abs_sub (A i j) (2 * project valid (strictTruncation A β) i j)).trans
    (add_le_add (hA i j) (by simpa only [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] using
      mul_le_mul_of_nonneg_left hmask (by norm_num : (0:ℝ)≤2)))
  apply h.trans
  have hb : 1 ≤ 1 / β := (le_div_iff₀ hβ).2 (by simpa using hβone)
  rw [show 3 / β = 3 * (1 / β) by ring]
  linarith

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B ∈ ℝ^(I × I); β ∈ ℝ, assume 0 < β; ∀ i, j, |A(i, j)| ≤ 1. Then

‖ (B ⊙ strictTruncation(A, β))‖ₒₚ ≤ ‖ B‖ₒₚ / β.
-/
theorem strictPart_schur (A B : Matrix I I ℝ) (β : ℝ) (hβ : 0 < β)
    (hA : ∀ i j, |A i j| ≤ 1) :
    largestSingularCoefficient (B ⊙ strictTruncation A β) ≤ largestSingularCoefficient B / β := by
  have hp : strictTruncation A β = innerProductTable (truncationLeftFactor A β) (truncationRightFactor A β) := by
    ext i j
    exact strictTruncation_factorization A β i j
  have hl : ∀ i, ‖truncationLeftFactor A β i‖ ≤ Real.sqrt (1 / β) := fun i =>
    Real.le_sqrt_of_sq_le (truncationLeftFactor_energy A β hβ hA i)
  have hr : ∀ i, ‖truncationRightFactor A β i‖ ≤ Real.sqrt (1 / β) := fun i =>
    Real.le_sqrt_of_sq_le (truncationRightFactor_energy A β hβ hA i)
  have h := schur_multiplier_norm_le_of_bounds (truncationLeftFactor A β) (truncationRightFactor A β)
    B (Real.sqrt (1 / β)) (Real.sqrt (1 / β)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hl hr
  rw [← hp, Matrix.hadamard_comm] at h
  rw [Real.mul_self_sqrt (by positivity : 0 ≤ 1 / β)] at h
  exact (div_le_div_of_nonneg_right h (Nat.cast_nonneg _)).trans_eq (by
    unfold largestSingularCoefficient
    ring)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For valid ∈ I → I → Prop; A ∈ ℝ^(I × I); β ∈ ℝ, assume DecidableRel(valid). Then

approximationResidual(valid, A, β) = (A - strictTruncation(A, β)) - refreshSign(valid) ⊙ strictTruncation(A, β).
-/
theorem approximationResidual_split (valid : I → I → Prop) [DecidableRel valid]
    (A : Matrix I I ℝ) (β : ℝ) :
    approximationResidual valid A β =
      (A - strictTruncation A β) - refreshSign valid ⊙ strictTruncation A β := by
  ext i j
  simp only [approximationResidual, project, refreshSign, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.hadamard_apply]
  split_ifs <;> ring

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For valid ∈ I → I → Prop; A ∈ ℝ^(I × I); β ∈ ℝ, assume DecidableRel(valid); 0 < β; ∀ i, j, |A(i, j)| ≤ 1. Then

‖ approximationResidual(valid, A, β)‖ₒₚ ≤ β + ‖ refreshSign(valid)‖ₒₚ / β.
-/
theorem approximationResidual_op (valid : I → I → Prop) [DecidableRel valid]
    (A : Matrix I I ℝ) (β : ℝ) (hβ : 0 < β) (hA : ∀ i j, |A i j| ≤ 1) :
    largestSingularCoefficient (approximationResidual valid A β) ≤ β + largestSingularCoefficient (refreshSign valid) / β := by
  rw [approximationResidual_split]
  have h := div_le_div_of_nonneg_right
    (norm_sub_le (A - strictTruncation A β) (refreshSign valid ⊙ strictTruncation A β))
    (Nat.cast_nonneg (Fintype.card I) : (0 : ℝ) ≤ _)
  change largestSingularCoefficient _ ≤ _ at h
  rw [add_div] at h
  exact h.trans (add_le_add (strictTruncation_tail_op A β hβ.le)
    (strictPart_schur A (refreshSign valid) β hβ hA))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B ∈ ℝ^(I × I), we have

|pairing(A, B)| ≤ ‖ A‖_* · ‖ B‖ₒₚ.
-/
theorem normalized_pairing_duality (A B : Matrix I I ℝ) :
    |pairing A B| ≤ tableNuclearNorm A * largestSingularCoefficient B := by
  rw [pairing_eq_countingPairing_div_card, abs_div,
    abs_of_nonneg (sq_nonneg (Fintype.card I : ℝ))]
  exact (div_le_div_of_nonneg_right (abs_countingPairing_le A B) (sq_nonneg _)).trans_eq (by
    unfold tableNuclearNorm largestSingularCoefficient
    ring)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For valid ∈ I → I → Prop; A ∈ ℝ^(I × I); β ∈ ℝ, assume DecidableRel(valid); ∀ i, j, ¬ (valid(i, j)) → A(i, j) = 0. Then

(‖ approximationResidual(valid, A, β)‖₂)² = pairing(A, approximationResidual(valid, A, β)) + 2 · pairing(strictTruncation(A, β), (refreshSign(valid) ⊙ strictTruncation(A, β))).
-/
theorem approximationResidual_exact_identity (valid : I → I → Prop) [DecidableRel valid]
    (A : Matrix I I ℝ) (β : ℝ) (hA : ∀ i j, ¬valid i j → A i j = 0) :
    tableL2Norm (approximationResidual valid A β) ^ 2 =
      pairing A (approximationResidual valid A β) +
        2 * pairing (strictTruncation A β) (refreshSign valid ⊙ strictTruncation A β) := by
  have h := strict_truncation_residual_identity valid A β hA
  dsimp only at h
  unfold approximationResidual
  rw [h]
  simp only [pairing, consistencySign, Matrix.hadamard_apply, Matrix.smul_apply,
    smul_eq_mul]
  have he (x y : I) : strictTruncation A β x y *
      (1 / 2 * refreshSign valid x y * strictTruncation A β x y) =
      (1 / 2 : ℝ) * (strictTruncation A β x y *
        (refreshSign valid x y * strictTruncation A β x y)) := by ring
  simp_rw [he, uavg_const_mul]
  ring

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For valid ∈ I → I → Prop; A ∈ ℝ^(I × I); β ∈ ℝ; i ∈ I, assume DecidableRel(valid); ∀ i, j, |A(i, j)| ≤ 1. Then

𝔼ⱼ [(approximationResidual(valid, A, β, i, j))²] ≤ 16.
-/
theorem approximationResidual_row_sq (valid : I → I → Prop) [DecidableRel valid]
    (A : Matrix I I ℝ) (β : ℝ) (hA : ∀ i j, |A i j| ≤ 1) (i : I) :
    uavg (fun j => approximationResidual valid A β i j ^ 2) ≤ 16 := by
  have hH := (strictTruncation_rowL2_le A β i).trans (rowL2_le_one_of_entry_bound A hA i)
  have hHsq : uavg (fun j => strictTruncation A β i j ^ 2) ≤ 1 := by
    rw [← rowL2_sq]
    nlinarith [rowL2_nonneg (strictTruncation A β) i]
  have hpoint (j : I) : approximationResidual valid A β i j ^ 2 ≤
      2 * A i j ^ 2 + 8 * strictTruncation A β i j ^ 2 := by
    simp only [approximationResidual, project, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> nlinarith [sq_nonneg (A i j + 2 * strictTruncation A β i j), sq_nonneg (A i j),
      sq_nonneg (strictTruncation A β i j)]
  have hAsq : uavg (fun j => A i j ^ 2) ≤ 1 := by
    apply (uavg_mono (fun j => ?_)).trans_eq (uavg_const 1)
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 (hA i j)
  have h := uavg_mono hpoint
  rw [uavg_add, uavg_const_mul, uavg_const_mul] at h
  linarith

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For valid ∈ I → I → Prop; A ∈ ℝ^(I × I); β ∈ ℝ; j ∈ I, assume DecidableRel(valid); ∀ i, j, |A(i, j)| ≤ 1. Then

𝔼ᵢ [(approximationResidual(valid, A, β, i, j))²] ≤ 16.
-/
theorem approximationResidual_column_sq (valid : I → I → Prop) [DecidableRel valid]
    (A : Matrix I I ℝ) (β : ℝ) (hA : ∀ i j, |A i j| ≤ 1) (j : I) :
    uavg (fun i => approximationResidual valid A β i j ^ 2) ≤ 16 := by
  have hH := (strictTruncation_columnL2_le A β j).trans
    (columnL2_le_one_of_entry_bound A hA j)
  have hHsq : uavg (fun i => strictTruncation A β i j ^ 2) ≤ 1 := by
    rw [← columnL2_sq]
    nlinarith [columnL2_nonneg (strictTruncation A β) j]
  have hpoint (i : I) : approximationResidual valid A β i j ^ 2 ≤
      2 * A i j ^ 2 + 8 * strictTruncation A β i j ^ 2 := by
    simp only [approximationResidual, project, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> nlinarith [sq_nonneg (A i j + 2 * strictTruncation A β i j), sq_nonneg (A i j),
      sq_nonneg (strictTruncation A β i j)]
  have hAsq : uavg (fun i => A i j ^ 2) ≤ 1 := by
    apply (uavg_mono (fun i => ?_)).trans_eq (uavg_const 1)
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 (hA i j)
  have h := uavg_mono hpoint
  rw [uavg_add, uavg_const_mul, uavg_const_mul] at h
  linarith

end

end CircuitCompiler.AnswerApproximation
