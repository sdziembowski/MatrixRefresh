import Proofs.Compiler.Foundations.LinearAlgebra.GramMixing
import Proofs.Compiler.Foundations.LinearAlgebra.NuclearIdentification
import Proofs.Compiler.Foundations.LinearAlgebra.RowTrimming
import Proofs.Compiler.Foundations.LinearAlgebra.Truncation



/-!
# Spectral cutoff in the uniform-table convention

The raw matrix cutoff is `d * ε`: the singular values of the uniform table operator `A / d` are the raw singular values divided by `d`. Singular functions are raw Euclidean singular vectors multiplied by `sqrt d`. The returned table and its weighted features retain the original entry scale.
-/

set_option autoImplicit false

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace TableAnalysis

open MatrixRefresh

noncomputable section

variable {n : ℕ}

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, we have

‖ spectralTruncate(A, ε)‖_(*,count) ≤ ‖ A‖_(*,count).
-/
theorem spectralTruncate_nuclearNorm_le (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    nuclearNorm (spectralTruncate A ε) ≤ nuclearNorm A := by
  rw [nuclearNorm_eq_matrixSVD_sum A]
  change nuclearNorm (svdMatrix (matrixSVD A).left (matrixSVD A).right
    (retainedSigma A ε)) ≤ _
  rw [(svdMatrix_decomposition (matrixSVD A).left (matrixSVD A).right
    (retainedSigma A ε) (retainedSigma_nonneg A ε)).nuclearNorm_eq_sum_sigma]
  exact retainedSigma_sum_le A ε

/- Mathematical definition (normal notation): The jth normalized singular coefficient of an n × n table is σⱼ := σ̂ⱼ/n, where σ̂ⱼ is its Euclidean singular value. The empty-index normalization is assigned 0. -/
def tableSingularValue (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : ℝ :=
  (matrixSVD A).sigma k / n

/- Mathematical definition (normal notation): From the normalized orthonormal expansion A = ∑ⱼ σⱼ · uⱼ · vⱼᵀ, retain terms with σⱼ ≥ ε. This auxiliary truncation uses an inclusive cutoff; the paper's >β truncation is defined separately. -/
def tableSpectralTruncate (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    Matrix (Fin n) (Fin n) ℝ := spectralTruncate A ((n : ℝ) * ε)

/- Mathematical definition (normal notation): The discarded normalized spectral tail is A-A^(≥ ε), where the auxiliary retained table uses the inclusive cutoff σⱼ ≥ ε. -/
def tableSpectralTail (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    Matrix (Fin n) (Fin n) ℝ := spectralTail A ((n : ℝ) * ε)

/- Mathematical definition (normal notation): The retained directions are precisely the singular indices j with σ̂ⱼ ≥ nε, equivalently σⱼ ≥ ε when n>0. -/
abbrev TableRetainedDirection (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :=
  RetainedDirection A ((n : ℝ) * ε)

/- Mathematical definition (normal notation): For each retained singular index j, define uⱼ(ℓ) := √n · ûⱼ(ℓ) from the Euclidean left singular vector. It has unit norm under uniform row measure when n>0. -/
def tableLeftDirection (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (k : TableRetainedDirection A ε) (i : Fin n) : ℝ :=
  Real.sqrt (n : ℝ) * (matrixSVD A).left k.val i

/- Mathematical definition (normal notation): For each retained singular index j, define vⱼ(r) := √n · v̂ⱼ(r) from the Euclidean right singular vector. It has unit norm under uniform column measure when n>0. -/
def tableRightDirection (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (k : TableRetainedDirection A ε) (j : Fin n) : ℝ :=
  Real.sqrt (n : ℝ) * (matrixSVD A).right k.val j

/- Mathematical definition (normal notation): The retained left feature vector at row ℓ has coordinates √(σ̂ⱼ) · ûⱼ(ℓ) = √σⱼ · uⱼ(ℓ) over retained singular indices j. -/
def tableLeftFeature (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (i : Fin n) :
    EuclideanSpace ℝ (TableRetainedDirection A ε) :=
  spectralLeftFeature A ((n : ℝ) * ε) i

/- Mathematical definition (normal notation): The retained right feature vector at column r has coordinates √(σ̂ⱼ) · v̂ⱼ(r) = √σⱼ · vⱼ(r) over retained singular indices j. -/
def tableRightFeature (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (j : Fin n) :
    EuclideanSpace ℝ (TableRetainedDirection A ε) :=
  spectralRightFeature A ((n : ℝ) * ε) j

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}), we have

(‖ A‖₂)² = matrixL2Sq(A) / n².
-/
theorem tableL2Norm_sq_eq_counting (A : Matrix (Fin n) (Fin n) ℝ) :
    tableL2Norm A ^ 2 = matrixL2Sq A / (n : ℝ) ^ 2 := by
  simp only [tableL2Norm, div_pow, entryVector_norm_sq, Fintype.card_fin,
    matrixL2Sq]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); i ∈ {0,…,n-1}, we have

(rowL2(A, i))² = (∑ⱼ ((A(i, j))²)) / n.
-/
theorem rowL2_sq_eq_counting (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    rowL2 A i ^ 2 = (∑ j, A i j ^ 2) / n := by
  rw [rowL2_sq]
  simp [uavg, div_eq_mul_inv, mul_comm]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); j ∈ {0,…,n-1}, we have

(columnL2(A, j))² = (∑ᵢ ((A(i, j))²)) / n.
-/
theorem columnL2_sq_eq_counting (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    columnL2 A j ^ 2 = (∑ i, A i j ^ 2) / n := by
  rw [columnL2_sq]
  simp [uavg, div_eq_mul_inv, mul_comm]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; i, j ∈ {0,…,n-1}, we have

tableSpectralTruncate(A, ε, i, j) = inner(ℝ, tableLeftFeature(A, ε, i), tableRightFeature(A, ε, j)).
-/
theorem tableSpectralTruncate_factorization (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (i j : Fin n) :
    tableSpectralTruncate A ε i j = inner ℝ (tableLeftFeature A ε i)
      (tableRightFeature A ε j) :=
  (spectralTruncate_factorization _ _ _ _).symm

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, we have

‖ tableSpectralTruncate(A, ε)‖ₒₚ ≤ ‖ A‖ₒₚ.
-/
theorem tableSpectralTruncate_largestSingularCoefficient_le (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    largestSingularCoefficient (tableSpectralTruncate A ε) ≤ largestSingularCoefficient A :=
  div_le_div_of_nonneg_right (spectralTruncate_operator_norm_le A _)
    (Nat.cast_nonneg _)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, we have

‖ tableSpectralTruncate(A, ε)‖_* ≤ ‖ A‖_*.
-/
theorem tableSpectralTruncate_tableNuclearNorm_le (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    tableNuclearNorm (tableSpectralTruncate A ε) ≤ tableNuclearNorm A :=
  div_le_div_of_nonneg_right (spectralTruncate_nuclearNorm_le A _)
    (Nat.cast_nonneg _)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; i ∈ {0,…,n-1}, we have

rowL2(tableSpectralTruncate(A, ε), i) ≤ rowL2(A, i).
-/
theorem tableSpectralTruncate_rowL2_le (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (i : Fin n) :
    rowL2 (tableSpectralTruncate A ε) i ≤ rowL2 A i := by
  have h := spectralTruncate_row_sq_le A ((n : ℝ) * ε) i
  have hs : rowL2 (tableSpectralTruncate A ε) i ^ 2 ≤ rowL2 A i ^ 2 := by
    rw [rowL2_sq_eq_counting, rowL2_sq_eq_counting]
    exact div_le_div_of_nonneg_right h (Nat.cast_nonneg _)
  nlinarith [rowL2_nonneg A i, rowL2_nonneg (tableSpectralTruncate A ε) i]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; j ∈ {0,…,n-1}, we have

columnL2(tableSpectralTruncate(A, ε), j) ≤ columnL2(A, j).
-/
theorem tableSpectralTruncate_columnL2_le (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (j : Fin n) :
    columnL2 (tableSpectralTruncate A ε) j ≤ columnL2 A j := by
  have h := spectralTruncate_column_sq_le A ((n : ℝ) * ε) j
  have hs : columnL2 (tableSpectralTruncate A ε) j ^ 2 ≤ columnL2 A j ^ 2 := by
    rw [columnL2_sq_eq_counting, columnL2_sq_eq_counting]
    exact div_le_div_of_nonneg_right h (Nat.cast_nonneg _)
  nlinarith [columnL2_nonneg A j, columnL2_nonneg (tableSpectralTruncate A ε) j]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, we have

‖ tableSpectralTruncate(A, ε)‖₂ ≤ ‖ A‖₂.
-/
theorem tableSpectralTruncate_tableL2Norm_le (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    tableL2Norm (tableSpectralTruncate A ε) ≤ tableL2Norm A := by
  have h := spectralTruncate_l2_sq_le A ((n : ℝ) * ε)
  have hs : tableL2Norm (tableSpectralTruncate A ε) ^ 2 ≤ tableL2Norm A ^ 2 := by
    rw [tableL2Norm_sq_eq_counting, tableL2Norm_sq_eq_counting]
    exact div_le_div_of_nonneg_right h (sq_nonneg _)
  nlinarith [tableL2Norm_nonneg A, tableL2Norm_nonneg (tableSpectralTruncate A ε)]

section Nonempty

variable [NeZero n]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

0 < n.
-/
theorem fin_card_real_pos : 0 < (n : ℝ) := by
  exact_mod_cast (NeZero.pos n)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); k ∈ {0,…,n-1}, we have

0 ≤ tableSingularValue(A, k).
-/
theorem tableSingularValue_nonneg (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    0 ≤ tableSingularValue A k :=
  div_nonneg ((matrixSVD A).nonneg k) fin_card_real_pos.le

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); k ∈ {0,…,n-1}, we have

tableSingularValue(A, k) ≤ ‖ A‖ₒₚ.
-/
theorem tableSingularValue_le_largestSingularCoefficient (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    tableSingularValue A k ≤ largestSingularCoefficient A := by
  change (matrixSVD A).sigma k / n ≤ ‖A‖ / Fintype.card (Fin n)
  simp only [Fintype.card_fin]
  apply div_le_div_of_nonneg_right _ fin_card_real_pos.le
  change (matrixSVD A).sigma k ≤ ‖A.toEuclideanLin.toContinuousLinearMap‖
  rw [matrixSVD_operator_norm]
  simpa only [Real.norm_eq_abs, abs_of_nonneg ((matrixSVD A).nonneg k)] using
    norm_le_pi_norm (matrixSVD A).sigma k

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; k ∈ {0,…,n-1}, we have

n · ε ≤ σ(matrixSVD(A))(k) ⇔ ε ≤ tableSingularValue(A, k).
-/
theorem tableRetainedDirection_mem_iff (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (k : Fin n) :
    (n : ℝ) * ε ≤ (matrixSVD A).sigma k ↔ ε ≤ tableSingularValue A k := by
  unfold tableSingularValue
  rw [le_div_iff₀ fin_card_real_pos]
  constructor <;> intro h <;> nlinarith

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, we have

OrthonormalFamily(tableLeftDirection(A, ε)).
-/
theorem tableLeftDirection_orthonormal (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    OrthonormalFamily (tableLeftDirection A ε) := by
  intro k l
  unfold tableLeftDirection uavg
  simp only [Fintype.card_fin]
  calc
    _ = (n : ℝ)⁻¹ * ((Real.sqrt (n : ℝ)) ^ 2 *
        ∑ i, (matrixSVD A).left k.val i * (matrixSVD A).left l.val i) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = indexDelta k l := by
      rw [Real.sq_sqrt fin_card_real_pos.le, orthonormalBasis_coordinate_inner]
      by_cases h : k = l
      · subst l
        simp [indexDelta, ne_of_gt fin_card_real_pos]
      · have hval : k.val ≠ l.val := fun hh => h (Subtype.ext hh)
        simp [indexDelta, h, hval]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, we have

OrthonormalFamily(tableRightDirection(A, ε)).
-/
theorem tableRightDirection_orthonormal (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    OrthonormalFamily (tableRightDirection A ε) := by
  intro k l
  unfold tableRightDirection uavg
  simp only [Fintype.card_fin]
  calc
    _ = (n : ℝ)⁻¹ * ((Real.sqrt (n : ℝ)) ^ 2 *
        ∑ j, (matrixSVD A).right k.val j * (matrixSVD A).right l.val j) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = indexDelta k l := by
      rw [Real.sq_sqrt fin_card_real_pos.le, orthonormalBasis_coordinate_inner]
      by_cases h : k = l
      · subst l
        simp [indexDelta, ne_of_gt fin_card_real_pos]
      · have hval : k.val ≠ l.val := fun hh => h (Subtype.ext hh)
        simp [indexDelta, h, hval]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; i, j ∈ {0,…,n-1}, we have

tableSpectralTruncate(A, ε, i, j) = ∑_(k ∈ TableRetainedDirection(A, ε)) (tableSingularValue(A, k) · tableLeftDirection(A, ε, k, i) · tableRightDirection(A, ε, k, j)).
-/
theorem tableSpectralTruncate_expansion (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (i j : Fin n) :
    tableSpectralTruncate A ε i j =
      ∑ k : TableRetainedDirection A ε, tableSingularValue A k.val *
        tableLeftDirection A ε k i * tableRightDirection A ε k j := by
  have hn : (n : ℝ) ≠ 0 := ne_of_gt fin_card_real_pos
  unfold tableSpectralTruncate spectralTruncate svdMatrix
  unfold tableSingularValue tableLeftDirection tableRightDirection
  calc
    _ = ∑ k : TableRetainedDirection A ε,
        (matrixSVD A).sigma k.val * (matrixSVD A).left k.val i *
          (matrixSVD A).right k.val j := by
      rw [sum_retainedDirections A ((n : ℝ) * ε)
        (fun k => (matrixSVD A).sigma k * (matrixSVD A).left k i *
          (matrixSVD A).right k j)]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : (n : ℝ) * ε ≤ (matrixSVD A).sigma k <;>
        simp [retainedSigma, hk]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      have hs := Real.sq_sqrt (fin_card_real_pos (n := n)).le
      have heq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
        nlinarith
      calc
        _ = ((matrixSVD A).sigma k.val / n) *
            (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) *
            (matrixSVD A).left k.val i * (matrixSVD A).right k.val j := by
          rw [heq]
          field_simp
        _ = _ := by ring

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, assume 0 < ε. Then

‖ tableSpectralTail(A, ε)‖ₒₚ ≤ ε.
-/
theorem tableSpectralTail_largestSingularCoefficient_le (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) : largestSingularCoefficient (tableSpectralTail A ε) ≤ ε := by
  unfold largestSingularCoefficient tableSpectralTail
  simp only [Fintype.card_fin]
  apply (div_le_iff₀ fin_card_real_pos).mpr
  have h := spectralTail_operator_norm_le A ((n : ℝ) * ε)
    (mul_pos fin_card_real_pos hε)
  nlinarith

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, assume 0 < ε. Then

(‖ tableSpectralTail(A, ε)‖₂)² ≤ ε · ‖ A‖_*.
-/
theorem tableSpectralTail_tableL2Norm_sq_le (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    tableL2Norm (tableSpectralTail A ε) ^ 2 ≤ ε * tableNuclearNorm A := by
  rw [tableL2Norm_sq_eq_counting]
  apply (div_le_iff₀ (sq_pos_of_pos fin_card_real_pos)).mpr
  have h := spectralTail_l2_sq_le A ((n : ℝ) * ε)
    (mul_pos fin_card_real_pos hε)
  rw [← nuclearNorm_eq_matrixSVD_sum] at h
  have heq : ε * tableNuclearNorm A * (n : ℝ) ^ 2 =
      ((n : ℝ) * ε) * nuclearNorm A := by
    unfold tableNuclearNorm
    simp only [Fintype.card_fin]
    field_simp
  rw [heq]
  exact h

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, assume 0 < ε. Then

tableL1(tableSpectralTail(A, ε)) ≤ √(ε · ‖ A‖_*).
-/
theorem tableSpectralTail_tableL1_le (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    tableL1 (tableSpectralTail A ε) ≤ Real.sqrt (ε * tableNuclearNorm A) :=
  (tableL1_le_tableL2Norm _).trans
    (Real.le_sqrt_of_sq_le (tableSpectralTail_tableL2Norm_sq_le A ε hε))

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, assume 0 < ε. Then

|TableRetainedDirection(A, ε)| · ε² ≤ (‖ A‖₂)².
-/
theorem tableRetainedDirection_count_sq_le (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    (Fintype.card (TableRetainedDirection A ε) : ℝ) * ε ^ 2 ≤ tableL2Norm A ^ 2 := by
  rw [tableL2Norm_sq_eq_counting]
  apply (le_div_iff₀ (sq_pos_of_pos fin_card_real_pos)).mpr
  have h := retained_direction_count_sq_le A ((n : ℝ) * ε)
    (mul_pos fin_card_real_pos hε)
  nlinarith

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; i ∈ {0,…,n-1}, assume 0 < ε. Then

(‖ tableLeftFeature(A, ε, i)‖)² ≤ (rowL2(A, i))² / ε.
-/
theorem tableLeftFeature_norm_sq_le (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) (i : Fin n) :
    ‖tableLeftFeature A ε i‖ ^ 2 ≤ rowL2 A i ^ 2 / ε := by
  rw [rowL2_sq_eq_counting]
  have h := spectralLeftFeature_norm_sq_le A ((n : ℝ) * ε)
    (mul_pos fin_card_real_pos hε) i
  simpa only [tableLeftFeature, div_div] using h

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; j ∈ {0,…,n-1}, assume 0 < ε. Then

(‖ tableRightFeature(A, ε, j)‖)² ≤ (columnL2(A, j))² / ε.
-/
theorem tableRightFeature_norm_sq_le (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) (j : Fin n) :
    ‖tableRightFeature A ε j‖ ^ 2 ≤ columnL2 A j ^ 2 / ε := by
  rw [columnL2_sq_eq_counting]
  have h := spectralRightFeature_norm_sq_le A ((n : ℝ) * ε)
    (mul_pos fin_card_real_pos hε) j
  simpa only [tableRightFeature, div_div] using h

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; i ∈ {0,…,n-1}, assume 0 < ε. Then

factorEnergy(tableLeftDirection(A, ε), i) ≤ (rowL2(A, i))² / ε².
-/
theorem tableLeftDirection_factorEnergy_le (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) (i : Fin n) :
    factorEnergy (tableLeftDirection A ε) i ≤ rowL2 A i ^ 2 / ε ^ 2 := by
  have h := retainedLeft_factorEnergy_le A ((n : ℝ) * ε)
    (mul_pos fin_card_real_pos hε) i
  unfold factorEnergy tableLeftDirection
  simp only [mul_pow, Real.sq_sqrt fin_card_real_pos.le, ← Finset.mul_sum]
  rw [rowL2_sq_eq_counting]
  calc
    _ ≤ (n : ℝ) * ((∑ j, A i j ^ 2) / ((n : ℝ) * ε) ^ 2) :=
      mul_le_mul_of_nonneg_left h fin_card_real_pos.le
    _ = _ := by field_simp

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): For ε>0, the uniformly normalized right singular directions retained at the inclusive threshold σⱼ ≥ ε satisfy ∑_(j:σⱼ ≥ ε) vⱼ(r)² ≤ ‖A(·,r)‖₂²/ε² at every column r. -/
theorem tableRightDirection_factorEnergy_le (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) (j : Fin n) :
    factorEnergy (tableRightDirection A ε) j ≤ columnL2 A j ^ 2 / ε ^ 2 := by
  have h := retainedRight_factorEnergy_le A ((n : ℝ) * ε)
    (mul_pos fin_card_real_pos hε) j
  unfold factorEnergy tableRightDirection
  simp only [mul_pow, Real.sq_sqrt fin_card_real_pos.le, ← Finset.mul_sum]
  rw [columnL2_sq_eq_counting]
  calc
    _ ≤ (n : ℝ) * ((∑ i, A i j ^ 2) / ((n : ℝ) * ε) ^ 2) :=
      mul_le_mul_of_nonneg_left h fin_card_real_pos.le
    _ = _ := by field_simp

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε, c ∈ ℝ, assume 0 < ε; 0 ≤ c; ‖ A‖₂ ≤ c. Then

|TableRetainedDirection(A, ε)| ≤ c² / ε².
-/
theorem tableRetainedDirection_count_le (A : Matrix (Fin n) (Fin n) ℝ)
    (ε c : ℝ) (hε : 0 < ε) (_hc : 0 ≤ c) (hA : tableL2Norm A ≤ c) :
    (Fintype.card (TableRetainedDirection A ε) : ℝ) ≤ c ^ 2 / ε ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  exact (tableRetainedDirection_count_sq_le A ε hε).trans
    (pow_le_pow_left₀ (tableL2Norm_nonneg A) hA 2)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε, L ∈ ℝ; i ∈ {0,…,n-1}, assume 0 < ε; ∀ i, rowL2(A, i) ≤ L. Then

(‖ tableLeftFeature(A, ε, i)‖)² ≤ L² / ε.
-/
theorem tableLeftFeature_norm_sq_le_of_row_bound (A : Matrix (Fin n) (Fin n) ℝ)
    (ε L : ℝ) (hε : 0 < ε) (hrow : ∀ i, rowL2 A i ≤ L) (i : Fin n) :
    ‖tableLeftFeature A ε i‖ ^ 2 ≤ L ^ 2 / ε :=
  (tableLeftFeature_norm_sq_le A ε hε i).trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (rowL2_nonneg A i) (hrow i) 2) hε.le)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε, L ∈ ℝ; j ∈ {0,…,n-1}, assume 0 < ε; ∀ j, columnL2(A, j) ≤ L. Then

(‖ tableRightFeature(A, ε, j)‖)² ≤ L² / ε.
-/
theorem tableRightFeature_norm_sq_le_of_column_bound (A : Matrix (Fin n) (Fin n) ℝ)
    (ε L : ℝ) (hε : 0 < ε) (hcol : ∀ j, columnL2 A j ≤ L) (j : Fin n) :
    ‖tableRightFeature A ε j‖ ^ 2 ≤ L ^ 2 / ε :=
  (tableRightFeature_norm_sq_le A ε hε j).trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (columnL2_nonneg A j) (hcol j) 2) hε.le)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε, L ∈ ℝ; i ∈ {0,…,n-1}, assume 0 < ε; ∀ i, rowL2(A, i) ≤ L. Then

factorEnergy(tableLeftDirection(A, ε), i) ≤ L² / ε².
-/
theorem tableLeftDirection_factorEnergy_le_of_row_bound (A : Matrix (Fin n) (Fin n) ℝ)
    (ε L : ℝ) (hε : 0 < ε) (hrow : ∀ i, rowL2 A i ≤ L) (i : Fin n) :
    factorEnergy (tableLeftDirection A ε) i ≤ L ^ 2 / ε ^ 2 :=
  (tableLeftDirection_factorEnergy_le A ε hε i).trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (rowL2_nonneg A i) (hrow i) 2)
      (sq_nonneg ε))

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε, L ∈ ℝ; j ∈ {0,…,n-1}, assume 0 < ε; ∀ j, columnL2(A, j) ≤ L. Then

factorEnergy(tableRightDirection(A, ε), j) ≤ L² / ε².
-/
theorem tableRightDirection_factorEnergy_le_of_column_bound (A : Matrix (Fin n) (Fin n) ℝ)
    (ε L : ℝ) (hε : 0 < ε) (hcol : ∀ j, columnL2 A j ≤ L) (j : Fin n) :
    factorEnergy (tableRightDirection A ε) j ≤ L ^ 2 / ε ^ 2 :=
  (tableRightDirection_factorEnergy_le A ε hε j).trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (columnL2_nonneg A j) (hcol j) 2)
      (sq_nonneg ε))

/-
Mathematical definition (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); t, ε ∈ ℝ, define

trimThenCut(A, t, ε) := tableSpectralTruncate(rowColumnTrim(A, t), ε).
-/
def trimThenCut (A : Matrix (Fin n) (Fin n) ℝ) (t ε : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  tableSpectralTruncate (rowColumnTrim A t) ε

omit [NeZero n] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B, C ∈ ℝ^({0,…,n−1} × {0,…,n−1}), we have

tableL1((A - C)) ≤ tableL1((A - B)) + tableL1((B - C)).
-/
theorem tableL1_sub_triangle (A B C : Matrix (Fin n) (Fin n) ℝ) :
    tableL1 (A - C) ≤ tableL1 (A - B) + tableL1 (B - C) := by
  have h := uavg_mono (fun p : Fin n × Fin n => abs_add_le (A p.1 p.2 - B p.1 p.2)
    (B p.1 p.2 - C p.1 p.2))
  change (uavg (fun p : Fin n × Fin n => |A p.1 p.2 - C p.1 p.2|)) ≤
    (uavg (fun p : Fin n × Fin n => |A p.1 p.2 - B p.1 p.2|)) +
    (uavg (fun p : Fin n × Fin n => |B p.1 p.2 - C p.1 p.2|))
  simpa only [sub_add_sub_cancel, uavg_add] using h

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); H, c, α ∈ ℝ, assume 0 < H; 0 < c; 0 < α; ‖ A‖₂ ≤ c. Then

tableL1((A - trimThenCut(A, (H · c), (α · c)))) ≤ 2 · c / H + √(α · c · ‖ A‖_*).
-/
theorem trimThenCut_input_loss_le (A : Matrix (Fin n) (Fin n) ℝ)
    (H c α : ℝ) (hH : 0 < H) (hc : 0 < c) (hα : 0 < α) (hA : tableL2Norm A ≤ c) :
    tableL1 (A - trimThenCut A (H * c) (α * c)) ≤
      2 * c / H + Real.sqrt (α * c * tableNuclearNorm A) := by
  have hε := mul_pos hα hc
  calc
    _ ≤ tableL1 (A - rowColumnTrim A (H * c)) +
        tableL1 (rowColumnTrim A (H * c) - trimThenCut A (H * c) (α * c)) :=
      tableL1_sub_triangle _ _ _
    _ ≤ 2 * c / H + Real.sqrt (α * c * tableNuclearNorm (rowColumnTrim A (H * c))) :=
      add_le_add (rowColumnTrim_input_loss_le A H c hH hc.le hA)
        (tableSpectralTail_tableL1_le (rowColumnTrim A (H * c)) (α * c) hε)
    _ ≤ _ := by
      apply add_le_add (le_refl _)
      apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_left (rowColumnTrim_tableNuclearNorm_le A (H * c)) hε.le

omit [NeZero n] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); t, ε ∈ ℝ, we have

‖ trimThenCut(A, t, ε)‖ₒₚ ≤ ‖ A‖ₒₚ.
-/
theorem trimThenCut_largestSingularCoefficient_le (A : Matrix (Fin n) (Fin n) ℝ) (t ε : ℝ) :
    largestSingularCoefficient (trimThenCut A t ε) ≤ largestSingularCoefficient A :=
  (tableSpectralTruncate_largestSingularCoefficient_le _ _).trans (rowColumnTrim_largestSingularCoefficient_le _ _)

omit [NeZero n] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); t, ε ∈ ℝ, we have

‖ trimThenCut(A, t, ε)‖₂ ≤ ‖ A‖₂.
-/
theorem trimThenCut_tableL2Norm_le (A : Matrix (Fin n) (Fin n) ℝ) (t ε : ℝ) :
    tableL2Norm (trimThenCut A t ε) ≤ tableL2Norm A :=
  (tableSpectralTruncate_tableL2Norm_le _ _).trans (rowColumnTrim_tableL2Norm_le _ _)

omit [NeZero n] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); t, ε ∈ ℝ, we have

‖ trimThenCut(A, t, ε)‖_* ≤ ‖ A‖_*.
-/
theorem trimThenCut_tableNuclearNorm_le (A : Matrix (Fin n) (Fin n) ℝ) (t ε : ℝ) :
    tableNuclearNorm (trimThenCut A t ε) ≤ tableNuclearNorm A :=
  (tableSpectralTruncate_tableNuclearNorm_le _ _).trans (rowColumnTrim_tableNuclearNorm_le _ _)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); H, c, α ∈ ℝ; i ∈ {0,…,n-1}, assume 0 ≤ H; 0 < c; 0 < α. Then

factorEnergy(tableLeftDirection(rowColumnTrim(A, (H · c)), (α · c)), i) ≤ H² / α².
-/
theorem trimThenCut_left_factorEnergy_le (A : Matrix (Fin n) (Fin n) ℝ)
    (H c α : ℝ) (hH : 0 ≤ H) (hc : 0 < c) (hα : 0 < α) (i : Fin n) :
    factorEnergy (tableLeftDirection (rowColumnTrim A (H * c)) (α * c)) i ≤ H ^ 2 / α ^ 2 := by
  calc
    _ ≤ (H * c) ^ 2 / (α * c) ^ 2 :=
      tableLeftDirection_factorEnergy_le_of_row_bound _ _ _ (mul_pos hα hc)
        (rowColumnTrim_rowL2_le A (H * c) (mul_nonneg hH hc.le)) i
    _ = _ := by field_simp

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); H, c, α ∈ ℝ; j ∈ {0,…,n-1}, assume 0 ≤ H; 0 < c; 0 < α. Then

factorEnergy(tableRightDirection(rowColumnTrim(A, (H · c)), (α · c)), j) ≤ H² / α².
-/
theorem trimThenCut_right_factorEnergy_le (A : Matrix (Fin n) (Fin n) ℝ)
    (H c α : ℝ) (hH : 0 ≤ H) (hc : 0 < c) (hα : 0 < α) (j : Fin n) :
    factorEnergy (tableRightDirection (rowColumnTrim A (H * c)) (α * c)) j ≤ H ^ 2 / α ^ 2 := by
  calc
    _ ≤ (H * c) ^ 2 / (α * c) ^ 2 :=
      tableRightDirection_factorEnergy_le_of_column_bound _ _ _ (mul_pos hα hc)
        (rowColumnTrim_columnL2_le A (H * c) (mul_nonneg hH hc.le)) j
    _ = _ := by field_simp

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); H, c, α ∈ ℝ; i ∈ {0,…,n-1}, assume 0 ≤ H; 0 < c; 0 < α. Then

(‖ tableLeftFeature(rowColumnTrim(A, (H · c)), (α · c), i)‖)² ≤ H² · c / α .
-/
theorem trimThenCut_leftFeature_sq_le (A : Matrix (Fin n) (Fin n) ℝ)
    (H c α : ℝ) (hH : 0 ≤ H) (hc : 0 < c) (hα : 0 < α) (i : Fin n) :
    ‖tableLeftFeature (rowColumnTrim A (H * c)) (α * c) i‖ ^ 2 ≤ H ^ 2 * c / α := by
  calc
    _ ≤ (H * c) ^ 2 / (α * c) :=
      tableLeftFeature_norm_sq_le_of_row_bound _ _ _ (mul_pos hα hc)
        (rowColumnTrim_rowL2_le A (H * c) (mul_nonneg hH hc.le)) i
    _ = _ := by field_simp

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); H, c, α ∈ ℝ; j ∈ {0,…,n-1}, assume 0 ≤ H; 0 < c; 0 < α. Then

(‖ tableRightFeature(rowColumnTrim(A, (H · c)), (α · c), j)‖)² ≤ H² · c / α.
-/
theorem trimThenCut_rightFeature_sq_le (A : Matrix (Fin n) (Fin n) ℝ)
    (H c α : ℝ) (hH : 0 ≤ H) (hc : 0 < c) (hα : 0 < α) (j : Fin n) :
    ‖tableRightFeature (rowColumnTrim A (H * c)) (α * c) j‖ ^ 2 ≤ H ^ 2 * c / α := by
  calc
    _ ≤ (H * c) ^ 2 / (α * c) :=
      tableRightFeature_norm_sq_le_of_column_bound _ _ _ (mul_pos hα hc)
        (rowColumnTrim_columnL2_le A (H * c) (mul_nonneg hH hc.le)) j
    _ = _ := by field_simp

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); H, c, α ∈ ℝ, assume 0 < c; 0 < α; ‖ A‖₂ ≤ c. Then

|TableRetainedDirection(rowColumnTrim(A, (H · c)), (α · c))| ≤ 1 / α².
-/
theorem trimThenCut_rank_le (A : Matrix (Fin n) (Fin n) ℝ)
    (H c α : ℝ) (hc : 0 < c) (hα : 0 < α) (hA : tableL2Norm A ≤ c) :
    (Fintype.card (TableRetainedDirection (rowColumnTrim A (H * c)) (α * c)) : ℝ) ≤
      1 / α ^ 2 := by
  calc
    _ ≤ c ^ 2 / (α * c) ^ 2 := tableRetainedDirection_count_le _ _ _ (mul_pos hα hc)
      hc.le ((rowColumnTrim_tableL2Norm_le A (H * c)).trans hA)
    _ = _ := by field_simp

end Nonempty

end

end TableAnalysis
