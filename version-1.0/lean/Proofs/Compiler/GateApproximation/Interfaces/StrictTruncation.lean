import Proofs.Compiler.GateApproximation.MatrixPhase.SVD



/-!
# Strict singular-value truncation of an answer table

The retained table uses exactly `σ > β` in normalized table units, including at an equality boundary. Its SVD is the concrete finite-table decomposition used by the refresh analysis. In particular, the retained-pairing identity below is proved from that decomposition; it is not an additional assumption.
-/

set_option autoImplicit false

set_option maxHeartbeats 1500000

open scoped BigOperators Matrix Matrix.Norms.L2Operator RealInnerProductSpace

namespace CircuitCompiler.SingularTruncation

open MatrixRefresh TableAnalysis RefreshAnalysis

noncomputable section

variable {n : ℕ}

/-- Retain precisely the raw singular values strictly exceeding `n * β`. Raw singular values divided by `n` are the manuscript's singular coefficients. -/
/-
Mathematical definition (normal notation): If sₖ is the ordinary Euclidean singular value of an n × n matrix, retain it exactly when its normalized coefficient sₖ/n exceeds β:

sₖ^(>β) := { sₖ, n · β<sₖ,; 0, otherwise }
-/
def strictSigma (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (k : Fin n) : ℝ :=
  if (n : ℝ) * β < (matrixSVD A).sigma k then (matrixSVD A).sigma k else 0

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; k ∈ {0,…,n-1}, we have

0 ≤ strictSigma(A, β, k).
-/
theorem strictSigma_nonneg (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (k : Fin n) :
    0 ≤ strictSigma A β k := by
  unfold strictSigma
  split_ifs
  · exact (matrixSVD A).nonneg k
  · exact le_rfl

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; k ∈ {0,…,n-1}, we have

strictSigma(A, β, k) ≤ σ(matrixSVD(A))(k).
-/
theorem strictSigma_le (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (k : Fin n) :
    strictSigma A β k ≤ (matrixSVD A).sigma k := by
  unfold strictSigma
  split_ifs
  · exact le_rfl
  · exact (matrixSVD A).nonneg k

/-- A singular coefficient at the cutoff is discarded, as the manuscript's strict inequality requires. -/
-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; k ∈ {0,…,n-1}, assume σ(matrixSVD(A))(k) = n · β. Then

strictSigma(A, β, k) = 0.
-/
theorem strictSigma_eq_zero_at_cutoff (A : Matrix (Fin n) (Fin n) ℝ)
    (β : ℝ) (k : Fin n) (hk : (matrixSVD A).sigma k = (n : ℝ) * β) :
    strictSigma A β k = 0 := by
  simp [strictSigma, hk]

/-
Mathematical definition (normal notation): If A = ∑ₖ sₖ · uₖ · vₖᵀ is its Euclidean singular-value expansion, define

A^(>β) := ∑_(k:sₖ>nβ) sₖ · uₖ · vₖᵀ.

This keeps exactly the normalized singular coefficients greater than β.
-/
def strictFinitePart (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  svdMatrix (matrixSVD A).left (matrixSVD A).right (strictSigma A β)

/-- A retained component pairs with the original table exactly as it pairs with itself: deleted singular directions are orthogonal to retained ones. -/
-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ, we have

countingPairing(A, strictFinitePart(A, β)) = matrixL2Sq(strictFinitePart(A, β)).
-/
theorem strictFinitePart_countingPairing (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) :
    countingPairing A (strictFinitePart A β) =
      matrixL2Sq (strictFinitePart A β) := by
  rw [(matrixSVD A).countingPairing_eq_sum]
  unfold strictFinitePart
  rw [svdMatrix_l2_sq]
  simp only [svdMatrix_map_basis, inner_smul_right, (matrixSVD A).left.inner_eq_ite,
    if_true, mul_one]
  apply Finset.sum_congr rfl
  intro k _
  unfold strictSigma
  split_ifs <;> ring

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ, we have

‖ strictFinitePart(A, β)‖₂ ≤ ‖ A‖₂.
-/
theorem strictFinitePart_l2 (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) :
    tableL2Norm (strictFinitePart A β) ≤ tableL2Norm A := by
  have hsq : matrixL2Sq (strictFinitePart A β) ≤
      matrixL2Sq A := by
    have hA := svdMatrix_l2_sq
      (matrixSVD A).left (matrixSVD A).right (matrixSVD A).sigma
    rw [matrixSVD_reconstruct] at hA
    unfold strictFinitePart
    rw [svdMatrix_l2_sq, hA]
    apply Finset.sum_le_sum
    intro k _
    exact pow_le_pow_left₀ (strictSigma_nonneg A β k) (strictSigma_le A β k) 2
  have hn : tableL2Norm (strictFinitePart A β) ^ 2 ≤ tableL2Norm A ^ 2 := by
    rw [tableL2Norm_sq_eq_counting, tableL2Norm_sq_eq_counting]
    exact div_le_div_of_nonneg_right hsq (sq_nonneg _)
  nlinarith [tableL2Norm_nonneg (strictFinitePart A β), tableL2Norm_nonneg A]

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; i ∈ {0,…,n-1}, we have

rowL2(strictFinitePart(A, β), i) ≤ rowL2(A, i).
-/
theorem strictFinitePart_rowL2_le (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (i : Fin n) :
    rowL2 (strictFinitePart A β) i ≤ rowL2 A i := by
  have hsum : (∑ j, strictFinitePart A β i j ^ 2) ≤ ∑ j, A i j ^ 2 := by
    rw [matrixSVD_row_sq A i]
    unfold strictFinitePart
    rw [svdMatrix_row_sq]
    exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (strictSigma_nonneg A β k) (strictSigma_le A β k) 2)
      (sq_nonneg _))
  have hs : rowL2 (strictFinitePart A β) i ^ 2 ≤ rowL2 A i ^ 2 := by
    rw [rowL2_sq_eq_counting, rowL2_sq_eq_counting]
    exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)
  nlinarith [rowL2_nonneg (strictFinitePart A β) i, rowL2_nonneg A i]

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; j ∈ {0,…,n-1}, we have

columnL2(strictFinitePart(A, β), j) ≤ columnL2(A, j).
-/
theorem strictFinitePart_columnL2_le (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (j : Fin n) :
    columnL2 (strictFinitePart A β) j ≤ columnL2 A j := by
  have hsum : (∑ i, strictFinitePart A β i j ^ 2) ≤ ∑ i, A i j ^ 2 := by
    rw [matrixSVD_column_sq A j]
    unfold strictFinitePart
    rw [svdMatrix_column_sq]
    exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (strictSigma_nonneg A β k) (strictSigma_le A β k) 2)
      (sq_nonneg _))
  have hs : columnL2 (strictFinitePart A β) j ^ 2 ≤ columnL2 A j ^ 2 := by
    rw [columnL2_sq_eq_counting, columnL2_sq_eq_counting]
    exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)
  nlinarith [columnL2_nonneg (strictFinitePart A β) j, columnL2_nonneg A j]

/-- The exact nuclear coefficient sum for the strictly retained table. -/
-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ, we have

‖ strictFinitePart(A, β)‖_* = (∑ₖ (strictSigma(A, β, k))) / n.
-/
theorem strictFinitePart_nuclear_eq (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) :
    tableNuclearNorm (strictFinitePart A β) = (∑ k, strictSigma A β k) / (n : ℝ) := by
  unfold tableNuclearNorm strictFinitePart
  rw [(svdMatrix_decomposition (matrixSVD A).left (matrixSVD A).right
    (strictSigma A β) (strictSigma_nonneg A β)).nuclearNorm_eq_sum_sigma]
  simp only [Fintype.card_fin, svdMatrix_decomposition]

/-
Mathematical definition (normal notation): Keep the complementary singular coefficients, including equality at the threshold:

sₖ^(≤ β) := { 0, n · β<sₖ,; sₖ, otherwise }

Here sₖ denotes an ordinary Euclidean singular value.
-/
def strictDiscardedSigma (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (k : Fin n) : ℝ :=
  if (n : ℝ) * β < (matrixSVD A).sigma k then 0 else (matrixSVD A).sigma k

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; k ∈ {0,…,n-1}, we have

0 ≤ strictDiscardedSigma(A, β, k).
-/
theorem strictDiscardedSigma_nonneg (A : Matrix (Fin n) (Fin n) ℝ)
    (β : ℝ) (k : Fin n) : 0 ≤ strictDiscardedSigma A β k := by
  unfold strictDiscardedSigma
  split_ifs
  · exact le_rfl
  · exact (matrixSVD A).nonneg k

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ, we have

A - strictFinitePart(A, β) = svdMatrix(left(matrixSVD(A)), right(matrixSVD(A)), strictDiscardedSigma(A, β)).
-/
theorem strictFinitePart_tail_eq (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) :
    A - strictFinitePart A β =
      svdMatrix (matrixSVD A).left (matrixSVD A).right (strictDiscardedSigma A β) := by
  ext i j
  change A i j - (∑ k, strictSigma A β k * (matrixSVD A).left k i *
    (matrixSVD A).right k j) = _
  rw [matrixSVD_entry A i j, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  unfold strictSigma strictDiscardedSigma
  split_ifs <;> ring

/-- The discarded tail includes the equality case and has normalized operator norm at most the cutoff. -/
-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ, assume n ≠ 0; 0 ≤ β. Then

‖ (A - strictFinitePart(A, β))‖ₒₚ ≤ β.
-/
theorem strictFinitePart_tail_op [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (hβ : 0 ≤ β) :
    largestSingularCoefficient (A - strictFinitePart A β) ≤ β := by
  have hn := fin_card_real_pos (n := n)
  have hraw : ‖A - strictFinitePart A β‖ ≤ (n : ℝ) * β := by
    change ‖(A - strictFinitePart A β).toEuclideanLin.toContinuousLinearMap‖ ≤ _
    rw [strictFinitePart_tail_eq,
      (svdMatrix_decomposition (matrixSVD A).left (matrixSVD A).right
        (strictDiscardedSigma A β) (strictDiscardedSigma_nonneg A β)).operator_norm]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hn.le hβ)).mpr
    intro k
    change ‖strictDiscardedSigma A β k‖ ≤ (n : ℝ) * β
    rw [Real.norm_of_nonneg (strictDiscardedSigma_nonneg A β k)]
    unfold strictDiscardedSigma
    split_ifs with hk
    · exact mul_nonneg hn.le hβ
    · exact le_of_not_gt hk
  unfold largestSingularCoefficient
  simp only [Fintype.card_fin]
  exact (div_le_iff₀ hn).mpr (by simpa only [mul_comm] using hraw)

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ, assume n ≠ 0; ‖ A‖ₒₚ ≤ β. Then

strictFinitePart(A, β) = 0.
-/
theorem strictFinitePart_eq_zero_of_op_le [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (hA : largestSingularCoefficient A ≤ β) :
    strictFinitePart A β = 0 := by
  have hcoeff (k : Fin n) : strictSigma A β k = 0 := by
    have hk := (tableSingularValue_le_largestSingularCoefficient A k).trans hA
    have hraw : (matrixSVD A).sigma k ≤ (n : ℝ) * β := by
      simpa only [mul_comm] using (div_le_iff₀ (fin_card_real_pos (n := n))).mp hk
    simp [strictSigma, not_lt_of_ge hraw]
  ext i j
  simp only [strictFinitePart, svdMatrix, hcoeff, zero_mul, Finset.sum_const_zero,
    Matrix.zero_apply]

/-- Square-root-weighted features, with zero coordinates for discarded directions. Keeping zero coordinates avoids an extra subtype of indices. -/
/-
Mathematical definition (normal notation): The left factor vector at coordinate i has components

√(sₖ^(>β)) · uₖ(i),

where sₖ and uₖ are the Euclidean singular values and singular vectors. Discarded directions have zero coordinates.
-/
def strictFiniteLeft (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun k => Real.sqrt (strictSigma A β k) * (matrixSVD A).left k i)

/-
Mathematical definition (normal notation): The right factor vector at coordinate i has components

√(sₖ^(>β)) · vₖ(i),

where sₖ and vₖ are the Euclidean singular values and singular vectors. Discarded directions have zero coordinates.
-/
def strictFiniteRight (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (j : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun k => Real.sqrt (strictSigma A β k) * (matrixSVD A).right k j)

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; i, j ∈ {0,…,n-1}, we have

strictFinitePart(A, β, i, j) = inner(ℝ, strictFiniteLeft(A, β, i), strictFiniteRight(A, β, j)).
-/
theorem strictFinitePart_factorization (A : Matrix (Fin n) (Fin n) ℝ)
    (β : ℝ) (i j : Fin n) :
    strictFinitePart A β i j =
      inner ℝ (strictFiniteLeft A β i) (strictFiniteRight A β j) := by
  simp only [strictFinitePart, svdMatrix, strictFiniteLeft, strictFiniteRight,
    PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro k _
  have hs := Real.mul_self_sqrt (strictSigma_nonneg A β k)
  calc
    _ = (Real.sqrt (strictSigma A β k) * Real.sqrt (strictSigma A β k)) *
        ((matrixSVD A).left k i * (matrixSVD A).right k j) := by rw [hs]; ring
    _ = _ := by ring

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; i ∈ {0,…,n-1}, we have

(‖ strictFiniteLeft(A, β, i)‖)² = ∑ₖ (strictSigma(A, β, k) · (left(matrixSVD(A))(k, i))²) .
-/
theorem strictFiniteLeft_norm_sq (A : Matrix (Fin n) (Fin n) ℝ)
    (β : ℝ) (i : Fin n) :
    ‖strictFiniteLeft A β i‖ ^ 2 =
      ∑ k, strictSigma A β k * (matrixSVD A).left k i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [strictFiniteLeft, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (strictSigma_nonneg A β _)]

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; j ∈ {0,…,n-1}, we have

(‖ strictFiniteRight(A, β, j)‖)² = ∑ₖ (strictSigma(A, β, k) · (right(matrixSVD(A))(k, j))²).
-/
theorem strictFiniteRight_norm_sq (A : Matrix (Fin n) (Fin n) ℝ)
    (β : ℝ) (j : Fin n) :
    ‖strictFiniteRight A β j‖ ^ 2 =
      ∑ k, strictSigma A β k * (matrixSVD A).right k j ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [strictFiniteRight, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (strictSigma_nonneg A β _)]

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; k ∈ {0,…,n-1}, we have

(n · β) · strictSigma(A, β, k) ≤ (σ(matrixSVD(A))(k))².
-/
theorem cutoff_mul_strictSigma_le (A : Matrix (Fin n) (Fin n) ℝ)
    (β : ℝ) (k : Fin n) :
    ((n : ℝ) * β) * strictSigma A β k ≤ (matrixSVD A).sigma k ^ 2 := by
  unfold strictSigma
  split_ifs with hk
  · simpa only [sq] using mul_le_mul_of_nonneg_right hk.le ((matrixSVD A).nonneg k)
  · simpa only [mul_zero] using sq_nonneg ((matrixSVD A).sigma k)

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ, assume n ≠ 0; 0 < β. Then

‖ strictFinitePart(A, β)‖_* ≤ (‖ A‖₂)² / β.
-/
theorem strictFinitePart_nuclear_le [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (hβ : 0 < β) :
    tableNuclearNorm (strictFinitePart A β) ≤ tableL2Norm A ^ 2 / β := by
  have hn := fin_card_real_pos (n := n)
  have hA := svdMatrix_l2_sq
    (matrixSVD A).left (matrixSVD A).right (matrixSVD A).sigma
  rw [matrixSVD_reconstruct] at hA
  have hs : (∑ k, strictSigma A β k) ≤ matrixL2Sq A / ((n : ℝ) * β) := by
    apply (le_div_iff₀ (mul_pos hn hβ)).mpr
    rw [Finset.sum_mul, hA]
    exact Finset.sum_le_sum (fun k _ => by
      simpa only [mul_comm] using cutoff_mul_strictSigma_le A β k)
  rw [strictFinitePart_nuclear_eq, tableL2Norm_sq_eq_counting]
  calc
    _ ≤ (matrixL2Sq A / ((n : ℝ) * β)) / n :=
      div_le_div_of_nonneg_right hs hn.le
    _ = _ := by ring

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; i ∈ {0,…,n-1}, assume n ≠ 0; 0 < β. Then

(‖ strictFiniteLeft(A, β, i)‖)² ≤ (rowL2(A, i))² / β.
-/
theorem strictFiniteLeft_energy [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (hβ : 0 < β) (i : Fin n) :
    ‖strictFiniteLeft A β i‖ ^ 2 ≤ rowL2 A i ^ 2 / β := by
  have hn := fin_card_real_pos (n := n)
  have h : ‖strictFiniteLeft A β i‖ ^ 2 ≤
      (∑ j, A i j ^ 2) / ((n : ℝ) * β) := by
    apply (le_div_iff₀ (mul_pos hn hβ)).mpr
    rw [strictFiniteLeft_norm_sq, matrixSVD_row_sq A i, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    have hk := mul_le_mul_of_nonneg_right (cutoff_mul_strictSigma_le A β k)
      (sq_nonneg ((matrixSVD A).left k i))
    nlinarith only [hk]
  rw [rowL2_sq_eq_counting, div_div]
  exact h

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; j ∈ {0,…,n-1}, assume n ≠ 0; 0 < β. Then

(‖ strictFiniteRight(A, β, j)‖)² ≤ (columnL2(A, j))² / β.
-/
theorem strictFiniteRight_energy [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (hβ : 0 < β) (j : Fin n) :
    ‖strictFiniteRight A β j‖ ^ 2 ≤ columnL2 A j ^ 2 / β := by
  have hn := fin_card_real_pos (n := n)
  have h : ‖strictFiniteRight A β j‖ ^ 2 ≤
      (∑ i, A i j ^ 2) / ((n : ℝ) * β) := by
    apply (le_div_iff₀ (mul_pos hn hβ)).mpr
    rw [strictFiniteRight_norm_sq, matrixSVD_column_sq A j, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    have hk := mul_le_mul_of_nonneg_right (cutoff_mul_strictSigma_le A β k)
      (sq_nonneg ((matrixSVD A).right k j))
    nlinarith only [hk]
  rw [columnL2_sq_eq_counting, div_div]
  exact h

variable {I : Type*} [Fintype I]

/-- The exact manuscript cutoff on an arbitrary finite table carrier. -/
/-
Mathematical definition (normal notation): For a real table A on an arbitrary finite square carrier, define

A^(>β) := ∑_(k:σₖ>β) σₖ · uₖ · vₖᵀ,

using the paper's normalized orthonormal expansion. Reindexing the carrier through a finite coordinate set makes this a concrete matrix construction.
-/
def strictTruncation (A : Matrix I I ℝ) (β : ℝ) : Matrix I I ℝ :=
  reindexTable (strictFinitePart (svdFiniteTable A) β)
    (Fintype.equivFin I).symm (Fintype.equivFin I).symm

/-
Mathematical definition (normal notation): For the normalized expansion of A, use the factor vector

(√σₖ · uₖ(i))_(σₖ>β),

with zero coordinates in discarded directions. These square-root-weighted factors reconstruct A^(>β).
-/
def truncationLeftFactor (A : Matrix I I ℝ) (β : ℝ) (i : I) :
    EuclideanSpace ℝ (Fin (Fintype.card I)) :=
  strictFiniteLeft (svdFiniteTable A) β (Fintype.equivFin I i)

/-
Mathematical definition (normal notation): For the normalized expansion of A, use the factor vector

(√σₖ · vₖ(i))_(σₖ>β),

with zero coordinates in discarded directions. These square-root-weighted factors reconstruct A^(>β).
-/
def truncationRightFactor (A : Matrix I I ℝ) (β : ℝ) (i : I) :
    EuclideanSpace ℝ (Fin (Fintype.card I)) :=
  strictFiniteRight (svdFiniteTable A) β (Fintype.equivFin I i)


/-
Mathematical statement (normal notation): For every real square table A and every threshold β, retaining only singular coefficients strictly exceeding β cannot increase its normalized L₂ norm:

‖A^(>β)‖₂ ≤ ‖A‖₂.
-/
theorem strictTruncation_l2 (A : Matrix I I ℝ) (β : ℝ) :
    tableL2Norm (strictTruncation A β) ≤ tableL2Norm A := by
  unfold strictTruncation
  rw [reindexTable_tableL2Norm]
  exact (strictFinitePart_l2 _ _).trans_eq (reindexTable_tableL2Norm _ _ _)

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; i ∈ I, we have

rowL2(strictTruncation(A, β), i) ≤ rowL2(A, i).
-/
theorem strictTruncation_rowL2_le (A : Matrix I I ℝ) (β : ℝ) (i : I) :
    rowL2 (strictTruncation A β) i ≤ rowL2 A i := by
  have hl : rowL2 (strictTruncation A β) i =
      rowL2 (strictFinitePart (svdFiniteTable A) β) (Fintype.equivFin I i) := by
    unfold rowL2 strictTruncation reindexTable
    congr 1
    exact uavg_equiv (Fintype.equivFin I) (fun j =>
      strictFinitePart (svdFiniteTable A) β (Fintype.equivFin I i) j ^ 2)
  have hr : rowL2 (svdFiniteTable A) (Fintype.equivFin I i) = rowL2 A i := by
    unfold rowL2 svdFiniteTable reindexTable
    simp only [Equiv.symm_apply_apply]
    congr 1
    exact uavg_equiv (Fintype.equivFin I).symm (fun j => A i j ^ 2)
  rw [hl, ← hr]
  exact strictFinitePart_rowL2_le _ _ _

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; j ∈ I, we have

columnL2(strictTruncation(A, β), j) ≤ columnL2(A, j).
-/
theorem strictTruncation_columnL2_le (A : Matrix I I ℝ) (β : ℝ) (j : I) :
    columnL2 (strictTruncation A β) j ≤ columnL2 A j := by
  have hl : columnL2 (strictTruncation A β) j =
      columnL2 (strictFinitePart (svdFiniteTable A) β) (Fintype.equivFin I j) := by
    unfold columnL2 strictTruncation reindexTable
    congr 1
    exact uavg_equiv (Fintype.equivFin I) (fun i =>
      strictFinitePart (svdFiniteTable A) β i (Fintype.equivFin I j) ^ 2)
  have hr : columnL2 (svdFiniteTable A) (Fintype.equivFin I j) = columnL2 A j := by
    unfold columnL2 svdFiniteTable reindexTable
    simp only [Equiv.symm_apply_apply]
    congr 1
    exact uavg_equiv (Fintype.equivFin I).symm (fun i => A i j ^ 2)
  rw [hl, ← hr]
  exact strictFinitePart_columnL2_le _ _ _

/-- The nuclear norm is exactly the sum of the retained normalized singular coefficients, with a zero summand for each discarded direction. -/
-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

‖ strictTruncation(A, β)‖_* = (∑ₖ (strictSigma(svdFiniteTable(A), β, k))) / |I|.
-/
theorem strictTruncation_nuclear_eq [DecidableEq I] (A : Matrix I I ℝ) (β : ℝ) :
    tableNuclearNorm (strictTruncation A β) =
      (∑ k, strictSigma (svdFiniteTable A) β k) / (Fintype.card I : ℝ) := by
  classical
  unfold strictTruncation
  rw [reindexTable_tableNuclearNorm, strictFinitePart_nuclear_eq]

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, assume I ≠ ∅; 0 < β. Then

‖ strictTruncation(A, β)‖_* ≤ (‖ A‖₂)² / β.
-/
theorem strictTruncation_nuclear_le_l2 [DecidableEq I] [Nonempty I]
    (A : Matrix I I ℝ) (β : ℝ) (hβ : 0 < β) :
    tableNuclearNorm (strictTruncation A β) ≤ tableL2Norm A ^ 2 / β := by
  classical
  letI : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  unfold strictTruncation
  rw [reindexTable_tableNuclearNorm]
  simpa only [svdFiniteTable, reindexTable_tableL2Norm] using
    strictFinitePart_nuclear_le (svdFiniteTable A) β hβ

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, assume I ≠ ∅; 0 < β; ∀ i, j, |A(i, j)| ≤ 1. Then

‖ strictTruncation(A, β)‖_* ≤ 1 / β.
-/
theorem strictTruncation_nuclear_le [DecidableEq I] [Nonempty I]
    (A : Matrix I I ℝ) (β : ℝ) (hβ : 0 < β) (hA : ∀ i j, |A i j| ≤ 1) :
    tableNuclearNorm (strictTruncation A β) ≤ 1 / β := by
  apply (strictTruncation_nuclear_le_l2 A β hβ).trans
  apply div_le_div_of_nonneg_right _ hβ.le
  simpa only [one_pow] using
    (sq_le_sq₀ (tableL2Norm_nonneg A) zero_le_one).2 (tableL2Norm_le_one_of_entry_bound A hA)

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, assume I ≠ ∅; 0 ≤ β. Then

‖ (A - strictTruncation(A, β))‖ₒₚ ≤ β.
-/
theorem strictTruncation_tail_op [DecidableEq I] [Nonempty I]
    (A : Matrix I I ℝ) (β : ℝ) (hβ : 0 ≤ β) :
    largestSingularCoefficient (A - strictTruncation A β) ≤ β := by
  classical
  letI : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  have he : A - strictTruncation A β =
      reindexTable (svdFiniteTable A - strictFinitePart (svdFiniteTable A) β)
        (Fintype.equivFin I).symm (Fintype.equivFin I).symm := by
    ext i j
    simp [strictTruncation, svdFiniteTable, reindexTable]
  rw [he, reindexTable_largestSingularCoefficient]
  exact strictFinitePart_tail_op _ _ hβ

/-- Once the cutoff reaches the largest singular coefficient, every direction is discarded. This includes equality at the cutoff. -/
-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, assume I ≠ ∅; ‖ A‖ₒₚ ≤ β. Then

strictTruncation(A, β) = 0.
-/
theorem strictTruncation_eq_zero_of_op_le [DecidableEq I] [Nonempty I]
    (A : Matrix I I ℝ) (β : ℝ) (hA : largestSingularCoefficient A ≤ β) :
    strictTruncation A β = 0 := by
  classical
  letI : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  have hfinite : largestSingularCoefficient (svdFiniteTable A) ≤ β := by
    simpa only [svdFiniteTable, reindexTable_largestSingularCoefficient] using hA
  unfold strictTruncation
  rw [strictFinitePart_eq_zero_of_op_le _ _ hfinite]
  rfl

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I), assume I ≠ ∅. Then

strictTruncation(A, ‖ A‖ₒₚ) = 0.
-/
theorem strictTruncation_eq_zero_at_op [DecidableEq I] [Nonempty I] (A : Matrix I I ℝ) :
    strictTruncation A (largestSingularCoefficient A) = 0 :=
  strictTruncation_eq_zero_of_op_le A (largestSingularCoefficient A) le_rfl

/-- The definitions also cover an empty carrier, whose only table is zero. -/
-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, assume IsEmpty(I). Then

strictTruncation(A, β) = 0.
-/
theorem strictTruncation_eq_zero_of_isEmpty [IsEmpty I]
    (A : Matrix I I ℝ) (β : ℝ) : strictTruncation A β = 0 := by
  ext i
  exact isEmptyElim i

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; i, j ∈ I, we have

strictTruncation(A, β, i, j) = inner(ℝ, truncationLeftFactor(A, β, i), truncationRightFactor(A, β, j)).
-/
theorem strictTruncation_factorization (A : Matrix I I ℝ) (β : ℝ) (i j : I) :
    strictTruncation A β i j =
      inner ℝ (truncationLeftFactor A β i) (truncationRightFactor A β j) :=
  strictFinitePart_factorization _ _ _ _

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For J a set; A, B ∈ ℝ^(I × I); e, f ∈ I ≃ J, assume J is finite. Then

pairing(reindexTable(A, e, f), reindexTable(B, e, f)) = pairing(A, B).
-/
theorem reindexTable_pairing {J : Type*} [Fintype J]
    (A B : Matrix I I ℝ) (e f : I ≃ J) :
    pairing (reindexTable A e f) (reindexTable B e f) = pairing A B := by
  unfold pairing reindexTable
  calc
    _ = uavg (fun i => uavg (fun j => A (e.symm i) j * B (e.symm i) j)) := by
      apply uavg_congr
      intro i
      exact uavg_equiv f.symm (fun j => A (e.symm i) j * B (e.symm i) j)
    _ = _ := uavg_equiv e.symm (fun i => uavg (fun j => A i j * B i j))

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B ∈ ℝ^(I × I), we have

pairing(A, B) = countingPairing(A, B) / (|I|)².
-/
theorem pairing_eq_countingPairing_div_card (A B : Matrix I I ℝ) :
    pairing A B = countingPairing A B / (Fintype.card I : ℝ) ^ 2 := by
  simp only [pairing, uavg, countingPairing, ← Finset.mul_sum, div_eq_mul_inv, pow_two]
  ring

/-- Exact retained-pairing identity in the normalized uniform convention. -/
-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

pairing(A, strictTruncation(A, β)) = (‖ strictTruncation(A, β)‖₂)².
-/
theorem strictTruncation_pairing (A : Matrix I I ℝ) (β : ℝ) :
    pairing A (strictTruncation A β) = tableL2Norm (strictTruncation A β) ^ 2 := by
  have hp : pairing (svdFiniteTable A) (strictFinitePart (svdFiniteTable A) β) =
      tableL2Norm (strictFinitePart (svdFiniteTable A) β) ^ 2 := by
    rw [pairing_eq_countingPairing_div_card, tableL2Norm_sq_eq_counting,
      strictFinitePart_countingPairing, Fintype.card_fin]
  have hr := reindexTable_pairing (svdFiniteTable A)
    (strictFinitePart (svdFiniteTable A) β)
    (Fintype.equivFin I).symm (Fintype.equivFin I).symm
  simpa only [strictTruncation, svdFiniteTable, reindexTable_inverse,
    reindexTable_tableL2Norm] using hr.trans hp


/-
Mathematical statement (normal notation): Let A be a real square table on a nonempty finite set, with |A(i,j)| ≤ 1 at every entry, and let β>0. For the chosen square-root-weighted singular factors of A^(>β),

∑ₖ aₖ(i)² ≤ 1/β for every i.

The squared Euclidean norm of the factor vector is precisely this sum.
-/
theorem truncationLeftFactor_energy [Nonempty I] (A : Matrix I I ℝ) (β : ℝ) (hβ : 0 < β)
    (hA : ∀ i j, |A i j| ≤ 1) (i : I) : ‖truncationLeftFactor A β i‖ ^ 2 ≤ 1 / β := by
  letI : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  apply (strictFiniteLeft_energy _ _ hβ _).trans
  apply div_le_div_of_nonneg_right _ hβ.le
  simpa only [one_pow] using (sq_le_sq₀ (rowL2_nonneg (svdFiniteTable A) _) zero_le_one).2
    (rowL2_le_one_of_entry_bound _ (fun x y => hA _ _) _)


/-
Mathematical statement (normal notation): Let A be a real square table on a nonempty finite set, with |A(i,j)| ≤ 1 at every entry, and let β>0. For the chosen square-root-weighted singular factors of A^(>β),

∑ₖ bₖ(j)² ≤ 1/β for every j.

The squared Euclidean norm of the factor vector is precisely this sum.
-/
theorem truncationRightFactor_energy [Nonempty I] (A : Matrix I I ℝ) (β : ℝ) (hβ : 0 < β)
    (hA : ∀ i j, |A i j| ≤ 1) (j : I) : ‖truncationRightFactor A β j‖ ^ 2 ≤ 1 / β := by
  letI : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  apply (strictFiniteRight_energy _ _ hβ _).trans
  apply div_le_div_of_nonneg_right _ hβ.le
  simpa only [one_pow] using (sq_le_sq₀ (columnL2_nonneg (svdFiniteTable A) _) zero_le_one).2
    (columnL2_le_one_of_entry_bound _ (fun x y => hA _ _) _)

end

end CircuitCompiler.SingularTruncation
