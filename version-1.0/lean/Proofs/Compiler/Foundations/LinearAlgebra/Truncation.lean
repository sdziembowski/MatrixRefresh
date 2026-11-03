import Proofs.Compiler.Foundations.LinearAlgebra.SchurMultiplier
import Proofs.Compiler.Foundations.LinearAlgebra.SingularValues



/-!
# Spectral truncation of finite real matrices

The truncation is formed from a genuine singular-value decomposition, and retains precisely the singular values at least the positive cutoff. The matrix and vector norms here use counting-measure Euclidean conventions.
-/

set_option autoImplicit false

open scoped BigOperators RealInnerProductSpace Matrix Matrix.Norms.L2Operator

open WithLp

noncomputable section

namespace TableAnalysis

variable {n : ℕ}

/-- A matrix diagonal between two specified Euclidean orthonormal bases. -/
/- Mathematical definition (normal notation): Given Euclidean orthonormal bases (uⱼ),(vⱼ) and real coefficients cⱼ, define A := ∑ⱼ cⱼ · uⱼ · vⱼᵀ. -/
def svdMatrix (u v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (c : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ k, c k * u k i * v k j

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For v ∈ OrthonormalBasis({0,…,n-1}, ℝ, EuclideanSpace(ℝ, {0,…,n-1})); k, l ∈ {0,…,n-1}, we have

(∑ⱼ (v(k, j) · v(l, j))) = { 1 if k = l,; 0 otherwise }.
-/
theorem orthonormalBasis_coordinate_inner
    (v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (k l : Fin n) :
    (∑ j, v k j * v l j) = if k = l then 1 else 0 := by
  simpa [PiLp.inner_apply, mul_comm] using v.inner_eq_ite k l

/-- The diagonal-basis matrix has the prescribed action on its right basis. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u, v ∈ OrthonormalBasis({0,…,n-1}, ℝ, EuclideanSpace(ℝ, {0,…,n-1})); c ∈ {0,…,n-1} → ℝ; l ∈ {0,…,n-1}, we have

toEuclideanLin(svdMatrix(u, v, c))(v(l)) = c(l) · u(l).
-/
theorem svdMatrix_map_basis
    (u v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (c : Fin n → ℝ) (l : Fin n) :
    (svdMatrix u v c).toEuclideanLin (v l) = c l • u l := by
  ext i
  change (∑ j, (∑ k, c k * u k i * v k j) * v l j) = c l * u l i
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have he (k : Fin n) :
      (∑ j, c k * u k i * v k j * v l j) =
        c k * u k i * (∑ j, v k j * v l j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he, orthonormalBasis_coordinate_inner]
  simp

/-- Any nonnegative diagonal coefficients give an SVD with these same bases. -/
/- Mathematical definition (normal notation): If all cⱼ ≥ 0, the bases (uⱼ),(vⱼ) with coefficients (cⱼ) form a singular-value decomposition of ∑ⱼ cⱼ · uⱼ · vⱼᵀ. -/
def svdMatrix_decomposition
    (u v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (c : Fin n → ℝ) (hc : ∀ k, 0 ≤ c k) :
    RealSVD (svdMatrix u v c).toEuclideanLin n where
  left := u
  right := v
  sigma := c
  nonneg := hc
  map_basis := svdMatrix_map_basis u v c

/-- The Euclidean squared norm of a linear combination of an orthonormal basis is the sum of squares of its coefficients. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For v ∈ OrthonormalBasis({0,…,n-1}, ℝ, EuclideanSpace(ℝ, {0,…,n-1})); c ∈ {0,…,n-1} → ℝ, we have

(‖ ∑ₖ (c(k) · v(k))‖)² = ∑ₖ ((c(k))²).
-/
theorem orthonormalBasis_sum_norm_sq
    (v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (c : Fin n → ℝ) : ‖∑ k, c k • v k‖ ^ 2 = ∑ k, c k ^ 2 := by
  rw [← v.sum_sq_inner_right]
  simp [inner_sum, inner_smul_right, v.inner_eq_ite]

/-- Row Parseval identity for a diagonal-basis matrix. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u, v ∈ OrthonormalBasis({0,…,n-1}, ℝ, EuclideanSpace(ℝ, {0,…,n-1})); c ∈ {0,…,n-1} → ℝ; i ∈ {0,…,n-1}, we have

(∑ⱼ ((svdMatrix(u, v, c, i, j))²)) = ∑ₖ ((c(k))² · (u(k, i))²).
-/
theorem svdMatrix_row_sq
    (u v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (c : Fin n → ℝ) (i : Fin n) :
    (∑ j, svdMatrix u v c i j ^ 2) = ∑ k, c k ^ 2 * u k i ^ 2 := by
  have he : toLp 2 (fun j => svdMatrix u v c i j) =
      ∑ k, (c k * u k i) • v k := by
    ext j
    simp [svdMatrix, Finset.sum_apply, mul_assoc]
  have h := orthonormalBasis_sum_norm_sq v (fun k => c k * u k i)
  rw [← he, EuclideanSpace.norm_sq_eq] at h
  simpa only [ofLp_toLp, Real.norm_eq_abs, sq_abs, mul_pow] using h

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u, v ∈ OrthonormalBasis({0,…,n-1}, ℝ, EuclideanSpace(ℝ, {0,…,n-1})); c ∈ {0,…,n-1} → ℝ, we have

transpose(svdMatrix(u, v, c)) = svdMatrix(v, u, c).
-/
theorem svdMatrix_transpose
    (u v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (c : Fin n → ℝ) : (svdMatrix u v c).transpose = svdMatrix v u c := by
  ext i j
  simp only [Matrix.transpose_apply, svdMatrix]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Column Parseval identity for a diagonal-basis matrix. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u, v ∈ OrthonormalBasis({0,…,n-1}, ℝ, EuclideanSpace(ℝ, {0,…,n-1})); c ∈ {0,…,n-1} → ℝ; j ∈ {0,…,n-1}, we have

(∑ᵢ ((svdMatrix(u, v, c, i, j))²)) = ∑ₖ ((c(k))² · (v(k, j))²).
-/
theorem svdMatrix_column_sq
    (u v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (c : Fin n → ℝ) (j : Fin n) :
    (∑ i, svdMatrix u v c i j ^ 2) = ∑ k, c k ^ 2 * v k j ^ 2 := by
  have h := svdMatrix_row_sq v u c j
  rw [← svdMatrix_transpose] at h
  exact h

/-- Reconstructing the genuine SVD returns the original matrix. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}), we have

svdMatrix(left(matrixSVD(A)), right(matrixSVD(A)), σ(matrixSVD(A))) = A.
-/
theorem matrixSVD_reconstruct (A : Matrix (Fin n) (Fin n) ℝ) :
    svdMatrix (matrixSVD A).left (matrixSVD A).right (matrixSVD A).sigma = A := by
  ext i j
  exact (matrixSVD_entry A i j).symm

/-- Counting-measure L2 identity for a diagonal-basis matrix. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u, v ∈ OrthonormalBasis({0,…,n-1}, ℝ, EuclideanSpace(ℝ, {0,…,n-1})); c ∈ {0,…,n-1} → ℝ, we have

matrixL2Sq(svdMatrix(u, v, c)) = ∑ₖ ((c(k))²).
-/
theorem svdMatrix_l2_sq
    (u v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (c : Fin n → ℝ) :
    matrixL2Sq (svdMatrix u v c) = ∑ k, c k ^ 2 := by
  unfold matrixL2Sq
  simp_rw [svdMatrix_row_sq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.mul_sum]
  have hu : (∑ i, u k i ^ 2) = 1 := by
    simpa only [sq, if_true] using orthonormalBasis_coordinate_inner u k k
  rw [hu, mul_one]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); i ∈ {0,…,n-1}, we have

(∑ⱼ ((A(i, j))²)) = ∑ₖ ((σ(matrixSVD(A))(k))² · (left(matrixSVD(A))(k, i))²) .
-/
theorem matrixSVD_row_sq (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (∑ j, A i j ^ 2) = ∑ k, (matrixSVD A).sigma k ^ 2 * (matrixSVD A).left k i ^ 2 := by
  simpa only [matrixSVD_reconstruct] using
    svdMatrix_row_sq (matrixSVD A).left (matrixSVD A).right (matrixSVD A).sigma i

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); j ∈ {0,…,n-1}, we have

(∑ᵢ ((A(i, j))²)) = ∑ₖ ((σ(matrixSVD(A))(k))² · (right(matrixSVD(A))(k, j))²).
-/
theorem matrixSVD_column_sq (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    (∑ i, A i j ^ 2) = ∑ k, (matrixSVD A).sigma k ^ 2 * (matrixSVD A).right k j ^ 2 := by
  simpa only [matrixSVD_reconstruct] using
    svdMatrix_column_sq (matrixSVD A).left (matrixSVD A).right (matrixSVD A).sigma j

/-- The singular values retained at the specified cutoff. -/
/- Mathematical definition (normal notation): Define σⱼ^keep := σⱼ when σⱼ ≥ ε, and 0 otherwise. These are Euclidean singular coefficients and the auxiliary cutoff is inclusive. -/
def retainedSigma (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (k : Fin n) : ℝ :=
  if ε ≤ (matrixSVD A).sigma k then (matrixSVD A).sigma k else 0

/-- The singular values discarded at the specified cutoff. -/
/- Mathematical definition (normal notation): Define σⱼ^tail := σⱼ when σⱼ<ε, and 0 otherwise. These are the coefficients discarded by the inclusive Euclidean cutoff. -/
def discardedSigma (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (k : Fin n) : ℝ :=
  if ε ≤ (matrixSVD A).sigma k then 0 else (matrixSVD A).sigma k

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; k ∈ {0,…,n-1}, we have

0 ≤ retainedSigma(A, ε, k).
-/
theorem retainedSigma_nonneg (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (k : Fin n) :
    0 ≤ retainedSigma A ε k := by
  unfold retainedSigma
  split_ifs
  · exact (matrixSVD A).nonneg k
  · exact le_rfl

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; k ∈ {0,…,n-1}, we have

retainedSigma(A, ε, k) ≤ σ(matrixSVD(A))(k).
-/
theorem retainedSigma_le (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (k : Fin n) :
    retainedSigma A ε k ≤ (matrixSVD A).sigma k := by
  unfold retainedSigma
  split_ifs
  · exact le_rfl
  · exact (matrixSVD A).nonneg k

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; k ∈ {0,…,n-1}, we have

(retainedSigma(A, ε, k))² ≤ (σ(matrixSVD(A))(k))².
-/
theorem retainedSigma_sq_le (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (k : Fin n) :
    retainedSigma A ε k ^ 2 ≤ (matrixSVD A).sigma k ^ 2 :=
  pow_le_pow_left₀ (retainedSigma_nonneg A ε k) (retainedSigma_le A ε k) 2

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, we have

(∑ₖ (retainedSigma(A, ε, k))) ≤ ∑ₖ (σ(matrixSVD(A))(k)).
-/
theorem retainedSigma_sum_le (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    (∑ k, retainedSigma A ε k) ≤ ∑ k, (matrixSVD A).sigma k :=
  Finset.sum_le_sum fun k _ => retainedSigma_le A ε k

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; k ∈ {0,…,n-1}, we have

0 ≤ discardedSigma(A, ε, k).
-/
theorem discardedSigma_nonneg (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (k : Fin n) :
    0 ≤ discardedSigma A ε k := by
  unfold discardedSigma
  split_ifs
  · exact le_rfl
  · exact (matrixSVD A).nonneg k

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; k ∈ {0,…,n-1}, we have

σ(matrixSVD(A))(k) - retainedSigma(A, ε, k) = discardedSigma(A, ε, k).
-/
theorem sigma_sub_retained (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (k : Fin n) :
    (matrixSVD A).sigma k - retainedSigma A ε k = discardedSigma A ε k := by
  unfold retainedSigma discardedSigma
  split_ifs <;> simp

/-- The actual matrix obtained by deleting singular values below the cutoff. -/
/- Mathematical definition (normal notation): The inclusive Euclidean spectral truncation is A^(≥ ε) := ∑_(j:σⱼ ≥ ε) σⱼ · uⱼ · vⱼᵀ. -/
def spectralTruncate (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  svdMatrix (matrixSVD A).left (matrixSVD A).right (retainedSigma A ε)

/-- The discarded spectral tail. -/
/- Mathematical definition (normal notation): The Euclidean spectral tail is A-A^(≥ ε), keeping exactly the components with σⱼ<ε. -/
def spectralTail (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    Matrix (Fin n) (Fin n) ℝ := A - spectralTruncate A ε

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, we have

spectralTail(A, ε) = svdMatrix(left(matrixSVD(A)), right(matrixSVD(A)), discardedSigma(A, ε)).
-/
theorem spectralTail_eq (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    spectralTail A ε =
      svdMatrix (matrixSVD A).left (matrixSVD A).right (discardedSigma A ε) := by
  ext i j
  change A i j - (∑ k, retainedSigma A ε k * (matrixSVD A).left k i *
    (matrixSVD A).right k j) = _
  rw [matrixSVD_entry A i j, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← sigma_sub_retained]
  ring

/-- Spectral truncation does not increase the Euclidean operator norm. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, we have

‖ spectralTruncate(A, ε)‖ ≤ ‖ A‖.
-/
theorem spectralTruncate_operator_norm_le (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    ‖spectralTruncate A ε‖ ≤ ‖A‖ := by
  change ‖(spectralTruncate A ε).toEuclideanLin.toContinuousLinearMap‖ ≤
    ‖A.toEuclideanLin.toContinuousLinearMap‖
  unfold spectralTruncate
  rw [matrixSVD_operator_norm A,
    (svdMatrix_decomposition (matrixSVD A).left (matrixSVD A).right
      (retainedSigma A ε) (retainedSigma_nonneg A ε)).operator_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro k
  calc
    ‖retainedSigma A ε k‖ = retainedSigma A ε k :=
      Real.norm_of_nonneg (retainedSigma_nonneg A ε k)
    _ ≤ (matrixSVD A).sigma k := retainedSigma_le A ε k
    _ ≤ ‖(matrixSVD A).sigma‖ := by
      simpa only [Real.norm_of_nonneg ((matrixSVD A).nonneg k)] using
        norm_le_pi_norm (matrixSVD A).sigma k

/-- The residual spectral tail has operator norm at most the cutoff. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, assume 0 < ε. Then

‖ spectralTail(A, ε)‖ ≤ ε.
-/
theorem spectralTail_operator_norm_le (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) : ‖spectralTail A ε‖ ≤ ε := by
  change ‖(spectralTail A ε).toEuclideanLin.toContinuousLinearMap‖ ≤ ε
  rw [spectralTail_eq,
    (svdMatrix_decomposition (matrixSVD A).left (matrixSVD A).right
      (discardedSigma A ε) (discardedSigma_nonneg A ε)).operator_norm]
  apply (pi_norm_le_iff_of_nonneg hε.le).mpr
  intro k
  change ‖discardedSigma A ε k‖ ≤ ε
  rw [Real.norm_of_nonneg (discardedSigma_nonneg A ε k)]
  unfold discardedSigma
  split_ifs with hk
  · exact hε.le
  · exact le_of_not_ge hk

/-- Row squared norms decrease under spectral truncation. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; i ∈ {0,…,n-1}, we have

(∑ⱼ ((spectralTruncate(A, ε, i, j))²)) ≤ ∑ⱼ ((A(i, j))²).
-/
theorem spectralTruncate_row_sq_le (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (i : Fin n) :
    (∑ j, spectralTruncate A ε i j ^ 2) ≤ ∑ j, A i j ^ 2 := by
  rw [matrixSVD_row_sq A i]
  change (∑ j, svdMatrix (matrixSVD A).left (matrixSVD A).right
    (retainedSigma A ε) i j ^ 2) ≤ _
  rw [svdMatrix_row_sq]
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_right (retainedSigma_sq_le A ε k) (sq_nonneg _)

/-- Column squared norms decrease under spectral truncation. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; j ∈ {0,…,n-1}, we have

(∑ᵢ ((spectralTruncate(A, ε, i, j))²)) ≤ ∑ᵢ ((A(i, j))²).
-/
theorem spectralTruncate_column_sq_le (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (j : Fin n) :
    (∑ i, spectralTruncate A ε i j ^ 2) ≤ ∑ i, A i j ^ 2 := by
  rw [matrixSVD_column_sq A j]
  change (∑ i, svdMatrix (matrixSVD A).left (matrixSVD A).right
    (retainedSigma A ε) i j ^ 2) ≤ _
  rw [svdMatrix_column_sq]
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_right (retainedSigma_sq_le A ε k) (sq_nonneg _)

/-- counting-measure L2 squared norm decreases under spectral truncation. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, we have

matrixL2Sq(spectralTruncate(A, ε)) ≤ matrixL2Sq(A).
-/
theorem spectralTruncate_l2_sq_le (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    matrixL2Sq (spectralTruncate A ε) ≤ matrixL2Sq A := by
  unfold matrixL2Sq
  exact Finset.sum_le_sum fun i _ => spectralTruncate_row_sq_le A ε i

/-- counting-measure L2 norm decreases under spectral truncation. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, we have

√(matrixL2Sq(spectralTruncate(A, ε))) ≤ √(matrixL2Sq(A)).
-/
theorem spectralTruncate_l2_le (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    Real.sqrt (matrixL2Sq (spectralTruncate A ε)) ≤
      Real.sqrt (matrixL2Sq A) :=
  Real.sqrt_le_sqrt (spectralTruncate_l2_sq_le A ε)

/-- The squared tail norm is at most the cutoff times the sum of singular values. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, assume 0 < ε. Then

matrixL2Sq(spectralTail(A, ε)) ≤ ε · ∑ₖ (σ(matrixSVD(A))(k)).
-/
theorem spectralTail_l2_sq_le (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    matrixL2Sq (spectralTail A ε) ≤ ε * ∑ k, (matrixSVD A).sigma k := by
  rw [spectralTail_eq, svdMatrix_l2_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  unfold discardedSigma
  split_ifs with hk
  · simp only [zero_pow (by norm_num : 2 ≠ 0)]
    exact mul_nonneg hε.le ((matrixSVD A).nonneg k)
  · have h := mul_le_mul_of_nonneg_right (le_of_not_ge hk) ((matrixSVD A).nonneg k)
    nlinarith

/-- The finite set of retained singular directions. -/
/-
Mathematical definition (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, define

retainedIndices(A, ε) := Finset.univ.filter((k ↦ ε ≤ σ(matrixSVD(A))(k))).
-/
def retainedIndices (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun k => ε ≤ (matrixSVD A).sigma k

/-- The retained number of directions has the usual squared-cutoff rank bound. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, assume 0 < ε. Then

|retainedIndices(A, ε)| · ε² ≤ matrixL2Sq(A).
-/
theorem retained_count_sq_le (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (hε : 0 < ε) :
    ((retainedIndices A ε).card : ℝ) * ε ^ 2 ≤ matrixL2Sq A := by
  rw [matrixSVD_l2_sq]
  calc
    _ = ∑ k ∈ retainedIndices A ε, ε ^ 2 := by simp
    _ ≤ ∑ k ∈ retainedIndices A ε, (matrixSVD A).sigma k ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      have h : ε ≤ (matrixSVD A).sigma k := (Finset.mem_filter.mp hk).2
      exact pow_le_pow_left₀ hε.le h 2
    _ ≤ ∑ k, (matrixSVD A).sigma k ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ => sq_nonneg _)

/-- The actual retained index type, with no zero padding of its basis vectors. -/
/- Mathematical definition (normal notation): The retained singular-direction index set is {j:σⱼ ≥ ε}, with Euclidean singular coefficients. -/
abbrev RetainedDirection (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :=
  {k : Fin n // ε ≤ (matrixSVD A).sigma k}

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; f ∈ {0,…,n-1} → ℝ, we have

(∑_(k ∈ RetainedDirection(A, ε)) (f(k))) = ∑ₖ ({ f(k) if ε ≤ σ(matrixSVD(A))(k),; 0 otherwise }).
-/
theorem sum_retainedDirections (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (f : Fin n → ℝ) :
    (∑ k : RetainedDirection A ε, f k.val) =
      ∑ k, if ε ≤ (matrixSVD A).sigma k then f k else 0 := by
  calc
    _ = ∑ k ∈ retainedIndices A ε, f k :=
      (Finset.sum_subtype (retainedIndices A ε) (by intro k; simp [retainedIndices]) f).symm
    _ = _ := by simp only [retainedIndices, Finset.sum_filter]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, we have

|RetainedDirection(A, ε)| = |retainedIndices(A, ε)|.
-/
theorem card_retainedDirections (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    Fintype.card (RetainedDirection A ε) = (retainedIndices A ε).card := by
  simp [RetainedDirection, retainedIndices, Fintype.card_subtype]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, assume 0 < ε. Then

|RetainedDirection(A, ε)| · ε² ≤ matrixL2Sq(A).
-/
theorem retained_direction_count_sq_le (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    (Fintype.card (RetainedDirection A ε) : ℝ) * ε ^ 2 ≤ matrixL2Sq A := by
  rw [card_retainedDirections]
  exact retained_count_sq_le A ε hε

/-- The left singular vectors restricted to retained directions. -/
/-
Mathematical definition (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; k ∈ RetainedDirection(A, ε), define

retainedLeftBasis(A, ε, k) := left(matrixSVD(A))(k).
-/
def retainedLeftBasis (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (k : RetainedDirection A ε) : EuclideanSpace ℝ (Fin n) := (matrixSVD A).left k.val

/-- The right singular vectors restricted to retained directions. -/
/-
Mathematical definition (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; k ∈ RetainedDirection(A, ε), define

retainedRightBasis(A, ε, k) := right(matrixSVD(A))(k).
-/
def retainedRightBasis (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (k : RetainedDirection A ε) : EuclideanSpace ℝ (Fin n) := (matrixSVD A).right k.val

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, we have

Orthonormal(ℝ, retainedLeftBasis(A, ε)).
-/
theorem retainedLeftBasis_orthonormal (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    Orthonormal ℝ (retainedLeftBasis A ε) :=
  (matrixSVD A).left.orthonormal.comp Subtype.val Subtype.val_injective

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, we have

Orthonormal(ℝ, retainedRightBasis(A, ε)).
-/
theorem retainedRightBasis_orthonormal (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    Orthonormal ℝ (retainedRightBasis A ε) :=
  (matrixSVD A).right.orthonormal.comp Subtype.val Subtype.val_injective

/-- The square-root-weighted left feature vector at one row. -/
/-
Mathematical definition (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; i ∈ {0,…,n-1}, define

spectralLeftFeature(A, ε, i) := toLp(2, ((k ↦ √(σ(matrixSVD(A))(k)) · left(matrixSVD(A))(k, i)))).
-/
def spectralLeftFeature (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (i : Fin n) :
    EuclideanSpace ℝ (RetainedDirection A ε) :=
  toLp 2 (fun k => Real.sqrt ((matrixSVD A).sigma k.val) * (matrixSVD A).left k.val i)

/-- The square-root-weighted right feature vector at one column. -/
/-
Mathematical definition (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; j ∈ {0,…,n-1}, define

spectralRightFeature(A, ε, j) := toLp(2, ((k ↦ √(σ(matrixSVD(A))(k)) · right(matrixSVD(A))(k, j)))).
-/
def spectralRightFeature (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (j : Fin n) :
    EuclideanSpace ℝ (RetainedDirection A ε) :=
  toLp 2 (fun k => Real.sqrt ((matrixSVD A).sigma k.val) * (matrixSVD A).right k.val j)

/-- These feature inner products reconstruct the actual truncated matrix. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; i, j ∈ {0,…,n-1}, we have

inner(ℝ, spectralLeftFeature(A, ε, i), spectralRightFeature(A, ε, j)) = spectralTruncate(A, ε, i, j).
-/
theorem spectralTruncate_factorization (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (i j : Fin n) :
    inner ℝ (spectralLeftFeature A ε i) (spectralRightFeature A ε j) =
      spectralTruncate A ε i j := by
  calc
    _ = ∑ k : RetainedDirection A ε,
        (matrixSVD A).sigma k.val * (matrixSVD A).left k.val i *
          (matrixSVD A).right k.val j := by
      simp only [spectralLeftFeature, spectralRightFeature, PiLp.inner_apply,
        RCLike.inner_apply, starRingEnd_apply, star_trivial]
      apply Finset.sum_congr rfl
      intro k _
      have h := Real.mul_self_sqrt ((matrixSVD A).nonneg k.val)
      calc
        _ = (Real.sqrt ((matrixSVD A).sigma k.val) *
            Real.sqrt ((matrixSVD A).sigma k.val)) *
            ((matrixSVD A).left k.val i * (matrixSVD A).right k.val j) := by ring
        _ = _ := by rw [h]; ring
    _ = _ := by
      rw [sum_retainedDirections A ε (fun k => (matrixSVD A).sigma k *
        (matrixSVD A).left k i * (matrixSVD A).right k j)]
      unfold spectralTruncate svdMatrix
      apply Finset.sum_congr rfl
      intro k _
      unfold retainedSigma
      split_ifs <;> ring

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ, we have

spectralTruncate(A, ε) = innerProductTable(spectralLeftFeature(A, ε), spectralRightFeature(A, ε)).
-/
theorem spectralTruncate_eq_innerProductTable (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    spectralTruncate A ε =
      innerProductTable (spectralLeftFeature A ε) (spectralRightFeature A ε) := by
  ext i j
  exact (spectralTruncate_factorization A ε i j).symm

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; i ∈ {0,…,n-1}, we have

(‖ spectralLeftFeature(A, ε, i)‖)² = ∑ₖ (retainedSigma(A, ε, k) · (left(matrixSVD(A))(k, i))²) .
-/
theorem spectralLeftFeature_norm_sq (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (i : Fin n) :
    ‖spectralLeftFeature A ε i‖ ^ 2 =
      ∑ k, retainedSigma A ε k * (matrixSVD A).left k i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [spectralLeftFeature, ofLp_toLp, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt ((matrixSVD A).nonneg _)]
  rw [sum_retainedDirections A ε (fun k =>
    (matrixSVD A).sigma k * (matrixSVD A).left k i ^ 2)]
  apply Finset.sum_congr rfl
  intro k _
  unfold retainedSigma
  split_ifs <;> ring

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; j ∈ {0,…,n-1}, we have

(‖ spectralRightFeature(A, ε, j)‖)² = ∑ₖ (retainedSigma(A, ε, k) · (right(matrixSVD(A))(k, j))²).
-/
theorem spectralRightFeature_norm_sq (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (j : Fin n) :
    ‖spectralRightFeature A ε j‖ ^ 2 =
      ∑ k, retainedSigma A ε k * (matrixSVD A).right k j ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [spectralRightFeature, ofLp_toLp, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt ((matrixSVD A).nonneg _)]
  rw [sum_retainedDirections A ε (fun k =>
    (matrixSVD A).sigma k * (matrixSVD A).right k j ^ 2)]
  apply Finset.sum_congr rfl
  intro k _
  unfold retainedSigma
  split_ifs <;> ring

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; k ∈ {0,…,n-1}, we have

ε · retainedSigma(A, ε, k) ≤ (σ(matrixSVD(A))(k))².
-/
theorem cutoff_mul_retainedSigma_le (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (k : Fin n) :
    ε * retainedSigma A ε k ≤ (matrixSVD A).sigma k ^ 2 := by
  unfold retainedSigma
  split_ifs with hk
  · simpa only [sq] using mul_le_mul_of_nonneg_right hk ((matrixSVD A).nonneg k)
  · simpa only [mul_zero] using sq_nonneg ((matrixSVD A).sigma k)

/-- The weighted left features are controlled by the original squared row norm. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; i ∈ {0,…,n-1}, assume 0 < ε. Then

(‖ spectralLeftFeature(A, ε, i)‖)² ≤ (∑ⱼ ((A(i, j))²)) / ε.
-/
theorem spectralLeftFeature_norm_sq_le (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) (i : Fin n) :
    ‖spectralLeftFeature A ε i‖ ^ 2 ≤ (∑ j, A i j ^ 2) / ε := by
  apply (le_div_iff₀ hε).mpr
  rw [spectralLeftFeature_norm_sq, matrixSVD_row_sq A i, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  have h := mul_le_mul_of_nonneg_right (cutoff_mul_retainedSigma_le A ε k)
    (sq_nonneg ((matrixSVD A).left k i))
  nlinarith

/-- The weighted right features are controlled by the original squared column norm. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; j ∈ {0,…,n-1}, assume 0 < ε. Then

(‖ spectralRightFeature(A, ε, j)‖)² ≤ (∑ᵢ ((A(i, j))²)) / ε.
-/
theorem spectralRightFeature_norm_sq_le (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) (j : Fin n) :
    ‖spectralRightFeature A ε j‖ ^ 2 ≤ (∑ i, A i j ^ 2) / ε := by
  apply (le_div_iff₀ hε).mpr
  rw [spectralRightFeature_norm_sq, matrixSVD_column_sq A j, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  have h := mul_le_mul_of_nonneg_right (cutoff_mul_retainedSigma_le A ε k)
    (sq_nonneg ((matrixSVD A).right k j))
  nlinarith

/-- The retained orthonormal left directions have bounded pointwise factorEnergy. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; i ∈ {0,…,n-1}, assume 0 < ε. Then

(∑_(k ∈ RetainedDirection(A, ε)) ((left(matrixSVD(A))(k, i))²)) ≤ (∑ⱼ ((A(i, j))²)) / ε².
-/
theorem retainedLeft_factorEnergy_le (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) (i : Fin n) :
    (∑ k : RetainedDirection A ε, (matrixSVD A).left k.val i ^ 2) ≤
      (∑ j, A i j ^ 2) / ε ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  rw [sum_retainedDirections A ε (fun k => (matrixSVD A).left k i ^ 2),
    matrixSVD_row_sq A i, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  split_ifs with hk
  · have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hε.le hk 2)
      (sq_nonneg ((matrixSVD A).left k i))
    nlinarith
  · simp only [zero_mul]
    positivity

/-- The retained orthonormal right directions have bounded pointwise factorEnergy. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε ∈ ℝ; j ∈ {0,…,n-1}, assume 0 < ε. Then

(∑_(k ∈ RetainedDirection(A, ε)) ((right(matrixSVD(A))(k, j))²)) ≤ (∑ᵢ ((A(i, j))²)) / ε².
-/
theorem retainedRight_factorEnergy_le (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) (j : Fin n) :
    (∑ k : RetainedDirection A ε, (matrixSVD A).right k.val j ^ 2) ≤
      (∑ i, A i j ^ 2) / ε ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  rw [sum_retainedDirections A ε (fun k => (matrixSVD A).right k j ^ 2),
    matrixSVD_column_sq A j, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  split_ifs with hk
  · have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hε.le hk 2)
      (sq_nonneg ((matrixSVD A).right k j))
    nlinarith
  · simp only [zero_mul]
    positivity

/-- The factorization and row/column bounds give the Schur multiplier estimate needed for pairing a truncated input with a small-operator-norm spectral tail. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B ∈ ℝ^({0,…,n−1} × {0,…,n−1}); ε, P, Q ∈ ℝ, assume 0 < ε; ∀ i, (∑ⱼ ((A(i, j))²)) ≤ P; ∀ j, (∑ᵢ ((A(i, j))²)) ≤ Q. Then

‖ spectralTruncate(A, ε) ⊙ B‖ ≤ √(P / ε) · √(Q / ε) · ‖ B‖.
-/
theorem spectralTruncate_hadamard_norm_le (A B : Matrix (Fin n) (Fin n) ℝ)
    (ε P Q : ℝ) (hε : 0 < ε)
    (hrow : ∀ i, (∑ j, A i j ^ 2) ≤ P) (hcol : ∀ j, (∑ i, A i j ^ 2) ≤ Q) :
    ‖spectralTruncate A ε ⊙ B‖ ≤
      Real.sqrt (P / ε) * Real.sqrt (Q / ε) * ‖B‖ := by
  rw [spectralTruncate_eq_innerProductTable]
  apply schur_multiplier_norm_le_of_bounds _ _ B _ _
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · intro i
    apply Real.le_sqrt_of_sq_le
    exact (spectralLeftFeature_norm_sq_le A ε hε i).trans
      (div_le_div_of_nonneg_right (hrow i) hε.le)
  · intro j
    apply Real.le_sqrt_of_sq_le
    exact (spectralRightFeature_norm_sq_le A ε hε j).trans
      (div_le_div_of_nonneg_right (hcol j) hε.le)

end TableAnalysis
