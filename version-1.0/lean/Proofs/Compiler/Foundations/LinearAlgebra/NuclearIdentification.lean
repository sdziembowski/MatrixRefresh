import Proofs.Compiler.Foundations.LinearAlgebra.NuclearNorm
import Proofs.Compiler.Foundations.LinearAlgebra.SingularValues



/-!
# Identification of the dual nuclear norm with singular values

The upper bound tests the genuine singular-vector expansion against an arbitrary matrix. The lower bound uses the orthogonal polar matrix carrying every right singular vector to its corresponding left singular vector.
-/

set_option autoImplicit false

open scoped BigOperators Matrix Matrix.Norms.L2Operator RealInnerProductSpace

namespace TableAnalysis

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {A : Matrix ι ι ℝ}

namespace RealSVD

variable (s : RealSVD A.toEuclideanLin n)

/-- Entry expansion for any genuine SVD, independent of the chosen construction. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For i, j ∈ ι, we have

A(i, j) = ∑ₖ (s.sigma(k) · s.left(k, i) · s.right(k, j)).
-/
theorem matrix_entry (i j : ι) :
    A i j = ∑ k, s.sigma k * s.left k i * s.right k j := by
  have h := congrArg (fun x : EuclideanSpace ℝ ι => x i)
    (s.apply_eq_sum (EuclideanSpace.single j 1))
  simpa [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    PiLp.single_apply, OrthonormalBasis.repr_apply_apply,
    EuclideanSpace.inner_single_right, Finset.sum_apply, mul_assoc, mul_comm,
    mul_left_comm] using h

/-- SVD expansion of the counting pairing with an arbitrary test matrix. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For W ∈ ℝ^(ι × ι), we have

countingPairing(A, W) = ∑ₖ (s.sigma(k) · ⟨ s.left(k), W.toEuclideanLin(s.right(k))⟩) .
-/
theorem countingPairing_eq_sum (W : Matrix ι ι ℝ) :
    countingPairing A W = ∑ k, s.sigma k * ⟪s.left k, W.toEuclideanLin (s.right k)⟫ := by
  unfold countingPairing
  simp_rw [s.matrix_entry, Finset.sum_mul]
  calc
    _ = ∑ i : ι, ∑ k : Fin n, ∑ j : ι,
        (s.sigma k * s.left k i * s.right k j) * W i j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ∑ i : ι, ∑ j : ι,
        (s.sigma k * s.left k i * s.right k j) * W i j := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [PiLp.inner_apply, RCLike.inner_apply', Matrix.toLpLin_apply,
        Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [RCLike.conj_to_real]
      ring

/-- Every coefficient tested against a matrix is bounded by its L2 operator norm. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For W ∈ ℝ^(ι × ι); k ∈ {0,…,n-1}, we have

|⟨ s.left(k), W.toEuclideanLin(s.right(k))⟩| ≤ ‖ W‖.
-/
theorem abs_inner_test_le (W : Matrix ι ι ℝ) (k : Fin n) :
    |⟪s.left k, W.toEuclideanLin (s.right k)⟫| ≤ ‖W‖ := by
  have h := (abs_real_inner_le_norm (s.left k) (W.toEuclideanLin (s.right k))).trans
    (mul_le_mul_of_nonneg_left
      (W.toEuclideanLin.toContinuousLinearMap.le_opNorm (s.right k))
      (norm_nonneg _))
  simpa only [s.left.norm_eq_one, s.right.norm_eq_one, mul_one, one_mul,
    Matrix.l2_opNorm_def, LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap'] using h

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

0 ≤ ∑ₖ (s.sigma(k)).
-/
theorem sum_sigma_nonneg : 0 ≤ ∑ k, s.sigma k :=
  Finset.sum_nonneg (fun k _ => s.nonneg k)

/-- The dual norm is at most the sum of the genuine singular values. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

‖ A‖_(*,count) ≤ ∑ₖ (s.sigma(k)).
-/
theorem nuclearNorm_le_sum_sigma : nuclearNorm A ≤ ∑ k, s.sigma k := by
  apply ContinuousLinearMap.opNorm_le_bound _ s.sum_sigma_nonneg
  intro W
  rw [countingPairingDual_apply, Real.norm_eq_abs, s.countingPairing_eq_sum]
  calc
    _ ≤ ∑ k, |s.sigma k * ⟪s.left k, W.toEuclideanLin (s.right k)⟫| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, s.sigma k * ‖W‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul, abs_of_nonneg (s.nonneg k)]
      exact mul_le_mul_of_nonneg_left (s.abs_inner_test_le W k) (s.nonneg k)
    _ = (∑ k, s.sigma k) * ‖W‖ := (Finset.sum_mul _ _ _).symm

/-- The orthogonal polar factor: move right coordinates to the left basis. -/
/-
Mathematical definition (normal notation): Define

polarMatrix := (Matrix.toEuclideanLin)⁻¹(toLinearEquiv.toLinearMap(s.right.repr.trans((s.left.repr)⁻¹))) .
-/
def polarMatrix : Matrix ι ι ℝ :=
  Matrix.toEuclideanLin.symm
    (s.right.repr.trans s.left.repr.symm).toLinearEquiv.toLinearMap

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): Let (uⱼ),(vⱼ) be the left and right Euclidean singular bases of the chosen decomposition. Its polar matrix sends any vector x to ∑ⱼ ⟨ vⱼ,x⟩ · uⱼ; equivalently it replaces the right-basis coordinates by the same left-basis coordinates. -/
theorem polarMatrix_apply (x : EuclideanSpace ℝ ι) :
    s.polarMatrix.toEuclideanLin x = (s.right.repr.trans s.left.repr.symm) x := by
  unfold polarMatrix
  rw [LinearEquiv.apply_symm_apply]
  rfl

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For k ∈ {0,…,n-1}, we have

s.polarMatrix.toEuclideanLin(s.right(k)) = s.left(k).
-/
theorem polarMatrix_right (k : Fin n) :
    s.polarMatrix.toEuclideanLin (s.right k) = s.left k := by
  rw [s.polarMatrix_apply]
  simp [LinearIsometryEquiv.trans_apply]

/-- Polar norm is at most one, including the empty-dimensional case. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

‖ s.polarMatrix‖ ≤ 1.
-/
theorem polarMatrix_norm_le_one : ‖s.polarMatrix‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖s.polarMatrix.toEuclideanLin x‖ ≤ 1 * ‖x‖
  rw [s.polarMatrix_apply, LinearIsometryEquiv.norm_map, one_mul]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

countingPairing(A, s.polarMatrix) = ∑ₖ (s.sigma(k)).
-/
theorem countingPairing_polarMatrix : countingPairing A s.polarMatrix = ∑ k, s.sigma k := by
  rw [s.countingPairing_eq_sum]
  simp [s.polarMatrix_right]

/-- The polar test attains the singular-value sum in the dual pairing. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

(∑ₖ (s.sigma(k))) ≤ ‖ A‖_(*,count).
-/
theorem sum_sigma_le_nuclearNorm : (∑ k, s.sigma k) ≤ nuclearNorm A := by
  have h := abs_countingPairing_le A s.polarMatrix
  rw [s.countingPairing_polarMatrix, abs_of_nonneg s.sum_sigma_nonneg] at h
  calc
    _ ≤ nuclearNorm A * ‖s.polarMatrix‖ := h
    _ ≤ nuclearNorm A * 1 :=
      mul_le_mul_of_nonneg_left s.polarMatrix_norm_le_one (nuclearNorm_nonneg A)
    _ = nuclearNorm A := mul_one _

/-- Nuclear norm is the singular-value sum for every genuine SVD. -/

/-
Mathematical statement (normal notation): we have

‖ A‖_(*,count) = ∑ₖ (s.sigma(k)).
-/
theorem nuclearNorm_eq_sum_sigma : nuclearNorm A = ∑ k, s.sigma k :=
  le_antisymm s.nuclearNorm_le_sum_sigma s.sum_sigma_le_nuclearNorm

/-- The singular-value sum is independent of the orthonormal SVD choices. -/

/-
Mathematical statement (normal notation): For any two Euclidean singular-value decompositions of the same matrix A, their coefficient sums agree:

∑ⱼ σⱼ = ∑ⱼ σ̃ⱼ.

This statement establishes independence of the sum, without asserting uniqueness of the chosen singular vectors.
-/
theorem sum_sigma_eq (t : RealSVD A.toEuclideanLin n) :
    (∑ k, s.sigma k) = ∑ k, t.sigma k :=
  s.nuclearNorm_eq_sum_sigma.symm.trans t.nuclearNorm_eq_sum_sigma

end RealSVD

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}), we have

‖ A‖_(*,count) = ∑ₖ (σ(matrixSVD(A))(k)).
-/
theorem nuclearNorm_eq_matrixSVD_sum (A : Matrix (Fin n) (Fin n) ℝ) :
    nuclearNorm A = ∑ k, (matrixSVD A).sigma k :=
  (matrixSVD A).nuclearNorm_eq_sum_sigma

/-- Uniform-measure tables act by the raw matrix divided by the number of shares; their nuclear norm has the same explicit scaling. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}), we have

‖ ((n)⁻¹ · A)‖_(*,count) = (n)⁻¹ · ∑ₖ (σ(matrixSVD(A))(k)).
-/
theorem nuclearNorm_uniformScale (A : Matrix (Fin n) (Fin n) ℝ) :
    nuclearNorm ((n : ℝ)⁻¹ • A) = (n : ℝ)⁻¹ * ∑ k, (matrixSVD A).sigma k := by
  rw [nuclearNorm_smul, nuclearNorm_eq_matrixSVD_sum,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]

end

end TableAnalysis
