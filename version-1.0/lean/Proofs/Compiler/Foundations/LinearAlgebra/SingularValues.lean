import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Trace



/-!
# Finite real singular-value decompositions

Right singular vectors come from the spectral theorem for `T.adjoint ∘ T`. Its nonzero normalized images form an orthonormal family; the finite orthonormal-basis extension theorem supplies the remaining left vectors.
-/

set_option autoImplicit false

open scoped BigOperators RealInnerProductSpace

namespace TableAnalysis

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

/-- A genuine two-sided orthonormal singular-value decomposition. -/
/-
Mathematical definition (normal notation): A singular-value decomposition of a linear map T:E → E on an n-dimensional real inner-product space consists of orthonormal bases (uᵢ)ᵢ₌₁ⁿ,(vᵢ)ᵢ₌₁ⁿ and numbers σᵢ ≥ 0 such that

T(vᵢ) = σᵢ · uᵢ for every i.

Zero singular values are included.
-/
structure RealSVD (T : E →ₗ[ℝ] E) (n : ℕ) where
  left : OrthonormalBasis (Fin n) ℝ E
  right : OrthonormalBasis (Fin n) ℝ E
  sigma : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ sigma i
  map_basis : ∀ i, T (right i) = sigma i • left i

/-- Every endomorphism of a finite real inner-product space has an SVD, including the zero-dimensional and rank-deficient cases. -/

/- Mathematical statement (normal notation): Every linear map T:E → E on a real inner-product space of dimension n has orthonormal bases (uᵢ),(vᵢ) and coefficients σᵢ ≥ 0 satisfying T(vᵢ) = σᵢ · uᵢ for every i. This includes n = 0 and rank-deficient maps. -/
theorem exists_realSVD (T : E →ₗ[ℝ] E) (hn : Module.finrank ℝ E = n) :
    Nonempty (RealSVD T n) := by
  classical
  let P := T.adjoint ∘ₗ T
  have hP : P.IsPositive := LinearMap.isPositive_adjoint_comp_self T
  let v := hP.isSymmetric.eigenvectorBasis hn
  let σ : Fin n → ℝ := fun i => Real.sqrt (hP.isSymmetric.eigenvalues hn i)
  have hσ (i : Fin n) : 0 ≤ σ i := Real.sqrt_nonneg _
  have hσsq (i : Fin n) : σ i ^ 2 = hP.isSymmetric.eigenvalues hn i :=
    Real.sq_sqrt (hP.nonneg_eigenvalues hn i)
  have hTv (i j : Fin n) : ⟪T (v i), T (v j)⟫ =
      σ j ^ 2 * (if i = j then 1 else 0) := by
    rw [← LinearMap.adjoint_inner_right]
    change ⟪v i, P (v j)⟫ = _
    rw [hP.isSymmetric.apply_eigenvectorBasis hn j, real_inner_smul_right,
      v.inner_eq_ite, hσsq]
    simp
  let w : Fin n → E := fun i => (σ i)⁻¹ • T (v i)
  let s : Set (Fin n) := {i | σ i ≠ 0}
  have hw : Orthonormal ℝ (s.restrict w) := by
    rw [orthonormal_iff_ite]
    intro i j
    change ⟪w i.val, w j.val⟫ = if i = j then 1 else 0
    by_cases hij : i = j
    · subst j
      have hi : σ i.val ≠ 0 := i.property
      simp only [w, real_inner_smul_left, real_inner_smul_right, hTv]
      field_simp
    · have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      simp only [w, real_inner_smul_left, real_inner_smul_right, hTv,
        if_neg hval, if_neg hij, mul_zero]
  obtain ⟨u, hu⟩ := hw.exists_orthonormalBasis_extension_of_card_eq
    (by simpa using hn)
  refine ⟨⟨u, v, σ, hσ, ?_⟩⟩
  intro i
  by_cases hi : σ i = 0
  · have hnorm : ‖T (v i)‖ ^ 2 = 0 := by
      have h := hTv i i
      simpa [real_inner_self_eq_norm_sq, hi] using h
    have hz : T (v i) = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (T (v i))])
    simp [hi, hz]
  · rw [hu i hi]
    simp only [w, smul_smul, mul_inv_cancel₀ hi, one_smul]

namespace RealSVD

variable {T : E →ₗ[ℝ] E} (s : RealSVD T n)

omit [FiniteDimensional ℝ E] in
/-- Full singular-vector expansion of the operator. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For x ∈ E, we have

T(x) = ∑ₖ ((s.sigma(k) · s.right.repr(x, k)) · s.left(k)) .
-/
theorem apply_eq_sum (x : E) :
    T x = ∑ k, (s.sigma k * s.right.repr x k) • s.left k := by
  nth_rw 1 [← s.right.sum_repr x]
  simp only [map_sum, map_smul, s.map_basis, smul_smul]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm]

omit [FiniteDimensional ℝ E] in
/-- Left-basis coordinates are the diagonal singular values times right-basis coordinates. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For x ∈ E; i ∈ {0,…,n-1}, we have

s.left.repr(T(x), i) = s.sigma(i) · s.right.repr(x, i).
-/
theorem repr_apply (x : E) (i : Fin n) :
    s.left.repr (T x) i = s.sigma i * s.right.repr x i := by
  rw [s.left.repr_apply_apply, s.apply_eq_sum, inner_sum]
  simp [inner_smul_right, s.left.inner_eq_ite, mul_comm]

omit [FiniteDimensional ℝ E] in
/-- Parseval gives the diagonal squared-norm identity. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For x ∈ E, we have

(‖ T(x)‖)² = ∑ᵢ ((s.sigma(i) · s.right.repr(x, i))²).
-/
theorem norm_sq_apply (x : E) :
    ‖T x‖ ^ 2 = ∑ i, (s.sigma i * s.right.repr x i) ^ 2 := by
  rw [← s.left.sum_sq_inner_right (T x)]
  simp_rw [← s.left.repr_apply_apply, s.repr_apply]

omit [FiniteDimensional ℝ E] in
/-- The Euclidean norm of every image is bounded by the maximum singular value. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For x ∈ E, we have

‖ T(x)‖ ≤ ‖ s.sigma‖ · ‖ x‖.
-/
theorem norm_apply_le (x : E) : ‖T x‖ ≤ ‖s.sigma‖ * ‖x‖ := by
  have hσ (i : Fin n) : s.sigma i ^ 2 ≤ ‖s.sigma‖ ^ 2 := by
    apply (sq_le_sq₀ (s.nonneg i) (norm_nonneg _)).2
    simpa only [Real.norm_eq_abs, abs_of_nonneg (s.nonneg i)] using
      norm_le_pi_norm s.sigma i
  have hsum : ∑ i, (s.sigma i * s.right.repr x i) ^ 2 ≤
      ‖s.sigma‖ ^ 2 * ∑ i, (s.right.repr x i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (hσ i) (sq_nonneg _)
  have hright : ∑ i, (s.right.repr x i) ^ 2 = ‖x‖ ^ 2 := by
    simp_rw [s.right.repr_apply_apply]
    exact s.right.sum_sq_inner_right x
  rw [hright, ← s.norm_sq_apply x] at hsum
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    (by simpa only [mul_pow] using hsum)

/-- The usual operator norm equals the sup norm of the nonnegative singular value list, namely its maximum (and zero for an empty list). -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

‖ T.toContinuousLinearMap‖ = ‖ s.sigma‖.
-/
theorem operator_norm : ‖T.toContinuousLinearMap‖ = ‖s.sigma‖ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (s.norm_apply_le)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro i
    have h := T.toContinuousLinearMap.le_opNorm (s.right i)
    simpa only [LinearMap.coe_toContinuousLinearMap', s.map_basis, norm_smul,
      s.left.norm_eq_one, s.right.norm_eq_one, mul_one] using h

omit [FiniteDimensional ℝ E] in
/-- counting-measure L2 squared norm is the sum of squared singular values, independently of the reference orthonormal basis. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For b ∈ OrthonormalBasis({0,…,n-1}, ℝ, E), we have

∑ⱼ ((‖ T(b(j))‖)²) = ∑ₖ ((s.sigma(k))²).
-/
theorem l2_sq (b : OrthonormalBasis (Fin n) ℝ E) :
    ∑ j, ‖T (b j)‖ ^ 2 = ∑ k, s.sigma k ^ 2 := by
  simp_rw [s.norm_sq_apply, mul_pow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.mul_sum]
  have hb : ∑ j, (s.right.repr (b j) k) ^ 2 = 1 := by
    simp_rw [s.right.repr_apply_apply]
    rw [b.sum_sq_inner_left, s.right.norm_eq_one]
    norm_num
  rw [hb, mul_one]

end RealSVD

section Matrices

variable (A : Matrix (Fin n) (Fin n) ℝ)

/-- Singular values and both Euclidean orthonormal bases for a real square matrix. -/
/- Mathematical definition (normal notation): Choose a Euclidean singular-value decomposition A = ∑ⱼ₌₁ ⁿσⱼ · uⱼ · vⱼᵀ of the matrix A, including zero coefficients when its rank is less than n. -/
def matrixSVD : RealSVD A.toEuclideanLin n :=
  Classical.choice (exists_realSVD A.toEuclideanLin (by simp))


/-
Mathematical statement (normal notation): For the chosen Euclidean singular-value decomposition of A ∈ ℝ^(n × n), every entry satisfies

Aᵢⱼ = ∑ₖ₌₁ ⁿσₖ · uₖ(i) · vₖ(j).

Here the vectors have Euclidean norm one; the uniformly normalized table directions are scaled separately.
-/
theorem matrixSVD_entry (i j : Fin n) :
    A i j = ∑ k, (matrixSVD A).sigma k * (matrixSVD A).left k i *
      (matrixSVD A).right k j := by
  let s := matrixSVD A
  have h := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i)
    (s.apply_eq_sum (EuclideanSpace.single j 1))
  simpa [s, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    PiLp.single_apply, OrthonormalBasis.repr_apply_apply,
    EuclideanSpace.inner_single_right, Finset.sum_apply, mul_assoc, mul_comm,
    mul_left_comm] using h

/-- Squared matrix L2 norm with counting measure on both entries. -/
/-
Mathematical definition (normal notation): The squared L₂ size with counting measure is

∑_(i,j) Aᵢⱼ².

For an n × n table, divide this quantity by n² to obtain the paper's squared normalized L₂ norm.
-/
def matrixL2Sq : ℝ := ∑ i, ∑ j, A i j ^ 2

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

matrixL2Sq(A) = ∑ₖ ((σ(matrixSVD(A))(k))²).
-/
theorem matrixSVD_l2_sq :
    matrixL2Sq A = ∑ k, (matrixSVD A).sigma k ^ 2 := by
  have h := (matrixSVD A).l2_sq (EuclideanSpace.basisFun (Fin n) ℝ)
  have hcol (j : Fin n) : ‖A.toEuclideanLin (EuclideanSpace.basisFun (Fin n) ℝ j)‖ ^ 2 =
      ∑ i, A i j ^ 2 := by
    rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_sq_inner_right]
    simp [EuclideanSpace.basisFun_apply, Matrix.toLpLin_apply,
      EuclideanSpace.inner_single_left]
  simp_rw [hcol] at h
  rw [Finset.sum_comm] at h
  exact h

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

‖ A.toEuclideanLin.toContinuousLinearMap‖ = ‖ σ(matrixSVD(A))‖.
-/
theorem matrixSVD_operator_norm :
    ‖A.toEuclideanLin.toContinuousLinearMap‖ = ‖(matrixSVD A).sigma‖ :=
  (matrixSVD A).operator_norm

end Matrices

end

end TableAnalysis
