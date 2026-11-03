import Mathlib.Analysis.Complex.Basic
import Proofs.Compiler.Foundations.LinearAlgebra.SingularValues



/-!
# Complex singular-value decompositions for the character-twisted test

The refresh-only library uses real singular vectors. The joint-port argument must extract rank-one terms from complex additive-character twists. This file constructs the corresponding genuine complex SVD from the spectral theorem, including zero singular values and zero-dimensional spaces.
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {n : ℕ}

/-- A two-sided orthonormal SVD with nonnegative real singular values. -/
/- Mathematical definition (normal notation): A singular-value decomposition of T:E → E consists of orthonormal bases (uᵢ), (vᵢ) and nonnegative real numbers σᵢ such that T(vᵢ) = σᵢ uᵢ for every i. -/
structure ComplexSVD (T : E →ₗ[ℂ] E) (n : ℕ) where
  left : OrthonormalBasis (Fin n) ℂ E
  right : OrthonormalBasis (Fin n) ℂ E
  sigma : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ sigma i
  map_basis : ∀ i, T (right i) = (sigma i : ℂ) • left i

/-- Every finite-dimensional complex endomorphism has a full SVD. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For T ∈ E —linear over ℂ→ E, assume Module.finrank(ℂ, E) = n. Then

ComplexSVD(T, n) ≠ ∅.
-/
theorem exists_complexSVD (T : E →ₗ[ℂ] E) (hn : Module.finrank ℂ E = n) :
    Nonempty (ComplexSVD T n) := by
  classical
  let P := T.adjoint ∘ₗ T
  have hP : P.IsPositive := LinearMap.isPositive_adjoint_comp_self T
  let v := hP.isSymmetric.eigenvectorBasis hn
  let σ : Fin n → ℝ := fun i => Real.sqrt (hP.isSymmetric.eigenvalues hn i)
  have hσ (i : Fin n) : 0 ≤ σ i := Real.sqrt_nonneg _
  have hσsq (i : Fin n) : σ i ^ 2 = hP.isSymmetric.eigenvalues hn i :=
    Real.sq_sqrt (hP.nonneg_eigenvalues hn i)
  have hTv (i j : Fin n) : inner ℂ (T (v i)) (T (v j)) =
      (σ j : ℂ) ^ 2 * (if i = j then 1 else 0) := by
    rw [← LinearMap.adjoint_inner_right]
    change inner ℂ (v i) (P (v j)) = _
    rw [hP.isSymmetric.apply_eigenvectorBasis hn j, inner_smul_right, v.inner_eq_ite]
    rw [← Complex.ofReal_pow, hσsq]
    simp
  let w : Fin n → E := fun i => ((σ i : ℂ)⁻¹) • T (v i)
  let s : Set (Fin n) := {i | σ i ≠ 0}
  have hw : Orthonormal ℂ (s.restrict w) := by
    rw [orthonormal_iff_ite]
    intro i j
    change inner ℂ (w i.val) (w j.val) = if i = j then 1 else 0
    by_cases hij : i = j
    · subst j
      have hi : (σ i.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr i.property
      simp only [w, inner_smul_left, inner_smul_right, map_inv₀, Complex.conj_ofReal, hTv]
      field_simp
    · have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      simp only [w, inner_smul_left, inner_smul_right, hTv, if_neg hval, if_neg hij,
        mul_zero]
  obtain ⟨u, hu⟩ := hw.exists_orthonormalBasis_extension_of_card_eq
    (by simpa using hn)
  refine ⟨⟨u, v, σ, hσ, ?_⟩⟩
  intro i
  by_cases hi : σ i = 0
  · have hz : T (v i) = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℂ)).mp
      simpa [hi] using hTv i i
    simp [hi, hz]
  · rw [hu i hi]
    have hi' : (σ i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hi
    simp only [w, smul_smul, mul_inv_cancel₀ hi', one_smul]

namespace ComplexSVD

variable {T : E →ₗ[ℂ] E} (s : ComplexSVD T n)

/-- Full singular-vector expansion, with every complex phase retained. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For x ∈ E, we have

T(x) = ∑ₖ ((s.sigma(k) · s.right.repr(x, k)) · s.left(k)) .
-/
theorem apply_eq_sum (x : E) :
    T x = ∑ k, ((s.sigma k : ℂ) * s.right.repr x k) • s.left k := by
  nth_rw 1 [← s.right.sum_repr x]
  simp only [map_sum, map_smul, s.map_basis, smul_smul]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm]

/-- The adjoint carries each left singular vector to its right counterpart. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For i ∈ {0,…,n-1}, we have

T.adjoint(s.left(i)) = s.sigma(i) · s.right(i).
-/
theorem adjoint_map_basis (i : Fin n) :
    T.adjoint (s.left i) = (s.sigma i : ℂ) • s.right i := by
  apply s.right.repr.injective
  ext j
  simp only [OrthonormalBasis.repr_apply_apply]
  rw [LinearMap.adjoint_inner_right, s.map_basis, inner_smul_left, inner_smul_right,
    s.left.inner_eq_ite, s.right.inner_eq_ite, Complex.conj_ofReal]
  by_cases h : i = j
  · subst j; simp
  · simp [h, Ne.symm h]

/-- Left-basis coordinates are the singular values times right coordinates. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For x ∈ E; i ∈ {0,…,n-1}, we have

s.left.repr(T(x), i) = s.sigma(i) · s.right.repr(x, i).
-/
theorem repr_apply (x : E) (i : Fin n) :
    s.left.repr (T x) i = (s.sigma i : ℂ) * s.right.repr x i := by
  rw [s.left.repr_apply_apply, s.apply_eq_sum, inner_sum]
  simp [inner_smul_right, s.left.inner_eq_ite, mul_comm]

/-- Parseval gives the squared-norm identity over the complex coefficient field. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For x ∈ E, we have

(‖ T(x)‖)² = ∑ᵢ ((s.sigma(i))² · (‖ s.right.repr(x, i)‖)²).
-/
theorem norm_sq_apply (x : E) :
    ‖T x‖ ^ 2 = ∑ i, s.sigma i ^ 2 * ‖s.right.repr x i‖ ^ 2 := by
  rw [← s.left.sum_sq_norm_inner_right (T x)]
  simp_rw [← s.left.repr_apply_apply, s.repr_apply, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The operator acts with norm at most its largest singular value. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For x ∈ E, we have

‖ T(x)‖ ≤ ‖ s.sigma‖ · ‖ x‖.
-/
theorem norm_apply_le (x : E) : ‖T x‖ ≤ ‖s.sigma‖ * ‖x‖ := by
  have hσ (i : Fin n) : s.sigma i ^ 2 ≤ ‖s.sigma‖ ^ 2 := by
    apply (sq_le_sq₀ (s.nonneg i) (norm_nonneg _)).2
    simpa only [Real.norm_eq_abs, abs_of_nonneg (s.nonneg i)] using
      norm_le_pi_norm s.sigma i
  have hsum : ∑ i, s.sigma i ^ 2 * ‖s.right.repr x i‖ ^ 2 ≤
      ‖s.sigma‖ ^ 2 * ∑ i, ‖s.right.repr x i‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hσ i) (sq_nonneg _))
  have hright : ∑ i, ‖s.right.repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
    simp_rw [s.right.repr_apply_apply]
    exact s.right.sum_sq_norm_inner_right x
  rw [hright, ← s.norm_sq_apply x] at hsum
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    (by simpa only [mul_pow] using hsum)

/-- Exact operator norm, including the empty-dimensional case. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

‖ T.toContinuousLinearMap‖ = ‖ s.sigma‖.
-/
theorem operator_norm : ‖T.toContinuousLinearMap‖ = ‖s.sigma‖ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) s.norm_apply_le
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro i
    have h := T.toContinuousLinearMap.le_opNorm (s.right i)
    simpa only [LinearMap.coe_toContinuousLinearMap', s.map_basis, norm_smul,
      Complex.norm_real, s.left.norm_eq_one, s.right.norm_eq_one, mul_one] using h

/-- Squared `L₂` energy is the sum of squared singular values. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For J a set; b ∈ OrthonormalBasis(J, ℂ, E), assume J is finite. Then

∑ⱼ ((‖ T(b(j))‖)²) = ∑ₖ ((s.sigma(k))²).
-/
theorem l2_sq {J : Type*} [Fintype J] (b : OrthonormalBasis J ℂ E) :
    ∑ j, ‖T (b j)‖ ^ 2 = ∑ k, s.sigma k ^ 2 := by
  simp_rw [s.norm_sq_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.mul_sum]
  have hb : ∑ j, ‖s.right.repr (b j) k‖ ^ 2 = 1 := by
    simp_rw [s.right.repr_apply_apply]
    rw [b.sum_sq_norm_inner_left, s.right.norm_eq_one]
    norm_num
  rw [hb, mul_one]

/-- Remove one singular term, retaining its two phases. -/
/-
Mathematical definition (normal notation): For i ∈ {0,…,n-1}; x ∈ E, define

residual(i, x) := T(x) - (s.sigma(i) · s.right.repr(x, i)) · s.left(i).
-/
def residual (i : Fin n) (x : E) : E :=
  T x - ((s.sigma i : ℂ) * s.right.repr x i) • s.left i

/-- A singular-term removal decreases every input-vector energy exactly. For coordinate basis vectors this is the column-energy identity used in the greedy twisted decomposition. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For i ∈ {0,…,n-1}; x ∈ E, we have

(‖ s.residual(i, x)‖)² = (‖ T(x)‖)² - (s.sigma(i))² · (‖ s.right.repr(x, i)‖)².
-/
theorem residual_norm_sq (i : Fin n) (x : E) :
    ‖s.residual i x‖ ^ 2 = ‖T x‖ ^ 2 - s.sigma i ^ 2 * ‖s.right.repr x i‖ ^ 2 := by
  let y := ((s.sigma i : ℂ) * s.right.repr x i) • s.left i
  have hi : inner ℂ (s.left i) (T x - y) = 0 := by
    rw [inner_sub_right]
    rw [← s.left.repr_apply_apply]
    rw [s.repr_apply]
    simp [y, inner_smul_right]
  have horth : inner ℂ (T x - y) y = 0 := by
    rw [inner_smul_right]
    have hz : inner ℂ (T x - y) (s.left i) = 0 := by
      rw [← inner_conj_symm, hi, map_zero]
    rw [hz, mul_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (T x - y) y horth
  rw [sub_add_cancel] at h
  have hy : ‖y‖ ^ 2 = s.sigma i ^ 2 * ‖s.right.repr x i‖ ^ 2 := by
    simp only [y, norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      s.left.norm_eq_one, mul_one, mul_pow, sq_abs]
  simp only [← pow_two] at h
  rw [hy] at h
  change ‖T x - y‖ ^ 2 = _
  linarith

/-- Swapping the singular bases gives a certified SVD of the adjoint. -/
/-
Mathematical definition (normal notation): Define

adjoint := (s.right, s.left, s.sigma, s.nonneg, s.adjoint_map_basis).
-/
def adjoint : ComplexSVD T.adjoint n :=
  ⟨s.right, s.left, s.sigma, s.nonneg, s.adjoint_map_basis⟩

/-- Extraction of a term above any nonnegative residual threshold. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For β ∈ ℝ, assume 0 ≤ β; β < ‖ T.toContinuousLinearMap‖. Then

∃ i, β < s.sigma(i).
-/
theorem exists_large_singular (β : ℝ) (hβ : 0 ≤ β)
    (hlarge : β < ‖T.toContinuousLinearMap‖) :
    ∃ i, β < s.sigma i := by
  by_contra hn
  push_neg at hn
  have hle : ‖s.sigma‖ ≤ β := (pi_norm_le_iff_of_nonneg hβ).2 (fun i => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (s.nonneg i)] using hn i)
  rw [s.operator_norm] at hlarge
  exact not_lt_of_ge hle hlarge

/-- Each extraction lowers the total squared `L₂` energy by its squared singular value, so terms above a fixed positive threshold cannot be extracted indefinitely. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For J a set; b ∈ OrthonormalBasis(J, ℂ, E); i ∈ {0,…,n-1}, assume J is finite. Then

∑ⱼ ((‖ s.residual(i, b(j))‖)²) = (∑ⱼ ((‖ T(b(j))‖)²)) - (s.sigma(i))².
-/
theorem residual_l2_sq {J : Type*} [Fintype J] (b : OrthonormalBasis J ℂ E) (i : Fin n) :
    ∑ j, ‖s.residual i (b j)‖ ^ 2 = (∑ j, ‖T (b j)‖ ^ 2) - s.sigma i ^ 2 := by
  simp_rw [s.residual_norm_sq]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hb : ∑ j, ‖s.right.repr (b j) i‖ ^ 2 = 1 := by
    simp_rw [s.right.repr_apply_apply]
    rw [b.sum_sq_norm_inner_left, s.right.norm_eq_one]
    norm_num
  rw [hb, mul_one]

/-- The corresponding exact decrease holds for every row energy. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For i ∈ {0,…,n-1}; x ∈ E, we have

(‖ s.adjoint.residual(i, x)‖)² = (‖ T.adjoint(x)‖)² - (s.sigma(i))² · (‖ s.left.repr(x, i)‖)².
-/
theorem adjoint_residual_norm_sq (i : Fin n) (x : E) :
    ‖s.adjoint.residual i x‖ ^ 2 =
      ‖T.adjoint x‖ ^ 2 - s.sigma i ^ 2 * ‖s.left.repr x i‖ ^ 2 :=
  s.adjoint.residual_norm_sq i x

end ComplexSVD

end

end CircuitCompiler
