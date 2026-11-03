import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.Tactic



/-!
# A vector-factor Schur multiplier bound

All matrix norms in this file are the operator norms between Euclidean spaces. The vector factors have counting-measure Euclidean norms, and a family of factors has its usual supremum norm. The final lemma records the common `1/d` scaling needed for square tables acting on the uniform probability space.
-/

set_option autoImplicit false

open scoped BigOperators Matrix Matrix.Norms.L2Operator

open WithLp

noncomputable section

namespace TableAnalysis

variable {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
  [DecidableEq κ]

/-- The scalar Euclidean operator bound, written entirely as finite sums. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For B ∈ ℝ^(ι × κ); x ∈ κ → ℝ, we have

(∑ᵢ ((∑ⱼ (B(i, j) · x(j)))²)) ≤ (‖ B‖)² · ∑ⱼ ((x(j))²).
-/
theorem sum_sq_matrix_action_le (B : Matrix ι κ ℝ) (x : κ → ℝ) :
    (∑ i, (∑ j, B i j * x j) ^ 2) ≤ ‖B‖ ^ 2 * ∑ j, x j ^ 2 := by
  have h := B.l2_opNorm_mulVec (toLp 2 x)
  change ‖toLp 2 (B *ᵥ x)‖ ≤ ‖B‖ * ‖toLp 2 x‖ at h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [mul_pow, EuclideanSpace.norm_sq_eq, Matrix.mulVec, dotProduct,
    ofLp_toLp, Real.norm_eq_abs, sq_abs] using hsq

/-- Applying the same scalar matrix to every coordinate of vector-valued inputs has the same squared operator bound. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For B ∈ ℝ^(ι × κ); v ∈ κ → EuclideanSpace(ℝ, η), we have

(∑ᵢ ((‖ ∑ⱼ (B(i, j) · v(j))‖)²)) ≤ (‖ B‖)² · ∑ⱼ ((‖ v(j)‖)²).
-/
theorem sum_sq_vector_matrix_action_le (B : Matrix ι κ ℝ)
    (v : κ → EuclideanSpace ℝ η) :
    (∑ i, ‖∑ j, B i j • v j‖ ^ 2) ≤ ‖B‖ ^ 2 * ∑ j, ‖v j‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_comm]
  calc
    (∑ k, ∑ i, ((∑ j, B i j • v j) k) ^ 2)
        = ∑ k, ∑ i, (∑ j, B i j * v j k) ^ 2 := by
          simp
    _ ≤ ∑ k, ‖B‖ ^ 2 * ∑ j, v j k ^ 2 :=
      Finset.sum_le_sum fun k _ => sum_sq_matrix_action_le B (fun j => v j k)
    _ = ‖B‖ ^ 2 * ∑ j, ∑ k, v j k ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]

/-- A table factored through an inner product. -/
/-
Mathematical definition (normal notation): For a ∈ ι → EuclideanSpace(ℝ, η); b ∈ κ → EuclideanSpace(ℝ, η), define

innerProductTable(a, b) := (i, j ↦ inner(ℝ, a(i), b(j))).
-/
def innerProductTable (a : ι → EuclideanSpace ℝ η) (b : κ → EuclideanSpace ℝ η) :
    Matrix ι κ ℝ := fun i j => inner ℝ (a i) (b j)

omit [Fintype ι] [DecidableEq κ] in
/-- The Schur product acts by taking a row-wise inner product after the vector-valued matrix action. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ ι → EuclideanSpace(ℝ, η); b ∈ κ → EuclideanSpace(ℝ, η); B ∈ ℝ^(ι × κ); x ∈ κ → ℝ; i ∈ ι, we have

(innerProductTable(a, b) ⊙ B) · ᵥ(x)(i) = inner(ℝ, a(i), (∑ⱼ (B(i, j) · (x(j) · b(j))))).
-/
theorem innerProductTable_hadamard_mulVec (a : ι → EuclideanSpace ℝ η)
    (b : κ → EuclideanSpace ℝ η) (B : Matrix ι κ ℝ) (x : κ → ℝ) (i : ι) :
    ((innerProductTable a b ⊙ B) *ᵥ x) i =
      inner ℝ (a i) (∑ j, B i j • (x j • b j)) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.hadamard_apply, innerProductTable,
    inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Pointwise bounds on the vector factors control the Euclidean operator norm of the corresponding Schur multiplier. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ ι → EuclideanSpace(ℝ, η); b ∈ κ → EuclideanSpace(ℝ, η); B ∈ ℝ^(ι × κ); A, C ∈ ℝ, assume 0 ≤ A; 0 ≤ C; ∀ i, ‖ a(i)‖ ≤ A; ∀ j, ‖ b(j)‖ ≤ C. Then

‖ innerProductTable(a, b) ⊙ B‖ ≤ A · C · ‖ B‖.
-/
theorem schur_multiplier_norm_le_of_bounds (a : ι → EuclideanSpace ℝ η)
    (b : κ → EuclideanSpace ℝ η) (B : Matrix ι κ ℝ) (A C : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ A) (hb : ∀ j, ‖b j‖ ≤ C) :
    ‖innerProductTable a b ⊙ B‖ ≤ A * C * ‖B‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  change ‖(EuclideanSpace.equiv ι ℝ).symm
    ((innerProductTable a b ⊙ B) *ᵥ x)‖ ^ 2 ≤ (A * C * ‖B‖ * ‖x‖) ^ 2
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  calc
    (∑ i, (((innerProductTable a b ⊙ B) *ᵥ x) i) ^ 2)
        ≤ A ^ 2 * ∑ i, ‖∑ j, B i j • (x j • b j)‖ ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i _
          rw [innerProductTable_hadamard_mulVec]
          have h := (abs_real_inner_le_norm (a i)
            (∑ j, B i j • (x j • b j))).trans
            (mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _))
          have hsq := pow_le_pow_left₀ (abs_nonneg _) h 2
          simpa only [sq_abs, mul_pow] using hsq
    _ ≤ A ^ 2 * (‖B‖ ^ 2 * ∑ j, ‖x j • b j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (sum_sq_vector_matrix_action_le B (fun j => x j • b j)) (sq_nonneg A)
    _ ≤ A ^ 2 * (‖B‖ ^ 2 * (C ^ 2 * ∑ j, (x j) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg A)
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg ‖B‖)
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      have hsq := pow_le_pow_left₀ (norm_nonneg _) (hb j) 2
      nlinarith [sq_nonneg (x j)]
    _ = (A * C * ‖B‖ * ‖x‖) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]
      ring

/-- The factor families use their supremum norms; the matrix uses its Euclidean operator norm. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ ι → EuclideanSpace(ℝ, η); b ∈ κ → EuclideanSpace(ℝ, η); B ∈ ℝ^(ι × κ), we have

‖ innerProductTable(a, b) ⊙ B‖ ≤ ‖ a‖ · ‖ b‖ · ‖ B‖.
-/
theorem schur_multiplier_norm_le (a : ι → EuclideanSpace ℝ η)
    (b : κ → EuclideanSpace ℝ η) (B : Matrix ι κ ℝ) :
    ‖innerProductTable a b ⊙ B‖ ≤ ‖a‖ * ‖b‖ * ‖B‖ :=
  schur_multiplier_norm_le_of_bounds a b B ‖a‖ ‖b‖ (norm_nonneg _) (norm_nonneg _)
    (fun i => norm_le_pi_norm a i) (fun j => norm_le_pi_norm b j)

/-- The same estimate after a common scalar normalization of the table and its Schur product. For `c = 1/d`, this is the uniform-measure convention for equal-sized table index spaces. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ ι → EuclideanSpace(ℝ, η); b ∈ κ → EuclideanSpace(ℝ, η); B ∈ ℝ^(ι × κ); c ∈ ℝ, we have

‖ c · (innerProductTable(a, b) ⊙ B)‖ ≤ ‖ a‖ · ‖ b‖ · ‖ c · B‖.
-/
theorem scaled_schur_multiplier_norm_le (a : ι → EuclideanSpace ℝ η)
    (b : κ → EuclideanSpace ℝ η) (B : Matrix ι κ ℝ) (c : ℝ) :
    ‖c • (innerProductTable a b ⊙ B)‖ ≤ ‖a‖ * ‖b‖ * ‖c • B‖ := by
  rw [← Matrix.hadamard_smul]
  exact schur_multiplier_norm_le a b (c • B)

/-- The continuous linear operator represented by a finite real matrix. -/
/-
Mathematical definition (normal notation): For B ∈ ℝ^(ι × κ), define

matrixOperator(B) := trans(Matrix.toEuclideanLin(𝕜 = ℝ, m = ι, n = κ))(LinearMap.toContinuousLinearMap, B).
-/
def matrixOperator (B : Matrix ι κ ℝ) : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι :=
  ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := ι) (n := κ)).trans
    LinearMap.toContinuousLinearMap) B

/-- The operator-norm version with explicit continuous linear maps. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ ι → EuclideanSpace(ℝ, η); b ∈ κ → EuclideanSpace(ℝ, η); B ∈ ℝ^(ι × κ), we have

‖ matrixOperator((innerProductTable(a, b) ⊙ B))‖ ≤ ‖ a‖ · ‖ b‖ · ‖ matrixOperator(B)‖.
-/
theorem schur_multiplier_operator_norm_le (a : ι → EuclideanSpace ℝ η)
    (b : κ → EuclideanSpace ℝ η) (B : Matrix ι κ ℝ) :
    ‖matrixOperator (innerProductTable a b ⊙ B)‖ ≤ ‖a‖ * ‖b‖ * ‖matrixOperator B‖ := by
  simpa only [Matrix.l2_opNorm_def, matrixOperator] using schur_multiplier_norm_le a b B

section UniformTables

variable [DecidableEq ι]

/-- A square table acts by averaging over its column index. The same counting Euclidean space appears on both sides, so rescaling both vector norms by `1 / sqrt(card ι)` leaves this operator norm unchanged. -/
/-
Mathematical definition (normal notation): For B ∈ ℝ^(ι × ι), define

uniformTableOperator(B) := (|ι|)⁻¹ · matrixOperator(B).
-/
def uniformTableOperator (B : Matrix ι ι ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  (Fintype.card ι : ℝ)⁻¹ • matrixOperator B

/-- The uniform table operator is exactly the matrix operator of `B/d`. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For B ∈ ℝ^(ι × ι), we have

uniformTableOperator(B) = matrixOperator(((|ι|)⁻¹ · B)) .
-/
theorem uniformTableOperator_eq (B : Matrix ι ι ℝ) :
    uniformTableOperator B = matrixOperator ((Fintype.card ι : ℝ)⁻¹ • B) := by
  exact (map_smul ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := ι) (n := ι)).trans
    LinearMap.toContinuousLinearMap) (Fintype.card ι : ℝ)⁻¹ B).symm

/-- The Schur multiplier inequality in the uniform-measure table convention. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ ι → EuclideanSpace(ℝ, η); B ∈ ℝ^(ι × ι), we have

‖ uniformTableOperator((innerProductTable(a, b) ⊙ B))‖ ≤ ‖ a‖ · ‖ b‖ · ‖ uniformTableOperator(B)‖.
-/
theorem schur_multiplier_uniform_operator_norm_le (a b : ι → EuclideanSpace ℝ η)
    (B : Matrix ι ι ℝ) :
    ‖uniformTableOperator (innerProductTable a b ⊙ B)‖ ≤
      ‖a‖ * ‖b‖ * ‖uniformTableOperator B‖ := by
  rw [uniformTableOperator_eq, uniformTableOperator_eq, ← Matrix.hadamard_smul]
  exact schur_multiplier_operator_norm_le a b ((Fintype.card ι : ℝ)⁻¹ • B)

end UniformTables

end TableAnalysis
