import Mathlib.Data.Matrix.ColumnRowPartitioned
import Proofs.Compiler.GateApproximation.MatrixPhase.JointSchur



/-!
# Operator perturbation from nonorthogonal feature Grams

Augmenting each mean synthesis matrix by a scaled identity gives a dominating Gram matrix. Pointwise domination transfers through matrix multiplication and adjoints. Expanding the augmented product gives the four blocks in the paper, without requiring orthogonal extracted features or continuity of matrix roots.
-/

set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler

noncomputable section

variable {I J K L P : Type*}
  [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype P]
  [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [DecidableEq P]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × J); x ∈ EuclideanSpace(ℂ, J), we have

‖ toEuclideanLin(Matrix.fromRows(A, 0))(x)‖ = ‖ A.toEuclideanLin(x)‖.
-/
lemma complex_fromRows_zero_action_norm (A : Matrix I J ℂ) (x : EuclideanSpace ℂ J) :
    ‖(Matrix.fromRows A (0 : Matrix K J ℂ)).toEuclideanLin x‖ = ‖A.toEuclideanLin x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  simp [PiLp.norm_sq_eq_of_L2, Matrix.toLpLin_apply, Matrix.fromRows_mulVec,
    Fintype.sum_sum_type]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × J); x ∈ EuclideanSpace(ℂ, J), we have

‖ toEuclideanLin(Matrix.fromRows(0, A))(x)‖ = ‖ A.toEuclideanLin(x)‖.
-/
lemma complex_fromRows_zero_left_action_norm (A : Matrix I J ℂ) (x : EuclideanSpace ℂ J) :
    ‖(Matrix.fromRows (0 : Matrix K J ℂ) A).toEuclideanLin x‖ = ‖A.toEuclideanLin x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  simp [PiLp.norm_sq_eq_of_L2, Matrix.toLpLin_apply, Matrix.fromRows_mulVec,
    Fintype.sum_sum_type]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × J), we have

‖ Matrix.fromRows(A, 0)‖ ≤ ‖ A‖.
-/
lemma complex_fromRows_zero_norm_le (A : Matrix I J ℂ) :
    ‖Matrix.fromRows A (0 : Matrix K J ℂ)‖ ≤ ‖A‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖(Matrix.fromRows A (0 : Matrix K J ℂ)).toEuclideanLin x‖ ≤ _
  rw [complex_fromRows_zero_action_norm]
  exact A.l2_opNorm_mulVec x

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × J), we have

‖ Matrix.fromRows(0, A)‖ ≤ ‖ A‖.
-/
lemma complex_fromRows_zero_left_norm_le (A : Matrix I J ℂ) :
    ‖Matrix.fromRows (0 : Matrix K J ℂ) A‖ ≤ ‖A‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖(Matrix.fromRows (0 : Matrix K J ℂ) A).toEuclideanLin x‖ ≤ _
  rw [complex_fromRows_zero_left_action_norm]
  exact A.l2_opNorm_mulVec x

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × J), we have

‖ Matrix.fromCols(A, 0)‖ ≤ ‖ A‖.
-/
lemma complex_fromCols_zero_norm_le (A : Matrix I J ℂ) :
    ‖Matrix.fromCols A (0 : Matrix I K ℂ)‖ ≤ ‖A‖ := by
  rw [← Matrix.l2_opNorm_conjTranspose (Matrix.fromCols A (0 : Matrix I K ℂ)),
    Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.conjTranspose_zero]
  exact (complex_fromRows_zero_norm_le Aᴴ).trans_eq (Matrix.l2_opNorm_conjTranspose A)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × J), we have

‖ Matrix.fromCols(0, A)‖ ≤ ‖ A‖.
-/
lemma complex_fromCols_zero_left_norm_le (A : Matrix I J ℂ) :
    ‖Matrix.fromCols (0 : Matrix I K ℂ) A‖ ≤ ‖A‖ := by
  rw [← Matrix.l2_opNorm_conjTranspose (Matrix.fromCols (0 : Matrix I K ℂ) A),
    Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.conjTranspose_zero]
  exact (complex_fromRows_zero_left_norm_le Aᴴ).trans_eq (Matrix.l2_opNorm_conjTranspose A)

/-- Bounding a block operator by the sum of its four block norms. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × J); B ∈ ℂ^(I × K); C ∈ ℂ^(L × J); D ∈ ℂ^(L × K), we have

‖ Matrix.fromBlocks(A, B, C, D)‖ ≤ ‖ A‖ + ‖ B‖ + ‖ C‖ + ‖ D‖.
-/
theorem complex_fromBlocks_norm_le (A : Matrix I J ℂ) (B : Matrix I K ℂ)
    (C : Matrix L J ℂ) (D : Matrix L K ℂ) :
    ‖Matrix.fromBlocks A B C D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
  have hA : ‖Matrix.fromBlocks A (0 : Matrix I K ℂ) (0 : Matrix L J ℂ) 0‖ ≤ ‖A‖ := by
    convert (complex_fromRows_zero_norm_le (K := L) (Matrix.fromCols A (0 : Matrix I K ℂ))).trans
      (complex_fromCols_zero_norm_le A) using 1
    congr 1
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks]
  have hB : ‖Matrix.fromBlocks (0 : Matrix I J ℂ) B (0 : Matrix L J ℂ) 0‖ ≤ ‖B‖ := by
    convert (complex_fromRows_zero_norm_le (K := L) (Matrix.fromCols (0 : Matrix I J ℂ) B)).trans
      (complex_fromCols_zero_left_norm_le B) using 1
    congr 1
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks]
  have hC : ‖Matrix.fromBlocks (0 : Matrix I J ℂ) (0 : Matrix I K ℂ) C 0‖ ≤ ‖C‖ := by
    convert (complex_fromRows_zero_left_norm_le (K := I) (Matrix.fromCols C (0 : Matrix L K ℂ))).trans
      (complex_fromCols_zero_norm_le C) using 1
    congr 1
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks]
  have hD : ‖Matrix.fromBlocks (0 : Matrix I J ℂ) (0 : Matrix I K ℂ) (0 : Matrix L J ℂ) D‖ ≤ ‖D‖ := by
    convert (complex_fromRows_zero_left_norm_le (K := I) (Matrix.fromCols (0 : Matrix L J ℂ) D)).trans
      (complex_fromCols_zero_left_norm_le D) using 1
    congr 1
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks]
  have he : Matrix.fromBlocks A B C D =
      Matrix.fromBlocks A 0 0 0 + Matrix.fromBlocks 0 B 0 0 +
      Matrix.fromBlocks 0 0 C 0 + Matrix.fromBlocks 0 0 0 D := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks]
  rw [he]
  exact (norm_add_le _ _).trans (by
    have h := norm_add_le (Matrix.fromBlocks A (0 : Matrix I K ℂ) (0 : Matrix L J ℂ) 0 +
      Matrix.fromBlocks (0 : Matrix I J ℂ) B 0 0) (Matrix.fromBlocks (0 : Matrix I J ℂ) 0 C 0)
    have h' := norm_add_le (Matrix.fromBlocks A (0 : Matrix I K ℂ) (0 : Matrix L J ℂ) 0)
      (Matrix.fromBlocks (0 : Matrix I J ℂ) B 0 0)
    linarith)

/-- Add the features `sqrt(u) I` to a synthesis matrix. -/
/-
Mathematical definition (normal notation): For A ∈ ℂ^(I × P); u ∈ ℝ, define

augmentedSynthesis(A, u) := Matrix.fromRows(A, (√u · 1)).
-/
def augmentedSynthesis (A : Matrix I P ℂ) (u : ℝ) : Matrix (I ⊕ P) P ℂ :=
  Matrix.fromRows A ((Real.sqrt u : ℂ) • (1 : Matrix P P ℂ))

/-- Augmentation adds exactly `u‖x‖²` to each squared output norm. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × P); u ∈ ℝ; x ∈ EuclideanSpace(ℂ, P), assume 0 ≤ u. Then

(‖ toEuclideanLin(augmentedSynthesis(A, u))(x)‖)² = (‖ A.toEuclideanLin(x)‖)² + u · (‖ x‖)².
-/
lemma augmentedSynthesis_action_norm_sq (A : Matrix I P ℂ) (u : ℝ) (hu : 0 ≤ u)
    (x : EuclideanSpace ℂ P) :
    ‖(augmentedSynthesis A u).toEuclideanLin x‖ ^ 2 =
      ‖A.toEuclideanLin x‖ ^ 2 + u * ‖x‖ ^ 2 := by
  simp only [augmentedSynthesis, PiLp.norm_sq_eq_of_L2, Matrix.toLpLin_apply,
    PiLp.toLp_apply, Matrix.fromRows_mulVec, Fintype.sum_sum_type]
  simp [Matrix.smul_mulVec, norm_smul, mul_pow, Real.sq_sqrt hu, Finset.mul_sum]

/-- Multiplying two augmented synthesis matrices yields the four explicit blocks. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × P); B ∈ ℂ^(J × P); u, v ∈ ℝ, we have

augmentedSynthesis(A, u) · augmentedSynthesis(B, v, ᴴ) = Matrix.fromBlocks((A · Bᴴ), (√v · A), (√u · Bᴴ), (√u · √v · 1)).
-/
lemma augmentedSynthesis_product (A : Matrix I P ℂ) (B : Matrix J P ℂ) (u v : ℝ) :
    augmentedSynthesis A u * (augmentedSynthesis B v)ᴴ =
      Matrix.fromBlocks (A * Bᴴ) ((Real.sqrt v : ℂ) • A)
        ((Real.sqrt u : ℂ) • Bᴴ) (((Real.sqrt u * Real.sqrt v : ℝ) : ℂ) • (1 : Matrix P P ℂ)) := by
  rw [augmentedSynthesis, augmentedSynthesis,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromRows_mul_fromCols]
  simp [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]

/-- The augmented product has the paper's four-block norm bound. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × P); B ∈ ℂ^(J × P); u, v ∈ ℝ, we have

‖ augmentedSynthesis(A, u) · augmentedSynthesis(B, v, ᴴ)‖ ≤ ‖ A · Bᴴ‖ + √v · ‖ A‖ + √u · ‖ B‖ + √u · √v.
-/
theorem augmentedSynthesis_product_norm_le (A : Matrix I P ℂ) (B : Matrix J P ℂ)
    (u v : ℝ) :
    ‖augmentedSynthesis A u * (augmentedSynthesis B v)ᴴ‖ ≤
      ‖A * Bᴴ‖ + Real.sqrt v * ‖A‖ + Real.sqrt u * ‖B‖ + Real.sqrt u * Real.sqrt v := by
  rw [augmentedSynthesis_product]
  have h := complex_fromBlocks_norm_le (A * Bᴴ) ((Real.sqrt v : ℂ) • A)
    ((Real.sqrt u : ℂ) • Bᴴ) (((Real.sqrt u * Real.sqrt v : ℝ) : ℂ) • (1 : Matrix P P ℂ))
  have hI : ‖(1 : Matrix P P ℂ)‖ ≤ 1 := by
    rcases isEmpty_or_nonempty P with hP | hP
    · letI := hP
      have hz : (1 : Matrix P P ℂ) = 0 := Subsingleton.elim _ _
      simp [hz]
    · letI := hP
      simp
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg v)),
    Matrix.l2_opNorm_conjTranspose] at h
  nlinarith [mul_le_mul_of_nonneg_left hI (mul_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg v))]

/-- Pointwise synthesis domination transfers to the norm of every product. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × P); A' ∈ ℂ^(K × P); B ∈ ℂ^(J × P), assume ∀ x ∈ EuclideanSpace(ℂ, P), ‖ A.toEuclideanLin(x)‖ ≤ ‖ toEuclideanLin(A')(x)‖. Then

‖ A · Bᴴ‖ ≤ ‖ A' · Bᴴ‖.
-/
lemma complex_product_norm_le_of_left_domination (A : Matrix I P ℂ) (A' : Matrix K P ℂ)
    (B : Matrix J P ℂ)
    (hA : ∀ x : EuclideanSpace ℂ P, ‖A.toEuclideanLin x‖ ≤ ‖A'.toEuclideanLin x‖) :
    ‖A * Bᴴ‖ ≤ ‖A' * Bᴴ‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖(A * Bᴴ).toEuclideanLin x‖ ≤ ‖A' * Bᴴ‖ * ‖x‖
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  have hprod : ‖(A' * Bᴴ).toEuclideanLin x‖ ≤ ‖A' * Bᴴ‖ * ‖x‖ :=
    (A' * Bᴴ).l2_opNorm_mulVec x
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply] at hprod
  exact (hA (Bᴴ.toEuclideanLin x)).trans hprod

/-- Domination of both feature Grams bounds their product in the original order. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × P); A' ∈ ℂ^(K × P); B ∈ ℂ^(J × P); B' ∈ ℂ^(L × P), assume ∀ x ∈ EuclideanSpace(ℂ, P), ‖ A.toEuclideanLin(x)‖ ≤ ‖ toEuclideanLin(A')(x)‖; ∀ x ∈ EuclideanSpace(ℂ, P), ‖ B.toEuclideanLin(x)‖ ≤ ‖ toEuclideanLin(B')(x)‖. Then

‖ A · Bᴴ‖ ≤ ‖ A' · B'(ᴴ)‖.
-/
theorem complex_product_norm_le_of_domination (A : Matrix I P ℂ) (A' : Matrix K P ℂ)
    (B : Matrix J P ℂ) (B' : Matrix L P ℂ)
    (hA : ∀ x : EuclideanSpace ℂ P, ‖A.toEuclideanLin x‖ ≤ ‖A'.toEuclideanLin x‖)
    (hB : ∀ x : EuclideanSpace ℂ P, ‖B.toEuclideanLin x‖ ≤ ‖B'.toEuclideanLin x‖) :
    ‖A * Bᴴ‖ ≤ ‖A' * B'ᴴ‖ := by
  apply (complex_product_norm_le_of_left_domination A A' B hA).trans
  have h := complex_product_norm_le_of_left_domination B B' A' hB
  simpa only [← Matrix.l2_opNorm_conjTranspose (B * A'ᴴ),
    ← Matrix.l2_opNorm_conjTranspose (B' * A'ᴴ), Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose] using h

/-- Squared action norm is the quadratic form of the synthesis Gram. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × P); x ∈ EuclideanSpace(ℂ, P), we have

(‖ A.toEuclideanLin(x)‖)² = re(inner(ℂ, x, toEuclideanLin((Aᴴ · A))(x))).
-/
lemma complex_action_norm_sq_eq_gram (A : Matrix I P ℂ) (x : EuclideanSpace ℂ P) :
    ‖A.toEuclideanLin x‖ ^ 2 = (inner ℂ x ((Aᴴ * A).toEuclideanLin x)).re := by
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]
  exact norm_sq_eq_re_inner (𝕜 := ℂ) _

/-- Gram operator error controls every synthesis energy error. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × P); B ∈ ℂ^(J × P); x ∈ EuclideanSpace(ℂ, P), we have

(‖ B.toEuclideanLin(x)‖)² - (‖ A.toEuclideanLin(x)‖)² ≤ ‖ Bᴴ · B - Aᴴ · A‖ · (‖ x‖)².
-/
theorem complex_action_energy_sub_le (A : Matrix I P ℂ) (B : Matrix J P ℂ)
    (x : EuclideanSpace ℂ P) :
    ‖B.toEuclideanLin x‖ ^ 2 - ‖A.toEuclideanLin x‖ ^ 2 ≤
      ‖Bᴴ * B - Aᴴ * A‖ * ‖x‖ ^ 2 := by
  calc
    _ = (inner ℂ x ((Bᴴ * B - Aᴴ * A).toEuclideanLin x)).re := by
      rw [complex_action_norm_sq_eq_gram, complex_action_norm_sq_eq_gram,
        map_sub]
      simp only [LinearMap.sub_apply, inner_sub_right, Complex.sub_re]
    _ ≤ ‖inner ℂ x ((Bᴴ * B - Aᴴ * A).toEuclideanLin x)‖ := Complex.re_le_norm _
    _ ≤ ‖x‖ * ‖(Bᴴ * B - Aᴴ * A).toEuclideanLin x‖ := norm_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ ‖x‖ * (‖Bᴴ * B - Aᴴ * A‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((Bᴴ * B - Aᴴ * A).l2_opNorm_mulVec x) (norm_nonneg _)
    _ = _ := by ring

/-- A Gram deviation bounded by `u` is dominated by adding `sqrt(u) I`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × P); B ∈ ℂ^(J × P); u ∈ ℝ; x ∈ EuclideanSpace(ℂ, P), assume 0 ≤ u; ‖ Bᴴ · B - Aᴴ · A‖ ≤ u. Then

‖ B.toEuclideanLin(x)‖ ≤ ‖ toEuclideanLin(augmentedSynthesis(A, u))(x)‖.
-/
theorem complex_gram_domination (A : Matrix I P ℂ) (B : Matrix J P ℂ)
    (u : ℝ) (hu : 0 ≤ u) (hgram : ‖Bᴴ * B - Aᴴ * A‖ ≤ u)
    (x : EuclideanSpace ℂ P) :
    ‖B.toEuclideanLin x‖ ≤ ‖(augmentedSynthesis A u).toEuclideanLin x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [augmentedSynthesis_action_norm_sq A u hu]
  have h := complex_action_energy_sub_le A B x
  have h' := mul_le_mul_of_nonneg_right hgram (sq_nonneg ‖x‖)
  linarith

/-- The exact nonorthogonal Gram perturbation estimate used in the manuscript. The leading term is the norm of the original product, not a product of trace bounds. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × P); B ∈ ℂ^(J × P); A' ∈ ℂ^(K × P); B' ∈ ℂ^(L × P); u, v ∈ ℝ, assume 0 ≤ u; 0 ≤ v; ‖ A'(ᴴ) · A' - Aᴴ · A‖ ≤ u; ‖ B'(ᴴ) · B' - Bᴴ · B‖ ≤ v. Then

‖ A' · B'(ᴴ)‖ ≤ ‖ A · Bᴴ‖ + √v · ‖ A‖ + √u · ‖ B‖ + √u · √v.
-/
theorem complex_gram_product_perturbation (A : Matrix I P ℂ) (B : Matrix J P ℂ)
    (A' : Matrix K P ℂ) (B' : Matrix L P ℂ) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hA : ‖A'ᴴ * A' - Aᴴ * A‖ ≤ u) (hB : ‖B'ᴴ * B' - Bᴴ * B‖ ≤ v) :
    ‖A' * B'ᴴ‖ ≤ ‖A * Bᴴ‖ + Real.sqrt v * ‖A‖ + Real.sqrt u * ‖B‖ +
      Real.sqrt u * Real.sqrt v := by
  exact (complex_product_norm_le_of_domination A' (augmentedSynthesis A u)
    B' (augmentedSynthesis B v) (complex_gram_domination A A' u hu hA)
    (complex_gram_domination B B' v hv hB)).trans
      (augmentedSynthesis_product_norm_le A B u v)

end

end CircuitCompiler
