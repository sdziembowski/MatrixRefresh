import Mathlib.LinearAlgebra.Matrix.Hadamard
import Proofs.Compiler.GateApproximation.MatrixPhase.JointTwisted



/-!
# Complex feature Schur multipliers

This proves the complex form of the vector-factor Schur bound used to separate character twists in the simultaneous decomposition.
-/

set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

open WithLp

namespace CircuitCompiler

noncomputable section

variable {I J P : Type*} [Fintype I] [Fintype J] [Fintype P] [DecidableEq J]

/-- The scalar complex matrix bound in squared-coordinate form. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For B ∈ ℂ^(I × J); x ∈ J → ℂ, we have

(∑ᵢ ((‖ ∑ⱼ (B(i, j) · x(j))‖)²)) ≤ (‖ B‖)² · ∑ⱼ ((‖ x(j)‖)²).
-/
theorem complex_sum_sq_matrix_action_le (B : Matrix I J ℂ) (x : J → ℂ) :
    (∑ i, ‖∑ j, B i j * x j‖ ^ 2) ≤ ‖B‖ ^ 2 * ∑ j, ‖x j‖ ^ 2 := by
  have h := B.l2_opNorm_mulVec (toLp 2 x)
  change ‖toLp 2 (B *ᵥ x)‖ ≤ ‖B‖ * ‖toLp 2 x‖ at h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [mul_pow, PiLp.norm_sq_eq_of_L2, Matrix.mulVec, dotProduct,
    ofLp_toLp, PiLp.toLp_apply] using hsq

/-- Applying one scalar matrix separately to each complex feature preserves its operator bound. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For B ∈ ℂ^(I × J); v ∈ J → EuclideanSpace(ℂ, P), we have

(∑ᵢ ((‖ ∑ⱼ (B(i, j) · v(j))‖)²)) ≤ (‖ B‖)² · ∑ⱼ ((‖ v(j)‖)²).
-/
theorem complex_sum_sq_vector_matrix_action_le (B : Matrix I J ℂ)
    (v : J → EuclideanSpace ℂ P) :
    (∑ i, ‖∑ j, B i j • v j‖ ^ 2) ≤ ‖B‖ ^ 2 * ∑ j, ‖v j‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm]
  calc
    (∑ p, ∑ i, ‖((∑ j, B i j • v j) p)‖ ^ 2)
        = ∑ p, ∑ i, ‖∑ j, B i j * v j p‖ ^ 2 := by simp
    _ ≤ ∑ p, ‖B‖ ^ 2 * ∑ j, ‖v j p‖ ^ 2 :=
      Finset.sum_le_sum fun p _ => complex_sum_sq_matrix_action_le B (fun j => v j p)
    _ = ‖B‖ ^ 2 * ∑ j, ∑ p, ‖v j p‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]

/-- An inner-product factorization, with conjugation in the first factor. -/
/-
Mathematical definition (normal notation): For a ∈ I → EuclideanSpace(ℂ, P); b ∈ J → EuclideanSpace(ℂ, P), define

complexInnerProductTable(a, b) := (i, j ↦ inner(ℂ, a(i), b(j))).
-/
def complexInnerProductTable (a : I → EuclideanSpace ℂ P) (b : J → EuclideanSpace ℂ P) :
    Matrix I J ℂ := fun i j => inner ℂ (a i) (b j)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ I → EuclideanSpace(ℂ, P); b ∈ J → EuclideanSpace(ℂ, P); B ∈ ℂ^(I × J); x ∈ J → ℂ; i ∈ I, we have

(complexInnerProductTable(a, b) ⊙ B) · ᵥ(x)(i) = inner(ℂ, a(i), (∑ⱼ (B(i, j) · (x(j) · b(j))))).
-/
lemma complexInnerProductTable_hadamard_mulVec (a : I → EuclideanSpace ℂ P)
    (b : J → EuclideanSpace ℂ P) (B : Matrix I J ℂ) (x : J → ℂ) (i : I) :
    ((complexInnerProductTable a b ⊙ B) *ᵥ x) i =
      inner ℂ (a i) (∑ j, B i j • (x j • b j)) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.hadamard_apply, complexInnerProductTable,
    inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The Schur multiplier norm is controlled by pointwise feature energy. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ I → EuclideanSpace(ℂ, P); b ∈ J → EuclideanSpace(ℂ, P); B ∈ ℂ^(I × J); A, C ∈ ℝ, assume 0 ≤ A; 0 ≤ C; ∀ i, ‖ a(i)‖ ≤ A; ∀ j, ‖ b(j)‖ ≤ C. Then

‖ complexInnerProductTable(a, b) ⊙ B‖ ≤ A · C · ‖ B‖.
-/
theorem complex_schur_multiplier_norm_le_of_bounds (a : I → EuclideanSpace ℂ P)
    (b : J → EuclideanSpace ℂ P) (B : Matrix I J ℂ) (A C : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ A) (hb : ∀ j, ‖b j‖ ≤ C) :
    ‖complexInnerProductTable a b ⊙ B‖ ≤ A * C * ‖B‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  change ‖(toLp 2 ((complexInnerProductTable a b ⊙ B) *ᵥ x) : EuclideanSpace ℂ I)‖ ^ 2 ≤
    (A * C * ‖B‖ * ‖x‖) ^ 2
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    (∑ i, ‖(((complexInnerProductTable a b ⊙ B) *ᵥ x) i)‖ ^ 2)
        ≤ A ^ 2 * ∑ i, ‖∑ j, B i j • (x j • b j)‖ ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i _
          rw [complexInnerProductTable_hadamard_mulVec]
          have h := (norm_inner_le_norm (𝕜 := ℂ) (a i)
            (∑ j, B i j • (x j • b j))).trans
            (mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _))
          simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2
    _ ≤ A ^ 2 * (‖B‖ ^ 2 * ∑ j, ‖x j • b j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (complex_sum_sq_vector_matrix_action_le B (fun j => x j • b j)) (sq_nonneg A)
    _ ≤ A ^ 2 * (‖B‖ ^ 2 * (C ^ 2 * ∑ j, ‖x j‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg A)
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg ‖B‖)
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, mul_pow]
      have hsq := pow_le_pow_left₀ (norm_nonneg _) (hb j) 2
      nlinarith [sq_nonneg ‖x j‖]
    _ = (A * C * ‖B‖ * ‖x‖) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, PiLp.norm_sq_eq_of_L2]
      ring

/-- The same bound using supremum norms of the feature families. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ I → EuclideanSpace(ℂ, P); b ∈ J → EuclideanSpace(ℂ, P); B ∈ ℂ^(I × J), we have

‖ complexInnerProductTable(a, b) ⊙ B‖ ≤ ‖ a‖ · ‖ b‖ · ‖ B‖.
-/
theorem complex_schur_multiplier_norm_le (a : I → EuclideanSpace ℂ P)
    (b : J → EuclideanSpace ℂ P) (B : Matrix I J ℂ) :
    ‖complexInnerProductTable a b ⊙ B‖ ≤ ‖a‖ * ‖b‖ * ‖B‖ :=
  complex_schur_multiplier_norm_le_of_bounds a b B ‖a‖ ‖b‖ (norm_nonneg _) (norm_nonneg _)
    (fun i => norm_le_pi_norm a i) (fun j => norm_le_pi_norm b j)

/-- Coordinatewise complex conjugation preserves the feature norm. -/
/-
Mathematical definition (normal notation): For v ∈ EuclideanSpace(ℂ, P), define

conjugateFeature(v) := toLp(2, ((p ↦ star(v(p))))).
-/
def conjugateFeature (v : EuclideanSpace ℂ P) : EuclideanSpace ℂ P :=
  toLp 2 (fun p => star (v p))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For v ∈ EuclideanSpace(ℂ, P), we have

‖ conjugateFeature(v)‖ = ‖ v‖.
-/
lemma conjugateFeature_norm (v : EuclideanSpace ℂ P) : ‖conjugateFeature v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  simp [conjugateFeature, PiLp.norm_sq_eq_of_L2]

/-- The singular-product convention used in the manuscript. -/
/-
Mathematical definition (normal notation): For ξ ∈ I → EuclideanSpace(ℂ, P); ζ ∈ J → EuclideanSpace(ℂ, P), define

complexProductTable(ξ, ζ) := (i, j ↦ ∑ₚ (ξ(i, p) · star(ζ(j, p)))).
-/
def complexProductTable (ξ : I → EuclideanSpace ℂ P) (ζ : J → EuclideanSpace ℂ P) :
    Matrix I J ℂ := fun i j => ∑ p, ξ i p * star (ζ j p)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ ∈ I → EuclideanSpace(ℂ, P); ζ ∈ J → EuclideanSpace(ℂ, P), we have

complexProductTable(ξ, ζ) = complexInnerProductTable(((i ↦ conjugateFeature(ξ(i)))), ((j ↦ conjugateFeature(ζ(j))))).
-/
lemma complexProductTable_eq_innerProductTable (ξ : I → EuclideanSpace ℂ P)
    (ζ : J → EuclideanSpace ℂ P) :
    complexProductTable ξ ζ =
      complexInnerProductTable (fun i => conjugateFeature (ξ i)) (fun j => conjugateFeature (ζ j)) := by
  ext i j
  simp [complexProductTable, complexInnerProductTable, conjugateFeature, PiLp.inner_apply,
    RCLike.inner_apply, mul_comm]

/-- The paper's Schur feature bound for arbitrary complex singular factors. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ ∈ I → EuclideanSpace(ℂ, P); ζ ∈ J → EuclideanSpace(ℂ, P); B ∈ ℂ^(I × J); A, C ∈ ℝ, assume 0 ≤ A; 0 ≤ C; ∀ i, ‖ ξ(i)‖ ≤ A; ∀ j, ‖ ζ(j)‖ ≤ C. Then

‖ B ⊙ complexProductTable(ξ, ζ)‖ ≤ ‖ B‖ · A · C.
-/
theorem complex_feature_schur_bound (ξ : I → EuclideanSpace ℂ P)
    (ζ : J → EuclideanSpace ℂ P) (B : Matrix I J ℂ) (A C : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hξ : ∀ i, ‖ξ i‖ ≤ A) (hζ : ∀ j, ‖ζ j‖ ≤ C) :
    ‖B ⊙ complexProductTable ξ ζ‖ ≤ ‖B‖ * A * C := by
  rw [Matrix.hadamard_comm, complexProductTable_eq_innerProductTable]
  have h := complex_schur_multiplier_norm_le_of_bounds
    (fun i => conjugateFeature (ξ i)) (fun j => conjugateFeature (ζ j)) B A C hA hC
    (fun i => by simpa only [conjugateFeature_norm] using hξ i)
    (fun j => by simpa only [conjugateFeature_norm] using hζ j)
  convert h using 1 <;> ring

end

end CircuitCompiler
