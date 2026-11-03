import Proofs.Compiler.GateApproximation.Interfaces.Residual
import Proofs.Compiler.GateApproximation.MatrixPhase.RefreshAnswerProbabilities



/-!
# Consistency cancellation for injective old-data encodings

The two feature maps give genuine row and column restrictions of the full Fourier matrix. Using both restrictions gives the injective-feature bound `2 / card X` for the sign table (and `1 / card X` for the paper's J).
-/

set_option autoImplicit false

set_option maxHeartbeats 1500000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker

namespace CircuitCompiler.AnswerApproximation

open Refresh MatrixRefresh TableAnalysis RefreshAnalysis

noncomputable section

section Restriction

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-
Mathematical definition (normal notation): For e ∈ I → J, define

coordinateEmbedding(e) := (j, i ↦ { 1 if j = e(i),; 0 otherwise }).
-/
def coordinateEmbedding (e : I → J) : Matrix J I ℂ :=
  fun j i => if j = e i then 1 else 0

omit [Fintype I] in
-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ I → J, assume e is injective. Then

coordinateEmbedding(e, ᴴ) · coordinateEmbedding(e) = 1.
-/
theorem coordinateEmbedding_gram (e : I → J) (he : Function.Injective e) :
    (coordinateEmbedding e)ᴴ * coordinateEmbedding e = 1 := by
  ext i k
  simp [coordinateEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, he.eq_iff, eq_comm]

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ I → J, assume I ≠ ∅; e is injective. Then

‖ coordinateEmbedding(e)‖ = 1.
-/
theorem coordinateEmbedding_norm [Nonempty I] (e : I → J)
    (he : Function.Injective e) : ‖coordinateEmbedding e‖ = 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (coordinateEmbedding e)
  rw [coordinateEmbedding_gram e he, norm_one] at h
  nlinarith [norm_nonneg (coordinateEmbedding e)]

omit [Fintype I] [DecidableEq I] in
-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(J × J); e, f ∈ I → J, we have

A.submatrix(e, f) = coordinateEmbedding(e, ᴴ) · A · coordinateEmbedding(f).
-/
theorem submatrix_embedding (A : Matrix J J ℂ) (e f : I → J) :
    A.submatrix e f = (coordinateEmbedding e)ᴴ * A * coordinateEmbedding f := by
  ext i k
  simp [coordinateEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.submatrix_apply]

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(J × J); e, f ∈ I → J, assume I ≠ ∅; e is injective; f is injective. Then

‖ A.submatrix(e, f)‖ ≤ ‖ A‖.
-/
theorem injective_submatrix_norm_le [Nonempty I] (A : Matrix J J ℂ)
    (e f : I → J) (he : Function.Injective e) (hf : Function.Injective f) :
    ‖A.submatrix e f‖ ≤ ‖A‖ := by
  rw [submatrix_embedding]
  calc
    _ ≤ ‖(coordinateEmbedding e)ᴴ * A‖ * ‖coordinateEmbedding f‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ (‖(coordinateEmbedding e)ᴴ‖ * ‖A‖) * ‖coordinateEmbedding f‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = ‖A‖ := by
      rw [Matrix.l2_opNorm_conjTranspose, coordinateEmbedding_norm e he,
        coordinateEmbedding_norm f hf]
      ring

end Restriction

variable {F X : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype X] [DecidableEq X] [Nonempty X] {m : ℕ}

/-
Mathematical definition (normal notation): For a, b ∈ X → U(F, m); ψ ∈ AddChar(F, ℂ), define

featureFourier(a, b, ψ) := (x, y ↦ ψ((a(x) · b(y)))).
-/
def featureFourier (a b : X → U F m) (ψ : AddChar F ℂ) : Matrix X X ℂ :=
  fun x y => ψ (dot (a x).val (b y).val)

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); ψ ∈ AddChar(F, ℂ), assume a is injective; b is injective; ψ.IsPrimitive. Then

‖ featureFourier(a, b, ψ)‖ ≤ √(|F|ᵐ).
-/
theorem injective_feature_fourier_norm
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖featureFourier a b ψ‖ ≤
      Real.sqrt (vectorCard F m : ℝ) := by
  have h := injective_submatrix_norm_le (dotFourierMatrix m ψ)
    (fun x => (a x).val) (fun y => (b y).val)
    (Subtype.val_injective.comp ha) (Subtype.val_injective.comp hb)
  rw [dotFourierMatrix_norm m ψ hψ] at h
  exact h


/-
Mathematical statement (normal notation): Over the binary field, let m ≥ 2 and let a,b:X → 𝔽₂ᵐ ∖ {0} be injective. Let S be the table taking value 1 on tuples with a(x) · b(y) = u · v, and value -1 elsewhere. Then its normalized operator norm satisfies

‖S‖ₒₚ ≤ 2/|X|.
-/
theorem injective_consistency_sign_op (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b) :
    largestSingularCoefficient (refreshSign (refreshConsistent a b)) ≤ 2 / (Fintype.card X : ℝ) := by
  let ψ := fieldCharacter F
  have hψ : ψ.IsPrimitive := fieldCharacter_primitive
  have he : (refreshSign (refreshConsistent a b)).map Complex.ofReal =
      jointTwistMatrix (fun x y => dot (a x).val (b y).val) m ψ 1 := by
    ext x y
    simp only [Matrix.map_apply, refreshSign, jointTwistMatrix, one_mul,
      binary_fieldCharacter hq, sub_eq_zero, refreshConsistent, ψ]
    by_cases h : dot x.2.val y.2.val = dot (a x.1).val (b y.1).val
    · simp [h]
    · simp [h, Ne.symm h]
  have hold := injective_feature_fourier_norm a b ha hb ψ hψ
  have hnew : ‖nonzeroDotFourierMatrix m (ψ.mulShift (-1))‖ ≤
      Real.sqrt (vectorCard F m : ℝ) := by
    have h := subtypeMatrix_norm_le (fun v : V F m => v ≠ 0)
      (dotFourierMatrix m (ψ.mulShift (-1)))
    rw [dotFourierMatrix_norm _ _
      (fieldCharacter_mulShift_primitive ψ hψ (-1) (by norm_num))] at h
    exact h
  have hraw : ‖(refreshSign (refreshConsistent a b)).map Complex.ofReal‖ ≤
      (vectorCard F m : ℝ) := by
    rw [he, jointTwistMatrix_factor]
    simp only [one_mul]
    exact (complex_kronecker_norm_le _ _).trans
      ((mul_le_mul hold hnew (norm_nonneg _) (Real.sqrt_nonneg _)).trans_eq
        (Real.mul_self_sqrt (Nat.cast_nonneg _)))
  rw [complexMatrix_ofReal_norm] at hraw
  have hD : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  have hQ := vectorCard_real_ge_four (F := F) hm
  have hcard : (Fintype.card (U F m) : ℝ) = (vectorCard F m : ℝ) - 1 := card_U_real F m
  unfold largestSingularCoefficient
  rw [Fintype.card_prod, Nat.cast_mul, hcard]
  apply (div_le_iff₀ (mul_pos hD (by linarith))).2
  have hc : (2 / (Fintype.card X : ℝ)) *
      ((Fintype.card X : ℝ) * ((vectorCard F m : ℝ) - 1)) = 2 * ((vectorCard F m : ℝ) - 1) := by
    field_simp
  rw [hc]
  linarith

end

end CircuitCompiler.AnswerApproximation
