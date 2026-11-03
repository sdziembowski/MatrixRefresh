import Mathlib.LinearAlgebra.Matrix.Kronecker
import Proofs.Compiler.GateApproximation.MatrixPhase.JointFourCycle
import Proofs.Compiler.GateApproximation.MatrixPhase.JointFourier
import Proofs.Compiler.GateApproximation.MatrixPhase.JointSchur



/-!
# Operator bound for nonzero joint-port character twists

A twist separates into an arbitrary unit-modulus old-port table and a nonzero dot-product Fourier table on the new ports. The product estimate below keeps the normalization by both port-space cardinalities explicit.
-/

set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker

namespace CircuitCompiler

open Refresh

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Euclidean operator norm is submultiplicative for the matrix tensor product. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); B ∈ ℂ^(J × J), we have

‖ A ⊗ ₖ(B)‖ ≤ ‖ A‖ · ‖ B‖.
-/
theorem complex_kronecker_norm_le (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    ‖A ⊗ₖ B‖ ≤ ‖A‖ * ‖B‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
  change ‖(A ⊗ₖ B).toEuclideanLin x‖ ^ 2 ≤ (‖A‖ * ‖B‖ * ‖x‖) ^ 2
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Matrix.toLpLin_apply, PiLp.toLp_apply, Matrix.mulVec, dotProduct,
    Matrix.kronecker_apply, Fintype.sum_prod_type]
  have he (i : I) (u : J) :
      (∑ j, ∑ v, A i j * B u v * x (j, v)) =
        ∑ j, A i j * (∑ v, B u v * x (j, v)) := by
    simp only [Finset.mul_sum, mul_assoc]
  simp_rw [he]
  rw [Finset.sum_comm]
  calc
    (∑ u, ∑ i, ‖∑ j, A i j * (∑ v, B u v * x (j, v))‖ ^ 2)
        ≤ ∑ u, ‖A‖ ^ 2 * ∑ j, ‖∑ v, B u v * x (j, v)‖ ^ 2 :=
      Finset.sum_le_sum (fun u _ => complex_sum_sq_matrix_action_le A
        (fun j => ∑ v, B u v * x (j, v)))
    _ = ‖A‖ ^ 2 * ∑ j, ∑ u, ‖∑ v, B u v * x (j, v)‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ ‖A‖ ^ 2 * ∑ j, ‖B‖ ^ 2 * ∑ v, ‖x (j, v)‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact Finset.sum_le_sum (fun j _ => complex_sum_sq_matrix_action_le B (fun v => x (j, v)))
    _ = (‖A‖ * ‖B‖ * ‖x‖) ^ 2 := by
      rw [← Finset.mul_sum, mul_pow, mul_pow, PiLp.norm_sq_eq_of_L2,
        Fintype.sum_prod_type]
      ring

/-- Unit-modulus entries have normalized operator norm at most one. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I), assume ∀ i, j, ‖ A(i, j)‖ = 1. Then

‖ A‖ ≤ |I|.
-/
theorem complex_phase_norm_le_card (A : Matrix I I ℂ) (hA : ∀ i j, ‖A i j‖ = 1) :
    ‖A‖ ≤ Fintype.card I := by
  have h := complexMatrix_norm_sq_le_L2Sq A
  have he : complexMatrixL2Sq A = (Fintype.card I : ℝ) ^ 2 := by
    simp [complexMatrixL2Sq, hA, pow_two]
  rw [he] at h
  exact (sq_le_sq₀ (norm_nonneg _) (Nat.cast_nonneg _)).1 h

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Nonzero scalar shifts of a primitive character remain primitive. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ψ ∈ AddChar(F, ℂ); c ∈ F, assume ψ.IsPrimitive; c ≠ 0. Then

IsPrimitive(ψ.mulShift(c)).
-/
theorem fieldCharacter_mulShift_primitive (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (c : F) (hc : c ≠ 0) : (ψ.mulShift c).IsPrimitive := by
  intro a ha
  simpa only [AddChar.mulShift_mulShift] using hψ (mul_ne_zero hc ha)

/-- An arbitrary unit-modulus old-port factor times a Fourier new-port factor has the required `sqrt(Q)/(Q−1)` uniform operator bound. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); n ∈ ℕ; ψ ∈ AddChar(F, ℂ), assume I ≠ ∅; ∀ i, j, ‖ A(i, j)‖ = 1; ψ.IsPrimitive. Then

‖ A ⊗ ₖ(nonzeroDotFourierMatrix, n, ψ)‖ / |I| · |U(F, n)| ≤ √((|F|)ⁿ) / (|F|)ⁿ - 1.
-/
theorem joint_character_uniform_norm_le [Nonempty I] (A : Matrix I I ℂ)
    (hA : ∀ i j, ‖A i j‖ = 1) (n : ℕ) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖A ⊗ₖ nonzeroDotFourierMatrix n ψ‖ /
        (Fintype.card I * Fintype.card (U F n) : ℝ) ≤
      Real.sqrt (fieldCard F ^ n : ℕ) / ((fieldCard F ^ n - 1 : ℕ) : ℝ) := by
  have hi : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := (complex_kronecker_norm_le A (nonzeroDotFourierMatrix n ψ)).trans
    (mul_le_mul_of_nonneg_right (complex_phase_norm_le_card A hA) (norm_nonneg _))
  calc
    _ ≤ ((Fintype.card I : ℝ) * ‖nonzeroDotFourierMatrix n ψ‖) /
        (Fintype.card I * Fintype.card (U F n) : ℝ) :=
      div_le_div_of_nonneg_right h (by positivity)
    _ = ‖nonzeroDotFourierMatrix n ψ‖ / (Fintype.card (U F n) : ℝ) := by
      rw [mul_div_mul_left _ _ (ne_of_gt hi)]
    _ ≤ _ := nonzeroDotFourierMatrix_uniform_norm_le n ψ hψ

/-- The old bilinear expression can be arbitrary: only its unit phase is used. -/
/-
Mathematical definition (normal notation): For s ∈ I → I → F; n ∈ ℕ; ψ ∈ AddChar(F, ℂ); c ∈ F, define

jointTwistMatrix(s, n, ψ, c) := (x, y ↦ ψ((c · (s((x)₁, (y)₁) - ((x)₂ · (y)₂))))).
-/
def jointTwistMatrix (s : I → I → F) (n : ℕ) (ψ : AddChar F ℂ) (c : F) :
    Matrix (I × U F n) (I × U F n) ℂ :=
  fun x y => ψ (c * (s x.1 y.1 - dot x.2.val y.2.val))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ I → I → F; n ∈ ℕ; ψ ∈ AddChar(F, ℂ); c ∈ F, we have

jointTwistMatrix(s, n, ψ, c) = ((i, j ↦ ψ((c · s(i, j))))) ⊗ ₖ(nonzeroDotFourierMatrix, n, ψ.mulShift(-(c))).
-/
lemma jointTwistMatrix_factor (s : I → I → F) (n : ℕ) (ψ : AddChar F ℂ) (c : F) :
    jointTwistMatrix s n ψ c =
      (fun i j => ψ (c * s i j)) ⊗ₖ nonzeroDotFourierMatrix n (ψ.mulShift (-c)) := by
  ext x y
  change ψ (c * (s x.1 y.1 - dot x.2.val y.2.val)) =
    ψ (c * s x.1 y.1) * ψ ((-c) * dot x.2.val y.2.val)
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- Nonzero joint-port twists have exactly the Fourier restriction bound. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ I → I → F; n ∈ ℕ; ψ ∈ AddChar(F, ℂ); c ∈ F, assume I ≠ ∅; ψ.IsPrimitive; c ≠ 0. Then

‖ jointTwistMatrix(s, n, ψ, c)‖ / |I| · |U(F, n)| ≤ √((|F|)ⁿ) / (|F|)ⁿ - 1.
-/
theorem jointTwistMatrix_uniform_norm_le [Nonempty I]
    (s : I → I → F) (n : ℕ) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (c : F) (hc : c ≠ 0) :
    ‖jointTwistMatrix s n ψ c‖ /
        (Fintype.card I * Fintype.card (U F n) : ℝ) ≤
      Real.sqrt (fieldCard F ^ n : ℕ) / ((fieldCard F ^ n - 1 : ℕ) : ℝ) := by
  rw [jointTwistMatrix_factor]
  exact joint_character_uniform_norm_le (fun i j => ψ (c * s i j))
    (fun i j => ψ.norm_apply _) n (ψ.mulShift (-c))
    (fieldCharacter_mulShift_primitive ψ hψ (-c) (neg_ne_zero.mpr hc))

/-- The harmless factor two in the manuscript follows whenever `Q ≥ 2`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Q ∈ ℝ, assume 2 ≤ Q. Then

√Q / (Q - 1) ≤ 2 / √Q.
-/
lemma sqrt_div_sub_one_le (Q : ℝ) (hQ : 2 ≤ Q) :
    Real.sqrt Q / (Q - 1) ≤ 2 / Real.sqrt Q := by
  have hpos : 0 < Q := by linarith
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.2 hpos
  apply (div_le_div_iff₀ (by linarith : 0 < Q - 1) hs).2
  nlinarith [Real.sq_sqrt hpos.le]

end

end CircuitCompiler
