import Proofs.Compiler.GateApproximation.MatrixPhase.JointFourCycle
import Proofs.Compiler.Foundations.LinearAlgebra.GramBounds



/-!
# Complex operator control of real rectangle tests
-/
set_option autoImplicit false

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler

open TableAnalysis MatrixRefresh

noncomputable section

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-
Mathematical definition (normal notation): For f ∈ X → ℝ, define

realTestVector(f) := WithLp.toLp(2, ((x ↦ f(x)))).
-/
def realTestVector (f : X → ℝ) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun x => (f x : ℂ))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ X → ℝ, we have

(‖ realTestVector(f)‖)² = |X| · ‖ f‖₂².
-/
lemma realTestVector_norm_sq (f : X → ℝ) :
    ‖realTestVector f‖ ^ 2 = (Fintype.card X : ℝ) * signedL2Sq f := by
  have hd : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [realTestVector, PiLp.norm_sq_eq_of_L2, PiLp.toLp_apply,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, signedL2Sq, uavg]
  field_simp

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ X → ℝ, we have

‖ realTestVector(f)‖ = √(|X|) · ‖ f‖₂.
-/
lemma realTestVector_norm (f : X → ℝ) :
    ‖realTestVector f‖ = Real.sqrt (Fintype.card X : ℝ) * signedL2 f := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (signedL2_nonneg _))).1
  rw [realTestVector_norm_sq, mul_pow, signedL2_sq, Real.sq_sqrt (Nat.cast_nonneg _)]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f, g ∈ X → ℝ; A ∈ ℂ^(X × X), we have

re(inner(ℂ, realTestVector(f), A.toEuclideanLin(realTestVector(g)))) = ∑ₓ (∑_y (f(x) · g(y) · re(A(x, y)))).
-/
lemma realTestVector_inner_matrix (f g : X → ℝ) (A : Matrix X X ℂ) :
    (inner ℂ (realTestVector f) (A.toEuclideanLin (realTestVector g))).re =
      ∑ x, ∑ y, f x * g y * (A x y).re := by
  simp only [realTestVector, PiLp.inner_apply, RCLike.inner_apply,
    Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, PiLp.toLp_apply,
    Complex.star_def, Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- A real rectangle test against a complex table is controlled by the uniformly normalized complex operator norm and the exact rectangle weight. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f, g ∈ X → ℝ; A ∈ ℂ^(X × X), we have

|𝔼ₓ [𝔼_y [f(x) · g(y) · re(A(x, y))]]| ≤ rectangleWeight(f, g) · (‖ A‖ / |X|).
-/
theorem complex_rectangle_pairing (f g : X → ℝ) (A : Matrix X X ℂ) :
    |uavg (fun x => uavg (fun y => f x * g y * (A x y).re))| ≤
      rectangleWeight f g * (‖A‖ / Fintype.card X) := by
  have hd : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  have hraw : |∑ x, ∑ y, f x * g y * (A x y).re| ≤
      ‖realTestVector f‖ * ‖A‖ * ‖realTestVector g‖ := by
    rw [← realTestVector_inner_matrix]
    calc
      _ ≤ ‖inner ℂ (realTestVector f) (A.toEuclideanLin (realTestVector g))‖ :=
        Complex.abs_re_le_norm _
      _ ≤ ‖realTestVector f‖ * ‖A.toEuclideanLin (realTestVector g)‖ :=
        norm_inner_le_norm (𝕜 := ℂ) _ _
      _ ≤ ‖realTestVector f‖ * (‖A‖ * ‖realTestVector g‖) :=
        mul_le_mul_of_nonneg_left (A.l2_opNorm_mulVec _) (norm_nonneg _)
      _ = _ := by ring
  rw [realTestVector_norm, realTestVector_norm] at hraw
  have hs := Real.sq_sqrt hd.le
  have hscaled := mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr (sq_nonneg (Fintype.card X : ℝ)))
  have havg : uavg (fun x => uavg (fun y => f x * g y * (A x y).re)) =
      ((Fintype.card X : ℝ) ^ 2)⁻¹ * (∑ x, ∑ y, f x * g y * (A x y).re) := by
    simp only [uavg, ← Finset.mul_sum]
    ring
  rw [havg, abs_mul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  apply hscaled.trans_eq
  unfold rectangleWeight
  have heq : Real.sqrt (Fintype.card X : ℝ) * signedL2 f * ‖A‖ *
      (Real.sqrt (Fintype.card X : ℝ) * signedL2 g) =
      (Fintype.card X : ℝ) * (signedL2 f * signedL2 g * ‖A‖) := by
    calc
      _ = (Real.sqrt (Fintype.card X : ℝ)) ^ 2 * (signedL2 f * signedL2 g * ‖A‖) := by ring
      _ = _ := by rw [hs]
  rw [heq]
  field_simp

end

end CircuitCompiler
