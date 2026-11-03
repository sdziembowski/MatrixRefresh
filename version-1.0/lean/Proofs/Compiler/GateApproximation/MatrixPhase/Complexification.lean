import Proofs.Compiler.GateApproximation.MatrixPhase.JointFourCycle



/-!
# Real and complex Euclidean matrix norms agree
-/
set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler

noncomputable section

variable {X : Type*} [Fintype X] [DecidableEq X]

/-
Mathematical definition (normal notation): For x ∈ EuclideanSpace(ℝ, X), define

complexifyVector(x) := WithLp.toLp(2, ((i ↦ x(i)))).
-/
def complexifyVector (x : EuclideanSpace ℝ X) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun i => (x i : ℂ))

/-
Mathematical definition (normal notation): For x ∈ EuclideanSpace(ℂ, X), define

realPartVector(x) := WithLp.toLp(2, ((i ↦ re(x(i))))).
-/
def realPartVector (x : EuclideanSpace ℂ X) : EuclideanSpace ℝ X :=
  WithLp.toLp 2 (fun i => (x i).re)

/-
Mathematical definition (normal notation): For x ∈ EuclideanSpace(ℂ, X), define

imagPartVector(x) := WithLp.toLp(2, ((i ↦ im(x(i))))).
-/
def imagPartVector (x : EuclideanSpace ℂ X) : EuclideanSpace ℝ X :=
  WithLp.toLp 2 (fun i => (x i).im)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For x ∈ EuclideanSpace(ℝ, X), we have

‖ complexifyVector(x)‖ = ‖ x‖.
-/
lemma complexifyVector_norm (x : EuclideanSpace ℝ X) : ‖complexifyVector x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  simp only [complexifyVector, PiLp.norm_sq_eq_of_L2, Complex.norm_real]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For x ∈ EuclideanSpace(ℂ, X), we have

(‖ x‖)² = (‖ realPartVector(x)‖)² + (‖ imagPartVector(x)‖)².
-/
lemma complexVector_norm_sq (x : EuclideanSpace ℂ X) :
    ‖x‖ ^ 2 = ‖realPartVector x‖ ^ 2 + ‖imagPartVector x‖ ^ 2 := by
  simp only [realPartVector, imagPartVector, PiLp.norm_sq_eq_of_L2,
    Real.norm_eq_abs, sq_abs, Complex.sq_norm, Complex.normSq_apply,
    ← pow_two, Finset.sum_add_distrib]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(X × X); x ∈ EuclideanSpace(ℂ, X), we have

realPartVector(toEuclideanLin((Complex.ofReal_*A))(x)) = A.toEuclideanLin(realPartVector(x)).
-/
lemma complexMatrix_realPart_mul (A : Matrix X X ℝ) (x : EuclideanSpace ℂ X) :
    realPartVector ((A.map Complex.ofReal).toEuclideanLin x) =
      A.toEuclideanLin (realPartVector x) := by
  ext i
  simp [realPartVector, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(X × X); x ∈ EuclideanSpace(ℂ, X), we have

imagPartVector(toEuclideanLin((Complex.ofReal_*A))(x)) = A.toEuclideanLin(imagPartVector(x)).
-/
lemma complexMatrix_imagPart_mul (A : Matrix X X ℝ) (x : EuclideanSpace ℂ X) :
    imagPartVector ((A.map Complex.ofReal).toEuclideanLin x) =
      A.toEuclideanLin (imagPartVector x) := by
  ext i
  simp [imagPartVector, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(X × X); x ∈ EuclideanSpace(ℝ, X), we have

toEuclideanLin((Complex.ofReal_*A))(complexifyVector(x)) = complexifyVector(A.toEuclideanLin(x)).
-/
lemma complexMatrix_complexify_mul (A : Matrix X X ℝ) (x : EuclideanSpace ℝ X) :
    (A.map Complex.ofReal).toEuclideanLin (complexifyVector x) =
      complexifyVector (A.toEuclideanLin x) := by
  ext i
  simp [complexifyVector, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

/-- Extending real matrix coefficients to the complex numbers preserves the Euclidean operator norm exactly. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(X × X), we have

‖ (Complex.ofReal_*A)‖ = ‖ A‖.
-/
theorem complexMatrix_ofReal_norm (A : Matrix X X ℝ) :
    ‖A.map Complex.ofReal‖ = ‖A‖ := by
  apply le_antisymm
  · rw [Matrix.l2_opNorm_def]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
    intro x
    change ‖(A.map Complex.ofReal).toEuclideanLin x‖ ≤ ‖A‖ * ‖x‖
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1
    rw [complexVector_norm_sq, complexMatrix_realPart_mul, complexMatrix_imagPart_mul,
      mul_pow, complexVector_norm_sq]
    have hr := pow_le_pow_left₀ (norm_nonneg _) (A.l2_opNorm_mulVec (realPartVector x)) 2
    have hi := pow_le_pow_left₀ (norm_nonneg _) (A.l2_opNorm_mulVec (imagPartVector x)) 2
    change ‖A.toEuclideanLin (realPartVector x)‖ ^ 2 ≤ (‖A‖ * ‖realPartVector x‖) ^ 2 at hr
    change ‖A.toEuclideanLin (imagPartVector x)‖ ^ 2 ≤ (‖A‖ * ‖imagPartVector x‖) ^ 2 at hi
    simp only [mul_pow] at hr hi
    nlinarith
  · rw [Matrix.l2_opNorm_def]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (A.map Complex.ofReal))
    intro x
    change ‖A.toEuclideanLin x‖ ≤ ‖A.map Complex.ofReal‖ * ‖x‖
    have h := (A.map Complex.ofReal).l2_opNorm_mulVec (complexifyVector x)
    change ‖(A.map Complex.ofReal).toEuclideanLin (complexifyVector x)‖ ≤
      ‖A.map Complex.ofReal‖ * ‖complexifyVector x‖ at h
    rw [complexMatrix_complexify_mul, complexifyVector_norm, complexifyVector_norm] at h
    exact h

end

end CircuitCompiler
