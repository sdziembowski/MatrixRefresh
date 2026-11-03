import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Proofs.Compiler.Foundations.LinearAlgebra.SchurMultiplier



/-!
# Nuclear norm as the dual of the Euclidean operator norm

This definition uses the real counting pairing and the L2 operator norm on matrices. It is intrinsically independent of a selected singular-vector basis. The singular-value identification is proved separately from genuine SVDs.
-/

set_option autoImplicit false

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace TableAnalysis

noncomputable section

variable {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
  [DecidableEq κ]

/-
Mathematical definition (normal notation): The counting-measure pairing of rectangular matrices is

⟨ A,B⟩_count := ∑_(i,j) Aᵢⱼ · Bᵢⱼ.

It is an unnormalized sum.
-/
def countingPairing (A B : Matrix ι κ ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

/- Mathematical definition (normal notation): For a fixed matrix A, define the linear functional B ↦ ∑_(i,j) Aᵢⱼ · Bᵢⱼ. Linearity is with respect to addition and real scalar multiplication of B. -/
def countingPairingLinear (A : Matrix ι κ ℝ) : Matrix ι κ ℝ →ₗ[ℝ] ℝ where
  toFun := countingPairing A
  map_add' B C := by simp [countingPairing, mul_add, Finset.sum_add_distrib]
  map_smul' r B := by
    simp [countingPairing, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

/- Mathematical definition (normal notation): Regard B ↦ ∑_(i,j) Aᵢⱼ · Bᵢⱼ as a continuous linear functional on the finite-dimensional matrix space equipped with its Euclidean operator norm. -/
def countingPairingDual (A : Matrix ι κ ℝ) : Matrix ι κ ℝ →L[ℝ] ℝ :=
  (countingPairingLinear A).toContinuousLinearMap

/-- The dual operator norm under counting pairing. For a square table on uniform shares, the paper uses this norm on the matrix `A / card ι`. -/
/-
Mathematical definition (normal notation): Define the unnormalized nuclear norm by operator-norm duality:

‖A‖_(*,count) := sup_(‖B‖_(op,Euclidean) ≤ 1) |∑_(i,j) Aᵢⱼ · Bᵢⱼ|.

For square d × d tables, the paper's normalized nuclear norm is this quantity divided by d.
-/
def nuclearNorm (A : Matrix ι κ ℝ) : ℝ := ‖countingPairingDual A‖

omit [DecidableEq κ] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B ∈ ℝ^(ι × κ), we have

countingPairingDual(A, B) = countingPairing(A, B).
-/
@[simp] theorem countingPairingDual_apply (A B : Matrix ι κ ℝ) :
    countingPairingDual A B = countingPairing A B :=
  rfl


/- Mathematical statement (normal notation): Every real matrix has nonnegative nuclear norm: 0 ≤ ‖A‖_(*,count). The counting convention is used in this auxiliary matrix lemma. -/
theorem nuclearNorm_nonneg (A : Matrix ι κ ℝ) : 0 ≤ nuclearNorm A :=
  norm_nonneg (countingPairingDual A)

omit [DecidableEq κ] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

countingPairingDual(0) = 0.
-/
@[simp] theorem countingPairingDual_zero : countingPairingDual (0 : Matrix ι κ ℝ) = 0 := by
  ext B
  simp [countingPairing]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

‖ 0‖_(*,count) = 0.
-/
@[simp] theorem nuclearNorm_zero : nuclearNorm (0 : Matrix ι κ ℝ) = 0 := by
  change ‖countingPairingDual (0 : Matrix ι κ ℝ)‖ = 0
  rw [countingPairingDual_zero]
  exact norm_zero (E := Matrix ι κ ℝ →L[ℝ] ℝ)

omit [DecidableEq κ] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B ∈ ℝ^(ι × κ), we have

countingPairingDual((A + B)) = countingPairingDual(A) + countingPairingDual(B) .
-/
theorem countingPairingDual_add (A B : Matrix ι κ ℝ) :
    countingPairingDual (A + B) = countingPairingDual A + countingPairingDual B := by
  ext W
  simp [countingPairing, add_mul, Finset.sum_add_distrib]

omit [DecidableEq κ] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ℝ; A ∈ ℝ^(ι × κ), we have

countingPairingDual((r · A)) = r · countingPairingDual(A).
-/
theorem countingPairingDual_smul (r : ℝ) (A : Matrix ι κ ℝ) :
    countingPairingDual (r • A) = r • countingPairingDual A := by
  ext W
  simp [countingPairing, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]


/-
Mathematical statement (normal notation): For equally sized real matrices, the nuclear norm obeys the triangle inequality:

‖A+B‖_(*,count) ≤ ‖A‖_(*,count)+‖B‖_(*,count).
-/
theorem nuclearNorm_add_le (A B : Matrix ι κ ℝ) :
    nuclearNorm (A + B) ≤ nuclearNorm A + nuclearNorm B := by
  unfold nuclearNorm
  rw [countingPairingDual_add]
  exact norm_add_le (countingPairingDual A) (countingPairingDual B)

set_option maxHeartbeats 800000 in


/-
Mathematical statement (normal notation): For every real scalar c and real matrix A,

‖c · A‖_(*,count) = |c| · ‖A‖_(*,count).
-/
theorem nuclearNorm_smul (r : ℝ) (A : Matrix ι κ ℝ) :
    nuclearNorm (r • A) = |r| * nuclearNorm A := by
  unfold nuclearNorm
  rw [countingPairingDual_smul]
  by_cases hr : 0 ≤ r
  · simpa only [abs_of_nonneg hr] using norm_smul_of_nonneg hr (countingPairingDual A)
  · have hnr : 0 ≤ -r := by linarith
    rw [abs_of_neg (lt_of_not_ge hr)]
    calc
      ‖r • countingPairingDual A‖ = ‖(-r) • countingPairingDual A‖ := by
        have hneg : (-r) • countingPairingDual A = -(r • countingPairingDual A) := by
          ext W
          simp [ContinuousLinearMap.smul_apply, smul_eq_mul]
        rw [hneg]
        exact (norm_neg (r • countingPairingDual A)).symm
      _ = -r * ‖countingPairingDual A‖ := norm_smul_of_nonneg hnr (countingPairingDual A)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B ∈ ℝ^(ι × κ), we have

|countingPairing(A, B)| ≤ ‖ A‖_(*,count) · ‖ B‖.
-/
theorem abs_countingPairing_le (A B : Matrix ι κ ℝ) :
    |countingPairing A B| ≤ nuclearNorm A * ‖B‖ := by
  simpa only [countingPairingDual_apply, Real.norm_eq_abs, nuclearNorm] using
    (countingPairingDual A).le_opNorm B

omit [DecidableEq κ] in
/-- The real Schur multiplier is its own adjoint for counting pairing. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K, A, B ∈ ℝ^(ι × κ), we have

countingPairing((K ⊙ A), B) = countingPairing(A, (K ⊙ B)).
-/
theorem countingPairing_hadamard_swap (K A B : Matrix ι κ ℝ) :
    countingPairing (K ⊙ A) B = countingPairing A (K ⊙ B) := by
  unfold countingPairing
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.hadamard_apply]
  ring

/-- The Schur multiplier estimate also holds for the dual nuclear norm. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ ι → EuclideanSpace(ℝ, η); b ∈ κ → EuclideanSpace(ℝ, η); B ∈ ℝ^(ι × κ), we have

‖ (innerProductTable(a, b) ⊙ B)‖_(*,count) ≤ ‖ a‖ · ‖ b‖ · ‖ B‖_(*,count).
-/
theorem schur_multiplier_nuclearNorm_le (a : ι → EuclideanSpace ℝ η)
    (b : κ → EuclideanSpace ℝ η) (B : Matrix ι κ ℝ) :
    nuclearNorm (innerProductTable a b ⊙ B) ≤ ‖a‖ * ‖b‖ * nuclearNorm B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (nuclearNorm_nonneg _))
  intro W
  calc
    ‖countingPairingDual (innerProductTable a b ⊙ B) W‖ =
        |countingPairing B (innerProductTable a b ⊙ W)| := by
      rw [countingPairingDual_apply, Real.norm_eq_abs, countingPairing_hadamard_swap]
    _ ≤ nuclearNorm B * ‖innerProductTable a b ⊙ W‖ := abs_countingPairing_le _ _
    _ ≤ nuclearNorm B * (‖a‖ * ‖b‖ * ‖W‖) :=
      mul_le_mul_of_nonneg_left (schur_multiplier_norm_le a b W) (nuclearNorm_nonneg _)
    _ = (‖a‖ * ‖b‖ * nuclearNorm B) * ‖W‖ := by ring

end

end TableAnalysis
