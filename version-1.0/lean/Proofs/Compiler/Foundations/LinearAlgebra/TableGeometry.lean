import Mathlib.Analysis.InnerProductSpace.PiL2
import Proofs.Compiler.Foundations.LinearAlgebra.NuclearNorm
import Proofs.Compiler.Foundations.LinearAlgebra.RefreshBounds



/-!
# Tables on the uniform probability space

The operator and nuclear norms are the ordinary matrix norms divided by the number of shares. The normalized L2 norm divides the Euclidean norm of the entries by the same number, matching uniform averaging over table entries.
-/

set_option autoImplicit false

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace TableAnalysis

open MatrixRefresh Refresh

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-
Mathematical definition (normal notation): For A ∈ ℝ^(ι × ι), define

entryVector(A) := WithLp.toLp(2, ((p ↦ A((p)₁, (p)₂)))).
-/
def entryVector (A : Matrix ι ι ℝ) : EuclideanSpace ℝ (ι × ι) :=
  WithLp.toLp 2 (fun p => A p.1 p.2)

/- Mathematical definition (normal notation): For a real d × d table F, the normalized L₂ norm is ‖F‖₂ := √(∑_(i,j) Fᵢⱼ²)/d. It equals the square root of the mean squared entry. The auxiliary empty-index case is assigned the value 0. -/
def tableL2Norm (A : Matrix ι ι ℝ) : ℝ := ‖entryVector A‖ / Fintype.card ι

/- Mathematical definition (normal notation): For a real d × d table F, the normalized operator norm is ‖F‖ₒₚ := ‖F‖_(op,Euclidean)/d, equivalently the operator norm of v ↦ F · v/d. The auxiliary empty-index case is assigned the value 0. -/
def largestSingularCoefficient (A : Matrix ι ι ℝ) : ℝ := ‖A‖ / Fintype.card ι

/- Mathematical definition (normal notation): For a real d × d table F, define the normalized nuclear norm by ‖F‖_* := ‖F‖_(*,count)/d. It equals the sum of the uniformly normalized singular coefficients. The auxiliary empty-index case is assigned the value 0. -/
def tableNuclearNorm (A : Matrix ι ι ℝ) : ℝ := nuclearNorm A / Fintype.card ι

/-
Mathematical definition (normal notation): For A ∈ ℝ^(ι × ι), define

tableL1(A) := signedL1(((p ∈ ι × ι ↦ A((p)₁, (p)₂)))).
-/
def tableL1 (A : Matrix ι ι ℝ) : ℝ := signedL1 (fun p : ι × ι => A p.1 p.2)

/-
Mathematical definition (normal notation): For A ∈ ℝ^(ι × ι); i ∈ ι, define

rowL2(A, i) := √(𝔼ⱼ [(A(i, j))²]) .
-/
def rowL2 (A : Matrix ι ι ℝ) (i : ι) : ℝ :=
  Real.sqrt (uavg (fun j => A i j ^ 2))

/-
Mathematical definition (normal notation): For A ∈ ℝ^(ι × ι); j ∈ ι, define

columnL2(A, j) := √(𝔼ᵢ [(A(i, j))²]).
-/
def columnL2 (A : Matrix ι ι ℝ) (j : ι) : ℝ :=
  Real.sqrt (uavg (fun i => A i j ^ 2))

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι), we have

0 ≤ ‖ A‖₂.
-/
theorem tableL2Norm_nonneg (A : Matrix ι ι ℝ) : 0 ≤ tableL2Norm A := by
  unfold tableL2Norm
  positivity

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι), we have

0 ≤ ‖ A‖ₒₚ.
-/
theorem largestSingularCoefficient_nonneg (A : Matrix ι ι ℝ) : 0 ≤ largestSingularCoefficient A := by
  unfold largestSingularCoefficient
  positivity

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι), we have

0 ≤ ‖ A‖_*.
-/
theorem tableNuclearNorm_nonneg (A : Matrix ι ι ℝ) : 0 ≤ tableNuclearNorm A :=
  div_nonneg (nuclearNorm_nonneg A) (Nat.cast_nonneg _)

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι), we have

(‖ entryVector(A)‖)² = ∑ᵢ (∑ⱼ ((A(i, j))²)).
-/
theorem entryVector_norm_sq (A : Matrix ι ι ℝ) :
    ‖entryVector A‖ ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  simp [entryVector, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι), we have

(‖ A‖₂)² = ‖ ((p ∈ ι × ι ↦ A((p)₁, (p)₂)))‖₂².
-/
theorem tableL2Norm_sq (A : Matrix ι ι ℝ) :
    tableL2Norm A ^ 2 = signedL2Sq (fun p : ι × ι => A p.1 p.2) := by
  simp only [tableL2Norm, div_pow, entryVector_norm_sq, signedL2Sq, uavg,
    Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
  ring

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι), we have

‖ A‖₂ = ‖ ((p ∈ ι × ι ↦ A((p)₁, (p)₂)))‖₂.
-/
theorem tableL2Norm_eq_signedL2 (A : Matrix ι ι ℝ) :
    tableL2Norm A = signedL2 (fun p : ι × ι => A p.1 p.2) := by
  have hsq := tableL2Norm_sq A
  rw [← signedL2_sq] at hsq
  nlinarith [tableL2Norm_nonneg A, signedL2_nonneg (fun p : ι × ι => A p.1 p.2)]

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B ∈ ℝ^(ι × ι), we have

entryVector((A + B)) = entryVector(A) + entryVector(B).
-/
theorem entryVector_add (A B : Matrix ι ι ℝ) :
    entryVector (A + B) = entryVector A + entryVector B := by
  ext p
  rfl

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B ∈ ℝ^(ι × ι), we have

entryVector((A - B)) = entryVector(A) - entryVector(B).
-/
theorem entryVector_sub (A B : Matrix ι ι ℝ) :
    entryVector (A - B) = entryVector A - entryVector B := by
  ext p
  rfl

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B ∈ ℝ^(ι × ι), we have

‖ (A + B)‖₂ ≤ ‖ A‖₂ + ‖ B‖₂.
-/
theorem tableL2Norm_add_le (A B : Matrix ι ι ℝ) :
    tableL2Norm (A + B) ≤ tableL2Norm A + tableL2Norm B := by
  unfold tableL2Norm
  rw [entryVector_add, ← add_div]
  exact div_le_div_of_nonneg_right (norm_add_le _ _) (Nat.cast_nonneg _)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι), assume ι ≠ ∅. Then

tableL1(A) ≤ ‖ A‖₂.
-/
theorem tableL1_le_tableL2Norm [Nonempty ι] (A : Matrix ι ι ℝ) :
    tableL1 A ≤ tableL2Norm A := by
  rw [tableL2Norm_eq_signedL2]
  have hcs := expect_mul_sq_le (FiniteDistribution.uniform : FiniteDistribution (ι × ι))
    (fun p => |A p.1 p.2|) (fun _ => 1)
  simp only [mul_one, sq_abs, one_pow, FiniteDistribution.expect_const,
    ← uavg_eq_expect_uniform] at hcs
  have hsq := signedL2_sq (fun p : ι × ι => A p.1 p.2)
  unfold tableL1 signedL1 signedL2Sq at *
  nlinarith [signedL1_nonneg (fun p : ι × ι => A p.1 p.2),
    signedL2_nonneg (fun p : ι × ι => A p.1 p.2)]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B ∈ ℝ^(ι × ι), we have

‖ (A + B)‖_* ≤ ‖ A‖_* + ‖ B‖_*.
-/
theorem tableNuclearNorm_add_le (A B : Matrix ι ι ℝ) :
    tableNuclearNorm (A + B) ≤ tableNuclearNorm A + tableNuclearNorm B := by
  unfold tableNuclearNorm
  rw [← add_div]
  exact div_le_div_of_nonneg_right (nuclearNorm_add_le A B) (Nat.cast_nonneg _)

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume ι ≠ ∅. Then

‖ ((x, x ∈ ι ↦ 1))‖₂ = 1.
-/
@[simp] theorem tableL2Norm_one [Nonempty ι] : tableL2Norm (fun _ _ : ι => (1 : ℝ)) = 1 := by
  convert! (tableL2Norm_eq_signedL2 (Matrix.of fun _ _ : ι => (1 : ℝ))) using 1 <;>
    simp [signedL2, signedL2Sq]

end

end TableAnalysis
