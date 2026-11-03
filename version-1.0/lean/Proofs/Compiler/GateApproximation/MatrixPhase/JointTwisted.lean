import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic
import Proofs.Compiler.GateApproximation.MatrixPhase.JointComplexSVD



/-!
# Finite simultaneous singular-term extraction

This file applies actual complex SVDs to phase-twisted matrices. Extraction lowers squared `L₂` energy, so a finite sequence reaches the operator-norm threshold for every twist. The retained terms are explicit singular products; no approximation theorem is assumed.
-/

set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler

noncomputable section

variable {I C : Type*} [Fintype I] [DecidableEq I]

/-- Squared `L₂` energy of a complex matrix under counting measure. -/
/-
Mathematical definition (normal notation): For A ∈ ℂ^(I × I), define

complexMatrixL2Sq(A) := ∑ⱼ (∑ᵢ ((‖ A(i, j)‖)²)).
-/
def complexMatrixL2Sq (A : Matrix I I ℂ) : ℝ := ∑ j, ∑ i, ‖A i j‖ ^ 2

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I), we have

0 ≤ complexMatrixL2Sq(A).
-/
lemma complexMatrixL2Sq_nonneg (A : Matrix I I ℂ) : 0 ≤ complexMatrixL2Sq A :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- An actual complex SVD of a matrix on any finite coordinate type. -/
/- Mathematical definition (normal notation): Choose a singular-value decomposition of the complex matrix acting on its finite Euclidean coordinate space, with as many singular directions as coordinates. The established SVD existence theorem supplies this choice. -/
def complexMatrixSVD (A : Matrix I I ℂ) :
    ComplexSVD A.toEuclideanLin (Fintype.card I) :=
  Classical.choice (exists_complexSVD A.toEuclideanLin (by simp))

/-- One rank-one matrix with complex singular directions. -/
/-
Mathematical definition (normal notation): For r ∈ ℝ; u, v ∈ EuclideanSpace(ℂ, I), define

singularProduct(r, u, v) := (i, j ↦ r · u(i) · star(v(j))).
-/
def singularProduct (r : ℝ) (u v : EuclideanSpace ℂ I) : Matrix I I ℂ :=
  fun i j => (r : ℂ) * u i * star (v j)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ℝ; u, v, x ∈ EuclideanSpace(ℂ, I), we have

toEuclideanLin(singularProduct(r, u, v))(x) = (r · inner(ℂ, v, x)) · u.
-/
lemma singularProduct_apply (r : ℝ) (u v x : EuclideanSpace ℂ I) :
    (singularProduct r u v).toEuclideanLin x =
      ((r : ℂ) * inner ℂ v x) • u := by
  ext i
  simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    PiLp.toLp_apply, singularProduct, PiLp.inner_apply, RCLike.inner_apply,
    Finset.mul_sum, Finset.sum_mul, PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [starRingEnd_apply]
  ring

/-- The matrix produced by subtracting one actual singular term. -/
/-
Mathematical definition (normal notation): For A ∈ ℂ^(I × I); k ∈ {0,…,|I|-1}, define

singularResidual(A, k) := A - singularProduct(σ(complexMatrixSVD(A))(k), left(complexMatrixSVD(A))(k), right(complexMatrixSVD(A))(k)) .
-/
def singularResidual (A : Matrix I I ℂ) (k : Fin (Fintype.card I)) : Matrix I I ℂ :=
  A - singularProduct ((complexMatrixSVD A).sigma k)
    ((complexMatrixSVD A).left k) ((complexMatrixSVD A).right k)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); k ∈ {0,…,|I|-1}; x ∈ EuclideanSpace(ℂ, I), we have

toEuclideanLin(singularResidual(A, k))(x) = residual(complexMatrixSVD(A))(k, x).
-/
lemma singularResidual_apply (A : Matrix I I ℂ) (k : Fin (Fintype.card I))
    (x : EuclideanSpace ℂ I) :
    (singularResidual A k).toEuclideanLin x = (complexMatrixSVD A).residual k x := by
  rw [singularResidual, map_sub]
  change A.toEuclideanLin x - (singularProduct _ _ _).toEuclideanLin x = _
  rw [singularProduct_apply]
  simp only [ComplexSVD.residual, OrthonormalBasis.repr_apply_apply]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I), we have

complexMatrixL2Sq(A) = ∑ⱼ ((‖ A.toEuclideanLin(EuclideanSpace.basisFun(I, ℂ, j))‖)²).
-/
lemma complexMatrixL2Sq_eq_basis (A : Matrix I I ℂ) :
    complexMatrixL2Sq A = ∑ j, ‖A.toEuclideanLin (EuclideanSpace.basisFun I ℂ j)‖ ^ 2 := by
  unfold complexMatrixL2Sq
  apply Finset.sum_congr rfl
  intro j _
  rw [PiLp.norm_sq_eq_of_L2]
  simp [EuclideanSpace.basisFun_apply, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, PiLp.single_apply]

/-- Subtracting an actual singular term lowers total energy by its squared singular value. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); k ∈ {0,…,|I|-1}, we have

complexMatrixL2Sq(singularResidual(A, k)) = complexMatrixL2Sq(A) - (σ(complexMatrixSVD(A))(k))².
-/
theorem singularResidual_energy (A : Matrix I I ℂ) (k : Fin (Fintype.card I)) :
    complexMatrixL2Sq (singularResidual A k) = complexMatrixL2Sq A -
      (complexMatrixSVD A).sigma k ^ 2 := by
  rw [complexMatrixL2Sq_eq_basis, complexMatrixL2Sq_eq_basis]
  simp_rw [singularResidual_apply]
  exact (complexMatrixSVD A).residual_l2_sq (EuclideanSpace.basisFun I ℂ) k

/-- A matrix whose operator norm exceeds the threshold has a singular term above it. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); β ∈ ℝ, assume 0 ≤ β; β < ‖ A‖. Then

∃ k, β < σ(complexMatrixSVD(A))(k).
-/
theorem complexMatrixSVD_large (A : Matrix I I ℂ) (β : ℝ) (hβ : 0 ≤ β)
    (hA : β < ‖A‖) : ∃ k, β < (complexMatrixSVD A).sigma k := by
  apply (complexMatrixSVD A).exists_large_singular β hβ
  simpa only [Matrix.l2_opNorm_def, LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap'] using hA

/-- Phase multiplication preserves the squared matrix `L₂` norm. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For χ, A ∈ ℂ^(I × I), assume ∀ i, j, ‖ χ(i, j)‖ = 1. Then

complexMatrixL2Sq((χ ⊙ A)) = complexMatrixL2Sq(A).
-/
theorem phase_matrix_energy (χ A : Matrix I I ℂ) (hχ : ∀ i j, ‖χ i j‖ = 1) :
    complexMatrixL2Sq (χ ⊙ A) = complexMatrixL2Sq A := by
  simp [complexMatrixL2Sq, Matrix.hadamard_apply, norm_mul, hχ]

/-- Entrywise reciprocal of a unit-modulus phase matrix. -/
/-
Mathematical definition (normal notation): For χ ∈ ℂ^(I × I), define

inversePhase(χ) := (i, j ↦ (χ(i, j))⁻¹).
-/
def inversePhase (χ : Matrix I I ℂ) : Matrix I I ℂ := fun i j => (χ i j)⁻¹

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For χ ∈ ℂ^(I × I), assume ∀ i, j, ‖ χ(i, j)‖ = 1. Then

∀ i, j, ‖ inversePhase(χ, i, j)‖ = 1.
-/
lemma inversePhase_unit (χ : Matrix I I ℂ) (hχ : ∀ i j, ‖χ i j‖ = 1) :
    ∀ i j, ‖inversePhase χ i j‖ = 1 := by
  intro i j
  simp [inversePhase, hχ]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For χ, A ∈ ℂ^(I × I), assume ∀ i, j, ‖ χ(i, j)‖ = 1. Then

inversePhase(χ) ⊙ (χ ⊙ A) = A.
-/
lemma inversePhase_twist (χ A : Matrix I I ℂ) (hχ : ∀ i j, ‖χ i j‖ = 1) :
    inversePhase χ ⊙ (χ ⊙ A) = A := by
  ext i j
  have hz : χ i j ≠ 0 := by intro h; simpa [h] using hχ i j
  simp [inversePhase, Matrix.hadamard_apply, ← mul_assoc, hz]

/-- Untwist after subtracting one singular term from a twisted matrix. -/
/-
Mathematical definition (normal notation): For χ ∈ C → ℂ^(I × I); A ∈ ℂ^(I × I); c ∈ C; k ∈ {0,…,|I|-1}, define

twistedResidual(χ, A, c, k) := inversePhase(χ(c)) ⊙ singularResidual((χ(c) ⊙ A), k).
-/
def twistedResidual (χ : C → Matrix I I ℂ) (A : Matrix I I ℂ)
    (c : C) (k : Fin (Fintype.card I)) : Matrix I I ℂ :=
  inversePhase (χ c) ⊙ singularResidual (χ c ⊙ A) k

/-- One twisted extraction has the exact energy decrease needed for finite termination. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For χ ∈ C → ℂ^(I × I); A ∈ ℂ^(I × I); c ∈ C; k ∈ {0,…,|I|-1}, assume ∀ c, i, j, ‖ χ(c, i, j)‖ = 1. Then

complexMatrixL2Sq(twistedResidual(χ, A, c, k)) = complexMatrixL2Sq(A) - (σ(complexMatrixSVD((χ(c) ⊙ A)))(k))².
-/
theorem twistedResidual_energy (χ : C → Matrix I I ℂ)
    (hχ : ∀ c i j, ‖χ c i j‖ = 1) (A : Matrix I I ℂ)
    (c : C) (k : Fin (Fintype.card I)) :
    complexMatrixL2Sq (twistedResidual χ A c k) = complexMatrixL2Sq A -
      (complexMatrixSVD (χ c ⊙ A)).sigma k ^ 2 := by
  rw [twistedResidual, phase_matrix_energy _ _ (inversePhase_unit _ (hχ c)),
    singularResidual_energy, phase_matrix_energy _ _ (hχ c)]

/-- A retained singular term records its twist and its two unit directions. -/
/- Mathematical definition (normal notation): A twisted singular term records a twist label, a real magnitude, and left and right vectors in the finite complex Euclidean coordinate space. Normalization conditions, when required, are supplied separately. -/
structure TwistedTerm (I C : Type*) [Fintype I] where
  tag : C
  magnitude : ℝ
  left : EuclideanSpace ℂ I
  right : EuclideanSpace ℂ I

/-- A term's contribution in the original (untwisted) matrix coordinates. -/
/-
Mathematical definition (normal notation): For χ ∈ C → ℂ^(I × I); t ∈ TwistedTerm(I, C), define

TwistedTerm.value(χ, t) := inversePhase(χ(t.tag)) ⊙ singularProduct(t.magnitude, t.left, t.right).
-/
def TwistedTerm.value (χ : C → Matrix I I ℂ) (t : TwistedTerm I C) : Matrix I I ℂ :=
  inversePhase (χ t.tag) ⊙ singularProduct t.magnitude t.left t.right

/-- The concrete retained term selected from a twisted matrix's SVD. -/
/-
Mathematical definition (normal notation): For χ ∈ C → ℂ^(I × I); A ∈ ℂ^(I × I); c ∈ C; k ∈ {0,…,|I|-1}, define

extractedTerm(χ, A, c, k) := (c, σ(complexMatrixSVD((χ(c) ⊙ A)))(k), left(complexMatrixSVD((χ(c) ⊙ A)))(k), right(complexMatrixSVD((χ(c) ⊙ A)))(k)).
-/
def extractedTerm (χ : C → Matrix I I ℂ) (A : Matrix I I ℂ)
    (c : C) (k : Fin (Fintype.card I)) : TwistedTerm I C :=
  ⟨c, (complexMatrixSVD (χ c ⊙ A)).sigma k,
    (complexMatrixSVD (χ c ⊙ A)).left k, (complexMatrixSVD (χ c ⊙ A)).right k⟩

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For χ ∈ C → ℂ^(I × I); A ∈ ℂ^(I × I); c ∈ C; k ∈ {0,…,|I|-1}, assume ∀ c, i, j, ‖ χ(c, i, j)‖ = 1. Then

A = value(extractedTerm(χ, A, c, k))(χ) + twistedResidual(χ, A, c, k).
-/
lemma twistedResidual_decomposition (χ : C → Matrix I I ℂ)
    (hχ : ∀ c i j, ‖χ c i j‖ = 1) (A : Matrix I I ℂ)
    (c : C) (k : Fin (Fintype.card I)) :
    A = (extractedTerm χ A c k).value χ + twistedResidual χ A c k := by
  rw [TwistedTerm.value, twistedResidual, singularResidual]
  change A = inversePhase (χ c) ⊙ singularProduct _ _ _ +
    inversePhase (χ c) ⊙ (χ c ⊙ A - singularProduct _ _ _)
  have hcancel := inversePhase_twist (χ c) A (hχ c)
  ext i j
  have hc := congrArg (fun B : Matrix I I ℂ => B i j) hcancel
  simp only [Matrix.hadamard_apply] at hc
  simp only [extractedTerm, Matrix.add_apply, Matrix.sub_apply, Matrix.hadamard_apply]
  linear_combination hc.symm

/-- Counting-measure squared energy in one column. -/
/-
Mathematical definition (normal notation): For A ∈ ℂ^(I × I); j ∈ I, define

complexColumnL2Sq(A, j) := ∑ᵢ ((‖ A(i, j)‖)²).
-/
def complexColumnL2Sq (A : Matrix I I ℂ) (j : I) : ℝ := ∑ i, ‖A i j‖ ^ 2

/-- Counting-measure squared energy in one row. -/
/-
Mathematical definition (normal notation): For A ∈ ℂ^(I × I); i ∈ I, define

complexRowL2Sq(A, i) := ∑ⱼ ((‖ A(i, j)‖)²).
-/
def complexRowL2Sq (A : Matrix I I ℂ) (i : I) : ℝ := ∑ j, ‖A i j‖ ^ 2

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); j ∈ I, we have

complexColumnL2Sq(A, j) = (‖ A.toEuclideanLin(EuclideanSpace.basisFun(I, ℂ, j))‖)².
-/
lemma complexColumnL2Sq_eq_basis (A : Matrix I I ℂ) (j : I) :
    complexColumnL2Sq A j = ‖A.toEuclideanLin (EuclideanSpace.basisFun I ℂ j)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [complexColumnL2Sq, EuclideanSpace.basisFun_apply, Matrix.toLpLin_apply]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); i ∈ I, we have

complexRowL2Sq(A, i) = (‖ A.toEuclideanLin.adjoint(EuclideanSpace.basisFun(I, ℂ, i))‖)².
-/
lemma complexRowL2Sq_eq_adjoint_basis (A : Matrix I I ℂ) (i : I) :
    complexRowL2Sq A i = ‖A.toEuclideanLin.adjoint (EuclideanSpace.basisFun I ℂ i)‖ ^ 2 := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    ← complexColumnL2Sq_eq_basis]
  simp [complexColumnL2Sq, complexRowL2Sq, Matrix.conjTranspose_apply]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ℝ; u, v ∈ EuclideanSpace(ℂ, I), we have

singularProduct(r, u, v, ᴴ) = singularProduct(r, v, u).
-/
lemma singularProduct_conjTranspose (r : ℝ) (u v : EuclideanSpace ℂ I) :
    (singularProduct r u v)ᴴ = singularProduct r v u := by
  ext i j
  simp [singularProduct, Matrix.conjTranspose_apply, mul_comm, mul_left_comm, mul_assoc]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); k ∈ {0,…,|I|-1}; x ∈ EuclideanSpace(ℂ, I), we have

toEuclideanLin.adjoint(singularResidual(A, k))(x) = adjoint.residual(complexMatrixSVD(A))(k, x).
-/
lemma singularResidual_adjoint_apply (A : Matrix I I ℂ) (k : Fin (Fintype.card I))
    (x : EuclideanSpace ℂ I) :
    (singularResidual A k).toEuclideanLin.adjoint x =
      (complexMatrixSVD A).adjoint.residual k x := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, singularResidual,
    Matrix.conjTranspose_sub, singularProduct_conjTranspose, map_sub]
  change Aᴴ.toEuclideanLin x - (singularProduct _ _ _).toEuclideanLin x = _
  rw [singularProduct_apply, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  simp only [ComplexSVD.residual, ComplexSVD.adjoint, OrthonormalBasis.repr_apply_apply]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); k ∈ {0,…,|I|-1}; j ∈ I, we have

complexColumnL2Sq(singularResidual(A, k), j) = complexColumnL2Sq(A, j) - (σ(complexMatrixSVD(A))(k))² · (‖ right(complexMatrixSVD(A))(k, j)‖)².
-/
lemma singularResidual_column_energy (A : Matrix I I ℂ)
    (k : Fin (Fintype.card I)) (j : I) :
    complexColumnL2Sq (singularResidual A k) j = complexColumnL2Sq A j -
      (complexMatrixSVD A).sigma k ^ 2 * ‖(complexMatrixSVD A).right k j‖ ^ 2 := by
  rw [complexColumnL2Sq_eq_basis, complexColumnL2Sq_eq_basis, singularResidual_apply,
    ComplexSVD.residual_norm_sq]
  simp [OrthonormalBasis.repr_apply_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_right]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); k ∈ {0,…,|I|-1}; i ∈ I, we have

complexRowL2Sq(singularResidual(A, k), i) = complexRowL2Sq(A, i) - (σ(complexMatrixSVD(A))(k))² · (‖ left(complexMatrixSVD(A))(k, i)‖)².
-/
lemma singularResidual_row_energy (A : Matrix I I ℂ)
    (k : Fin (Fintype.card I)) (i : I) :
    complexRowL2Sq (singularResidual A k) i = complexRowL2Sq A i -
      (complexMatrixSVD A).sigma k ^ 2 * ‖(complexMatrixSVD A).left k i‖ ^ 2 := by
  rw [complexRowL2Sq_eq_adjoint_basis, complexRowL2Sq_eq_adjoint_basis,
    singularResidual_adjoint_apply, ComplexSVD.adjoint_residual_norm_sq]
  simp [OrthonormalBasis.repr_apply_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_right]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For χ, A ∈ ℂ^(I × I); j ∈ I, assume ∀ i, j, ‖ χ(i, j)‖ = 1. Then

complexColumnL2Sq((χ ⊙ A), j) = complexColumnL2Sq(A, j).
-/
lemma phase_column_energy (χ A : Matrix I I ℂ) (hχ : ∀ i j, ‖χ i j‖ = 1) (j : I) :
    complexColumnL2Sq (χ ⊙ A) j = complexColumnL2Sq A j := by
  simp [complexColumnL2Sq, Matrix.hadamard_apply, hχ]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For χ, A ∈ ℂ^(I × I); i ∈ I, assume ∀ i, j, ‖ χ(i, j)‖ = 1. Then

complexRowL2Sq((χ ⊙ A), i) = complexRowL2Sq(A, i).
-/
lemma phase_row_energy (χ A : Matrix I I ℂ) (hχ : ∀ i j, ‖χ i j‖ = 1) (i : I) :
    complexRowL2Sq (χ ⊙ A) i = complexRowL2Sq A i := by
  simp [complexRowL2Sq, Matrix.hadamard_apply, hχ]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For χ ∈ C → ℂ^(I × I); A ∈ ℂ^(I × I); c ∈ C; k ∈ {0,…,|I|-1}; j ∈ I, assume ∀ c, i, j, ‖ χ(c, i, j)‖ = 1. Then

complexColumnL2Sq(twistedResidual(χ, A, c, k), j) = complexColumnL2Sq(A, j) - (magnitude(extractedTerm(χ, A, c, k)))² · (‖ right(extractedTerm(χ, A, c, k))(j)‖)².
-/
lemma twistedResidual_column_energy (χ : C → Matrix I I ℂ)
    (hχ : ∀ c i j, ‖χ c i j‖ = 1) (A : Matrix I I ℂ)
    (c : C) (k : Fin (Fintype.card I)) (j : I) :
    complexColumnL2Sq (twistedResidual χ A c k) j = complexColumnL2Sq A j -
      (extractedTerm χ A c k).magnitude ^ 2 * ‖(extractedTerm χ A c k).right j‖ ^ 2 := by
  rw [twistedResidual, phase_column_energy _ _ (inversePhase_unit _ (hχ c)),
    singularResidual_column_energy, phase_column_energy _ _ (hχ c)]
  rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For χ ∈ C → ℂ^(I × I); A ∈ ℂ^(I × I); c ∈ C; k ∈ {0,…,|I|-1}; i ∈ I, assume ∀ c, i, j, ‖ χ(c, i, j)‖ = 1. Then

complexRowL2Sq(twistedResidual(χ, A, c, k), i) = complexRowL2Sq(A, i) - (magnitude(extractedTerm(χ, A, c, k)))² · (‖ left(extractedTerm(χ, A, c, k))(i)‖)².
-/
lemma twistedResidual_row_energy (χ : C → Matrix I I ℂ)
    (hχ : ∀ c i j, ‖χ c i j‖ = 1) (A : Matrix I I ℂ)
    (c : C) (k : Fin (Fintype.card I)) (i : I) :
    complexRowL2Sq (twistedResidual χ A c k) i = complexRowL2Sq A i -
      (extractedTerm χ A c k).magnitude ^ 2 * ‖(extractedTerm χ A c k).left i‖ ^ 2 := by
  rw [twistedResidual, phase_row_energy _ _ (inversePhase_unit _ (hχ c)),
    singularResidual_row_energy, phase_row_energy _ _ (hχ c)]
  rfl

/-- A finite-budget simultaneous extraction theorem. Every retained term is an actual singular product from its extraction stage. The final residual obeys all twist bounds simultaneously, and the energy budget is an exact equality. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For χ ∈ C → ℂ^(I × I); β ∈ ℝ; B ∈ ℕ; A ∈ ℂ^(I × I), assume ∀ c, i, j, ‖ χ(c, i, j)‖ = 1; 0 < β; complexMatrixL2Sq(A) ≤ B · β². Then

∃ terms ∈ TwistedTerm(I, C)*, E ∈ ℂ^(I × I), |terms| ≤ B ∧ (∀ t ∈ terms, β < t.magnitude ∧ ‖ t.left‖ = 1 ∧ ‖ t.right‖ = 1) ∧ A = sum((TwistedTerm.value(χ)_*terms)) + E ∧ (∀ c, ‖ χ(c) ⊙ E‖ ≤ β) ∧ sum((((t ↦ (t.magnitude)²))_*terms)) + complexMatrixL2Sq(E) = complexMatrixL2Sq(A) ∧ (∀ i, sum((((t ↦ (t.magnitude)² · (‖ t.left(i)‖)²))_*terms)) + complexRowL2Sq(E, i) = complexRowL2Sq(A, i)) ∧ (∀ j, sum((((t ↦ (t.magnitude)² · (‖ t.right(j)‖)²))_*terms)) + complexColumnL2Sq(E, j) = complexColumnL2Sq(A, j)).
-/
theorem finite_twisted_extraction (χ : C → Matrix I I ℂ)
    (hχ : ∀ c i j, ‖χ c i j‖ = 1) (β : ℝ) (hβ : 0 < β)
    (B : ℕ) (A : Matrix I I ℂ) (hbound : complexMatrixL2Sq A ≤ (B : ℝ) * β ^ 2) :
    ∃ (terms : List (TwistedTerm I C)) (E : Matrix I I ℂ),
      terms.length ≤ B ∧
      (∀ t ∈ terms, β < t.magnitude ∧ ‖t.left‖ = 1 ∧ ‖t.right‖ = 1) ∧
      A = (terms.map (TwistedTerm.value χ)).sum + E ∧
      (∀ c, ‖χ c ⊙ E‖ ≤ β) ∧
      (terms.map (fun t => t.magnitude ^ 2)).sum + complexMatrixL2Sq E =
        complexMatrixL2Sq A ∧
      (∀ i, (terms.map (fun t => t.magnitude ^ 2 * ‖t.left i‖ ^ 2)).sum +
        complexRowL2Sq E i = complexRowL2Sq A i) ∧
      (∀ j, (terms.map (fun t => t.magnitude ^ 2 * ‖t.right j‖ ^ 2)).sum +
        complexColumnL2Sq E j = complexColumnL2Sq A j) := by
  induction B generalizing A with
  | zero =>
    have hsmall : ∀ c, ‖χ c ⊙ A‖ ≤ β := by
      intro c
      by_contra h
      obtain ⟨k, hk⟩ := complexMatrixSVD_large (χ c ⊙ A) β hβ.le (lt_of_not_ge h)
      have hd := twistedResidual_energy χ hχ A c k
      have hn := complexMatrixL2Sq_nonneg (twistedResidual χ A c k)
      norm_num at hbound
      nlinarith
    exact ⟨[], A, by simp, by simp, by simp, hsmall, by simp, by simp, by simp⟩
  | succ B ih =>
    by_cases hsmall : ∀ c, ‖χ c ⊙ A‖ ≤ β
    · exact ⟨[], A, by simp, by simp, by simp, hsmall, by simp, by simp, by simp⟩
    · push_neg at hsmall
      obtain ⟨c, hc⟩ := hsmall
      obtain ⟨k, hk⟩ := complexMatrixSVD_large (χ c ⊙ A) β hβ.le hc
      let t := extractedTerm χ A c k
      let A' := twistedResidual χ A c k
      have hd : complexMatrixL2Sq A' = complexMatrixL2Sq A - t.magnitude ^ 2 :=
        twistedResidual_energy χ hχ A c k
      have htm : β < t.magnitude := hk
      have hbound' : complexMatrixL2Sq A' ≤ (B : ℝ) * β ^ 2 := by
        rw [Nat.cast_add, Nat.cast_one] at hbound
        nlinarith
      obtain ⟨ts, E, hlen, hterms, hdecomp, hsmallE, henergy, hrows, hcols⟩ := ih A' hbound'
      refine ⟨t :: ts, E, by simpa using Nat.succ_le_succ hlen, ?_, ?_, hsmallE, ?_, ?_, ?_⟩
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact ⟨htm, (complexMatrixSVD (χ c ⊙ A)).left.norm_eq_one k,
            (complexMatrixSVD (χ c ⊙ A)).right.norm_eq_one k⟩
        · exact hterms u hu
      · rw [List.map_cons, List.sum_cons, add_assoc, ← hdecomp]
        exact twistedResidual_decomposition χ hχ A c k
      · simp only [List.map_cons, List.sum_cons]
        linarith
      · intro i
        have hr : complexRowL2Sq A' i = complexRowL2Sq A i -
            t.magnitude ^ 2 * ‖t.left i‖ ^ 2 :=
          twistedResidual_row_energy χ hχ A c k i
        simpa only [List.map_cons, List.sum_cons] using (by linarith [hrows i] :
          t.magnitude ^ 2 * ‖t.left i‖ ^ 2 +
            (ts.map (fun t => t.magnitude ^ 2 * ‖t.left i‖ ^ 2)).sum +
            complexRowL2Sq E i = complexRowL2Sq A i)
      · intro j
        have hc : complexColumnL2Sq A' j = complexColumnL2Sq A j -
            t.magnitude ^ 2 * ‖t.right j‖ ^ 2 :=
          twistedResidual_column_energy χ hχ A c k j
        simpa only [List.map_cons, List.sum_cons] using (by linarith [hcols j] :
          t.magnitude ^ 2 * ‖t.right j‖ ^ 2 +
            (ts.map (fun t => t.magnitude ^ 2 * ‖t.right j‖ ^ 2)).sum +
            complexColumnL2Sq E j = complexColumnL2Sq A j)

/-- Simultaneous twisted extraction terminates for every matrix and every positive threshold. No bound on the number of twists is needed for termination; the norm threshold itself forces each step to spend positive energy. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For χ ∈ C → ℂ^(I × I); β ∈ ℝ; A ∈ ℂ^(I × I), assume ∀ c, i, j, ‖ χ(c, i, j)‖ = 1; 0 < β. Then

∃ terms ∈ TwistedTerm(I, C)*, E ∈ ℂ^(I × I), (∀ t ∈ terms, β < t.magnitude ∧ ‖ t.left‖ = 1 ∧ ‖ t.right‖ = 1) ∧ A = sum((TwistedTerm.value(χ)_*terms)) + E ∧ (∀ c, ‖ χ(c) ⊙ E‖ ≤ β) ∧ sum((((t ↦ (t.magnitude)²))_*terms)) + complexMatrixL2Sq(E) = complexMatrixL2Sq(A) ∧ (∀ i, sum((((t ↦ (t.magnitude)² · (‖ t.left(i)‖)²))_*terms)) + complexRowL2Sq(E, i) = complexRowL2Sq(A, i)) ∧ (∀ j, sum((((t ↦ (t.magnitude)² · (‖ t.right(j)‖)²))_*terms)) + complexColumnL2Sq(E, j) = complexColumnL2Sq(A, j)).
-/
theorem exists_twisted_extraction (χ : C → Matrix I I ℂ)
    (hχ : ∀ c i j, ‖χ c i j‖ = 1) (β : ℝ) (hβ : 0 < β) (A : Matrix I I ℂ) :
    ∃ (terms : List (TwistedTerm I C)) (E : Matrix I I ℂ),
      (∀ t ∈ terms, β < t.magnitude ∧ ‖t.left‖ = 1 ∧ ‖t.right‖ = 1) ∧
      A = (terms.map (TwistedTerm.value χ)).sum + E ∧
      (∀ c, ‖χ c ⊙ E‖ ≤ β) ∧
      (terms.map (fun t => t.magnitude ^ 2)).sum + complexMatrixL2Sq E =
        complexMatrixL2Sq A ∧
      (∀ i, (terms.map (fun t => t.magnitude ^ 2 * ‖t.left i‖ ^ 2)).sum +
        complexRowL2Sq E i = complexRowL2Sq A i) ∧
      (∀ j, (terms.map (fun t => t.magnitude ^ 2 * ‖t.right j‖ ^ 2)).sum +
        complexColumnL2Sq E j = complexColumnL2Sq A j) := by
  obtain ⟨B, hB⟩ := exists_nat_ge (complexMatrixL2Sq A / β ^ 2)
  have hb : complexMatrixL2Sq A ≤ (B : ℝ) * β ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hβ)).1 hB
  obtain ⟨ts, E, _, ht, hd, hs, he, hr, hc⟩ := finite_twisted_extraction χ hχ β hβ B A hb
  exact ⟨ts, E, ht, hd, hs, he, hr, hc⟩

/-- The square-root singular factors retained by the greedy process. -/
/-
Mathematical definition (normal notation): For t ∈ TwistedTerm(I, C); i ∈ I, define

TwistedTerm.leftFeature(t, i) := √(t.magnitude) · t.left(i).
-/
def TwistedTerm.leftFeature (t : TwistedTerm I C) (i : I) : ℂ :=
  (Real.sqrt t.magnitude : ℂ) * t.left i

/-
Mathematical definition (normal notation): For t ∈ TwistedTerm(I, C); j ∈ I, define

TwistedTerm.rightFeature(t, j) := √(t.magnitude) · t.right(j).
-/
def TwistedTerm.rightFeature (t : TwistedTerm I C) (j : I) : ℂ :=
  (Real.sqrt t.magnitude : ℂ) * t.right j

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For t ∈ TwistedTerm(I, C); i ∈ I, assume 0 ≤ t.magnitude. Then

(‖ t.leftFeature(i)‖)² = t.magnitude · (‖ t.left(i)‖)².
-/
lemma TwistedTerm.leftFeature_norm_sq (t : TwistedTerm I C) (ht : 0 ≤ t.magnitude)
    (i : I) : ‖t.leftFeature i‖ ^ 2 = t.magnitude * ‖t.left i‖ ^ 2 := by
  simp [TwistedTerm.leftFeature, norm_mul, mul_pow, Real.sq_sqrt ht]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For t ∈ TwistedTerm(I, C); j ∈ I, assume 0 ≤ t.magnitude. Then

(‖ t.rightFeature(j)‖)² = t.magnitude · (‖ t.right(j)‖)² .
-/
lemma TwistedTerm.rightFeature_norm_sq (t : TwistedTerm I C) (ht : 0 ≤ t.magnitude)
    (j : I) : ‖t.rightFeature j‖ ^ 2 = t.magnitude * ‖t.right j‖ ^ 2 := by
  simp [TwistedTerm.rightFeature, norm_mul, mul_pow, Real.sq_sqrt ht]

/-- Dividing the exact squared-energy budget by the extraction threshold bounds the total nuclear mass, with no orthogonality assumption on retained terms. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ts ∈ TwistedTerm(I, C)*; β, H ∈ ℝ, assume 0 < β; ∀ t ∈ ts, β < t.magnitude; sum((((t ↦ (t.magnitude)²))_*ts)) ≤ H. Then

sum((TwistedTerm.magnitude_*ts)) ≤ H / β.
-/
lemma extracted_magnitude_budget (ts : List (TwistedTerm I C)) (β H : ℝ)
    (hβ : 0 < β) (ht : ∀ t ∈ ts, β < t.magnitude)
    (henergy : (ts.map (fun t => t.magnitude ^ 2)).sum ≤ H) :
    (ts.map TwistedTerm.magnitude).sum ≤ H / β := by
  apply (le_div_iff₀ hβ).2
  have h := List.sum_le_sum (l := ts) (f := fun t => β * t.magnitude)
    (g := fun t => t.magnitude ^ 2) (fun t ht' => by
      have hlarge := ht t ht'
      nlinarith)
  rw [List.sum_map_mul_left] at h
  nlinarith

/-- The same local argument bounds the squared sum of all extracted features at each coordinate. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ts ∈ TwistedTerm(I, C)*; w ∈ TwistedTerm(I, C) → ℝ; β, H ∈ ℝ, assume 0 < β; ∀ t ∈ ts, β < t.magnitude; ∀ t ∈ ts, 0 ≤ w(t); sum((((t ↦ (t.magnitude)² · w(t)))_*ts)) ≤ H. Then

sum((((t ↦ t.magnitude · w(t)))_*ts)) ≤ H / β.
-/
lemma extracted_weighted_budget (ts : List (TwistedTerm I C)) (w : TwistedTerm I C → ℝ)
    (β H : ℝ) (hβ : 0 < β) (ht : ∀ t ∈ ts, β < t.magnitude)
    (hw : ∀ t ∈ ts, 0 ≤ w t)
    (henergy : (ts.map (fun t => t.magnitude ^ 2 * w t)).sum ≤ H) :
    (ts.map (fun t => t.magnitude * w t)).sum ≤ H / β := by
  apply (le_div_iff₀ hβ).2
  have h := List.sum_le_sum (l := ts) (f := fun t => β * (t.magnitude * w t))
    (g := fun t => t.magnitude ^ 2 * w t) (fun t ht' => by
      have hlarge := ht t ht'
      have hm : β * t.magnitude ≤ t.magnitude ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hm (hw t ht')])
  rw [List.sum_map_mul_left] at h
  nlinarith

/-- Simultaneous extraction with all three budgets needed for the paper: total squared energy, total singular mass, and pointwise feature energy. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For χ ∈ C → ℂ^(I × I); β ∈ ℝ; A ∈ ℂ^(I × I), assume ∀ c, i, j, ‖ χ(c, i, j)‖ = 1; 0 < β. Then

∃ terms ∈ TwistedTerm(I, C)*, E ∈ ℂ^(I × I), (∀ t ∈ terms, β < t.magnitude ∧ ‖ t.left‖ = 1 ∧ ‖ t.right‖ = 1) ∧ A = sum((TwistedTerm.value(χ)_*terms)) + E ∧ (∀ c, ‖ χ(c) ⊙ E‖ ≤ β) ∧ sum((((t ↦ (t.magnitude)²))_*terms)) ≤ complexMatrixL2Sq(A) ∧ complexMatrixL2Sq(E) ≤ complexMatrixL2Sq(A) ∧ sum((TwistedTerm.magnitude_*terms)) ≤ complexMatrixL2Sq(A) / β ∧ (∀ i, sum((((t ↦ (‖ t.leftFeature(i)‖)²))_*terms)) ≤ complexRowL2Sq(A, i) / β) ∧ (∀ j, sum((((t ↦ (‖ t.rightFeature(j)‖)²))_*terms)) ≤ complexColumnL2Sq(A, j) / β).
-/
theorem exists_twisted_extraction_features (χ : C → Matrix I I ℂ)
    (hχ : ∀ c i j, ‖χ c i j‖ = 1) (β : ℝ) (hβ : 0 < β) (A : Matrix I I ℂ) :
    ∃ (terms : List (TwistedTerm I C)) (E : Matrix I I ℂ),
      (∀ t ∈ terms, β < t.magnitude ∧ ‖t.left‖ = 1 ∧ ‖t.right‖ = 1) ∧
      A = (terms.map (TwistedTerm.value χ)).sum + E ∧
      (∀ c, ‖χ c ⊙ E‖ ≤ β) ∧
      (terms.map (fun t => t.magnitude ^ 2)).sum ≤ complexMatrixL2Sq A ∧
      complexMatrixL2Sq E ≤ complexMatrixL2Sq A ∧
      (terms.map TwistedTerm.magnitude).sum ≤ complexMatrixL2Sq A / β ∧
      (∀ i, (terms.map (fun t => ‖t.leftFeature i‖ ^ 2)).sum ≤ complexRowL2Sq A i / β) ∧
      (∀ j, (terms.map (fun t => ‖t.rightFeature j‖ ^ 2)).sum ≤ complexColumnL2Sq A j / β) := by
  obtain ⟨ts, E, ht, hd, hs, he, hr, hc⟩ := exists_twisted_extraction χ hχ β hβ A
  have ht' : ∀ t ∈ ts, β < t.magnitude := fun t hm => (ht t hm).1
  have hsquares : 0 ≤ (ts.map (fun t => t.magnitude ^ 2)).sum :=
    List.sum_nonneg (by intro x hx; obtain ⟨t, _, rfl⟩ := List.mem_map.1 hx; positivity)
  have hbudget : (ts.map (fun t => t.magnitude ^ 2)).sum ≤ complexMatrixL2Sq A :=
    by linarith [complexMatrixL2Sq_nonneg E]
  refine ⟨ts, E, ht, hd, hs, hbudget, by linarith,
    extracted_magnitude_budget ts β _ hβ ht' hbudget, ?_, ?_⟩
  · intro i
    have hlocal : (ts.map (fun t => t.magnitude ^ 2 * ‖t.left i‖ ^ 2)).sum ≤
        complexRowL2Sq A i := by
      have hn : 0 ≤ complexRowL2Sq E i := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      linarith [hr i]
    have hrewrite : ts.map (fun t => ‖t.leftFeature i‖ ^ 2) =
        ts.map (fun t => t.magnitude * ‖t.left i‖ ^ 2) := by
      apply List.map_congr_left
      intro t hm
      exact t.leftFeature_norm_sq (hβ.le.trans (ht' t hm).le) i
    rw [hrewrite]
    exact extracted_weighted_budget ts (fun t => ‖t.left i‖ ^ 2) β _ hβ ht'
      (fun _ _ => sq_nonneg _) hlocal
  · intro j
    have hlocal : (ts.map (fun t => t.magnitude ^ 2 * ‖t.right j‖ ^ 2)).sum ≤
        complexColumnL2Sq A j := by
      have hn : 0 ≤ complexColumnL2Sq E j := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      linarith [hc j]
    have hrewrite : ts.map (fun t => ‖t.rightFeature j‖ ^ 2) =
        ts.map (fun t => t.magnitude * ‖t.right j‖ ^ 2) := by
      apply List.map_congr_left
      intro t hm
      exact t.rightFeature_norm_sq (hβ.le.trans (ht' t hm).le) j
    rw [hrewrite]
    exact extracted_weighted_budget ts (fun t => ‖t.right j‖ ^ 2) β _ hβ ht'
      (fun _ _ => sq_nonneg _) hlocal

end

end CircuitCompiler
