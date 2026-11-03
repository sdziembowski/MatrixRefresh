import Proofs.Compiler.GateApproximation.MatrixPhase.Complexification
import Proofs.Compiler.GateApproximation.MatrixPhase.JointTwistBound
import Proofs.Compiler.GateApproximation.MatrixPhase.Gram
import Proofs.Compiler.Foundations.LinearAlgebra.FiniteCarrier
import Proofs.Compiler.Foundations.LinearAlgebra.SpectralTables



/-!
# Non-strict SVD cutoff for the refresh operator estimate

The finite-dimensional spectral theorem is transported to an arbitrary finite table carrier. The operator/separation analysis retains coefficients at least `β`. The direct answer-table construction instead uses the strict cutoff in `Proofs/Compiler/GateApproximation/Interfaces/StrictTruncation.lean`.
-/

set_option autoImplicit false

set_option maxHeartbeats 1500000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

/- Mathematical definition (normal notation): Relabel the row and column carrier of a square table A:I × I → ℝ by {0,…,|I|-1}. This changes only indices and leaves all entries, uniform averages, and normalized norms unchanged. -/
def svdFiniteTable (A : Matrix I I ℝ) :
    Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℝ :=
  reindexTable A (Fintype.equivFin I) (Fintype.equivFin I)

/- Mathematical definition (normal notation): The retained index set consists of singular directions with normalized coefficient σₖ ≥ β. This auxiliary construction includes equality at the threshold; the paper-facing strict-truncation construction instead uses σₖ>β. -/
abbrev RefreshSVDIndex (A : Matrix I I ℝ) (β : ℝ) :=
  TableRetainedDirection (svdFiniteTable A) β

/-
Mathematical definition (normal notation): Define the auxiliary non-strict spectral part

A^(≥ β) := ∑_(k:σₖ ≥ β) σₖ · uₖ · vₖᵀ.

The carrier is reindexed through a finite coordinate set and then restored. Equality at the threshold is retained here.
-/
def refreshSVDPart (A : Matrix I I ℝ) (β : ℝ) : Matrix I I ℝ :=
  reindexTable (tableSpectralTruncate (svdFiniteTable A) β)
    (Fintype.equivFin I).symm (Fintype.equivFin I).symm

/- Mathematical definition (normal notation): The factor vector at i has one coordinate √σₖ · uₖ(i) for each retained direction σₖ ≥ β, using the normalized orthonormal expansion of A. These vectors factor the auxiliary non-strict spectral part. -/
def refreshSVDLeft (A : Matrix I I ℝ) (β : ℝ) (i : I) :
    EuclideanSpace ℝ (RefreshSVDIndex A β) :=
  tableLeftFeature (svdFiniteTable A) β (Fintype.equivFin I i)

/- Mathematical definition (normal notation): The factor vector at i has one coordinate √σₖ · vₖ(i) for each retained direction σₖ ≥ β, using the normalized orthonormal expansion of A. These vectors factor the auxiliary non-strict spectral part. -/
def refreshSVDRight (A : Matrix I I ℝ) (β : ℝ) (i : I) :
    EuclideanSpace ℝ (RefreshSVDIndex A β) :=
  tableRightFeature (svdFiniteTable A) β (Fintype.equivFin I i)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; i, j ∈ I, we have

refreshSVDPart(A, β, i, j) = inner(ℝ, refreshSVDLeft(A, β, i), refreshSVDRight(A, β, j)).
-/
theorem refreshSVDPart_factorization (A : Matrix I I ℝ) (β : ℝ) (i j : I) :
    refreshSVDPart A β i j =
      inner ℝ (refreshSVDLeft A β i) (refreshSVDRight A β j) :=
  tableSpectralTruncate_factorization _ _ _ _

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

‖ refreshSVDPart(A, β)‖ₒₚ ≤ ‖ A‖ₒₚ.
-/
theorem refreshSVDPart_op (A : Matrix I I ℝ) (β : ℝ) :
    largestSingularCoefficient (refreshSVDPart A β) ≤ largestSingularCoefficient A := by
  unfold refreshSVDPart
  rw [reindexTable_largestSingularCoefficient]
  exact (tableSpectralTruncate_largestSingularCoefficient_le _ _).trans_eq (reindexTable_largestSingularCoefficient _ _ _)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

‖ refreshSVDPart(A, β)‖₂ ≤ ‖ A‖₂.
-/
theorem refreshSVDPart_l2 (A : Matrix I I ℝ) (β : ℝ) :
    tableL2Norm (refreshSVDPart A β) ≤ tableL2Norm A := by
  unfold refreshSVDPart
  rw [reindexTable_tableL2Norm]
  exact (tableSpectralTruncate_tableL2Norm_le _ _).trans_eq (reindexTable_tableL2Norm _ _ _)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, assume 0 < β. Then

‖ (A - refreshSVDPart(A, β))‖ₒₚ ≤ β.
-/
theorem refreshSVDPart_tail (A : Matrix I I ℝ) (β : ℝ) (hβ : 0 < β) :
    largestSingularCoefficient (A - refreshSVDPart A β) ≤ β := by
  letI : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  have he : A - refreshSVDPart A β =
      reindexTable (tableSpectralTail (svdFiniteTable A) β)
        (Fintype.equivFin I).symm (Fintype.equivFin I).symm := by
    ext i j
    simp [refreshSVDPart, svdFiniteTable, reindexTable, tableSpectralTail,
      spectralTail, tableSpectralTruncate]
  rw [he, reindexTable_largestSingularCoefficient]
  exact tableSpectralTail_largestSingularCoefficient_le _ _ hβ

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); i ∈ I, assume ∀ i, j, |A(i, j)| ≤ 1. Then

rowL2(A, i) ≤ 1.
-/
theorem rowL2_le_one_of_entry_bound (A : Matrix I I ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) (i : I) : rowL2 A i ≤ 1 := by
  apply (Real.sqrt_le_one).2
  apply le_trans (uavg_mono (fun j => ?_)) (uavg_const 1).le
  simpa only [sq_abs, one_pow] using
    (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 (hA i j)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); j ∈ I, assume ∀ i, j, |A(i, j)| ≤ 1. Then

columnL2(A, j) ≤ 1.
-/
theorem columnL2_le_one_of_entry_bound (A : Matrix I I ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) (j : I) : columnL2 A j ≤ 1 := by
  apply (Real.sqrt_le_one).2
  apply le_trans (uavg_mono (fun i => ?_)) (uavg_const 1).le
  simpa only [sq_abs, one_pow] using
    (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 (hA i j)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I), assume ∀ i, j, |A(i, j)| ≤ 1. Then

‖ A‖₂ ≤ 1.
-/
theorem tableL2Norm_le_one_of_entry_bound (A : Matrix I I ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) : tableL2Norm A ≤ 1 := by
  have hs : tableL2Norm A ^ 2 ≤ 1 := by
    rw [tableL2Norm_sq]
    exact (uavg_mono (fun p : I × I => by
      simpa only [sq_abs, one_pow] using
        (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 (hA p.1 p.2))).trans_eq (uavg_const 1)
  nlinarith [tableL2Norm_nonneg A]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; i ∈ I, assume 0 < β; ∀ i, j, |A(i, j)| ≤ 1. Then

(‖ refreshSVDLeft(A, β, i)‖)² ≤ 1 / β.
-/
theorem refreshSVDLeft_energy (A : Matrix I I ℝ) (β : ℝ) (hβ : 0 < β)
    (hA : ∀ i j, |A i j| ≤ 1) (i : I) : ‖refreshSVDLeft A β i‖ ^ 2 ≤ 1 / β := by
  letI : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  apply (tableLeftFeature_norm_sq_le _ _ hβ _).trans
  apply div_le_div_of_nonneg_right _ hβ.le
  simpa only [one_pow] using (sq_le_sq₀ (rowL2_nonneg (svdFiniteTable A) _) zero_le_one).2
    (rowL2_le_one_of_entry_bound _ (fun x y => hA _ _) _)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; j ∈ I, assume 0 < β; ∀ i, j, |A(i, j)| ≤ 1. Then

(‖ refreshSVDRight(A, β, j)‖)² ≤ 1 / β.
-/
theorem refreshSVDRight_energy (A : Matrix I I ℝ) (β : ℝ) (hβ : 0 < β)
    (hA : ∀ i j, |A i j| ≤ 1) (j : I) : ‖refreshSVDRight A β j‖ ^ 2 ≤ 1 / β := by
  letI : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  apply (tableRightFeature_norm_sq_le _ _ hβ _).trans
  apply div_le_div_of_nonneg_right _ hβ.le
  simpa only [one_pow] using (sq_le_sq₀ (columnL2_nonneg (svdFiniteTable A) _) zero_le_one).2
    (columnL2_le_one_of_entry_bound _ (fun x y => hA _ _) _)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; i, j ∈ I, assume 0 < β; ∀ i, j, |A(i, j)| ≤ 1. Then

|refreshSVDPart(A, β, i, j)| ≤ 1 / β.
-/
theorem refreshSVDPart_entry (A : Matrix I I ℝ) (β : ℝ) (hβ : 0 < β)
    (hA : ∀ i j, |A i j| ≤ 1) (i j : I) : |refreshSVDPart A β i j| ≤ 1 / β := by
  rw [refreshSVDPart_factorization]
  have hl := refreshSVDLeft_energy A β hβ hA i
  have hr := refreshSVDRight_energy A β hβ hA j
  have h := abs_real_inner_le_norm (refreshSVDLeft A β i) (refreshSVDRight A β j)
  have hh : ‖refreshSVDLeft A β i‖ * ‖refreshSVDRight A β j‖ ≤ 1 / β := by
    nlinarith [sq_nonneg (‖refreshSVDLeft A β i‖ - ‖refreshSVDRight A β j‖)]
  exact h.trans hh

end

end CircuitCompiler.RefreshAnalysis
