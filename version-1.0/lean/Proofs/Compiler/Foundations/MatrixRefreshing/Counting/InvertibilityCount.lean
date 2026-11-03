import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Proofs.Compiler.Construction.Parameters
import Proofs.Compiler.Foundations.MatrixRefreshing.Analysis.Tables
import Proofs.Compiler.Foundations.MatrixRefreshing.Counting.LinearExtensions



set_option autoImplicit false

/-!
# A uniform finite-field matrix is invertible with probability at least one quarter

The exact general-linear-group cardinality formula is supplied by mathlib. The lower bound follows by comparison with the binary product, using a finite product defect estimate and the binary geometric sum. The generic product lemma was extracted from the old `Refresh/OrbitArithmetic.lean`; this module has no import of the old analytic route.

The analytical interface is `uavg_GL_le_four_mul_uavg_matrices`: a nonnegative statistic on all matrices increases by at most a factor four when restricted to invertible matrices and renormalized. In the application, nonnegativity holds for the complete four-cycle energy, although its individual corner products may be signed. This distinction is why conditioning is postponed until the complete statistic has been assembled.
-/

namespace MatrixRefresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open Refresh

open scoped BigOperators

/-- The number of all matrices is at most four times the number of invertible matrices, equivalently the invertibility probability is at least one quarter. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, we have

|F^({0,…,n−1} × {0,…,n−1})| ≤ 4 · |GLₙ(F)|.
-/
theorem card_all_matrices_le_four_mul_card_GL (n : ℕ) :
    Fintype.card (Matrix (Fin n) (Fin n) F) ≤ 4 * Fintype.card (Refresh.«GL» F n) := by
  have h := invertibility_probability_ge_quarter (F := F) n
  have hpos : (0 : ℝ) < Fintype.card (Matrix (Fin n) (Fin n) F) := by
    exact_mod_cast Fintype.card_pos
  have hmul := (le_div_iff₀ hpos).mp h
  have hc : (Fintype.card (Matrix (Fin n) (Fin n) F) : ℝ) ≤
      4 * Fintype.card (Refresh.«GL» F n) := by linarith
  exact_mod_cast hc

/-- Conditioning a nonnegative complete matrix statistic on invertibility costs at most four. Nonnegativity is needed both to enlarge the sum to all matrices and to compare the inverse cardinality factors. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; f ∈ F^({0,…,n−1} × {0,…,n−1}) → ℝ, assume ∀ A, 0 ≤ f(A). Then

𝔼_(g ∈ GLₙ(F)) [f(g)] ≤ 4 · 𝔼ᵤ [f(u)].
-/
theorem uavg_GL_le_four_mul_uavg_matrices {n : ℕ}
    (f : Matrix (Fin n) (Fin n) F → ℝ) (hf : ∀ A, 0 ≤ f A) :
    uavg (fun g : Refresh.«GL» F n => f g.val) ≤ 4 * uavg f := by
  classical
  -- First enlarge the unnormalized sum. Units have distinct underlying matrices, so this is a subset sum rather than a sum with multiplicities.
  have hsum : (∑ g : Refresh.«GL» F n, f g.val) ≤ ∑ A, f A := by
    calc
      (∑ g : Refresh.«GL» F n, f g.val) =
          ∑ A ∈ Finset.univ.image (fun g : Refresh.«GL» F n => g.val), f A := by
        rw [Finset.sum_image]
        intro a _ b _ hab
        exact Units.ext hab
      _ ≤ ∑ A, f A := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun A _ _ => hf A)
  have hGL : (0 : ℝ) < Fintype.card (Refresh.«GL» F n) := by
    exact_mod_cast Fintype.card_pos
  have hMat : (0 : ℝ) < Fintype.card (Matrix (Fin n) (Fin n) F) := by
    exact_mod_cast Fintype.card_pos
  have hc : (Fintype.card (Matrix (Fin n) (Fin n) F) : ℝ) ≤
      4 * Fintype.card (Refresh.«GL» F n) := by
    exact_mod_cast card_all_matrices_le_four_mul_card_GL (F := F) n
  -- Only this normalization step uses the quarter-probability bound.
  have hscale : (Fintype.card (Refresh.«GL» F n) : ℝ)⁻¹ ≤
      4 * (Fintype.card (Matrix (Fin n) (Fin n) F) : ℝ)⁻¹ := by
    rw [← one_div, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ hGL hMat).mpr
    simpa only [one_mul] using hc
  unfold uavg
  calc
    _ ≤ (Fintype.card (Refresh.«GL» F n) : ℝ)⁻¹ * ∑ A, f A :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (4 * (Fintype.card (Matrix (Fin n) (Fin n) F) : ℝ)⁻¹) * ∑ A, f A :=
      mul_le_mul_of_nonneg_right hscale (Finset.sum_nonneg (fun A _ => hf A))
    _ = _ := by ring

end MatrixRefresh
