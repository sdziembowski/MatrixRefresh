import Proofs.Refreshing.LocalSVD
import Mathlib.Tactic

/-!
# Mask coefficients of a nearly orthonormal frame

The finite-dimensional duality estimate used for the nuclear-norm bound. No independence between the left and right refresh frames is required.
-/

noncomputable section
open scoped BigOperators

namespace RefreshingProof.Local

variable {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]

/-- The probability-normalized Gram entry of two real frame functions. -/
def frameGram (u : J → X → ℝ) (j k : J) : ℝ := average (fun x => u j x * u k x)

/-- The L₂ norm, with counting measure on frame indices, of the Gram matrix minus the identity. -/
def frameDeviation (u : J → X → ℝ) : ℝ :=
  Real.sqrt (∑ j, ∑ k, (frameGram u j k - if j = k then 1 else 0) ^ 2)

/-- The uniform correlation of a test function with one frame function. -/
def frameCoefficient (u : J → X → ℝ) (f : X → ℝ) (j : J) : ℝ :=
  average (fun x => f x * u j x)

/-- A frame’s Gram deviation is nonnegative. -/
theorem frameDeviation_nonneg (u : J → X → ℝ) : 0 ≤ frameDeviation u :=
  Real.sqrt_nonneg _

omit [DecidableEq J] in
/-- Expansion of the squared norm of an arbitrary linear combination. -/
theorem frame_quadratic_expansion (u : J → X → ℝ) (a : J → ℝ) :
    average (fun x => (∑ j, a j * u j x) ^ 2) =
      ∑ j, ∑ k, (a j * a k) * frameGram u j k := by
  have hp (x : X) : (∑ j, a j * u j x) ^ 2 =
      ∑ j, ∑ k, (a j * a k) * (u j x * u k x) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hp, average_sum, average_smul]
  rfl

/-- The Frobenius deviation controls every frame quadratic form. -/
theorem frame_quadratic_le (u : J → X → ℝ) (a : J → ℝ) :
    average (fun x => (∑ j, a j * u j x) ^ 2) ≤
      (∑ j, a j ^ 2) * (1 + frameDeviation u) := by
  classical
  let N := ∑ j, a j ^ 2
  let D (j k : J) := frameGram u j k - if j = k then 1 else 0
  let E := ∑ j, ∑ k, (a j * a k) * D j k
  have hN : 0 ≤ N := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hD : (frameDeviation u) ^ 2 = ∑ j, ∑ k, D j k ^ 2 := by
    exact Real.sq_sqrt (Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hprod : (∑ p : J × J, (a p.1 * a p.2) ^ 2) = N ^ 2 := by
    calc
      _ = ∑ j, ∑ k, a j ^ 2 * a k ^ 2 := by simp [Fintype.sum_prod_type, mul_pow]
      _ = (∑ j, a j ^ 2) * ∑ k, a k ^ 2 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
      _ = N ^ 2 := by rw [pow_two]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : J × J => a p.1 * a p.2) (fun p : J × J => D p.1 p.2)
  rw [hprod] at hcs
  simp only [Fintype.sum_prod_type] at hcs
  change E ^ 2 ≤ N ^ 2 * (∑ j, ∑ k, D j k ^ 2) at hcs
  rw [← hD] at hcs
  have hE : E ≤ N * frameDeviation u := by
    have habs : |E| ≤ N * frameDeviation u :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hN (frameDeviation_nonneg u))).mp
        (by simpa only [sq_abs, mul_pow] using hcs)
    exact (le_abs_self _).trans habs
  have hsplit : (∑ j, ∑ k, (a j * a k) * frameGram u j k) = N + E := by
    have hp (j k : J) : (a j * a k) * frameGram u j k =
        (if j = k then a j ^ 2 else 0) + (a j * a k) * D j k := by
      by_cases h : j = k
      · subst k
        simp only [D, eq_self, ite_true]
        ring
      · simp [D, h]
    simp_rw [hp, Finset.sum_add_distrib]
    simp [N, E]
  rw [frame_quadratic_expansion, hsplit]
  nlinarith

/-- Dual frame bound for the coefficient vector of any real test function. -/
theorem frame_coefficient_sq_le (u : J → X → ℝ) (f : X → ℝ) :
    (∑ j, frameCoefficient u f j ^ 2) ≤
      average (fun x => f x ^ 2) * (1 + frameDeviation u) := by
  let a := frameCoefficient u f
  let N := ∑ j, a j ^ 2
  let F := average (fun x => f x ^ 2)
  have hN : 0 ≤ N := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hF : 0 ≤ F := average_nonneg (fun _ => sq_nonneg _)
  have hinner : average (fun x => f x * ∑ j, a j * u j x) = N := by
    have hp (x : X) : f x * ∑ j, a j * u j x =
        ∑ j, a j * (f x * u j x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp_rw [hp, average_sum, average_smul]
    change (∑ j, a j * a j) = ∑ j, a j ^ 2
    simp only [pow_two]
  have hcs := average_cauchy_schwarz f (fun x => ∑ j, a j * u j x)
  rw [hinner] at hcs
  have hquad := frame_quadratic_le u a
  have hmain : N ^ 2 ≤ F * (N * (1 + frameDeviation u)) :=
    hcs.trans (mul_le_mul_of_nonneg_left hquad hF)
  change N ≤ F * (1 + frameDeviation u)
  by_cases hzero : N = 0
  · rw [hzero]
    exact mul_nonneg hF (add_nonneg zero_le_one (frameDeviation_nonneg u))
  · have hpos : 0 < N := lt_of_le_of_ne hN (Ne.symm hzero)
    apply (mul_le_mul_iff_left₀ hpos).mp
    nlinarith [hmain]

/-- Boolean masks, or any test of squared norm at most one, satisfy the coefficient bound used at each fixed refresh matrix. -/
theorem mask_coefficient_sq_le (u : J → X → ℝ) (f : X → ℝ)
    (hf : average (fun x => f x ^ 2) ≤ 1) :
    (∑ j, frameCoefficient u f j ^ 2) ≤ 1 + frameDeviation u := by
  calc
    _ ≤ average (fun x => f x ^ 2) * (1 + frameDeviation u) := frame_coefficient_sq_le u f
    _ ≤ 1 * (1 + frameDeviation u) :=
      mul_le_mul_of_nonneg_right hf (add_nonneg zero_le_one (frameDeviation_nonneg u))
    _ = _ := one_mul _

end RefreshingProof.Local
