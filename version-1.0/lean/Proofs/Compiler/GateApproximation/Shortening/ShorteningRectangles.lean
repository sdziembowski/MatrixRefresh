import Proofs.Compiler.GateApproximation.Shortening.ShorteningTransport
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Discrepancy



/-!
# The rectangle energy calculation in nuclear transport

Fixing the communicated tail and pivot leaves a genuine rectangle partition. This file proves the manuscript's critical sum-of-products energy estimate and the resulting square-root dependence on the number of shortening answers.
-/

set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace CircuitCompiler.Shortening

open Refresh MatrixRefresh

variable {X Y D B : Type*} [Fintype X] [Fintype Y] [Fintype D] [Fintype B]

/-- A deterministic rectangle partition, after the private message is fixed. -/
/- Mathematical definition (normal notation): A rectangle partition assigns a left subset A_z ⊆ X and right subset B_z ⊆ Y to every answer z, such that every pair (x,y) belongs to exactly one rectangle A_z × B_z. -/
structure RectanglePartition (B X Y : Type*) [Fintype B] where
  left : B → X → Bool
  right : B → Y → Bool
  partition : ∀ x y, (∑ b, if left b x && right b y then (1 : ℝ) else 0) = 1

/-- Masked squared products recover the unmasked squared product when summed across the disjoint exhaustive answer rectangles. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ RectanglePartition(B, X, Y); a ∈ X → ℝ; b ∈ Y → ℝ; x ∈ X; y ∈ Y, we have

(∑ᵦ (({ (a(x))² if r.left(β, x),; 0 otherwise }) · ({ (b(y))² if r.right(β, y),; 0 otherwise }))) = (a(x))² · (b(y))².
-/
theorem rectangle_energy_pointwise (r : RectanglePartition B X Y)
    (a : X → ℝ) (b : Y → ℝ) (x : X) (y : Y) :
    (∑ β, (if r.left β x then a x ^ 2 else 0) *
      (if r.right β y then b y ^ 2 else 0)) = a x ^ 2 * b y ^ 2 := by
  calc
    _ = ∑ β, (a x ^ 2 * b y ^ 2) *
        (if r.left β x && r.right β y then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro β _
      cases hL : r.left β x <;> cases hR : r.right β y <;> simp
    _ = _ := by rw [← Finset.mul_sum, r.partition, mul_one]

/-- Independent left/right averaging turns the pointwise partition identity into the exact product of the two unrestricted squared `L₂` norms. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ RectanglePartition(B, X, Y); P ∈ 𝒟(X); Q ∈ 𝒟(Y); a ∈ X → ℝ; b ∈ Y → ℝ, we have

(∑ᵦ (𝔼_(x ← P) [{ (a(x))² if r.left(β, x),; 0 otherwise }] · 𝔼_(y ← Q) [{ (b(y))² if r.right(β, y),; 0 otherwise }])) = 𝔼_(x ← P) [(a(x))²] · 𝔼_(y ← Q) [(b(y))²].
-/
theorem rectangle_energy (r : RectanglePartition B X Y)
    (P : FiniteDistribution X) (Q : FiniteDistribution Y) (a : X → ℝ) (b : Y → ℝ) :
    (∑ β, (P.expect (fun x => if r.left β x then a x ^ 2 else 0)) *
      (Q.expect (fun y => if r.right β y then b y ^ 2 else 0))) =
      P.expect (fun x => a x ^ 2) * Q.expect (fun y => b y ^ 2) := by
  simp_rw [← expect_prod_mul]
  rw [← expect_sum]
  apply congrArg (P.prod Q).expect
  funext xy
  exact rectangle_energy_pointwise r a b xy.1 xy.2

/-- Averaging a right factor over its unrevealed tail contracts its squared norm, even after selecting one shortening rectangle. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ RectanglePartition(B, X, (Y × D)); Q ∈ 𝒟(Y); R ∈ 𝒟(D); b ∈ Y × D → ℝ; β ∈ B, we have

(‖ ((y ↦ 𝔼_(d ← R) [{ b((y, d)) if r.right(β, (y, d)),; 0 otherwise }]))‖_(2,Q))² ≤ 𝔼_(yd ← (Q ⊗ R)) [{ (b(yd))² if r.right(β, yd),; 0 otherwise }].
-/
theorem averaged_right_energy (r : RectanglePartition B X (Y × D))
    (Q : FiniteDistribution Y) (R : FiniteDistribution D) (b : Y × D → ℝ) (β : B) :
    rms Q (fun y => R.expect (fun d => if r.right β (y, d) then b (y, d) else 0)) ^ 2 ≤
      (Q.prod R).expect (fun yd => if r.right β yd then b yd ^ 2 else 0) := by
  rw [rms_sq, expect_prod]
  apply Q.expect_mono
  intro y
  have h := expect_mul_sq_le R
    (fun d => if r.right β (y, d) then b (y, d) else 0) (fun _ => 1)
  simpa only [mul_one, one_pow, FiniteDistribution.expect_const, ite_pow,
    zero_pow (by omega : 2 ≠ 0)] using h

/-- The exact energy estimate `Σ u_β² v_β² ≤ ||a||₂² ||b||₂²` for a rank-one long table, with arbitrary probability measures. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ RectanglePartition(B, X, (Y × D)); P ∈ 𝒟(X); Q ∈ 𝒟(Y); R ∈ 𝒟(D); a ∈ X → ℝ; b ∈ Y × D → ℝ, we have

(∑ᵦ ((‖ ((x ↦ { a(x) if r.left(β, x),; 0 otherwise }))‖_(2,P))² · (‖ ((y ↦ 𝔼_(d ← R) [{ b((y, d)) if r.right(β, (y, d)),; 0 otherwise }]))‖_(2,Q))²)) ≤ (‖ a‖_(2,P))² · (‖ b‖_(2,(Q ⊗ R)))².
-/
theorem rectangle_factor_energy (r : RectanglePartition B X (Y × D))
    (P : FiniteDistribution X) (Q : FiniteDistribution Y) (R : FiniteDistribution D)
    (a : X → ℝ) (b : Y × D → ℝ) :
    (∑ β, rms P (fun x => if r.left β x then a x else 0) ^ 2 *
      rms Q (fun y => R.expect (fun d => if r.right β (y, d) then b (y, d) else 0)) ^ 2) ≤
      rms P a ^ 2 * rms (Q.prod R) b ^ 2 := by
  calc
    _ ≤ ∑ β, rms P (fun x => if r.left β x then a x else 0) ^ 2 *
        (Q.prod R).expect (fun yd => if r.right β yd then b yd ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro β _
      exact mul_le_mul_of_nonneg_left (averaged_right_energy r Q R b β) (sq_nonneg _)
    _ = _ := by
      simp only [rms_sq, ite_pow, zero_pow (by omega : 2 ≠ 0)]
      exact rectangle_energy r P (Q.prod R) a b

/-- Summing factorization costs across leaves loses only the square root of the leaf count. This is the rectangle step in the nuclear transport proof. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): Let (A_z × B_z)_(z ∈ Z) partition X × (Y × D), and let P,Q,R be distributions on the three spaces. Restrict a(x) to A_z, and average the restriction of b(y,d) to B_z over d ∼ R. The sum over z of the products of these two L₂ norms is at most √(|Z|) ‖a‖_(2,P) ‖b‖_(2,Q ⊗ R). -/
theorem rectangle_factor_budget (r : RectanglePartition B X (Y × D))
    (P : FiniteDistribution X) (Q : FiniteDistribution Y) (R : FiniteDistribution D)
    (a : X → ℝ) (b : Y × D → ℝ) :
    (∑ β, rms P (fun x => if r.left β x then a x else 0) *
      rms Q (fun y => R.expect (fun d => if r.right β (y, d) then b (y, d) else 0))) ≤
      Real.sqrt (Fintype.card B) * rms P a * rms (Q.prod R) b := by
  let u := fun β => rms P (fun x => if r.left β x then a x else 0)
  let v := fun β => rms Q
    (fun y => R.expect (fun d => if r.right β (y, d) then b (y, d) else 0))
  have hu (β) : 0 ≤ u β := rms_nonneg _ _
  have hv (β) : 0 ≤ v β := rms_nonneg _ _
  have hs : 0 ≤ ∑ β, u β * v β := Finset.sum_nonneg (fun β _ => mul_nonneg (hu β) (hv β))
  have hcs := abs_sum_mul_le (fun β => u β * v β) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, abs_of_nonneg hs, mul_pow] at hcs
  have he := rectangle_factor_energy r P Q R a b
  change (∑ β, u β * v β) ≤ _
  calc
    _ ≤ Real.sqrt (∑ β, u β ^ 2 * v β ^ 2) * Real.sqrt (Fintype.card B) := hcs
    _ ≤ Real.sqrt (rms P a ^ 2 * rms (Q.prod R) b ^ 2) * Real.sqrt (Fintype.card B) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt he) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (rms_nonneg _ _), abs_of_nonneg (rms_nonneg _ _)]
      ring

end CircuitCompiler.Shortening
