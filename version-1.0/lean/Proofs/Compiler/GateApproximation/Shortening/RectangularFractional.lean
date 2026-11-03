import Proofs.Compiler.GateApproximation.MatrixPhase.NuclearTransportLift
import Proofs.Compiler.Construction.Parameters



/-!
# Fractional local leakage masks

A local sampler's private tape need not be determined by the sampled matrix. After averaging that tape conditional on the local sampled values, its answer masks take values in `[0,1]`. These lemmas accept those conditional masks explicitly. They do not identify a concrete sampler's tape distribution.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace CircuitCompiler.Shortening

open Refresh MatrixRefresh TableAnalysis

namespace FractionalRectanglePartition

variable {B X Y D : Type*} [Fintype B]

/-- Boolean rectangles are the special case whose masks are zero or one. -/
/- Mathematical definition (normal notation): Turn a Boolean rectangle partition into a fractional one by replacing each true left/right mask by 1 and each false mask by 0. Their products still sum to one for every input pair. -/
def ofBoolean (r : RectanglePartition B X Y) : FractionalRectanglePartition B X Y where
  left b x := if r.left b x then 1 else 0
  right b y := if r.right b y then 1 else 0
  left_nonneg b x := by split_ifs <;> norm_num
  left_le_one b x := by split_ifs <;> norm_num
  right_nonneg b y := by split_ifs <;> norm_num
  right_le_one b y := by split_ifs <;> norm_num
  partition x y := by
    convert r.partition x y using 1
    apply Finset.sum_congr rfl
    intro b _
    cases r.left b x <;> cases r.right b y <;> norm_num

/-- Squaring probabilities can only reduce their total rectangle weight. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ FractionalRectanglePartition(B, X, Y); x ∈ X; y ∈ Y, we have

(∑_b ((r.left(b, x))² · (r.right(b, y))²)) ≤ 1.
-/
theorem square_partition_le (r : FractionalRectanglePartition B X Y) (x : X) (y : Y) :
    (∑ b, r.left b x ^ 2 * r.right b y ^ 2) ≤ 1 := by
  rw [← r.partition x y]
  apply Finset.sum_le_sum
  intro b _
  have hl : r.left b x ^ 2 ≤ r.left b x := by
    nlinarith [r.left_nonneg b x, r.left_le_one b x]
  have hr : r.right b y ^ 2 ≤ r.right b y := by
    nlinarith [r.right_nonneg b y, r.right_le_one b y]
  exact mul_le_mul hl hr (sq_nonneg _) (r.left_nonneg b x)

variable [Fintype X] [Fintype Y] [Fintype D]

/-- Independent averaging of squared masked factors costs no more than the unrestricted product energy, even for non-Boolean masks. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ FractionalRectanglePartition(B, X, Y); P ∈ 𝒟(X); Q ∈ 𝒟(Y); a ∈ X → ℝ; b ∈ Y → ℝ, we have

(∑_z (𝔼_(x ← P) [(a(x) · r.left(z, x))²] · 𝔼_(y ← Q) [(b(y) · r.right(z, y))²])) ≤ 𝔼_(x ← P) [(a(x))²] · 𝔼_(y ← Q) [(b(y))²].
-/
theorem rectangle_energy_le (r : FractionalRectanglePartition B X Y)
    (P : FiniteDistribution X) (Q : FiniteDistribution Y) (a : X → ℝ) (b : Y → ℝ) :
    (∑ z, P.expect (fun x => (a x * r.left z x)^2) *
      Q.expect (fun y => (b y * r.right z y)^2)) ≤
      P.expect (fun x => a x^2) * Q.expect (fun y => b y^2) := by
  simp_rw [← expect_prod_mul]
  rw [← expect_sum]
  apply (P.prod Q).expect_mono
  intro xy
  calc
    _ = (a xy.1^2 * b xy.2^2) *
        (∑ z, r.left z xy.1^2 * r.right z xy.2^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ (a xy.1^2 * b xy.2^2) * 1 :=
      mul_le_mul_of_nonneg_left (r.square_partition_le _ _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := mul_one _

omit [Fintype X] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ FractionalRectanglePartition(B, X, (Y × D)); Q ∈ 𝒟(Y); R ∈ 𝒟(D); b ∈ Y × D → ℝ; z ∈ B, we have

(‖ ((y ↦ 𝔼_(d ← R) [b((y, d)) · r.right(z, (y, d))]))‖_(2,Q))² ≤ 𝔼_(yd ← (Q ⊗ R)) [(b(yd) · r.right(z, yd))²].
-/
theorem averaged_right_energy (r : FractionalRectanglePartition B X (Y × D))
    (Q : FiniteDistribution Y) (R : FiniteDistribution D) (b : Y × D → ℝ) (z : B) :
    rms Q (fun y => R.expect (fun d => b (y,d) * r.right z (y,d)))^2 ≤
      (Q.prod R).expect (fun yd => (b yd * r.right z yd)^2) := by
  rw [rms_sq, expect_prod]
  apply Q.expect_mono
  intro y
  have h := expect_mul_sq_le R (fun d => b (y,d) * r.right z (y,d)) (fun _ => 1)
  simpa only [mul_one, one_pow, FiniteDistribution.expect_const] using h

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ FractionalRectanglePartition(B, X, (Y × D)); P ∈ 𝒟(X); Q ∈ 𝒟(Y); R ∈ 𝒟(D); a ∈ X → ℝ; b ∈ Y × D → ℝ, we have

(∑_z ((‖ ((x ↦ a(x) · r.left(z, x)))‖_(2,P))² · (‖ ((y ↦ 𝔼_(d ← R) [b((y, d)) · r.right(z, (y, d))]))‖_(2,Q))²)) ≤ (‖ a‖_(2,P))² · (‖ b‖_(2,(Q ⊗ R)))².
-/
theorem rectangle_factor_energy (r : FractionalRectanglePartition B X (Y × D))
    (P : FiniteDistribution X) (Q : FiniteDistribution Y) (R : FiniteDistribution D)
    (a : X → ℝ) (b : Y × D → ℝ) :
    (∑ z, rms P (fun x => a x * r.left z x)^2 *
      rms Q (fun y => R.expect (fun d => b (y,d) * r.right z (y,d)))^2) ≤
      rms P a^2 * rms (Q.prod R) b^2 := by
  calc
    _ ≤ ∑ z, rms P (fun x => a x * r.left z x)^2 *
        (Q.prod R).expect (fun yd => (b yd * r.right z yd)^2) := by
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_left (r.averaged_right_energy Q R b z) (sq_nonneg _)
    _ ≤ _ := by
      simp only [rms_sq]
      exact r.rectangle_energy_le P (Q.prod R) a b

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ FractionalRectanglePartition(B, X, (Y × D)); P ∈ 𝒟(X); Q ∈ 𝒟(Y); R ∈ 𝒟(D); a ∈ X → ℝ; b ∈ Y × D → ℝ, we have

(∑_z (‖ ((x ↦ a(x) · r.left(z, x)))‖_(2,P) · ‖ ((y ↦ 𝔼_(d ← R) [b((y, d)) · r.right(z, (y, d))]))‖_(2,Q))) ≤ √(|B|) · ‖ a‖_(2,P) · ‖ b‖_(2,(Q ⊗ R)).
-/
theorem rectangle_factor_budget (r : FractionalRectanglePartition B X (Y × D))
    (P : FiniteDistribution X) (Q : FiniteDistribution Y) (R : FiniteDistribution D)
    (a : X → ℝ) (b : Y × D → ℝ) :
    (∑ z, rms P (fun x => a x * r.left z x) *
      rms Q (fun y => R.expect (fun d => b (y,d) * r.right z (y,d)))) ≤
      Real.sqrt (Fintype.card B) * rms P a * rms (Q.prod R) b := by
  let u := fun z => rms P (fun x => a x * r.left z x)
  let v := fun z => rms Q (fun y => R.expect (fun d => b (y,d) * r.right z (y,d)))
  have hs : 0 ≤ ∑ z, u z * v z :=
    Finset.sum_nonneg (fun z _ => mul_nonneg (rms_nonneg _ _) (rms_nonneg _ _))
  have hcs := abs_sum_mul_le (fun z => u z * v z) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, abs_of_nonneg hs, mul_pow] at hcs
  have he := r.rectangle_factor_energy P Q R a b
  change (∑ z, u z * v z) ≤ _
  calc
    _ ≤ Real.sqrt (∑ z, u z^2 * v z^2) * Real.sqrt (Fintype.card B) := hcs
    _ ≤ Real.sqrt (rms P a^2 * rms (Q.prod R) b^2) * Real.sqrt (Fintype.card B) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt he) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (rms_nonneg _ _), abs_of_nonneg (rms_nonneg _ _)]
      ring

/-- The same square-root answer-count loss for fractional masks. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ FractionalRectanglePartition(B, X, (X × D)); R ∈ 𝒟(D); a ∈ X → ℝ; b ∈ X × D → ℝ, assume X ≠ ∅. Then

(∑_z (‖ ((x, y ↦ (a(x) · r.left(z, x)) · 𝔼_(d ← R) [b((y, d)) · r.right(z, (y, d))]))‖_*)) ≤ √(|B|) · ‖ a‖_(2,𝒰_X) · ‖ b‖_(2,(𝒰_X ⊗ R)).
-/
theorem rectangle_nuclear_budget [DecidableEq X] [Nonempty X]
    (r : FractionalRectanglePartition B X (X × D)) (R : FiniteDistribution D)
    (a : X → ℝ) (b : X × D → ℝ) :
    (∑ z, tableNuclearNorm (fun x y => (a x * r.left z x) *
      R.expect (fun d => b (y,d) * r.right z (y,d)))) ≤
      Real.sqrt (Fintype.card B) * rms (FiniteDistribution.uniform : FiniteDistribution X) a *
        rms ((FiniteDistribution.uniform : FiniteDistribution X).prod R) b := by
  refine le_trans ?_ (r.rectangle_factor_budget FiniteDistribution.uniform FiniteDistribution.uniform R a b)
  exact Finset.sum_le_sum (fun z _ => rankOne_tableNuclearNorm_le _ _)

end FractionalRectanglePartition

end CircuitCompiler.Shortening
