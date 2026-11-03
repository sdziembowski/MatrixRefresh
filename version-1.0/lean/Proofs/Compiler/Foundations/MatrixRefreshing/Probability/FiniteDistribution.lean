import Proofs.EfficientSimulaiton.PublicModel
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Proofs.Compiler.Foundations.MatrixRefreshing.Probability.FiniteProbability
/-!
# Finite expectations and root mean squares

This is the analytic vocabulary used by the matrix-refresh argument. A `FiniteDistribution` has nonnegative real weights of total mass one, so all expectations below are finite sums. No measure-theoretic integrability or positive-support premise is needed, and the functions being averaged may have either sign.

The file first records how expectation interacts with sampling (`map`, `bind`, and independent `prod`), then proves Cauchy--Schwarz and the triangle inequality for `rms`. Finally, pointwise domination of probability weights transfers an RMS estimate between distributions at the square root of the density cost. Keeping this normalization explicit matters when endpoint estimates enter the hybrid proof.
-/
set_option autoImplicit false
open scoped BigOperators
namespace MatrixRefresh
open Refresh
variable {α β J : Type*} [Fintype α] [Fintype β] [Fintype J]
/-- Expectation of a pointwise sum is the sum of the two finite expectations. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f, g ∈ α → ℝ, we have

𝔼_(a ← P) [f(a) + g(a)] = 𝔼_(v ← P) [f(v)] + 𝔼_(w ← P) [g(w)].
-/
theorem expect_add (P : FiniteDistribution α) (f g : α → ℝ) :
    P.expect (fun a => f a + g a) = P.expect f + P.expect g := by
  simp [FiniteDistribution.expect, mul_add, Finset.sum_add_distrib]
/-- Expectation of a pointwise difference is the difference of the expectations. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f, g ∈ α → ℝ, we have

𝔼_(a ← P) [f(a) - g(a)] = 𝔼_(v ← P) [f(v)] - 𝔼_(w ← P) [g(w)].
-/
theorem expect_sub (P : FiniteDistribution α) (f g : α → ℝ) :
    P.expect (fun a => f a - g a) = P.expect f - P.expect g := by
  simp [FiniteDistribution.expect, mul_sub, Finset.sum_sub_distrib]
/-- A real scalar multiplying every sampled value factors out of expectation. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); c ∈ ℝ; f ∈ α → ℝ, we have

𝔼_(a ← P) [c · f(a)] = c · 𝔼_(v ← P) [f(v)].
-/
theorem expect_smul (P : FiniteDistribution α) (c : ℝ) (f : α → ℝ) :
    P.expect (fun a => c * f a) = c * P.expect f := by
  simp only [FiniteDistribution.expect, Finset.mul_sum, mul_left_comm]
/-- A constant right factor can be moved outside a finite expectation. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f ∈ α → ℝ; c ∈ ℝ, we have

𝔼_(a ← P) [f(a) · c] = 𝔼_(v ← P) [f(v)] · c.
-/
theorem expect_mul_const (P : FiniteDistribution α) (f : α → ℝ) (c : ℝ) :
    P.expect (fun a => f a * c) = P.expect f * c := by
  simp [FiniteDistribution.expect, mul_assoc, Finset.sum_mul]
/-- Expectation commutes with a finite sum of real-valued functions. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f ∈ J → α → ℝ, we have

𝔼_(a ← P) [∑ⱼ (f(j, a))] = ∑ⱼ (𝔼_(v ← P) [f(j, v)]).
-/
theorem expect_sum (P : FiniteDistribution α) (f : J → α → ℝ) :
    P.expect (fun a => ∑ j, f j a) = ∑ j, P.expect (f j) := by
  simp only [FiniteDistribution.expect, Finset.mul_sum]
  exact Finset.sum_comm
/-- A function averaged under a pushed-forward distribution equals its composition with the sampling map averaged under the original distribution. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f ∈ α → β; g ∈ β → ℝ, we have

𝔼_(u ← (f_*P)) [g(u)] = 𝔼_(a ← P) [g(f(a))].
-/
theorem expect_map (P : FiniteDistribution α) (f : α → β) (g : β → ℝ) :
    (P.map f).expect g = P.expect (fun a => g (f a)) := by
  classical
  simp only [FiniteDistribution.expect, FiniteDistribution.map, FiniteDistribution.bind, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [FiniteDistribution.pure]
/-- Sequential sampling averages first under each conditional distribution, then under the distribution of the first sample. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); Q ∈ α → 𝒟(β); f ∈ β → ℝ, we have

𝔼_(u ← bind(P, Q)) [f(u)] = 𝔼_(a ← P) [𝔼_(y ← Q(a)) [f(y)]].
-/
theorem expect_bind (P : FiniteDistribution α) (Q : α → FiniteDistribution β) (f : β → ℝ) :
    (P.bind Q).expect f = P.expect (fun a => (Q a).expect f) := by
  simp only [FiniteDistribution.expect, FiniteDistribution.bind, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm
/-- Average an independent pair by averaging its two coordinates successively. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); Q ∈ 𝒟(β); f ∈ α × β → ℝ, we have

𝔼_(u ← (P ⊗ Q)) [f(u)] = 𝔼_(a ← P) [𝔼_(b ← Q) [f((a, b))]].
-/
theorem expect_prod (P : FiniteDistribution α) (Q : FiniteDistribution β) (f : α × β → ℝ) :
    (P.prod Q).expect f = P.expect (fun a => Q.expect (fun b => f (a, b))) := by
  simp [FiniteDistribution.expect, FiniteDistribution.prod, FiniteDistribution.joint, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
/-- The two successive expectations can be exchanged when their sampling distributions are independent and the sums are finite. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); Q ∈ 𝒟(β); f ∈ α → β → ℝ, we have

𝔼_(a ← P) [𝔼_(x ← Q) [f(a, x)]] = 𝔼_(b ← Q) [𝔼_(a ← P) [f(a, b)]].
-/
theorem expect_comm (P : FiniteDistribution α) (Q : FiniteDistribution β) (f : α → β → ℝ) :
    P.expect (fun a => Q.expect (f a)) = Q.expect (fun b => P.expect (fun a => f a b)) := by
  simp only [FiniteDistribution.expect, Finset.mul_sum, mul_left_comm]
  exact Finset.sum_comm
/-- The expectation of separate factors on independent coordinates is the product of their expectations. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); Q ∈ 𝒟(β); f ∈ α → ℝ; g ∈ β → ℝ, we have

𝔼_(ab ← (P ⊗ Q)) [f((ab)₁) · g((ab)₂)] = 𝔼_(v ← P) [f(v)] · 𝔼_(w ← Q) [g(w)].
-/
theorem expect_prod_mul (P : FiniteDistribution α) (Q : FiniteDistribution β) (f : α → ℝ) (g : β → ℝ) :
    (P.prod Q).expect (fun ab => f ab.1 * g ab.2) = P.expect f * Q.expect g := by
  simp only [expect_prod, expect_smul, expect_mul_const]
/-- The absolute value of a finite expectation is at most the expectation of the pointwise absolute value. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f ∈ α → ℝ, we have

|𝔼_(u ← P) [f(u)]| ≤ 𝔼_(a ← P) [|f(a)|].
-/
theorem abs_expect_le_expect_abs (P : FiniteDistribution α) (f : α → ℝ) :
    |P.expect f| ≤ P.expect (fun a => |f a|) := by
  simpa only [FiniteDistribution.expect, abs_mul, abs_of_nonneg (P.nonneg _)] using
    (Finset.abs_sum_le_sum_abs (fun a => P.weight a * f a) Finset.univ)
/-- The root mean square is nonnegative for every real-valued function. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f ∈ α → ℝ, we have

0 ≤ ‖ f‖_(2,P).
-/
theorem rms_nonneg (P : FiniteDistribution α) (f : α → ℝ) : 0 ≤ rms P f :=
  Real.sqrt_nonneg _
/-- Squaring the RMS recovers the expectation of the squared function. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f ∈ α → ℝ, we have

(‖ f‖_(2,P))² = 𝔼_(a ← P) [(f(a))²].
-/
@[simp] theorem rms_sq (P : FiniteDistribution α) (f : α → ℝ) :
    rms P f ^ 2 = P.expect (fun a => f a ^ 2) :=
  Real.sq_sqrt (P.expect_nonneg _ (fun _ => sq_nonneg _))
/-- Under a probability distribution, the RMS of a constant is its absolute value. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); c ∈ ℝ, we have

‖ ((x₁ ↦ c))‖_(2,P) = |c|.
-/
@[simp] theorem rms_const (P : FiniteDistribution α) (c : ℝ) : rms P (fun _ => c) = |c| := by
  simp [rms, Real.sqrt_sq_eq_abs]
/-- Replacing each value by its absolute value leaves the RMS unchanged. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f ∈ α → ℝ, we have

‖ ((a ↦ |f(a)|))‖_(2,P) = ‖ f‖_(2,P).
-/
@[simp] theorem rms_abs (P : FiniteDistribution α) (f : α → ℝ) :
    rms P (fun a => |f a|) = rms P f := by
  simp [rms]
/-- Weighted Cauchy--Schwarz in a form avoiding any nonzero-weight assumptions. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f, g ∈ α → ℝ, we have

(𝔼_(a ← P) [f(a) · g(a)])² ≤ 𝔼_(a ← P) [(f(a))²] · 𝔼_(a ← P) [(g(a))²].
-/
theorem expect_mul_sq_le (P : FiniteDistribution α) (f g : α → ℝ) :
    P.expect (fun a => f a * g a) ^ 2 ≤
      P.expect (fun a => f a ^ 2) * P.expect (fun a => g a ^ 2) := by
  -- Put the same probability weight in all three sums. The pointwise identity is polynomial, so zero weights cause no division or square-root side goals.
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (r := fun a => P.weight a * (f a * g a))
    (f := fun a => P.weight a * f a ^ 2)
    (g := fun a => P.weight a * g a ^ 2)
  · intro a _
    exact mul_nonneg (P.nonneg a) (sq_nonneg _)
  · intro a _
    exact mul_nonneg (P.nonneg a) (sq_nonneg _)
  · intro a _
    ring
/-- Cauchy--Schwarz for a signed product; both RMS factors are nonnegative. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f, g ∈ α → ℝ, we have

|𝔼_(a ← P) [f(a) · g(a)]| ≤ ‖ f‖_(2,P) · ‖ g‖_(2,P).
-/
theorem abs_expect_mul_le_rms_mul_rms (P : FiniteDistribution α) (f g : α → ℝ) :
    |P.expect (fun a => f a * g a)| ≤ rms P f * rms P g := by
  simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_mul (P.expect_nonneg _ (fun _ => sq_nonneg _)),
    rms] using Real.sqrt_le_sqrt (expect_mul_sq_le P f g)
/-- The expected absolute product of two functions is bounded by the product of their RMS values under the same probability distribution. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f, g ∈ α → ℝ, we have

𝔼_(a ← P) [|f(a) · g(a)|] ≤ ‖ f‖_(2,P) · ‖ g‖_(2,P).
-/
theorem expect_abs_mul_le_rms_mul_rms (P : FiniteDistribution α) (f g : α → ℝ) :
    P.expect (fun a => |f a * g a|) ≤ rms P f * rms P g := by
  have h := abs_expect_mul_le_rms_mul_rms P (fun a => |f a|) (fun a => |g a|)
  have hn := P.expect_nonneg (fun a => |f a| * |g a|)
    (fun a => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  simpa only [abs_of_nonneg hn, rms_abs, abs_mul] using h
/-- Normalization makes the RMS of the constant function one equal to one, so Cauchy--Schwarz bounds the average absolute value without an extra factor. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f ∈ α → ℝ, we have

𝔼_(a ← P) [|f(a)|] ≤ ‖ f‖_(2,P).
-/
theorem expect_abs_le_rms (P : FiniteDistribution α) (f : α → ℝ) :
    P.expect (fun a => |f a|) ≤ rms P f := by
  simpa using expect_abs_mul_le_rms_mul_rms P f (fun _ => 1)
/-- The absolute expectation of a function is bounded by its root mean square. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f ∈ α → ℝ, we have

|𝔼_(u ← P) [f(u)]| ≤ ‖ f‖_(2,P).
-/
theorem abs_expect_le_rms (P : FiniteDistribution α) (f : α → ℝ) :
    |P.expect f| ≤ rms P f :=
  (abs_expect_le_expect_abs P f).trans (expect_abs_le_rms P f)
/-- The RMS triangle inequality used to add errors in a common ambient distribution. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f, g ∈ α → ℝ, we have

‖ ((a ↦ f(a) + g(a)))‖_(2,P) ≤ ‖ f‖_(2,P) + ‖ g‖_(2,P).
-/
theorem rms_add_le (P : FiniteDistribution α) (f g : α → ℝ) :
    rms P (fun a => f a + g a) ≤ rms P f + rms P g := by
  -- Expand the square before applying Cauchy--Schwarz to the cross term. Nonnegativity of each RMS then turns the squared comparison into the goal.
  have hexpand : P.expect (fun a => (f a + g a) ^ 2) =
      P.expect (fun a => f a ^ 2) + 2 * P.expect (fun a => f a * g a) +
        P.expect (fun a => g a ^ 2) := by
    calc
      _ = P.expect (fun a => f a ^ 2 + 2 * (f a * g a) + g a ^ 2) := by
        congr 1
        funext a
        ring
      _ = _ := by rw [expect_add, expect_add, expect_smul]
  have hcs := (le_abs_self (P.expect (fun a => f a * g a))).trans
    (abs_expect_mul_le_rms_mul_rms P f g)
  apply (sq_le_sq₀ (rms_nonneg P _) (add_nonneg (rms_nonneg P f) (rms_nonneg P g))).mp
  rw [add_sq, rms_sq, rms_sq, rms_sq, hexpand]
  nlinarith
/-- Pointwise domination of squared values implies domination of RMS values under the same distribution. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f, g ∈ α → ℝ, assume ∀ a, (f(a))² ≤ (g(a))². Then

‖ f‖_(2,P) ≤ ‖ g‖_(2,P).
-/
theorem rms_le_of_sq_le (P : FiniteDistribution α) {f g : α → ℝ}
    (h : ∀ a, f a ^ 2 ≤ g a ^ 2) : rms P f ≤ rms P g :=
  Real.sqrt_le_sqrt (P.expect_mono h)
/-- Transfer a nonnegative expectation through a pointwise density bound. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P, Q ∈ 𝒟(α); C ∈ ℝ; f ∈ α → ℝ, assume ∀ a, P(a) ≤ C · Q(a); ∀ a, 0 ≤ f(a). Then

𝔼_(u ← P) [f(u)] ≤ C · 𝔼_(v ← Q) [f(v)].
-/
theorem expect_le_of_weight_le (P Q : FiniteDistribution α) (C : ℝ)
    (hweight : ∀ a, P.weight a ≤ C * Q.weight a) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) : P.expect f ≤ C * Q.expect f := by
  unfold FiniteDistribution.expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  calc
    _ ≤ (C * Q.weight a) * f a := mul_le_mul_of_nonneg_right (hweight a) (hf a)
    _ = _ := by ring
end MatrixRefresh
