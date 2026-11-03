import Proofs.Compiler.GateApproximation.MatrixPhase.JointGraphDecomposition
import Proofs.Compiler.GateApproximation.MatrixPhase.JointL1Projection
import Proofs.Compiler.Foundations.LinearAlgebra.GramBounds



/-!
# Moment estimates for the random-refresh operator bound

The energy-sensitive exceptional-product estimate and the passage from second/fourth moments to the operator bound are proved here. The unrestricted binary-matrix rank calculation supplying these moments is proved in `Proofs/Compiler/GateApproximation/MatrixPhase/ResidualBound.lean`; `Proofs/Compiler/GateApproximation/MatrixPhase/InjectiveRefreshOperator.lean` instantiates the resulting operator and local approximation bounds for the actual tensor graph.
-/
set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

/-- Retain a squared-entry factor rather than bounding everything by `B^4`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b, c, d, B ∈ ℝ, assume 0 ≤ B; |a| ≤ B; |b| ≤ B; |c| ≤ B; |d| ≤ B. Then

|a · b · c · d| ≤ B² / 4 · (a² + b² + c² + d²).
-/
theorem four_entry_energy_bound (a b c d B : ℝ) (hB : 0 ≤ B)
    (ha : |a| ≤ B) (hb : |b| ≤ B) (hc : |c| ≤ B) (hd : |d| ≤ B) :
    |a * b * c * d| ≤ B ^ 2 / 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  have hab : |a| * |b| ≤ B ^ 2 := by
    simpa only [pow_two] using mul_le_mul ha hb (abs_nonneg b) hB
  have hcd : |c| * |d| ≤ B ^ 2 := by
    simpa only [pow_two] using mul_le_mul hc hd (abs_nonneg d) hB
  have habsq : 2 * (|a| * |b|) ≤ a ^ 2 + b ^ 2 := by
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  have hcdsq : 2 * (|c| * |d|) ≤ c ^ 2 + d ^ 2 := by
    nlinarith [sq_nonneg (|c| - |d|), sq_abs c, sq_abs d]
  have h₁ := mul_le_mul_of_nonneg_right hab (mul_nonneg (abs_nonneg c) (abs_nonneg d))
  have h₂ := mul_le_mul_of_nonneg_left hcd (mul_nonneg (abs_nonneg a) (abs_nonneg b))
  have h₃ := mul_le_mul_of_nonneg_left habsq (sq_nonneg B)
  have h₄ := mul_le_mul_of_nonneg_left hcdsq (sq_nonneg B)
  simp only [abs_mul]
  nlinarith

/-- If each corner's weighted second moment is at most `p*E`, the exceptional four-entry product costs at most `p*B²*E`, even when products have either sign. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Ω a set; P ∈ 𝒟(Ω); w, a, b, c, d ∈ Ω → ℝ; B, p, E ∈ ℝ, assume Ω is finite; 0 ≤ B; ∀ x, 0 ≤ w(x); ∀ x, |a(x)| ≤ B; ∀ x, |b(x)| ≤ B; ∀ x, |c(x)| ≤ B; ∀ x, |d(x)| ≤ B; 𝔼_(x ← P) [w(x) · (a(x))²] ≤ p · E; 𝔼_(x ← P) [w(x) · (b(x))²] ≤ p · E; 𝔼_(x ← P) [w(x) · (c(x))²] ≤ p · E; 𝔼_(x ← P) [w(x) · (d(x))²] ≤ p · E. Then

𝔼_(x ← P) [w(x) · |a(x) · b(x) · c(x) · d(x)|] ≤ p · B² · E.
-/
theorem weighted_four_entry_energy_bound {Ω : Type*} [Fintype Ω]
    (P : FiniteDistribution Ω) (w a b c d : Ω → ℝ) (B p E : ℝ)
    (hB : 0 ≤ B) (hw : ∀ x, 0 ≤ w x)
    (ha : ∀ x, |a x| ≤ B) (hb : ∀ x, |b x| ≤ B)
    (hc : ∀ x, |c x| ≤ B) (hd : ∀ x, |d x| ≤ B)
    (hma : P.expect (fun x => w x * a x ^ 2) ≤ p * E)
    (hmb : P.expect (fun x => w x * b x ^ 2) ≤ p * E)
    (hmc : P.expect (fun x => w x * c x ^ 2) ≤ p * E)
    (hmd : P.expect (fun x => w x * d x ^ 2) ≤ p * E) :
    P.expect (fun x => w x * |a x * b x * c x * d x|) ≤ p * B ^ 2 * E := by
  have hp := P.expect_mono (fun x =>
    mul_le_mul_of_nonneg_left
      (four_entry_energy_bound (a x) (b x) (c x) (d x) B hB (ha x) (hb x) (hc x) (hd x))
      (hw x))
  have heq : P.expect (fun x => w x * (B ^ 2 / 4 *
      (a x ^ 2 + b x ^ 2 + c x ^ 2 + d x ^ 2))) =
      B ^ 2 / 4 * (P.expect (fun x => w x * a x ^ 2) +
        P.expect (fun x => w x * b x ^ 2) + P.expect (fun x => w x * c x ^ 2) +
        P.expect (fun x => w x * d x ^ 2)) := by
    have hpoint (x : Ω) : w x * (B ^ 2 / 4 *
        (a x ^ 2 + b x ^ 2 + c x ^ 2 + d x ^ 2)) =
        B ^ 2 / 4 * ((w x * a x ^ 2 + w x * b x ^ 2) +
          w x * c x ^ 2 + w x * d x ^ 2) := by ring
    simp_rw [hpoint, MatrixRefresh.expect_smul, MatrixRefresh.expect_add]
  rw [heq] at hp
  have hm := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add hma hmb) hmc) hmd)
    (by positivity : 0 ≤ B ^ 2 / 4)
  exact hp.trans (hm.trans_eq (by ring))

/-- The first-moment consequence of Cauchy--Schwarz. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Ω a set; P ∈ 𝒟(Ω); f ∈ Ω → ℝ, assume Ω is finite. Then

𝔼_(u ← P) [f(u)] ≤ √(𝔼_(x ← P) [(f(x))²]).
-/
theorem mean_le_sqrt_second {Ω : Type*} [Fintype Ω]
    (P : FiniteDistribution Ω) (f : Ω → ℝ) :
    P.expect f ≤ Real.sqrt (P.expect (fun x => f x ^ 2)) := by
  have h := expect_mul_sq_le P f (fun _ => 1)
  simp only [mul_one, one_pow, FiniteDistribution.expect_one] at h
  have hE := P.expect_nonneg (fun x => f x ^ 2) (fun _ => sq_nonneg _)
  nlinarith [Real.sq_sqrt hE, Real.sqrt_nonneg (P.expect (fun x => f x ^ 2))]

/-- The current Gram argument takes a sum of the two deviations, without an additional square root of a deviation. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Ω a set; P ∈ 𝒟(Ω); h, u, v ∈ Ω → ℝ; θ, A, B ∈ ℝ, assume Ω is finite; ∀ x, h(x) ≤ θ + (u(x) + v(x)) / 2; 𝔼_(x ← P) [(u(x))²] ≤ A; 𝔼_(x ← P) [(v(x))²] ≤ B. Then

𝔼_(a ← P) [h(a)] ≤ θ + (√A + √B) / 2.
-/
theorem gram_mean_of_second_moments {Ω : Type*} [Fintype Ω]
    (P : FiniteDistribution Ω) (h u v : Ω → ℝ) (θ A B : ℝ)
    (hpoint : ∀ x, h x ≤ θ + (u x + v x) / 2)
    (hu : P.expect (fun x => u x ^ 2) ≤ A)
    (hv : P.expect (fun x => v x ^ 2) ≤ B) :
    P.expect h ≤ θ + (Real.sqrt A + Real.sqrt B) / 2 := by
  have hp := P.expect_mono hpoint
  have hmean : P.expect (fun x => θ + (u x + v x) / 2) =
      θ + (P.expect u + P.expect v) / 2 := by
    simp only [div_eq_mul_inv, MatrixRefresh.expect_add, FiniteDistribution.expect_const,
      MatrixRefresh.expect_mul_const]
  rw [hmean] at hp
  have hu' := (mean_le_sqrt_second P u).trans (Real.sqrt_le_sqrt hu)
  have hv' := (mean_le_sqrt_second P v).trans (Real.sqrt_le_sqrt hv)
  linarith

/-- A residual fourth moment gives exactly the square-root threshold loss. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Ω a set; P ∈ 𝒟(Ω); f ∈ Ω → ℝ; C, β ∈ ℝ, assume Ω is finite; ∀ x, 0 ≤ f(x); 0 ≤ C; 0 ≤ β; 𝔼_(x ← P) [(f(x))⁴] ≤ C⁴ · β². Then

𝔼_(v ← P) [f(v)] ≤ C · √β.
-/
theorem residual_mean_of_fourth_moment {Ω : Type*} [Fintype Ω]
    (P : FiniteDistribution Ω) (f : Ω → ℝ) (C β : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hm : P.expect (fun x => f x ^ 4) ≤ C ^ 4 * β ^ 2) :
    P.expect f ≤ C * Real.sqrt β := by
  have h := expect_fourthRoot_le P (fun x => f x ^ 4) (fun _ => by positivity)
  simp only [fourthRoot_pow_four_of_nonneg (hf _)] at h
  refine h.trans ((fourthRoot_mono hm).trans_eq ?_)
  rw [fourthRoot_mul (by positivity), fourthRoot_pow_four_of_nonneg hC]
  simp only [fourthRoot, Real.sqrt_sq hβ]

/-- Explicit residual arithmetic after the four-rank calculation; `L` is the squared L2 norm, bounded by nine, and `B` is the largest absolute entry. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For moment, cycle, B, L, β, C ∈ ℝ, assume 0 ≤ L; L ≤ 9; cycle ≤ C² · β² · L; β² · B² ≤ 9; moment ≤ 64 · cycle + 168 · β⁴ · B² · L. Then

moment ≤ (576 · C² + 13608) · β².
-/
theorem residual_moment_bound (moment cycle B L β C : ℝ)
    (hL0 : 0 ≤ L) (hL : L ≤ 9)
    (hcycle : cycle ≤ C ^ 2 * β ^ 2 * L)
    (hentry : β ^ 2 * B ^ 2 ≤ 9)
    (hmoment : moment ≤ 64 * cycle + 168 * β ^ 4 * B ^ 2 * L) :
    moment ≤ (576 * C ^ 2 + 13608) * β ^ 2 := by
  have hc := mul_le_mul_of_nonneg_left hcycle (by norm_num : (0 : ℝ) ≤ 64)
  have hL' := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ C ^ 2 * β ^ 2)
  have hB' := mul_le_mul_of_nonneg_left hentry (by positivity : 0 ≤ β ^ 2 * L)
  have hL'' := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ β ^ 2)
  nlinarith

/-- Assembly of the factor-two split from explicit second and fourth moments. The actual matrix counting estimates are hypotheses, not silently assumed. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Ω a set; P ∈ 𝒟(Ω); f, h, d, u, v ∈ Ω → ℝ; θ, β, C₁, C₂ ∈ ℝ, assume Ω is finite; 0 ≤ β; β ≤ 1; 0 ≤ C₁; 0 ≤ C₂; ∀ x, 0 ≤ d(x); ∀ x, f(x) ≤ 2 · h(x) + d(x); ∀ x, h(x) ≤ θ + (u(x) + v(x)) / 2; 𝔼_(x ← P) [(u(x))²] ≤ (C₁ · β)²; 𝔼_(x ← P) [(v(x))²] ≤ (C₁ · β)²; 𝔼_(x ← P) [(d(x))⁴] ≤ C₂⁴ · β². Then

𝔼_(b ← P) [f(b)] ≤ 2 · θ + (2 · C₁ + C₂) · √β.
-/
theorem operator_mean_of_split_moments {Ω : Type*} [Fintype Ω]
    (P : FiniteDistribution Ω) (f h d u v : Ω → ℝ) (θ β C₁ C₂ : ℝ)
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hd : ∀ x, 0 ≤ d x)
    (hsplit : ∀ x, f x ≤ 2 * h x + d x)
    (hgram : ∀ x, h x ≤ θ + (u x + v x) / 2)
    (hu : P.expect (fun x => u x ^ 2) ≤ (C₁ * β) ^ 2)
    (hv : P.expect (fun x => v x ^ 2) ≤ (C₁ * β) ^ 2)
    (hresidual : P.expect (fun x => d x ^ 4) ≤ C₂ ^ 4 * β ^ 2) :
    P.expect f ≤ 2 * θ + (2 * C₁ + C₂) * Real.sqrt β := by
  have hg := gram_mean_of_second_moments P h u v θ _ _ hgram hu hv
  rw [Real.sqrt_sq (mul_nonneg hC₁ hβ)] at hg
  have hr := residual_mean_of_fourth_moment P d C₂ β hd hC₂ hβ hresidual
  have hp := P.expect_mono hsplit
  rw [MatrixRefresh.expect_add, MatrixRefresh.expect_smul] at hp
  have hsmall : β ≤ Real.sqrt β := by
    nlinarith [Real.sq_sqrt hβ, Real.sqrt_nonneg β]
  have hsmall' := mul_le_mul_of_nonneg_left hsmall hC₁
  nlinarith

end

end CircuitCompiler.RefreshAnalysis
