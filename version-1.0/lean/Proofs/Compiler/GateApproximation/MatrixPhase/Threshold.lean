import Proofs.Compiler.GateApproximation.MatrixPhase.Moments



/-!
# The threshold and numerical assembly in the random-refresh estimate

These lemmas supply the exact substitution β = D^(-1/4). The four-cycle estimate remains an explicit premise until instantiated by the matrix-counting argument; this file is not itself the supported operator theorem.
-/
set_option autoImplicit false

set_option maxHeartbeats 1000000

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

/-
Mathematical definition (normal notation): For D ∈ ℝ, define

refreshThreshold(D) := D^(−(1 / 4)).
-/
def refreshThreshold (D : ℝ) : ℝ := D ^ (-(1 / 4 : ℝ))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D ∈ ℝ, assume 0 < D. Then

0 < refreshThreshold(D).
-/
theorem refreshThreshold_pos {D : ℝ} (hD : 0 < D) : 0 < refreshThreshold D :=
  Real.rpow_pos_of_pos hD _

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D ∈ ℝ, assume 1 ≤ D. Then

refreshThreshold(D) ≤ 1.
-/
theorem refreshThreshold_le_one {D : ℝ} (hD : 1 ≤ D) : refreshThreshold D ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos hD (by norm_num)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D ∈ ℝ, assume 0 < D. Then

(refreshThreshold(D))⁴ = (D)⁻¹.
-/
theorem refreshThreshold_fourth {D : ℝ} (hD : 0 < D) :
    refreshThreshold D ^ 4 = D⁻¹ := by
  unfold refreshThreshold
  rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le]
  norm_num [Real.rpow_neg_one]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D ∈ ℝ, assume 0 < D. Then

√(refreshThreshold(D)) = D^(−(1 / 8)).
-/
theorem sqrt_refreshThreshold {D : ℝ} (hD : 0 < D) :
    Real.sqrt (refreshThreshold D) = D ^ (-(1 / 8 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, refreshThreshold, ← Real.rpow_mul hD.le]
  congr 1
  norm_num

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D ∈ ℝ, assume 0 < D. Then

(refreshThreshold(D))² = (√D)⁻¹.
-/
theorem refreshThreshold_square {D : ℝ} (hD : 0 < D) :
    refreshThreshold D ^ 2 = (Real.sqrt D)⁻¹ := by
  unfold refreshThreshold
  rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le, Real.sqrt_eq_rpow,
    ← Real.rpow_neg hD.le]
  congr 1
  norm_num

/-- The actual tensor Gram denominator is at least the square root of the feature count; after division by β, its error is at most β. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D, Q ∈ ℝ, assume 0 < D; √D ≤ Q. Then

1 / (Q · refreshThreshold(D)) ≤ refreshThreshold(D).
-/
theorem gram_threshold_bound {D Q : ℝ} (hD : 0 < D) (hQ : Real.sqrt D ≤ Q) :
    1 / (Q * refreshThreshold D) ≤ refreshThreshold D := by
  have hβ := refreshThreshold_pos hD
  have hs := Real.sqrt_pos.mpr hD
  have hQ0 : 0 < Q := hs.trans_le hQ
  apply (div_le_iff₀ (mul_pos hQ0 hβ)).2
  have h := mul_le_mul_of_nonneg_right hQ (sq_nonneg (refreshThreshold D))
  have heq : Real.sqrt D * refreshThreshold D ^ 2 = 1 := by
    rw [refreshThreshold_square hD, mul_inv_cancel₀ hs.ne']
  rw [heq] at h
  nlinarith

/-- The binary consistency-mask loss is at most twice β² when its ambient field-vector carrier is at least the feature carrier. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D, Q ∈ ℝ, assume 0 < D; 2 ≤ Q; D ≤ Q. Then

√Q / (Q - 1) ≤ 2 · (refreshThreshold(D))².
-/
theorem binary_mask_threshold_bound {D Q : ℝ} (hD : 0 < D) (hQ : 2 ≤ Q)
    (hDQ : D ≤ Q) :
    Real.sqrt Q / (Q - 1) ≤ 2 * refreshThreshold D ^ 2 := by
  have hQ0 : 0 < Q := by linarith
  have hsQ := Real.sqrt_pos.mpr hQ0
  have hsD := Real.sqrt_pos.mpr hD
  have hsqQ := Real.sq_sqrt hQ0.le
  have hratio : Real.sqrt Q / (Q-1) ≤ 2 / Real.sqrt Q := by
    apply (div_le_div_iff₀ (by linarith : 0 < Q-1) hsQ).2
    nlinarith
  rw [refreshThreshold_square hD]
  calc
    Real.sqrt Q / (Q-1) ≤ 2 / Real.sqrt Q := hratio
    _ ≤ 2 / Real.sqrt D := by
      exact div_le_div_of_nonneg_left (by norm_num) hsD (Real.sqrt_le_sqrt hDQ)
    _ = _ := by rw [div_eq_mul_inv]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D ∈ ℝ, assume 1 ≤ D. Then

refreshThreshold(D) ≤ √(refreshThreshold(D)).
-/
theorem refreshThreshold_le_sqrt {D : ℝ} (hD : 1 ≤ D) :
    refreshThreshold D ≤ Real.sqrt (refreshThreshold D) := by
  have hp := (refreshThreshold_pos (lt_of_lt_of_le zero_lt_one hD)).le
  have h1 := refreshThreshold_le_one hD
  nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg (refreshThreshold D)]

/-- The inverse feature-cardinality factor in the collision calculation is β⁴. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D, moment, cycle, B, L, C ∈ ℝ, assume 0 < D; 0 ≤ L; L ≤ 9; cycle ≤ C² · (refreshThreshold(D))² · L; (refreshThreshold(D))² · B² ≤ 9; moment ≤ 64 · cycle + 168 / D · B² · L. Then

moment ≤ (576 · C² + 13608) · (refreshThreshold(D))².
-/
theorem residual_moment_at_feature_count (D moment cycle B L C : ℝ)
    (hD : 0 < D) (hL0 : 0 ≤ L) (hL : L ≤ 9)
    (hcycle : cycle ≤ C ^ 2 * refreshThreshold D ^ 2 * L)
    (hentry : refreshThreshold D ^ 2 * B ^ 2 ≤ 9)
    (hmoment : moment ≤ 64 * cycle + 168 / D * B ^ 2 * L) :
    moment ≤ (576 * C ^ 2 + 13608) * refreshThreshold D ^ 2 := by
  apply residual_moment_bound moment cycle B L (refreshThreshold D) C hL0 hL hcycle hentry
  simpa only [refreshThreshold_fourth hD, div_eq_mul_inv] using hmoment

/-- A convenient explicit constant bounds the fourth root of the residual coefficient. No hidden dimension-dependent constant is introduced. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For C ∈ ℝ, assume 0 ≤ C. Then

576 · C² + 13608 ≤ (24 · (C + 1))⁴.
-/
theorem residual_constant_bound (C : ℝ) (hC : 0 ≤ C) :
    576 * C ^ 2 + 13608 ≤ (24 * (C + 1)) ^ 4 := by
  have h2 : C ^ 2 ≤ (C+1)^2 := by nlinarith
  have h4 : (C+1)^2 ≤ (C+1)^4 := by nlinarith [sq_nonneg (C^2+2*C)]
  have hone : 1 ≤ (C+1)^4 := by nlinarith [sq_nonneg (C^2+2*C)]
  nlinarith

/-- Assemble an actual large-part mean and residual four-cycle estimate at the paper's threshold. This is the numeric final step, with its input estimates stated explicitly. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Ω a set; P ∈ 𝒟(Ω); f, h, d ∈ Ω → ℝ; D, θ, C₁, C₂, cycle, B, L ∈ ℝ, assume Ω is finite; 1 ≤ D; 0 ≤ C₁; 0 ≤ C₂; ∀ x, 0 ≤ d(x); ∀ x, f(x) ≤ 2 · h(x) + d(x); 𝔼_(u ← P) [h(u)] ≤ θ + C₁ · refreshThreshold(D); 0 ≤ L; L ≤ 9; cycle ≤ C₂² · (refreshThreshold(D))² · L; (refreshThreshold(D))² · B² ≤ 9; 𝔼_(x ← P) [(d(x))⁴] ≤ 64 · cycle + 168 / D · B² · L. Then

𝔼_(w ← P) [f(w)] ≤ 2 · θ + (2 · C₁ + 24 · (C₂ + 1)) · D^(−(1 / 8)).
-/
theorem operator_mean_at_feature_count {Ω : Type*} [Fintype Ω]
    (P : FiniteDistribution Ω) (f h d : Ω → ℝ) (D θ C₁ C₂ cycle B L : ℝ)
    (hD : 1 ≤ D) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hd : ∀ x, 0 ≤ d x)
    (hsplit : ∀ x, f x ≤ 2 * h x + d x)
    (hlarge : P.expect h ≤ θ + C₁ * refreshThreshold D)
    (hL0 : 0 ≤ L) (hL : L ≤ 9)
    (hcycle : cycle ≤ C₂ ^ 2 * refreshThreshold D ^ 2 * L)
    (hentry : refreshThreshold D ^ 2 * B ^ 2 ≤ 9)
    (hresidual : P.expect (fun x => d x ^ 4) ≤ 64 * cycle + 168 / D * B ^ 2 * L) :
    P.expect f ≤ 2 * θ + (2 * C₁ + 24 * (C₂ + 1)) * D ^ (-(1 / 8 : ℝ)) := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hm := residual_moment_at_feature_count D _ cycle B L C₂ hD0 hL0 hL hcycle hentry hresidual
  have hc := mul_le_mul_of_nonneg_right (residual_constant_bound C₂ hC₂)
    (sq_nonneg (refreshThreshold D))
  have hr := residual_mean_of_fourth_moment P d (24*(C₂+1)) (refreshThreshold D)
    hd (by positivity) (refreshThreshold_pos hD0).le (hm.trans hc)
  have hp := P.expect_mono hsplit
  have heq : P.expect (fun x => 2 * h x + d x) = 2 * P.expect h + P.expect d := by
    simp only [MatrixRefresh.expect_add, MatrixRefresh.expect_smul]
  rw [heq] at hp
  have hβ := mul_le_mul_of_nonneg_left (refreshThreshold_le_sqrt hD) hC₁
  rw [← sqrt_refreshThreshold hD0]
  linarith

end

end CircuitCompiler.RefreshAnalysis
