import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring



/-!
# The scalar bootstrap in the direct residual estimate

The matrix argument for local approximation gives `t² ≤ C * sqrt β * sqrt t + C * β²`. This module proves only the final scalar implication, with the explicit harmless constant `2*C+2`. The matrix inequality itself is an explicit hypothesis, not a proved input of this file.
-/

set_option autoImplicit false

namespace CircuitCompiler.AnswerApproximation

/-- The elementary absorption inequality used at the cube-root scale. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For β, t ∈ ℝ, assume 0 < β; 0 ≤ t. Then

√β · √t ≤ β^(1 / 3) · t + (β^(1 / 3))².
-/
theorem sqrt_product_le_cuberoot (β t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) :
    Real.sqrt β * Real.sqrt t ≤ β ^ (1 / 3 : ℝ) * t +
      (β ^ (1 / 3 : ℝ)) ^ 2 := by
  let b := β ^ (1 / 3 : ℝ)
  have hb : 0 < b := Real.rpow_pos_of_pos hβ _
  have hcube : b ^ 3 = β := by
    dsimp [b]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hβ.le]
    norm_num
  have hβsq := Real.sq_sqrt hβ.le
  have htsq := Real.sq_sqrt ht
  have hprod : (Real.sqrt β * Real.sqrt t) ^ 2 = β * t := by
    rw [mul_pow, hβsq, htsq]
  have hnonneg : 0 ≤ b * t + b ^ 2 := by positivity
  have hrest : 0 ≤ b ^ 2 * t ^ 2 + b ^ 3 * t + b ^ 4 := by positivity
  change Real.sqrt β * Real.sqrt t ≤ b * t + b ^ 2
  nlinarith [hprod, hrest]

/-- The exact scalar step after the residual four-cycle estimate. The constant is explicit; deriving the hypothesis from the actual table remains separate. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For β, t, C ∈ ℝ, assume 0 < β; β ≤ 1; 0 ≤ t; 0 ≤ C; t² ≤ C · √β · √t + C · β². Then

t ≤ (2 · C + 2) · β^(1 / 3).
-/
theorem residual_error_bootstrap (β t C : ℝ) (hβ : 0 < β) (hβone : β ≤ 1)
    (ht : 0 ≤ t) (hC : 0 ≤ C)
    (herror : t ^ 2 ≤ C * Real.sqrt β * Real.sqrt t + C * β ^ 2) :
    t ≤ (2 * C + 2) * β ^ (1 / 3 : ℝ) := by
  let b := β ^ (1 / 3 : ℝ)
  have hb : 0 < b := Real.rpow_pos_of_pos hβ _
  have hβb : β ≤ b := Real.self_le_rpow_of_le_one hβ.le hβone (by norm_num)
  have hsquare : β ^ 2 ≤ b ^ 2 := by nlinarith
  have hyoung := sqrt_product_le_cuberoot β t hβ ht
  change Real.sqrt β * Real.sqrt t ≤ b * t + b ^ 2 at hyoung
  have hscaled := mul_le_mul_of_nonneg_left hyoung hC
  have hsmall := mul_le_mul_of_nonneg_left hsquare hC
  have hquadratic : t ^ 2 ≤ C * b * t + 2 * C * b ^ 2 := by
    nlinarith [herror, hscaled, hsmall]
  change t ≤ (2 * C + 2) * b
  by_contra hnot
  have hlarge : (2 * C + 2) * b < t := lt_of_not_ge hnot
  have hCb : 0 ≤ C * b := mul_nonneg hC hb.le
  have htb : 2 * b < t := by nlinarith
  have hCt : 2 * C * b < t := by nlinarith
  have htpos : 0 < t := lt_trans (by positivity : 0 < 2 * b) htb
  have hlast := mul_le_mul_of_nonneg_left htb.le hCb
  have hcontradiction : 0 < t * (t - 2 * C * b) :=
    mul_pos htpos (sub_pos.mpr hCt)
  nlinarith

end CircuitCompiler.AnswerApproximation
