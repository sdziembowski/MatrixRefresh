import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar bootstrap for the local refreshing residual

This is the final scalar step of the local-approximation proof: an estimate `t² ≤ A sqrt(beta) sqrt(t) + B beta²` yields `t = O(beta^(1/3))`. All constants and hypotheses are explicit. The proof does not assume any security or local-approximation theorem.
-/

noncomputable section

namespace RefreshingProof.Local

/-- A quartic with nonnegative coefficients controls its nonnegative argument. -/
theorem quartic_bootstrap {v A B : ℝ} (_hv : 0 ≤ v) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : v ^ 4 ≤ A * v + B) : v ≤ A + B + 1 := by
  by_contra hn
  have hm : A + B + 1 < v := lt_of_not_ge hn
  have hv1 : 1 < v := by linarith
  have hprod : 0 < v * (v - (A + B + 1)) :=
    mul_pos (lt_trans zero_lt_one hv1) (sub_pos.mpr hm)
  have hBu : 0 ≤ B * (v - 1) := mul_nonneg hB (by linarith)
  have hsq1 : 0 ≤ v ^ 2 - 1 := by nlinarith
  have hfour : v ^ 2 ≤ v ^ 4 := by
    have hp := mul_nonneg (sq_nonneg v) hsq1
    nlinarith
  nlinarith

/-- Polynomial-scale version of the final residual bootstrap. -/
theorem residual_bootstrap_cube {r t A B : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (ht : 0 ≤ t) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : t ^ 2 ≤ A * Real.sqrt (r ^ 3) * Real.sqrt t + B * (r ^ 3) ^ 2) :
    t ≤ (A + B + 1) ^ 2 * r := by
  let v := Real.sqrt (t / r)
  have hv : 0 ≤ v := Real.sqrt_nonneg _
  have hv2 : v ^ 2 = t / r := Real.sq_sqrt (div_nonneg ht (le_of_lt hr))
  have htv : t = r * v ^ 2 := by
    rw [hv2]
    field_simp [ne_of_gt hr]
  have hroot : Real.sqrt (r ^ 3) * Real.sqrt t = r ^ 2 * v := by
    have hl0 : 0 ≤ Real.sqrt (r ^ 3) * Real.sqrt t := by positivity
    have hr0 : 0 ≤ r ^ 2 * v := mul_nonneg (sq_nonneg _) hv
    have hlsq : (Real.sqrt (r ^ 3) * Real.sqrt t) ^ 2 = r ^ 3 * t := by
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt ht]
    have hrsq : (r ^ 2 * v) ^ 2 = r ^ 3 * t := by
      rw [mul_pow, hv2]
      field_simp [ne_of_gt hr]
    nlinarith
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hr4 : r ^ 4 ≤ 1 := by
    have h0 : 0 ≤ r ^ 2 := sq_nonneg r
    have h2 : r ^ 2 ≤ 1 := by nlinarith [mul_nonneg (le_of_lt hr) (sub_nonneg.mpr hr1)]
    have hp := mul_nonneg (sub_nonneg.mpr h2) (by positivity : 0 ≤ 1 + r ^ 2)
    nlinarith
  have hscaled : r ^ 2 * v ^ 4 ≤ r ^ 2 * (A * v + B * r ^ 4) := by
    calc
      r ^ 2 * v ^ 4 = t ^ 2 := by rw [htv]; ring
      _ ≤ A * Real.sqrt (r ^ 3) * Real.sqrt t + B * (r ^ 3) ^ 2 := h
      _ = _ := by rw [mul_assoc A, hroot]; ring
  have hv4 : v ^ 4 ≤ A * v + B := by
    have hc : v ^ 4 ≤ A * v + B * r ^ 4 := (mul_le_mul_iff_right₀ hr2).mp hscaled
    have hb : B * r ^ 4 ≤ B := by nlinarith
    linarith
  have hvbound := quartic_bootstrap hv hA hB hv4
  have hvbound2 : v ^ 2 ≤ (A + B + 1) ^ 2 :=
    (sq_le_sq₀ hv (by positivity)).mpr hvbound
  rw [htv]
  nlinarith

/-- An explicit coefficient in the residual estimate; it depends only on the nonnegative constants in the scalar bootstrap inequality. -/
def residualBootstrapConstant (A B : ℝ) : ℝ := (A + B + 1) ^ 2

/-- The explicit bootstrap coefficient satisfies the paper's convention C ≥ 1. -/
theorem residualBootstrapConstant_one_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    1 ≤ residualBootstrapConstant A B := by
  unfold residualBootstrapConstant
  nlinarith [sq_nonneg (A + B)]

/-- Final local residual bound, with concrete constant `(A+B+1)²`. The fractional power is a real power, and the same constant works for every `0 < beta ≤ 1` and every nonnegative residual norm `t`. -/
theorem residual_bootstrap {beta t A B : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (ht : 0 ≤ t)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : t ^ 2 ≤ A * Real.sqrt beta * Real.sqrt t + B * beta ^ 2) :
    t ≤ residualBootstrapConstant A B * beta ^ (1 / 3 : ℝ) := by
  let r := beta ^ (1 / 3 : ℝ)
  have hr : 0 < r := Real.rpow_pos_of_pos hbeta _
  have hr1 : r ≤ 1 := by
    exact Real.rpow_le_one (le_of_lt hbeta) hbeta1 (by norm_num)
  have hr3 : r ^ 3 = beta := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hbeta)]
    norm_num
  have h' : t ^ 2 ≤ A * Real.sqrt (r ^ 3) * Real.sqrt t + B * (r ^ 3) ^ 2 := by
    simpa only [hr3] using h
  exact residual_bootstrap_cube hr hr1 ht hA hB h'

end RefreshingProof.Local
