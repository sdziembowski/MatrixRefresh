import Proofs.Refreshing.TwoSecret

/-!
# Concrete parameter choice for Theorem4.1

The local threshold is q^(-1/3), the residual error has rate q^(-1/9), and the discrepancy-to-threshold ratio is bounded by the same rate. All exponents and divisions in this file are real.
-/

noncomputable section

namespace RefreshingProof.Local
open Refreshing

/-- The refreshing proof uses truncation threshold β = q(n)^(−1/3). -/
def paperBeta (n : ℕ) : ℝ := (q n : ℝ) ^ (-(1 / 3 : ℝ))
/-- The target refreshing decay is q(n)^(−1/9). -/
def paperDecay (n : ℕ) : ℝ := (q n : ℝ) ^ (-(1 / 9 : ℝ))
/-- The two-secret discrepancy allowance is 3/√(q(n) − 1). -/
def paperDiscrepancy (n : ℕ) : ℝ := 3 / Real.sqrt ((q n : ℝ) - 1)

/-- For n ≥ 2, the prescribed refreshing threshold is positive. -/
theorem paperBeta_pos {n : ℕ} (hn : 2 ≤ n) : 0 < paperBeta n := by
  apply Real.rpow_pos_of_pos
  have := q_real_three_le hn
  linarith

/-- For n ≥ 2, the prescribed refreshing threshold is at most one. -/
theorem paperBeta_le_one {n : ℕ} (hn : 2 ≤ n) : paperBeta n ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos (by have := q_real_three_le hn; linarith) (by norm_num)

/-- The cube of the prescribed refreshing threshold equals 1/q(n). -/
theorem paperBeta_cube {n : ℕ} (hn : 2 ≤ n) : paperBeta n ^ 3 = (q n : ℝ)⁻¹ := by
  have hq : 0 ≤ (q n : ℝ) := by have := q_real_three_le hn; linarith
  unfold paperBeta
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq]
  norm_num [Real.rpow_neg_one]

/-- The prescribed refreshing threshold satisfies the exact identity q(n)β³ = 1. -/
theorem paperBeta_threshold {n : ℕ} (hn : 2 ≤ n) : (q n : ℝ) * paperBeta n ^ 3 = 1 := by
  rw [paperBeta_cube hn]
  exact mul_inv_cancel₀ (by have := q_real_three_le hn; linarith)

/-- The cube root of the prescribed refreshing threshold equals the target q(n)^(−1/9) decay. -/
theorem paperBeta_third {n : ℕ} (hn : 2 ≤ n) : paperBeta n ^ (1 / 3 : ℝ) = paperDecay n := by
  have hq : 0 ≤ (q n : ℝ) := by have := q_real_three_le hn; linarith
  unfold paperBeta paperDecay
  rw [← Real.rpow_mul hq]
  norm_num

/-- For n ≥ 2, the target refreshing decay is positive. -/
theorem paperDecay_pos {n : ℕ} (hn : 2 ≤ n) : 0 < paperDecay n := by
  apply Real.rpow_pos_of_pos
  have := q_real_three_le hn
  linarith

/-- The prescribed two-secret discrepancy allowance is nonnegative. -/
theorem paperDiscrepancy_nonneg (n : ℕ) : 0 ≤ paperDiscrepancy n := by
  unfold paperDiscrepancy
  positivity

/-- The discrepancy coefficient agrees exactly with the actual two-secret theorem. -/
theorem paperDiscrepancy_eq (n : ℕ) :
    paperDiscrepancy n = 3 / Real.sqrt ((2 : ℝ) ^ n - 2) := by
  unfold paperDiscrepancy
  rw [q_real_eq]
  congr 2
  ring

/-- The square-root discrepancy is at most6q^(-1/2) in every theorem dimension. -/
theorem paperDiscrepancy_le_six_half_decay {n : ℕ} (hn : 2 ≤ n) :
    paperDiscrepancy n ≤ 6 / Real.sqrt (q n : ℝ) := by
  have hq := q_real_three_le hn
  have hq0 : 0 < (q n : ℝ) := by linarith
  have hm0 : 0 < (q n : ℝ) - 1 := by linarith
  have hs : Real.sqrt (q n : ℝ) ≤ 2 * Real.sqrt ((q n : ℝ) - 1) := by
    have hs1 := Real.sq_sqrt (le_of_lt hq0)
    have hs2 := Real.sq_sqrt (le_of_lt hm0)
    have hp1 := Real.sqrt_nonneg (q n : ℝ)
    have hp2 := Real.sqrt_nonneg ((q n : ℝ) - 1)
    nlinarith
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hm0) (Real.sqrt_pos.mpr hq0)).mpr
  nlinarith

/-- Dividing the actual discrepancy by beta still decays at least as q^(-1/9). -/
theorem paperDiscrepancy_div_beta_le {n : ℕ} (hn : 2 ≤ n) :
    paperDiscrepancy n / paperBeta n ≤ 6 * paperDecay n := by
  have hq := q_real_three_le hn
  have hq0 : 0 < (q n : ℝ) := by linarith
  have hq1 : 1 ≤ (q n : ℝ) := by linarith
  calc
    _ ≤ (6 / Real.sqrt (q n : ℝ)) / paperBeta n :=
      div_le_div_of_nonneg_right (paperDiscrepancy_le_six_half_decay hn) (le_of_lt (paperBeta_pos hn))
    _ = 6 * ((q n : ℝ) ^ (-(1 / 2 : ℝ)) * (q n : ℝ) ^ (1 / 3 : ℝ)) := by
      unfold paperBeta
      rw [Real.sqrt_eq_rpow, Real.rpow_neg (le_of_lt hq0), div_inv_eq_mul, div_eq_mul_inv,
        ← Real.rpow_neg (le_of_lt hq0) (1 / 2 : ℝ)]
      ring
    _ = 6 * (q n : ℝ) ^ (-(1 / 6 : ℝ)) := by
      rw [← Real.rpow_add hq0]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num : -(1 / 6 : ℝ) ≤ -(1 / 9 : ℝ))) (by norm_num)

/-- The complete local comparison coefficient has an explicit absolute rate. -/
theorem paper_local_comparison_rate {n : ℕ} (hn : 2 ≤ n) :
    12 * (972 * paperBeta n ^ (1 / 3 : ℝ)) + 8 * paperDiscrepancy n / paperBeta n ≤
      12000 * paperDecay n := by
  rw [paperBeta_third hn]
  have hd := paperDiscrepancy_div_beta_le hn
  have hp := le_of_lt (paperDecay_pos hn)
  have he : 8 * paperDiscrepancy n / paperBeta n = 8 * (paperDiscrepancy n / paperBeta n) := by ring
  rw [he]
  nlinarith

end RefreshingProof.Local
