import Proofs.Refreshing.Residual
import Proofs.Refreshing.LocalBootstrap

/-!
# From an actual four-cycle transfer estimate to the local residual error

The transfer estimate is an explicit premise on the actual residual and actual uniform refreshing experiment. The resulting bound has a concrete universal constant and does not assume any local approximation or security theorem.
-/

noncomputable section
open scoped BigOperators Matrix

namespace RefreshingProof.Local
open Refreshing

/-- The actual residual restricted along one actual matrix refresh. -/
def actualResidualPullback {n leakage : ℕ} (f : LeakageQuery n leakage) (z : Answer leakage)
    (beta : ℝ) (M : RefreshMatrix n) : Table (Share n) (Share n) :=
  fun l r => actualResidual f z beta (l, refreshLeft l M) (r, refreshRight r M)

/-- Correlation of the actual refreshed residual with its actual two leakage masks. -/
def residualMaskCorrelation {n leakage : ℕ} (f : LeakageQuery n leakage) (z : Answer leakage)
    (beta : ℝ) (M : RefreshMatrix n) : ℝ :=
  average (fun l => leftAnswerMask f z l M *
    average (fun r => actualResidualPullback f z beta M l r * rightAnswerMask f z r M))

/-- The same correlation with the three factors grouped as in the operational identity. -/
theorem residualMaskCorrelation_reordered {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) (M : RefreshMatrix n) :
    average (fun l => average (fun r => leftAnswerMask f z l M * rightAnswerMask f z r M *
      actualResidualPullback f z beta M l r)) = residualMaskCorrelation f z beta M := by
  unfold residualMaskCorrelation
  apply average_congr
  intro l
  rw [← average_smul]
  apply average_congr
  intro r
  ring

/-- The actual mask correlation has fourth power at most its complete four-cycle average. -/
theorem residualMaskCorrelation_fourth_le {n leakage : ℕ} [Nonempty (Share n)]
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) (M : RefreshMatrix n) :
    residualMaskCorrelation f z beta M ^ 4 ≤ fourCycle (actualResidualPullback f z beta M) := by
  have h := fourCycle_test_fourth (actualResidualPullback f z beta M)
    (fun l => leftAnswerMask f z l M) (fun r => rightAnswerMask f z r M)
  have hL := leftAnswerMask_average_sq_le_one f z M
  have hR := rightAnswerMask_average_sq_le_one f z M
  have hL0 : 0 ≤ average (fun l => leftAnswerMask f z l M ^ 2) := average_nonneg fun _ => sq_nonneg _
  have hR0 : 0 ≤ average (fun r => rightAnswerMask f z r M ^ 2) := average_nonneg fun _ => sq_nonneg _
  have hL2 := (sq_le_sq₀ hL0 (by norm_num : (0 : ℝ) ≤ 1)).mpr hL
  have hR2 := (sq_le_sq₀ hR0 (by norm_num : (0 : ℝ) ≤ 1)).mpr hR
  have hp := mul_le_mul hL2 hR2 (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 ^ 2)
  norm_num only [one_pow, mul_one] at hp
  have hh := mul_le_mul_of_nonneg_right hp (fourCycle_nonneg (actualResidualPullback f z beta M))
  exact h.trans (by simpa only [one_mul] using hh)

/-- Jensen's fourth-power inequality derived from two finite Cauchy--Schwarz applications. -/
theorem average_fourth_power_le {M : Type*} [Fintype M] [Nonempty M] (a : M → ℝ) :
    average a ^ 4 ≤ average (fun m => a m ^ 4) := by
  have h1 := average_cauchy_schwarz a (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, RefreshingProof.average_const] at h1
  have h2 := average_cauchy_schwarz (fun m => a m ^ 2) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, RefreshingProof.average_const] at h2
  have h1sq := (sq_le_sq₀ (sq_nonneg (average a)) (average_nonneg fun m => sq_nonneg (a m))).mpr h1
  calc
    _ = (average a ^ 2) ^ 2 := by ring
    _ ≤ (average (fun m => a m ^ 2)) ^ 2 := h1sq
    _ ≤ _ := by simpa only [← pow_mul] using h2

/-- A transfer bound with the paper's constants controls the actual averaged mask correlation. The coarse fourth-root coefficient seven is universal. -/
theorem residualMaskCorrelation_average_abs_le {n leakage : ℕ} [Nonempty (Share n)]
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta t : ℝ}
    (hbeta : 0 ≤ beta) (ht : 0 ≤ t) (hnorm : normSq (actualResidual f z beta) = t ^ 2)
    (htransfer : average (fun M : RefreshMatrix n => fourCycle (actualResidualPullback f z beta M)) ≤
      1512 * beta ^ 2 * normSq (actualResidual f z beta)) :
    |average (residualMaskCorrelation f z beta)| ≤ 7 * Real.sqrt beta * Real.sqrt t := by
  have h4 := (average_fourth_power_le (residualMaskCorrelation f z beta)).trans
    ((average_mono (residualMaskCorrelation_fourth_le f z beta)).trans htransfer)
  rw [hnorm] at h4
  have hsqrt (a : ℝ) (ha : 0 ≤ a) : Real.sqrt a ^ 4 = a ^ 2 := by
    rw [show 4 = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt ha]
  have hpow : (7 * Real.sqrt beta * Real.sqrt t) ^ 4 = 2401 * beta ^ 2 * t ^ 2 := by
    rw [mul_pow, mul_pow, hsqrt beta hbeta, hsqrt t ht]
    norm_num
  apply le_of_pow_le_pow_left₀ (by norm_num : 4 ≠ 0) (by positivity)
  calc
    _ = average (residualMaskCorrelation f z beta) ^ 4 := by
      simp only [show 4 = 2 * 2 by norm_num, pow_mul, sq_abs]
    _ ≤ 1512 * beta ^ 2 * t ^ 2 := h4
    _ ≤ 2401 * beta ^ 2 * t ^ 2 := by nlinarith [mul_nonneg (sq_nonneg beta) (sq_nonneg t)]
    _ = _ := hpow.symm

/-- Concrete local residual bound, conditional only on an explicit transfer estimate for this actual residual under actual uniform refreshing. -/
theorem actualResidual_norm_le_of_fourCycle_transfer {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3)
    (htransfer : average (fun M : RefreshMatrix n => fourCycle (actualResidualPullback f z beta M)) ≤
      1512 * beta ^ 2 * normSq (actualResidual f z beta)) :
    Real.sqrt (normSq (actualResidual f z beta)) ≤ 324 * beta ^ (1 / 3 : ℝ) := by
  let : Nonempty (Share n) := share_nonempty_of_two_le hn
  let t := Real.sqrt (normSq (actualResidual f z beta))
  let P := spectralTruncation (groupedAnswerTable f z) beta
  let cross := pairing P (fun x y => refreshConsistencySign x y * P x y)
  have hn0 : 0 ≤ normSq (actualResidual f z beta) :=
    average_nonneg fun x => average_nonneg fun y => mul_self_nonneg _
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hnorm : normSq (actualResidual f z beta) = t ^ 2 := (Real.sq_sqrt hn0).symm
  have hm := residualMaskCorrelation_average_abs_le f z (le_of_lt hbeta) ht hnorm htransfer
  have hmask : average (fun l => average (fun r => average (fun M : RefreshMatrix n =>
      leftAnswerMask f z l M * rightAnswerMask f z r M *
        actualResidual f z beta (l, refreshLeft l M) (r, refreshRight r M)))) ≤
      7 * Real.sqrt beta * Real.sqrt t := by
    calc
      _ = average (residualMaskCorrelation f z beta) := by
        rw [average_third_first]
        apply average_congr
        intro M
        exact residualMaskCorrelation_reordered f z beta M
      _ ≤ |average (residualMaskCorrelation f z beta)| := le_abs_self _
      _ ≤ _ := hm
  have hw := groupedAnswerTable_weight_replacement hn f z (actualResidual f z beta)
    (by positivity : 0 ≤ 3 / beta) (actualResidual_entry_abs_le hn f z hbeta hbeta1)
  have hc : cross ≤ 2 / ((q n : ℝ) * beta) :=
    (le_abs_self cross).trans (actualTruncation_sign_cross_abs_le hn f z hbeta hbeta1 hthreshold)
  have hid := actualResidual_identity f z beta
  rw [hnorm] at hid
  have hq : 0 < (q n : ℝ) := by have := q_real_three_le hn; linarith
  have he : (3 / beta) / (q n : ℝ) = 3 * (1 / ((q n : ℝ) * beta)) := by
    field_simp
  rw [he] at hw
  have hrecip : 1 / ((q n : ℝ) * beta) ≤ beta ^ 2 := by
    apply (div_le_iff₀ (mul_pos hq hbeta)).mpr
    nlinarith
  simp only [div_eq_mul_inv, one_mul] at hw hc hrecip
  have hroot : 0 ≤ Real.sqrt beta * Real.sqrt t := by positivity
  have hmain : t ^ 2 ≤ 7 * Real.sqrt beta * Real.sqrt t + 10 * beta ^ 2 := by
    change t ^ 2 = pairing (groupedAnswerTable f z) (actualResidual f z beta) + 4 * cross at hid
    nlinarith [sq_nonneg beta]
  have h := residual_bootstrap hbeta hbeta1 ht (by norm_num : (0 : ℝ) ≤ 7)
    (by norm_num : (0 : ℝ) ≤ 10) hmain
  norm_num only [residualBootstrapConstant, show (7 + 10 + 1 : ℝ) ^ 2 = 324 by norm_num] at h
  exact h

end RefreshingProof.Local
