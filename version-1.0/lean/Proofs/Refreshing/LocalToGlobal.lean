import Proofs.Refreshing.WindowCosts
import Proofs.Refreshing.TranscriptComparison
import Proofs.Refreshing.Operational

/-!
# Actual local signed approximations imply continual security

The theorem below derives all adaptive hybrid and endpoint comparisons. Its only analytic error input is the actual per-query L₂ approximation bound.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RefreshingProof
open Refreshing

/-- At every adaptive history, use the proved local signed approximation for that round’s actual leakage query. -/
def actualSignedTables {n T leakage : ℕ} (A : Strategy n T leakage) (beta : ℝ) :
    SignedTables n T leakage :=
  fun i h z x y => actualSignedRound (A i h) z beta x y

/-- Complete local-to-global theorem, including T=0 and T=1. No full-transcript estimate or full hybrid-step estimate is a hypothesis. -/
theorem security_of_actual_approximation {n T leakage : ℕ}
    (hn : 2 ≤ n) (A : Strategy n T leakage) {beta ε : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3)
    (hε : 0 ≤ ε) (herror : ActualErrorBound n leakage beta ε) :
    statisticalDistance (transcriptDistribution hn A 0) (transcriptDistribution hn A 1) ≤
      (T : ℝ) * (K leakage : ℝ) ^ 3 *
        (12 * ε + 8 * ((3 / Real.sqrt ((2 : ℝ) ^ n - 2)) / beta)) := by
  let : Nonempty (Encoding n (0 : Bit)) := encoding_nonempty hn 0
  let : Nonempty (Encoding n (1 : Bit)) := encoding_nonempty hn 1
  cases T with
  | zero =>
      rw [security_zero_rounds hn leakage A]
      simp
  | succ t =>
      let G := actualSignedTables A beta
      let D : ℝ := 3 / Real.sqrt ((2 : ℝ) ^ n - 2)
      let δ : ℝ := 12 * ε + 8 * (D / beta)
      have hD : 0 ≤ D := by dsimp [D]; positivity
      have hDbeta : D ≤ D / beta := by
        apply (le_div_iff₀ hbeta).mpr
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hbeta1 hD
      have hδ : 0 ≤ δ := by dsimp [δ]; positivity
      have hendpoint : ε + 4 * D ≤ δ := by dsimp [δ]; nlinarith
      apply security_of_window_bounds hn A G δ hδ
      · intro z
        have h := actual_first_error_le hn (A ⟨0, by omega⟩ Fin.elim0) z
          hbeta hbeta1 hthreshold herror
        simpa only [G, actualSignedTables, firstKernelError, firstTrueKernel, firstSignedKernel,
          D, δ] using h.trans hendpoint
      · intro h z
        have hb := actual_last_error_le hn (A ⟨t, by omega⟩ h) z
          hbeta hbeta1 hthreshold herror
        simpa only [G, actualSignedTables, lastKernelError, lastSignedKernel, lastTrueKernel,
          D, δ] using hb.trans hendpoint
      · intro hT z₁ z₂
        have h := actual_two_round_error_le hn
          (A ⟨0, by omega⟩ Fin.elim0)
          (A ⟨1, by omega⟩ (appendAnswer Fin.elim0 z₁)) z₁ z₂
          hbeta hbeta1 hthreshold herror
        simpa only [G, actualSignedTables, initialWindowLeft, initialWindowRight, D, δ] using h
      · intro i hi c z
        have h := actual_two_round_error_le hn
          (A ⟨i + 1, by omega⟩ (appendAnswer c.2 z.1))
          (A ⟨i + 2, by omega⟩ (appendAnswer (appendAnswer c.2 z.1) z.2.1)) z.2.1 z.2.2
          hbeta hbeta1 hthreshold herror
        simpa only [G, actualSignedTables, twoRoundWindowError, windowLeftSigned, windowRightSigned,
          D, δ] using h

/-- After the actual residual four-cycle transfer is proved, no security or hybrid assumptions remain: the concrete signed approximation gives the rate. -/
theorem security_of_residual_transfer {n T leakage : ℕ}
    (hn : 2 ≤ n) (A : Strategy n T leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3)
    (htransfer : ∀ (f : LeakageQuery n leakage) (z : Answer leakage),
      Local.average (fun M : RefreshMatrix n => Local.fourCycle (Local.actualResidualPullback f z beta M)) ≤
        1512 * beta ^ 2 * Local.normSq (Local.actualResidual f z beta)) :
    statisticalDistance (transcriptDistribution hn A 0) (transcriptDistribution hn A 1) ≤
      (T : ℝ) * (K leakage : ℝ) ^ 3 *
        (12 * (972 * beta ^ (1 / 3 : ℝ)) + 8 * ((3 / Real.sqrt ((2 : ℝ) ^ n - 2)) / beta)) := by
  apply security_of_actual_approximation hn A hbeta hbeta1 hthreshold (by positivity)
  intro f z s
  exact Local.conditional_local_error_le hn f z hbeta hbeta1 hthreshold (htransfer f z) s

end RefreshingProof
