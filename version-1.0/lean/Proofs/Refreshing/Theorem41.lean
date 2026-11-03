import Proofs.Refreshing.LocalToGlobal
import Proofs.Refreshing.FourCycleTransfer
import Proofs.Refreshing.PaperParameters

/-!
# Theorem 4.1: Security of continual refreshing

The local approximation and adaptive comparison give C = 12000. The numerical rate conversion gives C' = 24000.
-/

noncomputable section
namespace RefreshingProof
open Refreshing

/-- The number of nonzero shares is at least half the full vector space. -/
theorem half_space_le_q {n : ℕ} (hn : 2 ≤ n) : 2 ^ (n - 1) ≤ q n := by
  have hp : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by omega)
  have he : n = (n - 1) + 1 := by omega
  unfold q
  conv_rhs => rw [he, pow_succ]
  omega

/-- Replace q^(-1/9) by 2 · 2^(-n/9). The factor 2 is an absolute constant. -/
theorem q_decay_bound {n : ℕ} (hn : 2 ≤ n) :
    (q n : ℝ) ^ (-(1 / 9 : ℝ)) ≤
      2 * (2 : ℝ) ^ (-(n : ℝ) / 9) := by
  have hbase : (0 : ℝ) < 2 ^ (n - 1) := by positivity
  have hq : (2 : ℝ) ^ (n - 1) ≤ (q n : ℝ) := by
    exact_mod_cast half_space_le_q hn
  have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  calc
    (q n : ℝ) ^ (-(1 / 9 : ℝ)) ≤
        ((2 : ℝ) ^ (n - 1)) ^ (-(1 / 9 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hbase hq (by norm_num)
    _ = (2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) * (-(1 / 9 : ℝ))) := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ (1 + (-(n : ℝ) / 9)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      rw [hc]
      linarith
    _ = 2 * (2 : ℝ) ^ (-(n : ℝ) / 9) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]

/-- Cubing the number K of answer pairs accounts for the exponent 6λ. -/
theorem answer_count_cube (leakage : ℕ) :
    (K leakage : ℝ) ^ 3 = (2 : ℝ) ^ (6 * (leakage : ℝ)) := by
  rw [K, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
  rw [show 2 * leakage * 3 = 6 * leakage by omega]
  norm_cast

/-- The second inequality of Theorem 4.1, with C' = 2C. -/
theorem rate_conversion {n T leakage : ℕ} (hn : 2 ≤ n) {C : ℝ} (hC : 0 ≤ C) :
    C * (T : ℝ) * (K leakage : ℝ) ^ 3 *
        (q n : ℝ) ^ (-(1 / 9 : ℝ)) ≤
      (2 * C) * (T : ℝ) *
        (2 : ℝ) ^ (6 * (leakage : ℝ) - (n : ℝ) / 9) := by
  calc
    C * (T : ℝ) * (K leakage : ℝ) ^ 3 *
        (q n : ℝ) ^ (-(1 / 9 : ℝ)) ≤
      C * (T : ℝ) * (K leakage : ℝ) ^ 3 *
        (2 * (2 : ℝ) ^ (-(n : ℝ) / 9)) := by
      exact mul_le_mul_of_nonneg_left (q_decay_bound hn) (by positivity)
    _ = (2 * C) * (T : ℝ) *
        (2 : ℝ) ^ (6 * (leakage : ℝ) - (n : ℝ) / 9) := by
      rw [answer_count_cube, sub_eq_add_neg,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [neg_div]
      ring

/-- The numerical clause in the exact specification's notation. -/
theorem rate_conversion_bounds {n T leakage : ℕ} (hn : 2 ≤ n)
    {C : ℝ} (hC : 0 ≤ C) :
    firstBound C n T leakage ≤ secondBound (2 * C) n T leakage := by
  simpa only [firstBound, secondBound, Nat.cast_ofNat, Real.rpow_eq_pow] using rate_conversion hn hC

/-- The actual secret-zero and secret-one transcript distributions satisfy the first Theorem 4.1 bound with C = 12000. -/
theorem security_bound {n T leakage : ℕ}
    (hn : 2 ≤ n) (A : Strategy n T leakage) :
    statisticalDistance (transcriptDistribution hn A 0)
      (transcriptDistribution hn A 1) ≤ firstBound 12000 n T leakage := by
  have hb := Local.paperBeta_pos hn
  have hb1 := Local.paperBeta_le_one hn
  have hthreshold : 1 ≤ (q n : ℝ) * Local.paperBeta n ^ 3 :=
    le_of_eq (Local.paperBeta_threshold hn).symm
  have h := security_of_residual_transfer hn A hb hb1 hthreshold
    (fun f z => Local.actualResidual_fourCycle_transfer hn f z hb hb1 hthreshold)
  have hlocal := Local.paper_local_comparison_rate hn
  rw [Local.paperDiscrepancy_eq] at hlocal
  have hcoef : 0 ≤ (T : ℝ) * (K leakage : ℝ) ^ 3 := by positivity
  calc
    _ ≤ (T : ℝ) * (K leakage : ℝ) ^ 3 *
        (12 * (972 * Local.paperBeta n ^ (1 / 3 : ℝ)) +
          8 * ((3 / Real.sqrt ((2 : ℝ) ^ n - 2)) / Local.paperBeta n)) := h
    _ ≤ (T : ℝ) * (K leakage : ℝ) ^ 3 * (12000 * Local.paperDecay n) := by
      apply mul_le_mul_of_nonneg_left _ hcoef
      simpa only [mul_div_assoc] using hlocal
    _ = firstBound 12000 n T leakage := by
      unfold firstBound Local.paperDecay
      rw [Real.rpow_eq_pow]
      ring

end RefreshingProof

namespace Refreshing

/-- Theorem 4.1: both rate bounds, uniformly over all adaptive strategies. -/
theorem theorem_4_1 :
    ∃ C C' : ℝ, 1 ≤ C ∧ 1 ≤ C' ∧
      ∀ (n T leakage : ℕ) (hn : 2 ≤ n),
        firstBound C n T leakage ≤ secondBound C' n T leakage ∧
        (∀ A : Strategy n T leakage,
          statisticalDistance (transcriptDistribution hn A 0)
            (transcriptDistribution hn A 1) ≤ firstBound C n T leakage) := by
  refine ⟨12000, 24000, by norm_num, by norm_num, ?_⟩
  intro n T leakage hn
  constructor
  · simpa only [show 2 * (12000 : ℝ) = 24000 by norm_num] using
      (RefreshingProof.rate_conversion_bounds (T := T) (leakage := leakage)
        hn (C := 12000) (by norm_num))
  · exact fun A => RefreshingProof.security_bound hn A

end Refreshing
