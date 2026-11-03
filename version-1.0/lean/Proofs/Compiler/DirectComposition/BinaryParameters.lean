import Proofs.Compiler.DirectComposition.Parameters
import Proofs.Compiler.Simulation.ShareGeometry

/-!
# Instantiating the parameters for binary shares

The share count is the number q = 2ⁿ−1 of nonzero n-bit vectors. The established inner-product discrepancy is bounded at the required q⁻¹ᐟ² scale. The approximation threshold also satisfies both the refresh and multiplication truncation conditions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.DirectComposition

open Refresh MatrixRefresh CircuitCompiler CircuitCompiler.SimulationParameters

/-- The usual square-root discrepancy estimate is at most eight times q⁻¹ᐟ² for q≥3. -/
theorem inverse_sqrt_sub_one_le {q : ℝ} (hq : 3≤q) :
    4/Real.sqrt (q-1)≤8*q^(-1/2:ℝ) := by
  have hq0 : 0<q := by linarith
  have hm0 : 0<q-1 := by linarith
  have hs : Real.sqrt q≤2*Real.sqrt (q-1) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt hq0.le,mul_pow,Real.sq_sqrt hm0.le]
    nlinarith
  rw [show (-1/2:ℝ)=-(1/2) by ring,Real.rpow_neg hq0.le,← Real.sqrt_eq_rpow]
  change 4/Real.sqrt (q-1)≤8/Real.sqrt q
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hm0) (Real.sqrt_pos.mpr hq0)).mpr
  nlinarith

/-- The actual binary encoding discrepancy meets the local tensor parameter bound at the nonzero-share count. -/
theorem binary_discrepancy_le {n : ℕ} (hn : 2≤n) :
    zeta Compiler.Bit n≤8*(Fintype.card (U Compiler.Bit n):ℝ)^(-1/2:ℝ) := by
  have hb : fieldCard Compiler.Bit=2 := by simp [fieldCard,Compiler.Bit]
  have hq := share_card_ge_three (F:=Compiler.Bit) hb hn
  exact (zeta_le_four_share_card hb hn).trans (inverse_sqrt_sub_one_le hq)

/-- The direct threshold satisfies the refresh truncation condition exactly. -/
theorem direct_refresh_admissible {q : ℝ} (hq : 1≤q) :
    1≤q*(betaParameter q)^3 := by
  have hq0 : 0<q := by linarith
  unfold betaParameter
  rw [← Real.rpow_natCast _ 3,← Real.rpow_mul hq0.le]
  norm_num
  rw [Real.rpow_neg_one]
  simp [hq0.ne']

/-- The multiplication truncation condition follows from refresh admissibility because q≥1. -/
theorem direct_compute_admissible {q : ℝ} (hq : 1≤q) :
    1≤q^2*(betaParameter q)^3 := by
  have h0 : 0≤(betaParameter q)^3 := by
    have hp := (betaParameter_bounds hq).1
    exact pow_nonneg hp.le _
  exact (direct_refresh_admissible hq).trans
    (mul_le_mul_of_nonneg_right (by nlinarith) h0)

/-- Taking a cube root of the direct threshold has exactly the raw-error exponent. -/
theorem betaParameter_cuberoot {q : ℝ} (hq : 1≤q) :
    (betaParameter q)^(1/3:ℝ)=q^(-1/9:ℝ) := by
  unfold betaParameter
  rw [← Real.rpow_mul (by linarith : 0≤q)]
  norm_num

/-- Any retry allowance at most twice the raw scale is absorbed by the deliberately generous local coefficient. -/
theorem raw_error_dominates {q τ : ℝ} (hq : 1≤q) (hτ : τ≤2*q^(-1/9:ℝ)) :
    396*(betaParameter q)^(1/3:ℝ)+τ≤rawErrorParameter q := by
  rw [betaParameter_cuberoot hq]
  unfold rawErrorParameter
  have h0 : 0≤q^(-1/9:ℝ) := Real.rpow_nonneg (by linarith) _
  linarith

/-- The actual rectangular retry allowance is smaller than twice the raw q⁻¹ᐟ⁹ approximation scale. -/
theorem binary_retry_le {n : ℕ} (hn : 2≤n) :
    2/(2:ℝ)^n≤2*(Fintype.card (U Compiler.Bit n):ℝ)^(-1/9:ℝ) := by
  have hb : fieldCard Compiler.Bit=2 := by simp [fieldCard,Compiler.Bit]
  have hq := share_card_ge_three (F:=Compiler.Bit) hb hn
  have hc := share_card_binary (F:=Compiler.Bit) (n:=n) hb
  have hq0 : 0<(Fintype.card (U Compiler.Bit n):ℝ) := by linarith
  calc
    _ ≤ 2/(Fintype.card (U Compiler.Bit n):ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hq0 (by linarith)
    _ = 2*(Fintype.card (U Compiler.Bit n):ℝ)^(-1:ℝ) := by
      rw [Real.rpow_neg_one];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)) (by norm_num)

end CompilerProof.DirectComposition
