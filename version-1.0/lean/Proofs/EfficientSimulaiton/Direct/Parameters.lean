import Proofs.Compiler.Direct.Parameters

/-!
# Logarithmic share length for the direct compiler

Following the parameter calculation after the compiler theorem, absorb the prefactor 2·10⁶ S into the binary exponent 18λ−n/27. The deliberately conservative coefficient 12000 is retained in the public statement, but the proof uses only the current paper's direct bound.
-/

set_option autoImplicit false
noncomputable section
namespace EfficientSimulationProof.Direct
open Compiler

/-- The elementary integral estimate gives log 2 ≥ 1/2, so converting a natural logarithm to a binary logarithm costs at most a factor two. -/
private theorem half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  exact h

/-- The absolute logarithmic condition implies the explicit sufficient threshold n ≥ 27(κ + 18λ + log₂(2000000T)). The fixed prefactor is absorbed using 2000000 ≤ 2³⁵ and κ ≥ 1. -/
theorem explicit_share_length {n T leakage : ℕ} {κ : ℝ} (hκ : 1 ≤ κ)
    (hT : 1 ≤ T)
    (hsize : 12000 * (κ + (leakage : ℝ) + Real.log ((T : ℝ) + 2)) ≤ n) :
    27 * (κ + 18 * (leakage : ℝ) +
      Real.log (2000000 * (T : ℝ)) / Real.log 2) ≤ n := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log ((T : ℝ) + 2) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) T; linarith)
  have hconstant : Real.log (2000000 : ℝ) ≤ 21 * Real.log 2 := by
    calc
      Real.log (2000000 : ℝ) ≤ Real.log ((2 : ℝ) ^ (21 : ℕ)) :=
        Real.log_le_log (by norm_num) (by norm_num)
      _ = 21 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hTlog : Real.log (T : ℝ) ≤ Real.log ((T : ℝ) + 2) :=
    Real.log_le_log hTpos (by linarith)
  have hprefactor : Real.log (2000000 * (T : ℝ)) ≤
      21 * Real.log 2 + Real.log ((T : ℝ) + 2) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hTpos)]
    linarith
  have hlogquotient : Real.log ((T : ℝ) + 2) / Real.log 2 ≤
      2 * Real.log ((T : ℝ) + 2) := by
    apply (div_le_iff₀ hlogtwo).2
    nlinarith [mul_nonneg hlog (sub_nonneg.mpr half_le_log_two)]
  have hprefactorquotient : Real.log (2000000 * (T : ℝ)) / Real.log 2 ≤
      21 + 2 * Real.log ((T : ℝ) + 2) := by
    calc
      _ ≤ (21 * Real.log 2 + Real.log ((T : ℝ) + 2)) / Real.log 2 :=
        div_le_div_of_nonneg_right hprefactor hlogtwo.le
      _ = 21 + Real.log ((T : ℝ) + 2) / Real.log 2 := by
        field_simp
      _ ≤ 21 + 2 * Real.log ((T : ℝ) + 2) := by linarith
  have hleak : (0 : ℝ) ≤ leakage := Nat.cast_nonneg _
  linarith

/-- The explicit coefficient-27 threshold makes the finite theorem's exponential bound at most 2^(−κ). -/
theorem secondBound_le_of_explicit {n T leakage : ℕ} {κ : ℝ} (hT : 1 ≤ T)
    (hsize : 27 * (κ + 18 * (leakage : ℝ) +
      Real.log (2000000 * (T : ℝ)) / Real.log 2) ≤ n) :
    2000000*(T:ℝ)*(2:ℝ)^(18*(leakage:ℝ)-(n:ℝ)/27) ≤ (2 : ℝ) ^ (-κ) := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexponent : Real.log (2000000 * (T : ℝ)) +
      Real.log 2 * (18 * (leakage : ℝ) - (n : ℝ) / 27) ≤ Real.log 2 * (-κ) := by
    have h := mul_le_mul_of_nonneg_right hsize hlogtwo.le
    have hcancel : (Real.log (2000000 * (T : ℝ)) / Real.log 2) * Real.log 2 =
        Real.log (2000000 * (T : ℝ)) := div_mul_cancel₀ _ (ne_of_gt hlogtwo)
    nlinarith
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ = Real.exp (Real.log (2000000 * (T : ℝ)) +
        Real.log 2 * (18 * (leakage : ℝ) - (n : ℝ) / 27)) := by
      rw [Real.exp_add, Real.exp_log (by positivity : (0 : ℝ) < 2000000 * (T : ℝ))]
    _ ≤ Real.exp (Real.log 2 * (-κ)) := Real.exp_le_exp.mpr hexponent

/-- The uniform sufficient condition n ≥ 12000(κ + λ + log(T+2)) gives B₂(2000000,n,T,λ) ≤ 2^(−κ) whenever κ ≥ 1 and T ≥ 1. -/
theorem secondBound_le {n T leakage : ℕ} {κ : ℝ} (hκ : 1 ≤ κ) (hT : 1 ≤ T)
    (hsize : 12000 * (κ + (leakage : ℝ) + Real.log ((T : ℝ) + 2)) ≤ n) :
    2000000*(T:ℝ)*(2:ℝ)^(18*(leakage:ℝ)-(n:ℝ)/27) ≤ (2 : ℝ) ^ (-κ) :=
  secondBound_le_of_explicit hT (explicit_share_length hκ hT hsize)

/-- The direct error is at most 2⁻κ when n ≥ 12000(κ+λ+ln(S+2)), including the empty execution S = 0. This uses the paper's binary rate with exponent 18λ−n/27. -/
theorem direct_bound_le {n S leakage : ℕ} {κ : ℝ} (hn : 2 ≤ n) (hκ : 1 ≤ κ)
    (hsize : 12000*(κ+(leakage:ℝ)+Real.log ((S:ℝ)+2)) ≤ n) :
    1000000*(S:ℝ)*(K leakage:ℝ)^9*(q n:ℝ)^(-1/27:ℝ) ≤ (2:ℝ)^(-κ) := by
  by_cases hS : S = 0
  · subst S
    simp only [Nat.cast_zero, mul_zero, zero_mul]
    exact Real.rpow_nonneg (by norm_num) _
  · exact (CompilerProof.Direct.direct_bound_binary hn).trans
      (secondBound_le hκ (by omega) hsize)

end EfficientSimulationProof.Direct
