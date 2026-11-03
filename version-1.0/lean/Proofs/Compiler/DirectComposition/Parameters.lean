import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.DirectComposition.Activities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-!
# Numerical parameters of the direct compiler

The local approximation uses β=q^(−1/3), separate energy trimming uses B=q^(1/9), and the third-moment error is at most 1000q^(−1/27). These elementary estimates also combine the operation and wire activities into one bound. The constants are deliberately loose so their numerical verification stays separate from the structural argument.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CompilerProof.DirectComposition
/-- Threshold for each party's factor energy. -/
def trimParameter (q : ℝ) : ℝ := q ^ (1/9 : ℝ)
/-- The cubic-error scale used by incidence-three Hölder. -/
def cubicErrorParameter (q : ℝ) : ℝ := 1000*q ^ (-1/27 : ℝ)
/-- The common decay scale in the final statistical-distance bound. -/
def decayParameter (q : ℝ) : ℝ := q ^ (-1/27 : ℝ)
/-- The approximation parameter lies in its required interval whenever q≥1. -/
theorem betaParameter_bounds {q : ℝ} (hq : 1≤q) :
    0<betaParameter q ∧ betaParameter q≤1 := by
  constructor
  · exact Real.rpow_pos_of_pos (by linarith) _
  · exact Real.rpow_le_one_of_one_le_of_nonpos hq (by norm_num)
/-- The trimming threshold is at least one. -/
theorem trimParameter_one_le {q : ℝ} (hq : 1≤q) : 1≤trimParameter q := by
  exact Real.one_le_rpow hq (by norm_num)
/-- Cubing the third-moment scale gives the same q^(−1/9) decay as the balanced trimming estimate. -/
theorem cubicErrorParameter_cube {q : ℝ} (hq : 0≤q) :
    (cubicErrorParameter q)^3=1000000000*q ^ (-1/9 : ℝ) := by
  have hpow : (q ^ (-1/27 : ℝ))^3=q ^ (-1/9 : ℝ) := by
    rw [← Real.rpow_mul_natCast hq]
    norm_num
  simp only [cubicErrorParameter,mul_pow,hpow]
  norm_num
/-- The original squared error and the two discarded energy tails fit within the chosen third moment. -/
theorem trimmed_error_parameter {q : ℝ} (hq : 1≤q) :
    (1+trimParameter q)*(rawErrorParameter q)^2+16/trimParameter q≤
      (cubicErrorParameter q)^3 := by
  have hq0 : 0<q := by linarith
  let r : ℝ := q ^ (-1/9 : ℝ)
  have hr0 : 0≤r := Real.rpow_nonneg hq0.le _
  have hr1 : r≤1 := Real.rpow_le_one_of_one_le_of_nonpos hq (by norm_num)
  have hB0 : 0<trimParameter q := Real.rpow_pos_of_pos hq0 _
  have hBr : trimParameter q*r=1 := by
    dsimp [trimParameter,r]
    rw [← Real.rpow_add hq0]
    norm_num
  have hdiv : 16/trimParameter q=16*r := by
    apply (div_eq_iff hB0.ne').mpr
    nlinarith [hBr]
  have hraw : rawErrorParameter q=10000*r := rfl
  rw [cubicErrorParameter_cube hq0.le,hraw,hdiv]
  change (1+trimParameter q)*(10000*r)^2+16*r≤1000000000*r
  calc
    _ = 100000000*r^2+100000000*(trimParameter q*r)*r+16*r := by ring
    _ ≤ 100000000*r+100000000*r+16*r := by
      rw [hBr]
      nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]
    _ ≤ _ := by nlinarith
/-- Three guarded appearances of a changed wire still leave enough decay in its one-wire discrepancy. -/
theorem scaled_wire_discrepancy_le {q δ : ℝ} (hq : 1≤q)
    (hδ : δ≤8*q ^ (-1/2 : ℝ)) :
    (trimParameter q)^3*δ≤8*decayParameter q := by
  have hq0 : 0<q := by linarith
  have hB0 : 0≤trimParameter q := (Real.rpow_pos_of_pos hq0 _).le
  have hpow : (trimParameter q)^3=q ^ (1/3 : ℝ) := by
    unfold trimParameter
    rw [← Real.rpow_mul_natCast hq0.le]
    norm_num
  calc
    _ ≤ (trimParameter q)^3*(8*q ^ (-1/2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hδ (pow_nonneg hB0 _)
    _ = 8*q ^ (-1/6 : ℝ) := by
      rw [hpow]
      calc
        _ = 8*(q ^ (1/3 : ℝ)*q ^ (-1/2 : ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add hq0]; norm_num
    _ ≤ 8*decayParameter q := by
      unfold decayParameter
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq (by norm_num)) (by norm_num)
/-- With at most S approximated operations and 3S encoded wires, the two families of activities have the claimed common K⁹q^(−1/27) scale. -/
theorem direct_activity_bound {q K δ a w S : ℝ} (hq : 1≤q) (hK : 1≤K)
    (hS : 0≤S) (hw0 : 0≤w) (ha : a≤S) (hw : w≤3*S)
    (hδ : δ≤8*q ^ (-1/2 : ℝ)) :
    2*(a*K^9*cubicErrorParameter q+w*K^3*(trimParameter q)^3*δ)≤
      1000000*S*K^9*decayParameter q := by
  have hK0 : 0≤K := by linarith
  have ht0 : 0≤decayParameter q := Real.rpow_nonneg (by linarith) _
  have hK39 : K^3≤K^9 := pow_le_pow_right₀ hK (by decide)
  have hfirst : a*K^9*cubicErrorParameter q≤
      S*K^9*(1000*decayParameter q) := by
    change a*K^9*(1000*decayParameter q)≤S*K^9*(1000*decayParameter q)
    gcongr
  have hsecond : w*K^3*(trimParameter q)^3*δ≤
      3*S*K^9*(8*decayParameter q) := by
    calc
      _ = w*K^3*((trimParameter q)^3*δ) := by ring
      _ ≤ w*K^3*(8*decayParameter q) := mul_le_mul_of_nonneg_left
        (scaled_wire_discrepancy_le hq hδ) (mul_nonneg hw0 (pow_nonneg hK0 _))
      _ ≤ _ := by gcongr
  calc
    _ ≤ 2*(S*K^9*(1000*decayParameter q)+3*S*K^9*(8*decayParameter q)) := by
      linarith
    _ = 2048*S*K^9*decayParameter q := by ring
    _ ≤ _ := by
      have hprod : 0≤S*K^9*decayParameter q :=
        mul_nonneg (mul_nonneg hS (pow_nonneg hK0 _)) ht0
      nlinarith
/-- Natural operation and wire counts instantiate the numerical activity bound without additional sign hypotheses. -/
theorem direct_activity_bound_nat {q K δ : ℝ} {a w S : ℕ}
    (hq : 1≤q) (hK : 1≤K) (ha : a≤S) (hw : w≤3*S)
    (hδ : δ≤8*q ^ (-1/2 : ℝ)) :
    2*((a:ℝ)*K^9*cubicErrorParameter q+(w:ℝ)*K^3*(trimParameter q)^3*δ)≤
      1000000*(S:ℝ)*K^9*decayParameter q := by
  apply direct_activity_bound hq hK (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact_mod_cast ha
  · exact_mod_cast hw
  · exact hδ
end CompilerProof.DirectComposition
