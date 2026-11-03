import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic



/-!
# Parameter arithmetic for the joint-port approximation

Use a tenth-root parameter `t`: `N=t^10`, `R=t`, `L=t^3`, and `β=1/t^2`. Every error term in the dual estimate is bounded explicitly.
-/

set_option autoImplicit false

namespace CircuitCompiler

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For t, a, b ∈ ℝ, assume 0 < t; 0 < b; a · t ≤ b. Then

a / b ≤ 1 / t.
-/
private theorem ratio_le_inverse (t a b : ℝ) (ht : 0 < t) (hb : 0 < b)
    (h : a * t ≤ b) : a / b ≤ 1 / t := by
  apply (div_le_div_iff₀ hb ht).2
  simpa using h

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For t, N, Q ∈ ℝ, assume 1 ≤ t; N = t¹⁰; N² ≤ Q. Then

Let R := t; Let L := t³; Let β := 1 / t²; 1 / R ≤ 1 / t ∧ 1 / L ≤ 1 / t ∧ R² / L ≤ 1 / t ∧ β ≤ 1 / t ∧ R² / (β · √Q) ≤ 1 / t ∧ √R / (β · √N) ≤ 1 / t ∧ R / (β · N) ≤ 1 / t ∧ √β ≤ 1 / t ∧ (L + R² / β) / √N ≤ 2 / t ∧ 1 / Q ≤ 1 / t.
-/
theorem joint_parameter_terms (t N Q : ℝ) (ht : 1 ≤ t)
    (hN : N = t ^ 10) (hQ : N ^ 2 ≤ Q) :
    let R := t
    let L := t ^ 3
    let β := 1 / t ^ 2
    1 / R ≤ 1 / t ∧
    1 / L ≤ 1 / t ∧
    R ^ 2 / L ≤ 1 / t ∧
    β ≤ 1 / t ∧
    R ^ 2 / (β * Real.sqrt Q) ≤ 1 / t ∧
    Real.sqrt R / (β * Real.sqrt N) ≤ 1 / t ∧
    R / (β * N) ≤ 1 / t ∧
    Real.sqrt β ≤ 1 / t ∧
    (L + R ^ 2 / β) / Real.sqrt N ≤ 2 / t ∧
    1 / Q ≤ 1 / t := by
  dsimp only
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have htne : t ≠ 0 := ht0.ne'
  have htp (a b : ℕ) (hab : a ≤ b) : t ^ a ≤ t ^ b := pow_le_pow_right₀ ht hab
  have hN0 : 0 < N := by rw [hN]; positivity
  have hQ0 : 0 < Q := lt_of_lt_of_le (sq_pos_of_pos hN0) hQ
  have hrootN : Real.sqrt N = t ^ 5 := by
    rw [hN, show t ^ 10 = (t ^ 5) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hrootQ : t ^ 10 ≤ Real.sqrt Q := by
    rw [← hN]
    exact (Real.le_sqrt hN0.le hQ0.le).2 hQ
  have hbeta : 0 < 1 / t ^ 2 := by positivity
  have hdenN : (1 / t ^ 2) * Real.sqrt N = t ^ 3 := by
    rw [hrootN]
    field_simp
  have hdenN' : (1 / t ^ 2) * N = t ^ 8 := by
    rw [hN]
    field_simp
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply one_div_le_one_div_of_le ht0
    simpa using htp 1 3 (by decide)
  · apply ratio_le_inverse t _ _ ht0 (by positivity)
    exact le_of_eq (by ring)
  · apply one_div_le_one_div_of_le ht0
    simpa using htp 1 2 (by decide)
  · apply ratio_le_inverse t _ _ ht0 (mul_pos hbeta (Real.sqrt_pos.2 hQ0))
    rw [show 1 / t ^ 2 * Real.sqrt Q = Real.sqrt Q / t ^ 2 by ring]
    apply (le_div_iff₀ (sq_pos_of_pos ht0)).2
    have h := (htp 5 10 (by decide)).trans hrootQ
    convert h using 1 <;> ring
  · rw [hdenN]
    apply ratio_le_inverse t _ _ ht0 (by positivity)
    have hsqrt : Real.sqrt t ≤ t := (Real.sqrt_le_left ht0.le).2 (by nlinarith)
    have hmul := mul_le_mul_of_nonneg_right hsqrt ht0.le
    have hpow := htp 2 3 (by decide)
    nlinarith
  · rw [hdenN']
    apply ratio_le_inverse t _ _ ht0 (by positivity)
    simpa only [pow_two] using htp 2 8 (by decide)
  · rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one, Real.sqrt_sq ht0.le]
  · rw [hrootN]
    apply (div_le_div_iff₀ (by positivity : 0 < t ^ 5) ht0).2
    have hpow := htp 4 5 (by decide)
    have hratio : t ^ 2 / (1 / t ^ 2) = t ^ 4 := by field_simp
    rw [hratio]
    nlinarith
  · apply one_div_le_one_div_of_le ht0
    have hp : t ≤ N := by simpa [hN] using htp 1 10 (by decide)
    have hNone : 1 ≤ N := by rw [hN]; exact one_le_pow₀ ht
    nlinarith

/-- The complete displayed error bracket is at most `11 N^(-1/10)`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For t, N, Q ∈ ℝ, assume 1 ≤ t; N = t¹⁰; N² ≤ Q. Then

Let R := t; Let L := t³; Let β := 1 / t²; (1 / R + 1 / L + R² / L + β + R² / (β · √Q) + √R / (β · √N) + R / (β · N)) + (√β + (L + R² / β) / √N + 1 / Q) ≤ 11 / t.
-/
theorem joint_parameter_bracket (t N Q : ℝ) (ht : 1 ≤ t)
    (hN : N = t ^ 10) (hQ : N ^ 2 ≤ Q) :
    let R := t
    let L := t ^ 3
    let β := 1 / t ^ 2
    (1 / R + 1 / L + R ^ 2 / L + β + R ^ 2 / (β * Real.sqrt Q) +
      Real.sqrt R / (β * Real.sqrt N) + R / (β * N)) +
      (Real.sqrt β + (L + R ^ 2 / β) / Real.sqrt N + 1 / Q) ≤ 11 / t := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ :=
    joint_parameter_terms t N Q ht hN hQ
  dsimp only at *
  simp only [div_eq_mul_inv] at *
  linarith

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For N ∈ ℝ, assume 1 ≤ N. Then

1 ≤ N^(1 / 10) ∧ N = (N^(1 / 10))¹⁰.
-/
theorem tenth_root_parameters (N : ℝ) (hN : 1 ≤ N) :
    1 ≤ N ^ (1 / 10 : ℝ) ∧ N = (N ^ (1 / 10 : ℝ)) ^ (10 : ℕ) := by
  have hN0 : 0 ≤ N := le_trans (by norm_num) hN
  constructor
  · exact Real.one_le_rpow hN (by norm_num)
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
    norm_num

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For N, Q ∈ ℝ, assume 1 ≤ N; N² ≤ Q. Then

Let R := N^(1 / 10); Let L := R³; Let β := 1 / R²; (1 / R + 1 / L + R² / L + β + R² / (β · √Q) + √R / (β · √N) + R / (β · N)) + (√β + (L + R² / β) / √N + 1 / Q) ≤ 11 · N^(−((1 / 10))).
-/
theorem joint_parameter_bracket_rpow (N Q : ℝ) (hN : 1 ≤ N) (hQ : N ^ 2 ≤ Q) :
    let R := N ^ (1 / 10 : ℝ)
    let L := R ^ 3
    let β := 1 / R ^ 2
    (1 / R + 1 / L + R ^ 2 / L + β + R ^ 2 / (β * Real.sqrt Q) +
      Real.sqrt R / (β * Real.sqrt N) + R / (β * N)) +
      (Real.sqrt β + (L + R ^ 2 / β) / Real.sqrt N + 1 / Q) ≤
        11 * N ^ (-(1 / 10) : ℝ) := by
  obtain ⟨ht, hpow⟩ := tenth_root_parameters N hN
  have h := joint_parameter_bracket (N ^ (1 / 10 : ℝ)) N Q ht hpow hQ
  simpa only [Real.rpow_neg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hN),
    div_eq_mul_inv] using h

end CircuitCompiler
