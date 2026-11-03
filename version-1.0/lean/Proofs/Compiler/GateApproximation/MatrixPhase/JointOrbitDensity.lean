import Proofs.Compiler.GateApproximation.MatrixPhase.JointOrbit



/-!
# Explicit near-uniform density of the compatible orbit

The exact orbit cardinality is bounded by sequential affine choices. After normalization its density differs from `q^4` by an explicit constant depending only on the field size, divided by `q^m`.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators Classical

namespace CircuitCompiler

open Refresh MatrixRefresh TableAnalysis

noncomputable section

/-- Removing four exceptional fractions from a product costs at most their sum. This elementary form keeps the density estimate independent of rank. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b, c, d ∈ ℝ, assume 0 ≤ a; a ≤ 1; 0 ≤ b; b ≤ 1; 0 ≤ c; c ≤ 1; 0 ≤ d; d ≤ 1. Then

1 - a · b · c · d ≤ (1 - a) + (1 - b) + (1 - c) + (1 - d).
-/
lemma four_factor_loss (a b c d : ℝ)
    (ha : 0 ≤ a) (ha' : a ≤ 1) (hb : 0 ≤ b) (hb' : b ≤ 1)
    (hc : 0 ≤ c) (hc' : c ≤ 1) (hd : 0 ≤ d) (hd' : d ≤ 1) :
    1 - a * b * c * d ≤ (1 - a) + (1 - b) + (1 - c) + (1 - d) := by
  have hab : a * b ≤ 1 := mul_le_one₀ ha' hb hb'
  have habc : a * b * c ≤ 1 := mul_le_one₀ hab hc hc'
  have h₁ : 1 - a * b ≤ (1 - a) + (1 - b) := by nlinarith [mul_nonneg (sub_nonneg.mpr ha') (sub_nonneg.mpr hb')]
  have h₂ : 1 - a * b * c ≤ (1 - a * b) + (1 - c) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hc')]
  have h₃ : 1 - a * b * c * d ≤ (1 - a * b * c) + (1 - d) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr habc) (sub_nonneg.mpr hd')]
  linarith

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b, c, d ∈ ℝ, assume 1 / 2 ≤ a; 1 / 2 ≤ b; 1 / 2 ≤ c; 1 / 2 ≤ d. Then

1 / 16 ≤ a · b · c · d.
-/
lemma four_factor_lower (a b c d : ℝ)
    (ha : 1 / 2 ≤ a) (hb : 1 / 2 ≤ b) (hc : 1 / 2 ≤ c) (hd : 1 / 2 ≤ d) :
    1 / 16 ≤ a * b * c * d := by
  have h₁ := mul_le_mul ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2) (by linarith : 0 ≤ a)
  have h₂ := mul_le_mul h₁ hc (by norm_num : (0 : ℝ) ≤ 1 / 2) (by nlinarith : 0 ≤ a * b)
  have h₃ := mul_le_mul h₂ hd (by norm_num : (0 : ℝ) ≤ 1 / 2) (by nlinarith : 0 ≤ a * b * c)
  norm_num at h₃
  exact h₃

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For h, v, E, D ∈ ℝ, assume 1 / 16 ≤ h; h ≤ 1; 0 ≤ v; v ≤ 1; 1 - h ≤ E; 1 - v ≤ D. Then

|v / h - 1| ≤ 16 · (E + D).
-/
lemma normalized_ratio_error (h v E D : ℝ) (hh : 1 / 16 ≤ h) (hh' : h ≤ 1)
    (hv : 0 ≤ v) (hv' : v ≤ 1) (hE : 1 - h ≤ E) (hD : 1 - v ≤ D) :
    |v / h - 1| ≤ 16 * (E + D) := by
  have hpos : 0 < h := by linarith
  have hED : 0 ≤ E + D := by linarith
  have habs : |v - h| ≤ E + D := by apply abs_le.mpr; constructor <;> linarith
  have he : v / h - 1 = (v - h) / h := by field_simp
  rw [he, abs_div, abs_of_pos hpos]
  apply (div_le_iff₀ hpos).2
  have hmul := mul_le_mul_of_nonneg_left hh hED
  nlinarith

/-- A purely real version of the orbit-count normalization. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For q, Q, a, C ∈ ℝ, assume 2 ≤ q; 2 · q ≤ a; Q = q² · a; (Q - 1) · (Q - q) · ((a - 1) · (a - q)) ≤ C; C ≤ (Q - 1) · (Q - q) · a². Then

|(Q - 1)⁴ / C - q⁴| ≤ 16 · q⁴ · (4 + (q + 1) · (1 + q²)) / Q.
-/
theorem orbit_density_real_bound (q Q a C : ℝ) (hq : 2 ≤ q) (ha : 2 * q ≤ a)
    (hQ : Q = q ^ 2 * a)
    (hlo : (Q - 1) * (Q - q) * ((a - 1) * (a - q)) ≤ C)
    (hhi : C ≤ (Q - 1) * (Q - q) * a ^ 2) :
    |(Q - 1) ^ 4 / C - q ^ 4| ≤
      16 * q ^ 4 * (4 + (q + 1) * (1 + q ^ 2)) / Q := by
  have hq0 : 0 < q := by linarith
  have ha0 : 0 < a := by linarith
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  have hQlarge : 2 * q ≤ Q := by rw [hQ]; nlinarith
  have hQtwo : 2 ≤ Q := by linarith
  have haTwo : 2 ≤ a := by linarith
  let x₁ := 1 - 1 / Q
  let x₂ := 1 - q / Q
  let x₃ := 1 - 1 / a
  let x₄ := 1 - q / a
  have hx₁ : 1 / 2 ≤ x₁ := by dsimp [x₁]; have := (div_le_iff₀ hQ0).2 (show (1 : ℝ) ≤ (1 / 2) * Q by linarith); linarith
  have hx₂ : 1 / 2 ≤ x₂ := by dsimp [x₂]; have := (div_le_iff₀ hQ0).2 (show q ≤ (1 / 2) * Q by linarith); linarith
  have hx₃ : 1 / 2 ≤ x₃ := by dsimp [x₃]; have := (div_le_iff₀ ha0).2 (show (1 : ℝ) ≤ (1 / 2) * a by linarith); linarith
  have hx₄ : 1 / 2 ≤ x₄ := by dsimp [x₄]; have := (div_le_iff₀ ha0).2 (show q ≤ (1 / 2) * a by linarith); linarith
  have hx₁' : x₁ ≤ 1 := by dsimp [x₁]; linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hQ0.le]
  have hx₂' : x₂ ≤ 1 := by dsimp [x₂]; linarith [div_nonneg hq0.le hQ0.le]
  have hx₃' : x₃ ≤ 1 := by dsimp [x₃]; linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) ha0.le]
  have hx₄' : x₄ ≤ 1 := by dsimp [x₄]; linarith [div_nonneg hq0.le ha0.le]
  let h := C / (Q ^ 2 * a ^ 2)
  have hden : 0 < Q ^ 2 * a ^ 2 := by positivity
  have hproduct : x₁ * x₂ * x₃ * x₄ ≤ h := by
    dsimp [h, x₁, x₂, x₃, x₄]
    apply (le_div_iff₀ hden).2
    convert hlo using 1 <;> field_simp <;> ring
  have hlow : 1 / 16 ≤ h := (four_factor_lower _ _ _ _ hx₁ hx₂ hx₃ hx₄).trans hproduct
  have hhigh : h ≤ 1 := by
    dsimp [h]
    apply (div_le_one hden).2
    have hp : (Q - 1) * (Q - q) ≤ Q ^ 2 := by nlinarith
    exact hhi.trans (mul_le_mul_of_nonneg_right hp (sq_nonneg _))
  have hE : 1 - h ≤ (q + 1) / Q + (q + 1) / a := by
    have he := four_factor_loss x₁ x₂ x₃ x₄ (by linarith) hx₁' (by linarith) hx₂'
      (by linarith) hx₃' (by linarith) hx₄'
    have hs : (1 - x₁) + (1 - x₂) + (1 - x₃) + (1 - x₄) =
        (q + 1) / Q + (q + 1) / a := by dsimp [x₁, x₂, x₃, x₄]; ring
    linarith
  have hv0 : 0 ≤ x₁ ^ 4 := by positivity
  have hv1 : x₁ ^ 4 ≤ 1 := by exact pow_le_one₀ (by linarith) hx₁'
  have hD : 1 - x₁ ^ 4 ≤ 4 / Q := by
    have he := four_factor_loss x₁ x₁ x₁ x₁ (by linarith) hx₁' (by linarith) hx₁'
      (by linarith) hx₁' (by linarith) hx₁'
    dsimp [x₁] at he ⊢
    convert he using 1 <;> ring
  have hr := normalized_ratio_error h (x₁ ^ 4) _ _ hlow hhigh hv0 hv1 hE hD
  have hC : 0 < C := by dsimp [h] at hlow; have := (le_div_iff₀ hden).1 hlow; nlinarith
  have heq : (Q - 1) ^ 4 / C - q ^ 4 = q ^ 4 * (x₁ ^ 4 / h - 1) := by
    dsimp [x₁, h]
    rw [hQ]
    field_simp <;> ring
  rw [heq, abs_mul, abs_of_nonneg (pow_nonneg hq0.le _)]
  refine (mul_le_mul_of_nonneg_left hr (pow_nonneg hq0.le _)).trans_eq ?_
  rw [hQ]
  field_simp <;> ring

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Density of the uniform compatible orbit relative to four independent uniform nonzero output vectors, on its exact support. -/
/-
Mathematical definition (normal notation): For m ∈ ℕ; S ∈ F^({0,…,2−1} × {0,…,2−1}), define

jointOrbitDensity(m, S) := (|U(F, m)|)⁴ / |CompatibleQuadruples(m = m, S)|.
-/
def jointOrbitDensity (m : ℕ) (S : Matrix (Fin 2) (Fin 2) F) : ℝ :=
  (Fintype.card (U F m) : ℝ) ^ 4 / Fintype.card (CompatibleQuadruples (m := m) S)

/-- An explicit field-size constant for the orbit-density approximation. -/
/-
Mathematical definition (normal notation): For F a set, assume F is a field; F is finite. define

jointOrbitDensityConstant := 16 · (|F|)⁴ · (4 + (|F| + 1) · (1 + (|F|)²)).
-/
def jointOrbitDensityConstant (F : Type*) [Field F] [Fintype F] : ℝ :=
  16 * (fieldCard F : ℝ) ^ 4 * (4 + ((fieldCard F : ℝ) + 1) * (1 + (fieldCard F : ℝ) ^ 2))

/-- The shared-matrix orbit density is `q⁴` up to `Cq/Q`, uniformly in all four prescribed pairings and hence in the rank of their matrix. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; S ∈ F^({0,…,2−1} × {0,…,2−1}), assume 4 ≤ m. Then

|jointOrbitDensity(m, S) - (|F|)⁴| ≤ jointOrbitDensityConstant(F) / (|F|)ᵐ.
-/
theorem jointOrbitDensity_error {m : ℕ} (hm : 4 ≤ m)
    (S : Matrix (Fin 2) (Fin 2) F) :
    |jointOrbitDensity m S - (fieldCard F : ℝ) ^ 4| ≤
      jointOrbitDensityConstant F / (fieldCard F : ℝ) ^ m := by
  have hq : (2 : ℝ) ≤ fieldCard F := by exact_mod_cast fieldCard_ge_two (F := F)
  have hq1 : 1 ≤ fieldCard F := by have := fieldCard_ge_two (F := F); omega
  have hQq : fieldCard F ≤ fieldCard F ^ m := by
    simpa only [pow_one] using Nat.pow_le_pow_right hq1 (show 1 ≤ m by omega)
  have haq : fieldCard F ≤ fieldCard F ^ (m - 2) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hq1 (show 1 ≤ m - 2 by omega)
  have hQ1 : 1 ≤ fieldCard F ^ m := hq1.trans hQq
  have ha1 : 1 ≤ fieldCard F ^ (m - 2) := hq1.trans haq
  have ha2 : (fieldCard F : ℝ) ^ 2 ≤ (fieldCard F : ℝ) ^ (m - 2) := by
    exact_mod_cast Nat.pow_le_pow_right hq1 (show 2 ≤ m - 2 by omega)
  have ha : 2 * (fieldCard F : ℝ) ≤ (fieldCard F : ℝ) ^ (m - 2) := by nlinarith
  have hQ : (fieldCard F : ℝ) ^ m = (fieldCard F : ℝ) ^ 2 * (fieldCard F : ℝ) ^ (m - 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hlo := Nat.cast_le (α := ℝ).2 (compatibleQuadruples_card_ge (m := m) (by omega) S)
  have hhi := Nat.cast_le (α := ℝ).2 (compatibleQuadruples_card_le (m := m) (by omega) S)
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hQ1, Nat.cast_sub hQq,
    Nat.cast_sub ha1, Nat.cast_sub haq, Nat.cast_one] at hlo hhi
  have h := orbit_density_real_bound (fieldCard F) ((fieldCard F : ℝ) ^ m) ((fieldCard F : ℝ) ^ (m - 2))
    (Fintype.card (CompatibleQuadruples (m := m) S)) hq ha hQ hlo hhi
  simpa only [jointOrbitDensity, nonzero_vector_card, Nat.cast_sub hQ1,
    Nat.cast_pow, Nat.cast_one, jointOrbitDensityConstant] using h

end

end CircuitCompiler
