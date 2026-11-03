import Proofs.Compiler.GateApproximation.MatrixPhase.PartialCollisions
import Proofs.Compiler.GateApproximation.MatrixPhase.ResidualExpansion
import Proofs.Compiler.GateApproximation.MatrixPhase.ZeroExtension



/-!
# The sharp energy-sensitive unrestricted residual moment

Exact rank counting and the four collision energy bounds combine here. The bound retains `B² L2²`, which is essential for the eighth-root operator estimate.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators Classical

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {F X Y : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] {m : ℕ}

/-- The signed main term has coefficient 16. The four exceptional corrections cost `20/a + 4/b + 16/Q + 2/(ab)` times squared-entry energy. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m); b ∈ Y → U(F, m); E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ; B ∈ ℝ, assume |F| = 2; 2 ≤ m; a is injective; b is injective; ∀ x, y, ((a((x)₁) · b((y)₁)) ≠ ((x)₂ · (y)₂)) ⇒ E(x, y) = 0; 0 ≤ B; ∀ x, y, |E(x, y)| ≤ B. Then

𝔼_(A ∈ F^({0,…,m−1} × {0,…,m−1})) [fourCycle(enlargedRestriction(a, b, E, A))] ≤ 16 · fourCycle(fullFeatureTable(E)) + (20 / |X| + 4 / |Y| + 16 / |F|ᵐ + 2 / (|X| · |Y|)) · B² · 𝔼_(p ∈ (X × V(F, m)) × (Y × V(F, m))) [(fullFeatureTable(E, (p)₁, (p)₂))²].
-/
theorem unrestricted_feature_fourCycle_le (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a : X → U F m) (b : Y → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (E : (X × U F m) → (Y × U F m) → ℝ)
    (hsupport : ∀ x y, dot (a x.1).val (b y.1).val ≠ dot x.2.val y.2.val → E x y = 0)
    (B : ℝ) (hB : 0 ≤ B) (hE : ∀ x y, |E x y| ≤ B) :
    uavg (fun A : Matrix (Fin m) (Fin m) F => fourCycle (enlargedRestriction a b E A)) ≤
      16 * fourCycle (fullFeatureTable E) +
        (20 / (Fintype.card X : ℝ) + 4 / (Fintype.card Y : ℝ) +
          16 / (vectorCard F m : ℝ) + 2 / ((Fintype.card X : ℝ) * Fintype.card Y)) * B^2 *
          uavg (fun p : (X × V F m) × (Y × V F m) => fullFeatureTable E p.1 p.2 ^ 2) := by
  let K := fullFeatureTable E
  have hK : ∀ x y, |K x y| ≤ B := by
    intro x y
    dsimp [K, fullFeatureTable, featureZeroExtend]
    split_ifs
    · exact hE _ _
    · simpa using hB
  have h := uavg_mono (weighted_corner_le_rank_errors hq hm a b ha hb E hsupport)
  have hlhs : uavg (fun p => (vectorCard F m : ℝ)^4 * cornerCompletionProbability a b p * cornerProduct K p) =
      (vectorCard F m : ℝ)^4 * uavg (fun p => cornerCompletionProbability a b p * cornerProduct K p) := by
    simp only [mul_assoc, uavg_const_mul]
  change uavg (fun p => (vectorCard F m : ℝ)^4 * cornerCompletionProbability a b p * cornerProduct K p) ≤ _ at h
  rw [hlhs, ← enlarged_fourCycle_expansion] at h
  simp only [uavg_add, uavg_const_mul] at h
  rw [← fourCycle_eq_uavg_cornerProduct] at h
  have hp := mul_le_mul_of_nonneg_left (partial_collision_energy_bound K B hB hK)
    (by norm_num : (0 : ℝ) ≤ 16)
  have hr := mul_le_mul_of_nonneg_left (row_collision_energy_bound K B hB hK)
    (show 0 ≤ 4*(vectorCard F m : ℝ) by positivity)
  have hc := mul_le_mul_of_nonneg_left (column_collision_energy_bound K B hB hK)
    (show 0 ≤ 4*(vectorCard F m : ℝ) by positivity)
  have hd := mul_le_mul_of_nonneg_left (double_collision_energy_bound K B hB hK)
    (show 0 ≤ 2*(vectorCard F m : ℝ)^2 by positivity)
  have hs := add_le_add (add_le_add (add_le_add
    (add_le_add (le_refl (16 * fourCycle K)) hp) hr) hc) hd
  apply h.trans
  convert hs.trans_eq ?_ using 1
  · congr 5
    all_goals first
      | (apply uavg_congr; intro p; split_ifs <;> rfl)
      | (funext p; split_ifs <;> rfl)
  · have hx : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hy : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hQ : (vectorCard F m : ℝ) ≠ 0 := by
      have hpos : 0 < vectorCard F m := by unfold vectorCard fieldCard; positivity
      exact_mod_cast hpos.ne'
    have hcard : (Fintype.card (V F m) : ℝ) = vectorCard F m := by simp [V,vectorCard,fieldCard]
    simp only [Fintype.card_prod, Nat.cast_mul, hcard]
    dsimp only [K]
    field_simp
    <;> ring

/-- Uniform cardinality lower bounds compress the coefficient into `42/D`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D, A, B, Q ∈ ℝ, assume 1 ≤ D; D ≤ A; D ≤ B; D ≤ Q. Then

20 / A + 4 / B + 16 / Q + 2 / (A · B) ≤ 42 / D.
-/
theorem residual_collision_coefficient_le (D A B Q : ℝ)
    (hD : 1 ≤ D) (hA : D ≤ A) (hB : D ≤ B) (hQ : D ≤ Q) :
    20/A + 4/B + 16/Q + 2/(A*B) ≤ 42/D := by
  have hDpos : 0 < D := by linarith
  have hApos : 0 < A := by linarith
  have hBpos : 0 < B := by linarith
  have hAB : D ≤ A*B := by nlinarith
  have h₁ := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 20) hDpos hA
  have h₂ := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4) hDpos hB
  have h₃ := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 16) hDpos hQ
  have h₄ := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hDpos hAB
  calc
    _ ≤ 20/D + 4/D + 16/D + 2/D := by linarith
    _ = 42/D := by ring

/-- The current residual moment on actual invertible matrices, still written with the zero-extended reference norms. The next normalization step only decreases these norms. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); E ∈ (X × U(F, m)) → (X × U(F, m)) → ℝ; B, D ∈ ℝ, assume |F| = 2; 2 ≤ m; a is injective; b is injective; ∀ x, y, ((a((x)₁) · b((y)₁)) ≠ ((x)₂ · (y)₂)) ⇒ E(x, y) = 0; 0 ≤ B; ∀ x, y, |E(x, y)| ≤ B; 1 ≤ D; D ≤ |X|; D ≤ |F|ᵐ. Then

𝔼_(M ∈ GLₘ(F)) [(GateTruncation.opNorm(((x, y ↦ refreshTable(a, b, E, M, x, y)))))⁴] ≤ 64 · fourCycle(fullFeatureTable(E)) + 168 / D · B² · 𝔼_(p ∈ (X × V(F, m)) × (X × V(F, m))) [(fullFeatureTable(E, (p)₁, (p)₂))²].
-/
theorem refreshTable_residual_fourth_full (hq : fieldCard F = 2) (hm : 2 ≤ m)
    [DecidableEq X] (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (E : (X × U F m) → (X × U F m) → ℝ)
    (hsupport : ∀ x y, dot (a x.1).val (b y.1).val ≠ dot x.2.val y.2.val → E x y = 0)
    (B D : ℝ) (hB : 0 ≤ B) (hE : ∀ x y, |E x y| ≤ B)
    (hD : 1 ≤ D) (hDX : D ≤ Fintype.card X) (hDQ : D ≤ vectorCard F m) :
    uavg (fun M : Refresh.«GL» F m =>
      GateTruncation.opNorm (fun x y => (refreshTable a b E M x y : ℂ)) ^ 4) ≤
      64 * fourCycle (fullFeatureTable E) + 168/D * B^2 *
        uavg (fun p : (X × V F m) × (X × V F m) => fullFeatureTable E p.1 p.2 ^ 2) := by
  have h₁ := refreshTable_op_four_le_unrestricted a b E
  have h₂ := mul_le_mul_of_nonneg_left
    (unrestricted_feature_fourCycle_le hq hm a b ha hb E hsupport B hB hE)
    (by norm_num : (0 : ℝ) ≤ 4)
  have h₃ := residual_collision_coefficient_le D (Fintype.card X) (Fintype.card X)
    (vectorCard F m) hD hDX hDX hDQ
  have he : 0 ≤ B^2 * uavg (fun p : (X × V F m) × (X × V F m) => fullFeatureTable E p.1 p.2 ^ 2) :=
    mul_nonneg (sq_nonneg _) (uavg_nonneg (fun _ => sq_nonneg _))
  have h₄ := mul_le_mul_of_nonneg_right h₃ he
  apply (h₁.trans h₂).trans
  simp only [div_eq_mul_inv] at h₄ ⊢
  nlinarith

/-- The complete current residual fourth-moment estimate, on the actual invertible-matrix graph and original nonzero-share normalized measures. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); E ∈ (X × U(F, m)) → (X × U(F, m)) → ℝ; B, D ∈ ℝ, assume |F| = 2; 2 ≤ m; a is injective; b is injective; ∀ x, y, ((a((x)₁) · b((y)₁)) ≠ ((x)₂ · (y)₂)) ⇒ E(x, y) = 0; 0 ≤ B; ∀ x, y, |E(x, y)| ≤ B; 1 ≤ D; D ≤ |X|; D ≤ |F|ᵐ. Then

𝔼_(M ∈ GLₘ(F)) [(GateTruncation.opNorm(((x, y ↦ refreshTable(a, b, E, M, x, y)))))⁴] ≤ 64 · fourCycle(E) + 168 / D · B² · 𝔼ₓ [𝔼_y [(E(x, y))²]].
-/
theorem refreshTable_residual_fourth (hq : fieldCard F = 2) (hm : 2 ≤ m)
    [DecidableEq X] (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (E : (X × U F m) → (X × U F m) → ℝ)
    (hsupport : ∀ x y, dot (a x.1).val (b y.1).val ≠ dot x.2.val y.2.val → E x y = 0)
    (B D : ℝ) (hB : 0 ≤ B) (hE : ∀ x y, |E x y| ≤ B)
    (hD : 1 ≤ D) (hDX : D ≤ Fintype.card X) (hDQ : D ≤ vectorCard F m) :
    uavg (fun M : Refresh.«GL» F m =>
      GateTruncation.opNorm (fun x y => (refreshTable a b E M x y : ℂ)) ^ 4) ≤
      64 * fourCycle E + 168/D * B^2 * uavg (fun x => uavg (fun y => E x y ^ 2)) := by
  letI : Nonempty (U F m) := ⟨a (Classical.choice inferInstance)⟩
  have h := refreshTable_residual_fourth_full hq hm a b ha hb E hsupport B D hB hE hD hDX hDQ
  have hc := mul_le_mul_of_nonneg_left (fullFeatureTable_fourCycle_le E)
    (by norm_num : (0 : ℝ) ≤ 64)
  have hDpos : 0 < D := by linarith
  have he := mul_le_mul_of_nonneg_left (fullFeatureTable_energy_le_nested E)
    (show 0 ≤ 168/D * B^2 by positivity)
  exact h.trans (add_le_add hc he)

end

end CircuitCompiler.RefreshAnalysis
