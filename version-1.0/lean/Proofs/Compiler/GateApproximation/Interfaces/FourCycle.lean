import Proofs.Compiler.GateApproximation.Interfaces.FourCycleCollisions
import Proofs.Compiler.GateApproximation.Interfaces.FourCycleRank
import Proofs.Compiler.GateApproximation.MatrixPhase.ZeroExtension



/-!
# The sharp four-cycle estimate under an actual random matrix refresh
-/
set_option autoImplicit false

set_option maxHeartbeats 2500000

open scoped BigOperators Classical

namespace CircuitCompiler.FourCycleEstimate

open Refresh MatrixRefresh TableAnalysis RefreshAnalysis

noncomputable section

variable {F X Y : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] {m : ℕ}

/-- Sharp rank-case assembly before the nonzero-share normalization. -/
-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m); b ∈ Y → U(F, m); E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ; B, R ∈ ℝ, assume |F| = 2; 2 ≤ m; a is injective; b is injective; ∀ x, y, ((a((x)₁) · b((y)₁)) ≠ ((x)₂ · (y)₂)) ⇒ E(x, y) = 0; 0 ≤ B; ∀ x, y, |E(x, y)| ≤ B; ∀ x, 𝔼_y [(fullFeatureTable(E, x, y))²] ≤ R²; ∀ y, 𝔼ₓ [(fullFeatureTable(E, x, y))²] ≤ R². Then

𝔼_(A ∈ F^({0,…,m−1} × {0,…,m−1})) [fourCycle(enlargedRestriction(a, b, E, A))] ≤ 16 · fourCycle(fullFeatureTable(E)) + (4 / |X| + 4 / |Y|) · R² · 𝔼_(p ∈ (X × V(F, m)) × (Y × V(F, m))) [(fullFeatureTable(E, (p)₁, (p)₂))²] + (16 / (|X| · |F|ᵐ) + 2 / (|X| · |Y|)) · B² · 𝔼_(p ∈ (X × V(F, m)) × (Y × V(F, m))) [(fullFeatureTable(E, (p)₁, (p)₂))²].
-/
theorem unrestricted_feature_fourCycle_sharp (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a : X → U F m) (b : Y → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (E : (X × U F m) → (Y × U F m) → ℝ)
    (hsupport : ∀ x y, dot (a x.1).val (b y.1).val ≠ dot x.2.val y.2.val → E x y = 0)
    (B R : ℝ) (hB : 0 ≤ B) (hE : ∀ x y, |E x y| ≤ B)
    (hrow : ∀ x, uavg (fun y => fullFeatureTable E x y ^ 2) ≤ R ^ 2)
    (hcol : ∀ y, uavg (fun x => fullFeatureTable E x y ^ 2) ≤ R ^ 2) :
    uavg (fun A : Matrix (Fin m) (Fin m) F => fourCycle (enlargedRestriction a b E A)) ≤
      16 * fourCycle (fullFeatureTable E) +
        (4 / (Fintype.card X : ℝ) + 4 / (Fintype.card Y : ℝ)) * R ^ 2 *
          uavg (fun p : (X × V F m) × (Y × V F m) => fullFeatureTable E p.1 p.2 ^ 2) +
        (16 / ((Fintype.card X : ℝ) * vectorCard F m) +
          2 / ((Fintype.card X : ℝ) * Fintype.card Y)) * B ^ 2 *
          uavg (fun p : (X × V F m) × (Y × V F m) => fullFeatureTable E p.1 p.2 ^ 2) := by
  let K := fullFeatureTable E
  have hK : ∀ x y, |K x y| ≤ B := fullFeatureTable_entry E B hB hE
  have h := uavg_mono (weighted_corner_le_sharp_rank_terms hq hm a b ha hb E hsupport)
  have hlhs : uavg (fun p => (vectorCard F m : ℝ)^4 * cornerCompletionProbability a b p * cornerProduct K p) =
      (vectorCard F m : ℝ)^4 * uavg (fun p => cornerCompletionProbability a b p * cornerProduct K p) := by
    simp only [mul_assoc, uavg_const_mul]
  change uavg (fun p => (vectorCard F m : ℝ)^4 * cornerCompletionProbability a b p * cornerProduct K p) ≤ _ at h
  rw [hlhs, ← enlarged_fourCycle_expansion] at h
  simp only [uavg_add, uavg_const_mul] at h
  have hp := mul_le_mul_of_nonneg_left (main_restriction_le K B hB hK)
    (by norm_num : (0 : ℝ) ≤ 16)
  have hr := mul_le_mul_of_nonneg_left (row_collision_l2_bound K R hrow)
    (show 0 ≤ 4*(vectorCard F m : ℝ) by positivity)
  have hc := mul_le_mul_of_nonneg_left (column_collision_l2_bound K R hcol)
    (show 0 ≤ 4*(vectorCard F m : ℝ) by positivity)
  have hd := mul_le_mul_of_nonneg_left (double_collision_energy_bound K B hB hK)
    (show 0 ≤ 2*(vectorCard F m : ℝ)^2 by positivity)
  have hs := add_le_add (add_le_add (add_le_add hp hr) hc) hd
  apply h.trans
  convert hs.trans_eq ?_ using 1
  · congr 4
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

/-- Zero extension contracts each normalized row energy. -/
-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ; R ∈ ℝ; x ∈ X × V(F, m), assume ∀ x, 𝔼_y [(E(x, y))²] ≤ R². Then

𝔼_y [(fullFeatureTable(E, x, y))²] ≤ R².
-/
theorem fullFeatureTable_row_l2 (E : (X × U F m) → (Y × U F m) → ℝ)
    (R : ℝ) (hrow : ∀ x, uavg (fun y => E x y ^ 2) ≤ R ^ 2)
    (x : X × V F m) :
    uavg (fun y => fullFeatureTable E x y ^ 2) ≤ R ^ 2 := by
  by_cases hx : x.2 = 0
  · simp only [fullFeatureTable, featureZeroExtend, hx, ne_eq, not_true_eq_false,
      false_and, ↓reduceDIte, zero_pow (by norm_num : 2 ≠ 0), uavg_zero]
    exact sq_nonneg R
  · letI : Nonempty (U F m) := ⟨⟨x.2,hx⟩⟩
    let e := featureCarrierEmbedding Y F m
    have hs (y : Y × V F m) (hy : y ∉ Set.range e) :
        fullFeatureTable E x y ^ 2 = 0 := by
      have hyzero : y.2 = 0 := by
        by_contra hh
        exact hy ⟨(y.1,⟨y.2,hh⟩),rfl⟩
      simp [fullFeatureTable, featureZeroExtend, hyzero]
    rw [uavg_eq_card_ratio_of_embedding e _ hs]
    have he (y : Y × U F m) :
        fullFeatureTable E x (e y) ^ 2 = E (x.1,⟨x.2,hx⟩) y ^ 2 := by
      exact congrArg (fun t : ℝ => t ^ 2)
        (featureZeroExtend_nonzero E x.1 ⟨x.2,hx⟩ y.1 y.2)
    simp_rw [he]
    have hr : (Fintype.card (Y × U F m) : ℝ) / Fintype.card (Y × V F m) ≤ 1 := by
      apply (div_le_one (by exact_mod_cast Fintype.card_pos :
        (0 : ℝ) < Fintype.card (Y × V F m))).2
      exact_mod_cast Fintype.card_le_of_injective e e.injective
    exact (mul_le_of_le_one_left (uavg_nonneg (fun _ => sq_nonneg _)) hr).trans
      (hrow (x.1,⟨x.2,hx⟩))

/-- Zero extension contracts each normalized column energy. -/
-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ; R ∈ ℝ; y ∈ Y × V(F, m), assume ∀ y, 𝔼ₓ [(E(x, y))²] ≤ R². Then

𝔼ₓ [(fullFeatureTable(E, x, y))²] ≤ R².
-/
theorem fullFeatureTable_column_l2 (E : (X × U F m) → (Y × U F m) → ℝ)
    (R : ℝ) (hcol : ∀ y, uavg (fun x => E x y ^ 2) ≤ R ^ 2)
    (y : Y × V F m) :
    uavg (fun x => fullFeatureTable E x y ^ 2) ≤ R ^ 2 := by
  by_cases hy : y.2 = 0
  · simp [fullFeatureTable, featureZeroExtend, hy]
    exact sq_nonneg R
  · letI : Nonempty (U F m) := ⟨⟨y.2,hy⟩⟩
    let e := featureCarrierEmbedding X F m
    have hs (x : X × V F m) (hx : x ∉ Set.range e) :
        fullFeatureTable E x y ^ 2 = 0 := by
      have hxzero : x.2 = 0 := by
        by_contra hh
        exact hx ⟨(x.1,⟨x.2,hh⟩),rfl⟩
      simp [fullFeatureTable, featureZeroExtend, hxzero]
    rw [uavg_eq_card_ratio_of_embedding e _ hs]
    have he (x : X × U F m) :
        fullFeatureTable E (e x) y ^ 2 = E x (y.1,⟨y.2,hy⟩) ^ 2 := by
      exact congrArg (fun t : ℝ => t ^ 2)
        (featureZeroExtend_nonzero E x.1 x.2 y.1 ⟨y.2,hy⟩)
    simp_rw [he]
    have hr : (Fintype.card (X × U F m) : ℝ) / Fintype.card (X × V F m) ≤ 1 := by
      apply (div_le_one (by exact_mod_cast Fintype.card_pos :
        (0 : ℝ) < Fintype.card (X × V F m))).2
      exact_mod_cast Fintype.card_le_of_injective e e.injective
    exact (mul_le_of_le_one_left (uavg_nonneg (fun _ => sq_nonneg _)) hr).trans
      (hcol (y.1,⟨y.2,hy⟩))

/-- The manuscript's sharp bound, with the actual random invertible refresh. The result applies to arbitrary injective left/right feature maps. -/

/-
Mathematical statement (normal notation): Work over the binary field with m ≥ 2, injective a,b:X → 𝔽₂ᵐ ∖ {0}, and a real table E supported on consistent tuples. Assume |E| ≤ B, with B ≥ 0, and that the mean squared entries in every row and every column are at most R². Let 0<D ≤ min{|X|,2ᵐ}. Then, for a uniformly random invertible refresh matrix,

𝔼_M [C₄(E^M)] ≤ 64 · C₄(E) +32R²/D · ‖E‖₂² +72B²/D² · ‖E‖₂².

Here C₄ is the uniformly averaged four-cycle product and E^M substitutes the refresh equations into E.
-/
theorem refreshTable_fourCycle_sharp (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (E : (X × U F m) → (X × U F m) → ℝ)
    (hsupport : ∀ x y, dot (a x.1).val (b y.1).val ≠ dot x.2.val y.2.val → E x y = 0)
    (B R D : ℝ) (hB : 0 ≤ B) (hE : ∀ x y, |E x y| ≤ B)
    (hrow : ∀ x, uavg (fun y => E x y ^ 2) ≤ R ^ 2)
    (hcol : ∀ y, uavg (fun x => E x y ^ 2) ≤ R ^ 2)
    (hD : 0 < D) (hDX : D ≤ Fintype.card X) (hDQ : D ≤ vectorCard F m) :
    uavg (fun M : Refresh.«GL» F m => fourCycle (refreshTable a b E M)) ≤
      64 * fourCycle E + (32 / D) * R ^ 2 *
        uavg (fun x => uavg (fun y => E x y ^ 2)) +
      (72 / D ^ 2) * B ^ 2 * uavg (fun x => uavg (fun y => E x y ^ 2)) := by
  letI : Nonempty (U F m) := ⟨a (Classical.choice inferInstance)⟩
  have h₁ := refreshTable_fourCycle_le_unrestricted a b E
  have h₂ := mul_le_mul_of_nonneg_left
    (unrestricted_feature_fourCycle_sharp hq hm a b ha hb E hsupport B R hB hE
      (fullFeatureTable_row_l2 E R hrow) (fullFeatureTable_column_l2 E R hcol))
    (by norm_num : (0 : ℝ) ≤ 4)
  have hc := mul_le_mul_of_nonneg_left (fullFeatureTable_fourCycle_le E)
    (by norm_num : (0 : ℝ) ≤ 64)
  let t := uavg (fun x => uavg (fun y => E x y ^ 2))
  let tf := uavg (fun p : (X × V F m) × (X × V F m) => fullFeatureTable E p.1 p.2 ^ 2)
  have ht : 0 ≤ t := uavg_nonneg (fun _ => uavg_nonneg (fun _ => sq_nonneg _))
  have htf : 0 ≤ tf := uavg_nonneg (fun _ => sq_nonneg _)
  have hft : tf ≤ t := fullFeatureTable_energy_le_nested E
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hQ : (0 : ℝ) < vectorCard F m := by
    have hp : 0 < vectorCard F m := by unfold vectorCard fieldCard; positivity
    exact_mod_cast hp
  have hDsq : 0 < D ^ 2 := sq_pos_of_pos hD
  have hDQprod : D ^ 2 ≤ (Fintype.card X : ℝ) * vectorCard F m := by nlinarith
  have hDXsq : D ^ 2 ≤ (Fintype.card X : ℝ) * Fintype.card X := by nlinarith
  have hmixed := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4) hD hDX
  have hdouble₁ := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 16) hDsq hDQprod
  have hdouble₂ := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hDsq hDXsq
  have hRnorm := mul_le_mul_of_nonneg_left hft (sq_nonneg R)
  have hBnorm := mul_le_mul_of_nonneg_left hft (sq_nonneg B)
  have hmixedbound := mul_le_mul hmixed hRnorm (mul_nonneg (sq_nonneg R) htf)
    (by positivity : (0 : ℝ) ≤ 4 / D)
  have hdoublebound₁ := mul_le_mul hdouble₁ hBnorm (mul_nonneg (sq_nonneg B) htf)
    (by positivity : (0 : ℝ) ≤ 16 / D ^ 2)
  have hdoublebound₂ := mul_le_mul hdouble₂ hBnorm (mul_nonneg (sq_nonneg B) htf)
    (by positivity : (0 : ℝ) ≤ 2 / D ^ 2)
  have hall := h₁.trans h₂
  change _ ≤ 64 * fourCycle E + (32 / D) * R ^ 2 * t + (72 / D ^ 2) * B ^ 2 * t
  change _ ≤ 4 * (16 * fourCycle (fullFeatureTable E) +
    (4 / (Fintype.card X : ℝ) + 4 / (Fintype.card X : ℝ)) * R ^ 2 * tf +
    (16 / ((Fintype.card X : ℝ) * vectorCard F m) +
      2 / ((Fintype.card X : ℝ) * Fintype.card X)) * B ^ 2 * tf) at hall
  simp only [div_eq_mul_inv] at hmixedbound hdoublebound₁ hdoublebound₂ hall ⊢
  nlinarith [hall]

/-- The same sharp estimate bounds the fourth power of the normalized operator norm; no singular-value hypothesis is needed for this transfer. -/

/-
Mathematical statement (normal notation): Work over the binary field with m ≥ 2, injective a,b:X → 𝔽₂ᵐ ∖ {0}, and a real table E supported on consistent tuples. Assume |E| ≤ B, with B ≥ 0, and that the mean squared entries in every row and every column are at most R². Let 0<D ≤ min{|X|,2ᵐ}. Then, for a uniformly random invertible refresh matrix,

𝔼_M [‖E^M‖ₒₚ⁴] ≤ 64 · C₄(E) +32R²/D · ‖E‖₂² +72B²/D² · ‖E‖₂².

Here C₄ is the uniformly averaged four-cycle product and E^M substitutes the refresh equations into E.
-/
theorem refreshTable_op_four_sharp (hq : fieldCard F = 2) (hm : 2 ≤ m) [DecidableEq X]
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (E : (X × U F m) → (X × U F m) → ℝ)
    (hsupport : ∀ x y, dot (a x.1).val (b y.1).val ≠ dot x.2.val y.2.val → E x y = 0)
    (B R D : ℝ) (hB : 0 ≤ B) (hE : ∀ x y, |E x y| ≤ B)
    (hrow : ∀ x, uavg (fun y => E x y ^ 2) ≤ R ^ 2)
    (hcol : ∀ y, uavg (fun x => E x y ^ 2) ≤ R ^ 2)
    (hD : 0 < D) (hDX : D ≤ Fintype.card X) (hDQ : D ≤ vectorCard F m) :
    uavg (fun M : Refresh.«GL» F m =>
      GateTruncation.opNorm (fun x y => (refreshTable a b E M x y : ℂ)) ^ 4) ≤
      64 * fourCycle E + (32 / D) * R ^ 2 *
        uavg (fun x => uavg (fun y => E x y ^ 2)) +
      (72 / D ^ 2) * B ^ 2 * uavg (fun x => uavg (fun y => E x y ^ 2)) := by
  exact (uavg_mono (fun M => real_opNorm_four_le_fourCycle
    (refreshTable a b E M))).trans
    (refreshTable_fourCycle_sharp hq hm a b ha hb E hsupport B R D hB hE
      hrow hcol hD hDX hDQ)

/-- At the natural choice `D = card X`, the cardinality condition on the ambient vector space follows from feature injectivity. -/

/-
Mathematical statement (normal notation): Work over the binary field with m ≥ 2, injective a,b:X → 𝔽₂ᵐ ∖ {0}, and a real table E supported on consistent tuples. Assume |E| ≤ B, with B ≥ 0, and that the mean squared entries in every row and every column are at most R². Put D = |X|. Then, for a uniformly random invertible refresh matrix,

𝔼_M [C₄(E^M)] ≤ 64 · C₄(E) +32R²/D · ‖E‖₂² +72B²/D² · ‖E‖₂².

Here C₄ is the uniformly averaged four-cycle product and E^M substitutes the refresh equations into E.
-/
theorem refreshTable_fourCycle_sharp_card (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (E : (X × U F m) → (X × U F m) → ℝ)
    (hsupport : ∀ x y, dot (a x.1).val (b y.1).val ≠ dot x.2.val y.2.val → E x y = 0)
    (B R : ℝ) (hB : 0 ≤ B) (hE : ∀ x y, |E x y| ≤ B)
    (hrow : ∀ x, uavg (fun y => E x y ^ 2) ≤ R ^ 2)
    (hcol : ∀ y, uavg (fun x => E x y ^ 2) ≤ R ^ 2) :
    uavg (fun M : Refresh.«GL» F m => fourCycle (refreshTable a b E M)) ≤
      64 * fourCycle E + (32 / (Fintype.card X : ℝ)) * R ^ 2 *
        uavg (fun x => uavg (fun y => E x y ^ 2)) +
      (72 / (Fintype.card X : ℝ) ^ 2) * B ^ 2 *
        uavg (fun x => uavg (fun y => E x y ^ 2)) := by
  have hcard : Fintype.card X ≤ vectorCard F m := by
    calc
      Fintype.card X ≤ Fintype.card (U F m) := Fintype.card_le_of_injective a ha
      _ ≤ Fintype.card (V F m) :=
        Fintype.card_le_of_injective (fun u : U F m => u.val) Subtype.val_injective
      _ = vectorCard F m := by simp [V,vectorCard,fieldCard]
  exact refreshTable_fourCycle_sharp hq hm a b ha hb E hsupport B R
    (Fintype.card X) hB hE hrow hcol
    (by exact_mod_cast Fintype.card_pos) (le_refl _) (by exact_mod_cast hcard)

end

end CircuitCompiler.FourCycleEstimate
