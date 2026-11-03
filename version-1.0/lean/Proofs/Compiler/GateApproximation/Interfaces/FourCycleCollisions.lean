import Proofs.Compiler.GateApproximation.MatrixPhase.PartialCollisions
import Proofs.Compiler.GateApproximation.MatrixPhase.ResidualExpansion



/-!
# Signed collision estimates for the sharp invertible-refresh four-cycle bound
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

open scoped BigOperators Classical

namespace CircuitCompiler.FourCycleEstimate

open MatrixRefresh TableAnalysis RefreshAnalysis

noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]

/-- A restriction involving just the two rows preserves nonnegativity of the complete column average, even for a signed table. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K ∈ A → B → ℝ; p ∈ A → A → Prop, we have

0 ≤ 𝔼_(z ∈ (A × A) × (B × B)) [{ cornerProduct(K, z) if p(((z)₁)₁, ((z)₁)₂),; 0 otherwise }].
-/
theorem restricted_row_cycle_nonneg (K : A → B → ℝ) (p : A → A → Prop) :
    0 ≤ uavg (fun z : (A × A) × (B × B) =>
      if p z.1.1 z.1.2 then cornerProduct K z else 0) := by
  simp only [uavg_prod]
  apply uavg_nonneg
  intro a
  apply uavg_nonneg
  intro a'
  by_cases h : p a a'
  · simp only [h, if_true, cornerProduct]
    have he : uavg (fun b => uavg (fun b' =>
        K a b * K a' b * K a' b' * K a b')) =
        (uavg (fun b => K a b * K a' b)) ^ 2 := by
      rw [pow_two, uavg_mul_uavg]
      apply uavg_congr
      intro b
      apply uavg_congr
      intro b'
      ring
    rw [he]
    positivity
  · simp only [h, if_false, uavg_zero, le_refl]

/-- The corresponding nonnegativity for a column-pair restriction. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K ∈ A → B → ℝ; p ∈ B → B → Prop, we have

0 ≤ 𝔼_(z ∈ (A × A) × (B × B)) [{ cornerProduct(K, z) if p(((z)₂)₁, ((z)₂)₂),; 0 otherwise }].
-/
theorem restricted_column_cycle_nonneg (K : A → B → ℝ) (p : B → B → Prop) :
    0 ≤ uavg (fun z : (A × A) × (B × B) =>
      if p z.2.1 z.2.2 then cornerProduct K z else 0) := by
  have h := restricted_row_cycle_nonneg (fun b a => K a b) p
  have he := uavg_equiv (Equiv.prodComm (A × A) (B × B))
    (fun z : (B × B) × (A × A) =>
      if p z.1.1 z.1.2 then cornerProduct (fun b a => K a b) z else 0)
  have hp (z : (A × A) × (B × B)) :
      cornerProduct (fun b a => K a b) (z.2,z.1) = cornerProduct K z := by
    unfold cornerProduct
    ring
  change uavg (fun z : (A × A) × (B × B) =>
    if p z.2.1 z.2.2 then cornerProduct (fun b a => K a b) (z.2,z.1) else 0) = _ at he
  simp only [hp] at he
  rw [he]
  exact h

/-- A complete repeated row is controlled by its mean squared entries, rather than by a supremum of its entries. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K ∈ A → B → ℝ; R ∈ ℝ, assume ∀ a, 𝔼_b [(K(a, b))²] ≤ R². Then

𝔼_(z ∈ (A × A) × (B × B)) [{ |cornerProduct(K, z)| if ((z)₁)₁ = ((z)₁)₂,; 0 otherwise }] ≤ (|A|)⁻¹ · R² · 𝔼_(z ∈ A × B) [(K((z)₁, (z)₂))²].
-/
theorem row_collision_l2_bound (K : A → B → ℝ) (R : ℝ)
    (hrow : ∀ a, uavg (fun b => K a b ^ 2) ≤ R ^ 2) :
    uavg (fun z : (A × A) × (B × B) =>
      if z.1.1 = z.1.2 then |cornerProduct K z| else 0) ≤
      (Fintype.card A : ℝ)⁻¹ * R ^ 2 *
        uavg (fun z : A × B => K z.1 z.2 ^ 2) := by
  have he : uavg (fun z : (A × A) × (B × B) =>
      if z.1.1 = z.1.2 then |cornerProduct K z| else 0) =
      (Fintype.card A : ℝ)⁻¹ * uavg (fun a =>
        (uavg (fun b => K a b ^ 2)) ^ 2) := by
    simp only [uavg, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
    have hsum : (∑ a : A, ∑ a' : A, ∑ b : B, ∑ b' : B,
        if a = a' then |cornerProduct K ((a,a'),(b,b'))| else 0) =
        ∑ a : A, (∑ b : B, K a b ^ 2) ^ 2 := by
      simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      apply Finset.sum_congr rfl
      intro a _
      rw [pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro b' _
      dsimp [cornerProduct]
      rw [show K a b * K a b * K a b' * K a b' =
        K a b ^ 2 * K a b' ^ 2 by ring, abs_of_nonneg (by positivity)]
    rw [hsum]
    simp_rw [mul_pow, ← Finset.mul_sum]
    ring
  rw [he, uavg_prod]
  have h := uavg_mono (fun a => mul_le_mul_of_nonneg_right (hrow a)
    (uavg_nonneg (fun b => sq_nonneg (K a b))))
  simp only [← pow_two, uavg_const_mul] at h
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)

/-- The column analogue of the row-energy collision estimate. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K ∈ A → B → ℝ; R ∈ ℝ, assume ∀ b, 𝔼ₐ [(K(a, b))²] ≤ R². Then

𝔼_(z ∈ (A × A) × (B × B)) [{ |cornerProduct(K, z)| if ((z)₂)₁ = ((z)₂)₂,; 0 otherwise }] ≤ (|B|)⁻¹ · R² · 𝔼_(z ∈ A × B) [(K((z)₁, (z)₂))²].
-/
theorem column_collision_l2_bound (K : A → B → ℝ) (R : ℝ)
    (hcol : ∀ b, uavg (fun a => K a b ^ 2) ≤ R ^ 2) :
    uavg (fun z : (A × A) × (B × B) =>
      if z.2.1 = z.2.2 then |cornerProduct K z| else 0) ≤
      (Fintype.card B : ℝ)⁻¹ * R ^ 2 *
        uavg (fun z : A × B => K z.1 z.2 ^ 2) := by
  have h := row_collision_l2_bound (fun b a => K a b) R hcol
  have he := uavg_equiv (Equiv.prodComm (A × A) (B × B))
    (fun z : (B × B) × (A × A) =>
      if z.1.1 = z.1.2 then |cornerProduct (fun b a => K a b) z| else 0)
  have hp (z : (A × A) × (B × B)) :
      cornerProduct (fun b a => K a b) (z.2,z.1) = cornerProduct K z := by
    unfold cornerProduct
    ring
  change uavg (fun z : (A × A) × (B × B) =>
    if z.2.1 = z.2.2 then |cornerProduct (fun b a => K a b) (z.2,z.1)| else 0) = _ at he
  simp only [hp] at he
  rw [← he] at h
  have havg : uavg (fun z : B × A => K z.2 z.1 ^ 2) =
      uavg (fun z : A × B => K z.1 z.2 ^ 2) := by
    simpa only [Equiv.prodComm_apply, Prod.swap] using
      uavg_equiv (Equiv.prodComm B A) (fun z : A × B => K z.1 z.2 ^ 2)
  simpa only [havg] using h

variable {X U Y V : Type*} [Fintype X] [Fintype U] [Fintype Y] [Fintype V]
  [Nonempty X] [Nonempty U] [Nonempty Y] [Nonempty V]

/-- Both partial collisions retain the full marginal distribution at each individual corner; only their inverse-cardinality probability is paid. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ (X × U) → (Y × V) → ℝ, we have

𝔼_(z ∈ ((X × U) × (X × U)) × ((Y × V) × (Y × V))) [{ f(((z)₁)₁, ((z)₂)₁) if (((z)₁)₁)₁ = (((z)₁)₂)₁ ∧ (((z)₂)₁)₂ = (((z)₂)₂)₂,; 0 otherwise }] = ((|X| · |V|))⁻¹ · 𝔼_(z ∈ (X × U) × (Y × V)) [f((z)₁, (z)₂)].
-/
theorem partial_double_first_corner_average (f : (X × U) → (Y × V) → ℝ) :
    uavg (fun z : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
      if z.1.1.1 = z.1.2.1 ∧ z.2.1.2 = z.2.2.2 then f z.1.1 z.2.1 else 0) =
      ((Fintype.card X : ℝ) * Fintype.card V)⁻¹ *
        uavg (fun z : (X × U) × (Y × V) => f z.1 z.2) := by
  simp only [uavg, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type, ite_and]
  have hsum : (∑ x : X, ∑ u : U, ∑ x' : X, ∑ u' : U,
      ∑ y : Y, ∑ v : V, ∑ y' : Y, ∑ v' : V,
      if x = x' then (if v = v' then f (x,u) (y,v) else 0) else 0) =
      (Fintype.card U : ℝ) * Fintype.card Y *
        ∑ x : X, ∑ u : U, ∑ y : Y, ∑ v : V, f (x,u) (y,v) := by
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp only [← Finset.mul_sum]
    ring
  rw [hsum]
  have hx : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hu : (Fintype.card U : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hy : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hv : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  <;> ring

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ (X × U) → (Y × V) → ℝ, we have

𝔼_(z ∈ ((X × U) × (X × U)) × ((Y × V) × (Y × V))) [{ f(((z)₁)₂, ((z)₂)₁) if (((z)₁)₁)₁ = (((z)₁)₂)₁ ∧ (((z)₂)₁)₂ = (((z)₂)₂)₂,; 0 otherwise }] = ((|X| · |V|))⁻¹ · 𝔼_(z ∈ (X × U) × (Y × V)) [f((z)₁, (z)₂)].
-/
theorem partial_double_second_corner_average (f : (X × U) → (Y × V) → ℝ) :
    uavg (fun z : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
      if z.1.1.1 = z.1.2.1 ∧ z.2.1.2 = z.2.2.2 then f z.1.2 z.2.1 else 0) =
      ((Fintype.card X : ℝ) * Fintype.card V)⁻¹ *
        uavg (fun z : (X × U) × (Y × V) => f z.1 z.2) := by
  have h := uavg_equiv
    (Equiv.prodCongr (Equiv.prodComm (X × U) (X × U))
      (Equiv.refl ((Y × V) × (Y × V))))
    (fun z : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
      if z.1.1.1 = z.1.2.1 ∧ z.2.1.2 = z.2.2.2 then f z.1.1 z.2.1 else 0)
  change uavg (fun z : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
    if z.1.2.1 = z.1.1.1 ∧ z.2.1.2 = z.2.2.2 then f z.1.2 z.2.1 else 0) = _ at h
  simpa only [eq_comm] using h.trans (partial_double_first_corner_average f)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ (X × U) → (Y × V) → ℝ, we have

𝔼_(z ∈ ((X × U) × (X × U)) × ((Y × V) × (Y × V))) [{ f(((z)₁)₁, ((z)₂)₂) if (((z)₁)₁)₁ = (((z)₁)₂)₁ ∧ (((z)₂)₁)₂ = (((z)₂)₂)₂,; 0 otherwise }] = ((|X| · |V|))⁻¹ · 𝔼_(z ∈ (X × U) × (Y × V)) [f((z)₁, (z)₂)].
-/
theorem partial_double_fourth_corner_average (f : (X × U) → (Y × V) → ℝ) :
    uavg (fun z : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
      if z.1.1.1 = z.1.2.1 ∧ z.2.1.2 = z.2.2.2 then f z.1.1 z.2.2 else 0) =
      ((Fintype.card X : ℝ) * Fintype.card V)⁻¹ *
        uavg (fun z : (X × U) × (Y × V) => f z.1 z.2) := by
  have h := uavg_equiv
    (Equiv.prodCongr (Equiv.refl ((X × U) × (X × U)))
      (Equiv.prodComm (Y × V) (Y × V)))
    (fun z : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
      if z.1.1.1 = z.1.2.1 ∧ z.2.1.2 = z.2.2.2 then f z.1.1 z.2.1 else 0)
  change uavg (fun z : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
    if z.1.1.1 = z.1.2.1 ∧ z.2.2.2 = z.2.1.2 then f z.1.1 z.2.2 else 0) = _ at h
  simpa only [eq_comm] using h.trans (partial_double_first_corner_average f)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ (X × U) → (Y × V) → ℝ, we have

𝔼_(z ∈ ((X × U) × (X × U)) × ((Y × V) × (Y × V))) [{ f(((z)₁)₂, ((z)₂)₂) if (((z)₁)₁)₁ = (((z)₁)₂)₁ ∧ (((z)₂)₁)₂ = (((z)₂)₂)₂,; 0 otherwise }] = ((|X| · |V|))⁻¹ · 𝔼_(z ∈ (X × U) × (Y × V)) [f((z)₁, (z)₂)].
-/
theorem partial_double_third_corner_average (f : (X × U) → (Y × V) → ℝ) :
    uavg (fun z : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
      if z.1.1.1 = z.1.2.1 ∧ z.2.1.2 = z.2.2.2 then f z.1.2 z.2.2 else 0) =
      ((Fintype.card X : ℝ) * Fintype.card V)⁻¹ *
        uavg (fun z : (X × U) × (Y × V) => f z.1 z.2) := by
  have h := uavg_equiv
    (Equiv.prodCongr (Equiv.refl ((X × U) × (X × U)))
      (Equiv.prodComm (Y × V) (Y × V)))
    (fun z : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
      if z.1.1.1 = z.1.2.1 ∧ z.2.1.2 = z.2.2.2 then f z.1.2 z.2.1 else 0)
  change uavg (fun z : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
    if z.1.1.1 = z.1.2.1 ∧ z.2.2.2 = z.2.1.2 then f z.1.2 z.2.2 else 0) = _ at h
  simpa only [eq_comm] using h.trans (partial_double_second_corner_average f)

/-- Only the simultaneous partial collision incurs the supremum-entry bound. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K ∈ (X × U) → (Y × V) → ℝ; B ∈ ℝ, assume 0 ≤ B; ∀ x, y, |K(x, y)| ≤ B. Then

𝔼_(z ∈ ((X × U) × (X × U)) × ((Y × V) × (Y × V))) [{ |cornerProduct(K, z)| if (((z)₁)₁)₁ = (((z)₁)₂)₁ ∧ (((z)₂)₁)₂ = (((z)₂)₂)₂,; 0 otherwise }] ≤ ((|X| · |V|))⁻¹ · B² · 𝔼_(z ∈ (X × U) × (Y × V)) [(K((z)₁, (z)₂))²].
-/
theorem partial_double_collision_energy_bound (K : (X × U) → (Y × V) → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hK : ∀ x y, |K x y| ≤ B) :
    uavg (fun z : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
      if z.1.1.1 = z.1.2.1 ∧ z.2.1.2 = z.2.2.2 then |cornerProduct K z| else 0) ≤
      ((Fintype.card X : ℝ) * Fintype.card V)⁻¹ * B ^ 2 *
        uavg (fun z : (X × U) × (Y × V) => K z.1 z.2 ^ 2) := by
  have hp (z : ((X × U) × (X × U)) × ((Y × V) × (Y × V))) :
      (if z.1.1.1 = z.1.2.1 ∧ z.2.1.2 = z.2.2.2 then |cornerProduct K z| else 0) ≤
      B ^ 2 / 4 * ((if z.1.1.1 = z.1.2.1 ∧ z.2.1.2 = z.2.2.2 then K z.1.1 z.2.1 ^ 2 else 0) +
        (if z.1.1.1 = z.1.2.1 ∧ z.2.1.2 = z.2.2.2 then K z.1.2 z.2.1 ^ 2 else 0) +
        (if z.1.1.1 = z.1.2.1 ∧ z.2.1.2 = z.2.2.2 then K z.1.2 z.2.2 ^ 2 else 0) +
        (if z.1.1.1 = z.1.2.1 ∧ z.2.1.2 = z.2.2.2 then K z.1.1 z.2.2 ^ 2 else 0)) := by
    by_cases h : z.1.1.1 = z.1.2.1 ∧ z.2.1.2 = z.2.2.2
    · simp only [h, if_true, cornerProduct]
      exact four_entry_energy_bound _ _ _ _ B hB (hK _ _) (hK _ _) (hK _ _) (hK _ _)
    · simp [h]
  have h := uavg_mono hp
  rw [uavg_const_mul, uavg_add, uavg_add, uavg_add,
    partial_double_first_corner_average (fun x y => K x y ^ 2),
    partial_double_second_corner_average (fun x y => K x y ^ 2),
    partial_double_third_corner_average (fun x y => K x y ^ 2),
    partial_double_fourth_corner_average (fun x y => K x y ^ 2)] at h
  exact h.trans_eq (by ring)

/-- Inclusion--exclusion subtracts nonnegative sliced four-cycles. Its only positive error is the simultaneous old-row/new-column collision. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K ∈ (X × U) → (Y × V) → ℝ; B ∈ ℝ, assume 0 ≤ B; ∀ x, y, |K(x, y)| ≤ B. Then

𝔼_(z ∈ ((X × U) × (X × U)) × ((Y × V) × (Y × V))) [{ cornerProduct(K, z) if (((z)₁)₁)₁ ≠ (((z)₁)₂)₁ ∧ (((z)₂)₁)₂ ≠ (((z)₂)₂)₂,; 0 otherwise }] ≤ fourCycle(K) + ((|X| · |V|))⁻¹ · B² · 𝔼_(z ∈ (X × U) × (Y × V)) [(K((z)₁, (z)₂))²].
-/
theorem main_restriction_le (K : (X × U) → (Y × V) → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hK : ∀ x y, |K x y| ≤ B) :
    uavg (fun z : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
      if z.1.1.1 ≠ z.1.2.1 ∧ z.2.1.2 ≠ z.2.2.2 then cornerProduct K z else 0) ≤
      fourCycle K + ((Fintype.card X : ℝ) * Fintype.card V)⁻¹ * B ^ 2 *
        uavg (fun z : (X × U) × (Y × V) => K z.1 z.2 ^ 2) := by
  have hr := restricted_row_cycle_nonneg K (fun x x' => x.1 = x'.1)
  have hc := restricted_column_cycle_nonneg K (fun y y' => y.2 = y'.2)
  have hd := partial_double_collision_energy_bound K B hB hK
  have habs : uavg (fun z : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
      if z.1.1.1 = z.1.2.1 ∧ z.2.1.2 = z.2.2.2 then cornerProduct K z else 0) ≤
      uavg (fun z : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
      if z.1.1.1 = z.1.2.1 ∧ z.2.1.2 = z.2.2.2 then |cornerProduct K z| else 0) := by
    apply uavg_mono
    intro z
    split_ifs <;> first | exact le_abs_self _ | exact le_refl _
  have he : uavg (fun z : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
      if z.1.1.1 ≠ z.1.2.1 ∧ z.2.1.2 ≠ z.2.2.2 then cornerProduct K z else 0) =
      fourCycle K -
        uavg (fun z : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
          if z.1.1.1 = z.1.2.1 then cornerProduct K z else 0) -
        uavg (fun z : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
          if z.2.1.2 = z.2.2.2 then cornerProduct K z else 0) +
        uavg (fun z : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
          if z.1.1.1 = z.1.2.1 ∧ z.2.1.2 = z.2.2.2 then cornerProduct K z else 0) := by
    rw [fourCycle_eq_uavg_cornerProduct, ← uavg_sub, ← uavg_sub, ← uavg_add]
    apply uavg_congr
    intro z
    by_cases hx : z.1.1.1 = z.1.2.1 <;> by_cases hv : z.2.1.2 = z.2.2.2 <;>
      simp [hx, hv]
  linarith

end

end CircuitCompiler.FourCycleEstimate
