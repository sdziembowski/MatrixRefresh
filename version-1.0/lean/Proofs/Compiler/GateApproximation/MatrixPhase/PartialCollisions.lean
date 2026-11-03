import Proofs.Compiler.GateApproximation.MatrixPhase.Collisions



/-!
# Collision costs for only one coordinate of a row or column
-/
set_option autoImplicit false

set_option maxHeartbeats 1500000

open scoped BigOperators Classical

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {X U Y V C : Type*} [Fintype X] [Fintype U] [Fintype Y] [Fintype V]
  [Fintype C] [Nonempty X] [Nonempty U] [Nonempty Y] [Nonempty V] [Nonempty C]

/-
Mathematical definition (normal notation): Regroup the same six coordinates by the bijection

(((x₁,u₁),(x₂,u₂)),(c₁,c₂)) ↔((x₁,x₂),((u₁,c₁),(u₂,c₂))).
-/
def partialRowShuffle : (((X × U) × (X × U)) × (C × C)) ≃
    ((X × X) × ((U × C) × (U × C))) where
  toFun p := ((p.1.1.1,p.1.2.1), ((p.1.1.2,p.2.1),(p.1.2.2,p.2.2)))
  invFun p := (((p.1.1,p.2.1.1),(p.1.2,p.2.2.1)),(p.2.1.2,p.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ (X × U) → C → ℝ, we have

𝔼_(p ∈ ((X × U) × (X × U)) × (C × C)) [{ f(((p)₁)₁, ((p)₂)₁) if (((p)₁)₁)₁ = (((p)₁)₂)₁,; 0 otherwise }] = (|X|)⁻¹ · 𝔼_(p ∈ (X × U) × C) [f((p)₁, (p)₂)].
-/
theorem partial_row_first_corner_average (f : (X × U) → C → ℝ) :
    uavg (fun p : ((X × U) × (X × U)) × (C × C) =>
      if p.1.1.1 = p.1.2.1 then f p.1.1 p.2.1 else 0) =
      (Fintype.card X : ℝ)⁻¹ * uavg (fun p : (X × U) × C => f p.1 p.2) := by
  have h := row_collision_corner_average (fun x (p : U × C) => f (x,p.1) p.2)
  have he := uavg_equiv (partialRowShuffle (X := X) (U := U) (C := C))
    (fun p : (X × X) × ((U × C) × (U × C)) =>
      if p.1.1 = p.1.2 then f (p.1.1,p.2.1.1) p.2.1.2 else 0)
  have hm := uavg_equiv (Equiv.prodAssoc X U C)
    (fun p : X × (U × C) => f (p.1,p.2.1) p.2.2)
  exact he.trans (h.trans (by rw [← hm]; rfl))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ (X × U) → C → ℝ, we have

𝔼_(p ∈ ((X × U) × (X × U)) × (C × C)) [{ f(((p)₁)₂, ((p)₂)₁) if (((p)₁)₁)₁ = (((p)₁)₂)₁,; 0 otherwise }] = (|X|)⁻¹ · 𝔼_(p ∈ (X × U) × C) [f((p)₁, (p)₂)].
-/
theorem partial_row_second_corner_average (f : (X × U) → C → ℝ) :
    uavg (fun p : ((X × U) × (X × U)) × (C × C) =>
      if p.1.1.1 = p.1.2.1 then f p.1.2 p.2.1 else 0) =
      (Fintype.card X : ℝ)⁻¹ * uavg (fun p : (X × U) × C => f p.1 p.2) := by
  have h := uavg_equiv
    (Equiv.prodCongr (Equiv.prodComm (X × U) (X × U)) (Equiv.refl (C × C)))
    (fun p : ((X × U) × (X × U)) × (C × C) =>
      if p.1.1.1 = p.1.2.1 then f p.1.1 p.2.1 else 0)
  change (uavg (fun p : ((X × U) × (X × U)) × (C × C) =>
    if p.1.2.1 = p.1.1.1 then f p.1.2 p.2.1 else 0)) = _ at h
  simpa only [eq_comm] using h.trans (partial_row_first_corner_average f)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ (X × U) → C → ℝ, we have

𝔼_(p ∈ ((X × U) × (X × U)) × (C × C)) [{ f(((p)₁)₁, ((p)₂)₂) if (((p)₁)₁)₁ = (((p)₁)₂)₁,; 0 otherwise }] = (|X|)⁻¹ · 𝔼_(p ∈ (X × U) × C) [f((p)₁, (p)₂)].
-/
theorem partial_row_fourth_corner_average (f : (X × U) → C → ℝ) :
    uavg (fun p : ((X × U) × (X × U)) × (C × C) =>
      if p.1.1.1 = p.1.2.1 then f p.1.1 p.2.2 else 0) =
      (Fintype.card X : ℝ)⁻¹ * uavg (fun p : (X × U) × C => f p.1 p.2) := by
  have h := uavg_equiv
    (Equiv.prodCongr (Equiv.refl ((X × U) × (X × U))) (Equiv.prodComm C C))
    (fun p : ((X × U) × (X × U)) × (C × C) =>
      if p.1.1.1 = p.1.2.1 then f p.1.1 p.2.1 else 0)
  exact h.trans (partial_row_first_corner_average f)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ (X × U) → C → ℝ, we have

𝔼_(p ∈ ((X × U) × (X × U)) × (C × C)) [{ f(((p)₁)₂, ((p)₂)₂) if (((p)₁)₁)₁ = (((p)₁)₂)₁,; 0 otherwise }] = (|X|)⁻¹ · 𝔼_(p ∈ (X × U) × C) [f((p)₁, (p)₂)].
-/
theorem partial_row_third_corner_average (f : (X × U) → C → ℝ) :
    uavg (fun p : ((X × U) × (X × U)) × (C × C) =>
      if p.1.1.1 = p.1.2.1 then f p.1.2 p.2.2 else 0) =
      (Fintype.card X : ℝ)⁻¹ * uavg (fun p : (X × U) × C => f p.1 p.2) := by
  have h := uavg_equiv
    (Equiv.prodCongr (Equiv.refl ((X × U) × (X × U))) (Equiv.prodComm C C))
    (fun p : ((X × U) × (X × U)) × (C × C) =>
      if p.1.1.1 = p.1.2.1 then f p.1.2 p.2.1 else 0)
  exact h.trans (partial_row_second_corner_average f)

/-- Equality of only the old-row coordinate costs its own inverse cardinality; the remaining row coordinate remains independently uniform. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K ∈ (X × U) → C → ℝ; B ∈ ℝ, assume 0 ≤ B; ∀ x, y, |K(x, y)| ≤ B. Then

𝔼_(p ∈ ((X × U) × (X × U)) × (C × C)) [{ |cornerProduct(K, p)| if (((p)₁)₁)₁ = (((p)₁)₂)₁,; 0 otherwise }] ≤ (|X|)⁻¹ · B² · 𝔼_(p ∈ (X × U) × C) [(K((p)₁, (p)₂))²].
-/
theorem partial_row_collision_energy_bound (K : (X × U) → C → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hK : ∀ x y, |K x y| ≤ B) :
    uavg (fun p : ((X × U) × (X × U)) × (C × C) =>
      if p.1.1.1 = p.1.2.1 then |cornerProduct K p| else 0) ≤
      (Fintype.card X : ℝ)⁻¹ * B ^ 2 * uavg (fun p : (X × U) × C => K p.1 p.2 ^ 2) := by
  have hp (p : ((X × U) × (X × U)) × (C × C)) :
      (if p.1.1.1 = p.1.2.1 then |cornerProduct K p| else 0) ≤
        B ^ 2 / 4 * ((if p.1.1.1 = p.1.2.1 then K p.1.1 p.2.1 ^ 2 else 0) +
          (if p.1.1.1 = p.1.2.1 then K p.1.2 p.2.1 ^ 2 else 0) +
          (if p.1.1.1 = p.1.2.1 then K p.1.2 p.2.2 ^ 2 else 0) +
          (if p.1.1.1 = p.1.2.1 then K p.1.1 p.2.2 ^ 2 else 0)) := by
    by_cases h : p.1.1.1 = p.1.2.1
    · simp only [h, if_true, cornerProduct]
      exact four_entry_energy_bound _ _ _ _ B hB (hK _ _) (hK _ _) (hK _ _) (hK _ _)
    · simp [h]
  have h := uavg_mono hp
  rw [uavg_const_mul, uavg_add, uavg_add, uavg_add,
    partial_row_first_corner_average (fun x y => K x y ^ 2),
    partial_row_second_corner_average (fun x y => K x y ^ 2),
    partial_row_third_corner_average (fun x y => K x y ^ 2),
    partial_row_fourth_corner_average (fun x y => K x y ^ 2)] at h
  exact h.trans_eq (by ring)

/-
Mathematical definition (normal notation): Transpose and regroup a four-corner tuple by the bijection

(((x₁,u₁),(x₂,u₂)),((y₁,v₁),(y₂,v₂))) ↔(((v₁,y₁),(v₂,y₂)),((x₁,u₁),(x₂,u₂))).
-/
def partialColumnTranspose :
    (((X × U) × (X × U)) × ((Y × V) × (Y × V))) ≃
      (((V × Y) × (V × Y)) × ((X × U) × (X × U))) where
  toFun p := (((p.2.1.2,p.2.1.1),(p.2.2.2,p.2.2.1)),p.1)
  invFun p := (p.2,((p.1.1.2,p.1.1.1),(p.1.2.2,p.1.2.1)))
  left_inv _ := rfl
  right_inv _ := rfl

/-
Mathematical definition (normal notation): Exchange the two sides and reverse the column-side coordinates:

((x,u),(y,v))↔((v,y),(x,u)).

This is a bijection, so finite uniform averages are preserved.
-/
def partialColumnPairTranspose : ((X × U) × (Y × V)) ≃ ((V × Y) × (X × U)) where
  toFun p := ((p.2.2,p.2.1),p.1)
  invFun p := (p.2,(p.1.2,p.1.1))
  left_inv _ := rfl
  right_inv _ := rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K ∈ (X × U) → (Y × V) → ℝ; B ∈ ℝ, assume 0 ≤ B; ∀ x, y, |K(x, y)| ≤ B. Then

𝔼_(p ∈ ((X × U) × (X × U)) × ((Y × V) × (Y × V))) [{ |cornerProduct(K, p)| if (((p)₂)₁)₂ = (((p)₂)₂)₂,; 0 otherwise }] ≤ (|V|)⁻¹ · B² · 𝔼_(p ∈ (X × U) × (Y × V)) [(K((p)₁, (p)₂))²].
-/
theorem partial_column_collision_energy_bound (K : (X × U) → (Y × V) → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hK : ∀ x y, |K x y| ≤ B) :
    uavg (fun p : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
      if p.2.1.2 = p.2.2.2 then |cornerProduct K p| else 0) ≤
      (Fintype.card V : ℝ)⁻¹ * B ^ 2 *
        uavg (fun p : (X × U) × (Y × V) => K p.1 p.2 ^ 2) := by
  let K' := fun (v : V × Y) (x : X × U) => K x (v.2,v.1)
  have h := partial_row_collision_energy_bound K' B hB (fun x y => hK y (x.2,x.1))
  have he := uavg_equiv
    (partialColumnTranspose (X := X) (U := U) (Y := Y) (V := V))
    (fun p : ((V × Y) × (V × Y)) × ((X × U) × (X × U)) =>
      if p.1.1.1 = p.1.2.1 then |cornerProduct K' p| else 0)
  have hp (p : ((X × U) × (X × U)) × ((Y × V) × (Y × V))) :
      cornerProduct K' (partialColumnTranspose p) = cornerProduct K p := by
    dsimp [partialColumnTranspose, cornerProduct, K']
    ring
  change (uavg (fun p : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
    if p.2.1.2 = p.2.2.2 then |cornerProduct K' (partialColumnTranspose p)| else 0)) = _ at he
  simp only [hp] at he
  rw [← he] at h
  have hm := uavg_equiv
    (partialColumnPairTranspose (X := X) (U := U) (Y := Y) (V := V))
    (fun p : (V × Y) × (X × U) => K' p.1 p.2 ^ 2)
  exact h.trans_eq (by rw [← hm]; rfl)

/-- The main rank-(2,2) term excludes only the old-row collision and the new-column collision. Removing those exclusions retains the squared-entry energy instead of paying a fourth power of the entry bound. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K ∈ (X × U) → (Y × V) → ℝ; B ∈ ℝ, assume 0 ≤ B; ∀ x, y, |K(x, y)| ≤ B. Then

𝔼_(p ∈ ((X × U) × (X × U)) × ((Y × V) × (Y × V))) [{ |cornerProduct(K, p)| if (((p)₁)₁)₁ = (((p)₁)₂)₁ ∨ (((p)₂)₁)₂ = (((p)₂)₂)₂,; 0 otherwise }] ≤ ((|X|)⁻¹ + (|V|)⁻¹) · B² · 𝔼_(p ∈ (X × U) × (Y × V)) [(K((p)₁, (p)₂))²].
-/
theorem partial_collision_energy_bound (K : (X × U) → (Y × V) → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hK : ∀ x y, |K x y| ≤ B) :
    uavg (fun p : ((X × U) × (X × U)) × ((Y × V) × (Y × V)) =>
      if p.1.1.1 = p.1.2.1 ∨ p.2.1.2 = p.2.2.2 then |cornerProduct K p| else 0) ≤
      ((Fintype.card X : ℝ)⁻¹ + (Fintype.card V : ℝ)⁻¹) * B ^ 2 *
        uavg (fun p : (X × U) × (Y × V) => K p.1 p.2 ^ 2) := by
  have hp (p : ((X × U) × (X × U)) × ((Y × V) × (Y × V))) :
      (if p.1.1.1 = p.1.2.1 ∨ p.2.1.2 = p.2.2.2 then |cornerProduct K p| else 0) ≤
        (if p.1.1.1 = p.1.2.1 then |cornerProduct K p| else 0) +
        (if p.2.1.2 = p.2.2.2 then |cornerProduct K p| else 0) := by
    split_ifs <;> simp_all [abs_nonneg]
  have h := uavg_mono hp
  rw [uavg_add] at h
  exact h.trans ((add_le_add (partial_row_collision_energy_bound K B hB hK)
    (partial_column_collision_energy_bound K B hB hK)).trans_eq (by ring))

section Double

variable {R S : Type*} [Fintype R] [Fintype S] [Nonempty R] [Nonempty S]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ R → S → ℝ, we have

𝔼_(p ∈ (R × R) × (S × S)) [{ f(((p)₁)₁, ((p)₂)₁) if ((p)₁)₁ = ((p)₁)₂ ∧ ((p)₂)₁ = ((p)₂)₂,; 0 otherwise }] = ((|R| · |S|))⁻¹ · 𝔼_(p ∈ R × S) [f((p)₁, (p)₂)].
-/
theorem double_collision_corner_average (f : R → S → ℝ) :
    uavg (fun p : (R × R) × (S × S) =>
      if p.1.1 = p.1.2 ∧ p.2.1 = p.2.2 then f p.1.1 p.2.1 else 0) =
      ((Fintype.card R : ℝ) * Fintype.card S)⁻¹ * uavg (fun p : R × S => f p.1 p.2) := by
  simp only [uavg, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type, ite_and]
  have hsum : (∑ a : R, ∑ b : R, ∑ c : S, ∑ d : S,
      if a = b then (if c = d then f a c else 0) else 0) = ∑ a : R, ∑ c : S, f a c := by
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  rw [hsum]
  ring

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K ∈ R → S → ℝ; B ∈ ℝ, assume 0 ≤ B; ∀ r, s, |K(r, s)| ≤ B. Then

𝔼_(p ∈ (R × R) × (S × S)) [{ |cornerProduct(K, p)| if ((p)₁)₁ = ((p)₁)₂ ∧ ((p)₂)₁ = ((p)₂)₂,; 0 otherwise }] ≤ ((|R| · |S|))⁻¹ · B² · 𝔼_(p ∈ R × S) [(K((p)₁, (p)₂))²].
-/
theorem double_collision_energy_bound (K : R → S → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hK : ∀ r s, |K r s| ≤ B) :
    uavg (fun p : (R × R) × (S × S) =>
      if p.1.1 = p.1.2 ∧ p.2.1 = p.2.2 then |cornerProduct K p| else 0) ≤
      ((Fintype.card R : ℝ) * Fintype.card S)⁻¹ * B ^ 2 *
        uavg (fun p : R × S => K p.1 p.2 ^ 2) := by
  have hp (p : (R × R) × (S × S)) :
      (if p.1.1 = p.1.2 ∧ p.2.1 = p.2.2 then |cornerProduct K p| else 0) ≤
        B ^ 2 * (if p.1.1 = p.1.2 ∧ p.2.1 = p.2.2 then K p.1.1 p.2.1 ^ 2 else 0) := by
    by_cases h : p.1.1 = p.1.2 ∧ p.2.1 = p.2.2
    · rw [if_pos h, if_pos h]
      unfold cornerProduct
      rw [← h.1, ← h.2]
      have hs := (sq_le_sq₀ (abs_nonneg _) hB).2 (hK p.1.1 p.2.1)
      have he : K p.1.1 p.2.1 * K p.1.1 p.2.1 * K p.1.1 p.2.1 * K p.1.1 p.2.1 =
          K p.1.1 p.2.1 ^ 2 * K p.1.1 p.2.1 ^ 2 := by ring
      rw [he, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (by simpa only [sq_abs] using hs)
        (sq_nonneg (K p.1.1 p.2.1))
    · simp [h]
  have h := uavg_mono hp
  rw [uavg_const_mul, double_collision_corner_average (fun r s => K r s ^ 2)] at h
  exact h.trans_eq (by ring)

end Double

end

end CircuitCompiler.RefreshAnalysis
