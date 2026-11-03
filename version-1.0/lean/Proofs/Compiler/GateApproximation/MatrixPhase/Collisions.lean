import Proofs.Compiler.GateApproximation.MatrixPhase.Moments



/-!
# Collision terms with their squared-entry energy retained

These finite averaging identities justify the exceptional-corner estimates used by the tensor operator four-cycle proof. They hold for signed real tables on arbitrary finite rectangular carriers.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

open scoped BigOperators Classical

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

/-- Conditioning a uniform row pair to coincide leaves each corner's row and column marginals uniform. The event itself costs `1/card X`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ X → Y → ℝ, we have

𝔼_(p ∈ (X × X) × (Y × Y)) [{ f(((p)₁)₁, ((p)₂)₁) if ((p)₁)₁ = ((p)₁)₂,; 0 otherwise }] = (|X|)⁻¹ · 𝔼_(p ∈ X × Y) [f((p)₁, (p)₂)].
-/
theorem row_collision_corner_average (f : X → Y → ℝ) :
    uavg (fun p : (X × X) × (Y × Y) =>
      if p.1.1 = p.1.2 then f p.1.1 p.2.1 else 0) =
      (Fintype.card X : ℝ)⁻¹ * uavg (fun p : X × Y => f p.1 p.2) := by
  simp only [uavg, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
  have hsum : (∑ a : X, ∑ b : X, ∑ c : Y, ∑ d : Y, if a = b then f a c else 0) =
      (Fintype.card Y : ℝ) * ∑ a : X, ∑ c : Y, f a c := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp_rw [mul_ite, mul_zero]
    simp [Finset.mul_sum]
  rw [hsum]
  have hx : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hy : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The same marginal identity for the second column of a corner product. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ X → Y → ℝ, we have

𝔼_(p ∈ (X × X) × (Y × Y)) [{ f(((p)₁)₁, ((p)₂)₂) if ((p)₁)₁ = ((p)₁)₂,; 0 otherwise }] = (|X|)⁻¹ · 𝔼_(p ∈ X × Y) [f((p)₁, (p)₂)].
-/
theorem row_collision_other_corner_average (f : X → Y → ℝ) :
    uavg (fun p : (X × X) × (Y × Y) =>
      if p.1.1 = p.1.2 then f p.1.1 p.2.2 else 0) =
      (Fintype.card X : ℝ)⁻¹ * uavg (fun p : X × Y => f p.1 p.2) := by
  have h := uavg_equiv (Equiv.prodCongr (Equiv.refl (X × X)) (Equiv.prodComm Y Y))
    (fun p : (X × X) × (Y × Y) => if p.1.1 = p.1.2 then f p.1.1 p.2.1 else 0)
  exact h.trans (row_collision_corner_average f)

/-- The real signed product around a four-cycle. -/
/-
Mathematical definition (normal notation): For K ∈ X → Y → ℝ; p ∈ (X × X) × (Y × Y), define

cornerProduct(K, p) := K(((p)₁)₁, ((p)₂)₁) · K(((p)₁)₂, ((p)₂)₁) · K(((p)₁)₂, ((p)₂)₂) · K(((p)₁)₁, ((p)₂)₂).
-/
def cornerProduct (K : X → Y → ℝ) (p : (X × X) × (Y × Y)) : ℝ :=
  K p.1.1 p.2.1 * K p.1.2 p.2.1 * K p.1.2 p.2.2 * K p.1.1 p.2.2

/-- Repeated rows cost `B² * L2² / card X`, not `B^4 / card X`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K ∈ X → Y → ℝ; B ∈ ℝ, assume 0 ≤ B; ∀ x, y, |K(x, y)| ≤ B. Then

𝔼_(p ∈ (X × X) × (Y × Y)) [{ |cornerProduct(K, p)| if ((p)₁)₁ = ((p)₁)₂,; 0 otherwise }] ≤ (|X|)⁻¹ · B² · 𝔼_(p ∈ X × Y) [(K((p)₁, (p)₂))²].
-/
theorem row_collision_energy_bound (K : X → Y → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hK : ∀ x y, |K x y| ≤ B) :
    uavg (fun p : (X × X) × (Y × Y) =>
      if p.1.1 = p.1.2 then |cornerProduct K p| else 0) ≤
      (Fintype.card X : ℝ)⁻¹ * B ^ 2 * uavg (fun p : X × Y => K p.1 p.2 ^ 2) := by
  have hpoint (p : (X × X) × (Y × Y)) :
      (if p.1.1 = p.1.2 then |cornerProduct K p| else 0) ≤
        B ^ 2 / 2 * ((if p.1.1 = p.1.2 then K p.1.1 p.2.1 ^ 2 else 0) +
          (if p.1.1 = p.1.2 then K p.1.1 p.2.2 ^ 2 else 0)) := by
    by_cases hp : p.1.1 = p.1.2
    · simp only [cornerProduct, ← hp, if_true]
      have h := four_entry_energy_bound (K p.1.1 p.2.1) (K p.1.1 p.2.1)
        (K p.1.1 p.2.2) (K p.1.1 p.2.2) B hB
        (hK _ _) (hK _ _) (hK _ _) (hK _ _)
      nlinarith
    · simp [hp]
  have h := uavg_mono hpoint
  rw [uavg_const_mul, uavg_add,
    row_collision_corner_average (fun x y => K x y ^ 2),
    row_collision_other_corner_average (fun x y => K x y ^ 2)] at h
  exact h.trans_eq (by ring)

/-- Transposing exchanges repeated-row and repeated-column contributions. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K ∈ X → Y → ℝ; B ∈ ℝ, assume 0 ≤ B; ∀ x, y, |K(x, y)| ≤ B. Then

𝔼_(p ∈ (X × X) × (Y × Y)) [{ |cornerProduct(K, p)| if ((p)₂)₁ = ((p)₂)₂,; 0 otherwise }] ≤ (|Y|)⁻¹ · B² · 𝔼_(p ∈ X × Y) [(K((p)₁, (p)₂))²].
-/
theorem column_collision_energy_bound (K : X → Y → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hK : ∀ x y, |K x y| ≤ B) :
    uavg (fun p : (X × X) × (Y × Y) =>
      if p.2.1 = p.2.2 then |cornerProduct K p| else 0) ≤
      (Fintype.card Y : ℝ)⁻¹ * B ^ 2 * uavg (fun p : X × Y => K p.1 p.2 ^ 2) := by
  have h := row_collision_energy_bound (fun y x => K x y) B hB (fun y x => hK x y)
  have he := uavg_equiv (Equiv.prodComm (X × X) (Y × Y))
    (fun p : (Y × Y) × (X × X) =>
      if p.1.1 = p.1.2 then |cornerProduct (fun y x => K x y) p| else 0)
  have hprod (p : (X × X) × (Y × Y)) :
      cornerProduct (fun y x => K x y) (p.2, p.1) = cornerProduct K p := by
    unfold cornerProduct
    ring
  change uavg (fun p : (X × X) × (Y × Y) =>
      if p.2.1 = p.2.2 then |cornerProduct (fun y x => K x y) (p.2, p.1)| else 0) = _ at he
  simp only [hprod] at he
  rw [← he] at h
  have havg : uavg (fun p : Y × X => K p.2 p.1 ^ 2) =
      uavg (fun p : X × Y => K p.1 p.2 ^ 2) :=
    by simpa only [Equiv.prodComm_apply, Prod.swap] using
      uavg_equiv (Equiv.prodComm Y X) (fun p : X × Y => K p.1 p.2 ^ 2)
  simpa only [havg] using h

/-- The union bound for either collision preserves the entry-energy factor. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K ∈ X → Y → ℝ; B ∈ ℝ, assume 0 ≤ B; ∀ x, y, |K(x, y)| ≤ B. Then

𝔼_(p ∈ (X × X) × (Y × Y)) [{ |cornerProduct(K, p)| if ((p)₁)₁ = ((p)₁)₂ ∨ ((p)₂)₁ = ((p)₂)₂,; 0 otherwise }] ≤ ((|X|)⁻¹ + (|Y|)⁻¹) · B² · 𝔼_(p ∈ X × Y) [(K((p)₁, (p)₂))²].
-/
theorem collision_energy_bound (K : X → Y → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hK : ∀ x y, |K x y| ≤ B) :
    uavg (fun p : (X × X) × (Y × Y) =>
      if p.1.1 = p.1.2 ∨ p.2.1 = p.2.2 then |cornerProduct K p| else 0) ≤
      ((Fintype.card X : ℝ)⁻¹ + (Fintype.card Y : ℝ)⁻¹) *
        B ^ 2 * uavg (fun p : X × Y => K p.1 p.2 ^ 2) := by
  have hp (p : (X × X) × (Y × Y)) :
      (if p.1.1 = p.1.2 ∨ p.2.1 = p.2.2 then |cornerProduct K p| else 0) ≤
        (if p.1.1 = p.1.2 then |cornerProduct K p| else 0) +
        (if p.2.1 = p.2.2 then |cornerProduct K p| else 0) := by
    split_ifs <;> simp_all [abs_nonneg]
  have h := uavg_mono hp
  rw [uavg_add] at h
  exact h.trans ((add_le_add (row_collision_energy_bound K B hB hK)
    (column_collision_energy_bound K B hB hK)).trans_eq (by ring))

end

end CircuitCompiler.RefreshAnalysis
