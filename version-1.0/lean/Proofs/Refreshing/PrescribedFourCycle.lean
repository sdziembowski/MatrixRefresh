import Proofs.Refreshing.RefreshTable
import Proofs.Refreshing.PrescribedLinear
import Proofs.Refreshing.FourCycleBounds
import Proofs.Refreshing.ZeroExtension

/-!
# Exact unrestricted refreshing four-cycle expansion

All identities retain the signed product of four table entries. No absolute value is taken before the rank cases have been separated.
-/

noncomputable section
open scoped BigOperators Matrix

namespace RefreshingProof
open Refreshing

/-- The signed product at one rectangle of the extended table. -/
def extendedCycleProduct {n : ℕ}
    (F : Local.Table (ExtendedSharePair n) (ExtendedSharePair n))
    (l₁ l₂ : Share n) (u₁ u₂ : Refreshing.Vector n)
    (r₁ r₂ : Share n) (v₁ v₂ : Refreshing.Vector n) : ℝ :=
  F (l₁, u₁) (r₁, v₁) * F (l₁, u₁) (r₂, v₂) *
    F (l₂, u₂) (r₁, v₁) * F (l₂, u₂) (r₂, v₂)

/-- Four copies of sqrt(Q) contribute exactly Q², and the two repeated column equations are each imposed once. -/
theorem unrestrictedRefreshTable_cycle_product {n : ℕ}
    (F : Local.Table (ExtendedSharePair n) (ExtendedSharePair n)) (A : BinaryMatrix n)
    (l₁ l₂ : Share n) (rr₁ rr₂ : ExtendedSharePair n) :
    unrestrictedRefreshTable F A l₁ rr₁ * unrestrictedRefreshTable F A l₁ rr₂ *
      unrestrictedRefreshTable F A l₂ rr₁ * unrestrictedRefreshTable F A l₂ rr₂ =
      if A *ᵥ rr₁.2 = rr₁.1.val ∧ A *ᵥ rr₂.2 = rr₂.1.val then
        ((2 : ℝ) ^ n) ^ 2 * extendedCycleProduct F l₁ l₂
          (l₁.val ᵥ* A) (l₂.val ᵥ* A) rr₁.1 rr₂.1 rr₁.2 rr₂.2 else 0 := by
  have hroot : Real.sqrt ((2 : ℝ) ^ n) ^ 4 = ((2 : ℝ) ^ n) ^ 2 := by
    calc
      _ = (Real.sqrt ((2 : ℝ) ^ n) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity)]
  by_cases h₁ : A *ᵥ rr₁.2 = rr₁.1.val <;> by_cases h₂ : A *ᵥ rr₂.2 = rr₂.1.val
  · simp only [unrestrictedRefreshTable, h₁, h₂, and_self, ite_true, extendedCycleProduct]
    calc
      _ = Real.sqrt ((2 : ℝ) ^ n) ^ 4 *
          (F (l₁, l₁.val ᵥ* A) rr₁ * F (l₁, l₁.val ᵥ* A) rr₂ *
            F (l₂, l₂.val ᵥ* A) rr₁ * F (l₂, l₂.val ᵥ* A) rr₂) := by ring
      _ = _ := by rw [hroot]
  all_goals simp [unrestrictedRefreshTable, h₁, h₂]

/-- Inserting the two prescribed output rows is an exact finite delta identity. -/
theorem sum_prescribedCycleOutputs {n : ℕ}
    (F : Local.Table (ExtendedSharePair n) (ExtendedSharePair n)) (A : BinaryMatrix n)
    (l₁ l₂ r₁ r₂ : Share n) (v₁ v₂ : Refreshing.Vector n) :
    (∑ u₁ : Refreshing.Vector n, ∑ u₂ : Refreshing.Vector n,
      if prescribedLinearRowsCols ![l₁.val, l₂.val] ![v₁, v₂]
          ![u₁, u₂] ![r₁.val, r₂.val] A then
        extendedCycleProduct F l₁ l₂ u₁ u₂ r₁ r₂ v₁ v₂ else 0) =
      if A *ᵥ v₁ = r₁.val ∧ A *ᵥ v₂ = r₂.val then
        extendedCycleProduct F l₁ l₂ (l₁.val ᵥ* A) (l₂.val ᵥ* A) r₁ r₂ v₁ v₂ else 0 := by
  classical
  by_cases h₁ : A *ᵥ v₁ = r₁.val <;> by_cases h₂ : A *ᵥ v₂ = r₂.val
  all_goals simp [prescribedLinearRowsCols, Fin.forall_fin_two, h₁, h₂,
    ite_and, Finset.sum_ite_irrel]

/-- Averaging one prescribed-output cycle yields its actual event probability, while keeping the signed cycle product unchanged. -/
theorem average_prescribedCycleOutput {n : ℕ}
    (F : Local.Table (ExtendedSharePair n) (ExtendedSharePair n))
    (l₁ l₂ r₁ r₂ : Share n) (u₁ u₂ v₁ v₂ : Refreshing.Vector n) :
    Local.average (fun A : BinaryMatrix n =>
      if prescribedLinearRowsCols ![l₁.val, l₂.val] ![v₁, v₂]
          ![u₁, u₂] ![r₁.val, r₂.val] A then
        extendedCycleProduct F l₁ l₂ u₁ u₂ r₁ r₂ v₁ v₂ else 0) =
      prescribedLinearProbability ![l₁.val, l₂.val] ![v₁, v₂]
        ![u₁, u₂] ![r₁.val, r₂.val] *
          extendedCycleProduct F l₁ l₂ u₁ u₂ r₁ r₂ v₁ v₂ := by
  classical
  rw [← uniformPMF_expectation]
  unfold prescribedLinearProbability
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro A _
  split_ifs <;> simp

/-- Matrix averaging commutes with insertion of the two output rows. -/
theorem average_cycle_columns {n : ℕ}
    (F : Local.Table (ExtendedSharePair n) (ExtendedSharePair n))
    (l₁ l₂ r₁ r₂ : Share n) (v₁ v₂ : Refreshing.Vector n) :
    Local.average (fun A : BinaryMatrix n =>
      if A *ᵥ v₁ = r₁.val ∧ A *ᵥ v₂ = r₂.val then
        extendedCycleProduct F l₁ l₂ (l₁.val ᵥ* A) (l₂.val ᵥ* A) r₁ r₂ v₁ v₂ else 0) =
      ∑ u₁ : Refreshing.Vector n, ∑ u₂ : Refreshing.Vector n,
        prescribedLinearProbability ![l₁.val, l₂.val] ![v₁, v₂]
          ![u₁, u₂] ![r₁.val, r₂.val] * extendedCycleProduct F l₁ l₂ u₁ u₂ r₁ r₂ v₁ v₂ := by
  classical
  calc
    _ = Local.average (fun A : BinaryMatrix n =>
        ∑ u₁ : Refreshing.Vector n, ∑ u₂ : Refreshing.Vector n,
          if prescribedLinearRowsCols ![l₁.val, l₂.val] ![v₁, v₂]
              ![u₁, u₂] ![r₁.val, r₂.val] A then
            extendedCycleProduct F l₁ l₂ u₁ u₂ r₁ r₂ v₁ v₂ else 0) := by
      apply Local.average_congr
      intro A
      exact (sum_prescribedCycleOutputs F A l₁ l₂ r₁ r₂ v₁ v₂).symm
    _ = _ := by simp only [Local.average_sum, average_prescribedCycleOutput]

/-- The row and column endpoint coordinates needed to expand one unrestricted refresh four-cycle. -/
abbrev RefreshCycleInput (n : ℕ) :=
  (Share n × Share n) × (ExtendedSharePair n × ExtendedSharePair n)

/-- The exact unrestricted-cycle expansion with output rows inserted as sums. -/
theorem unrestricted_fourCycle_prescribed_sum {n : ℕ}
    (F : Local.Table (ExtendedSharePair n) (ExtendedSharePair n)) :
    Local.average (fun A : BinaryMatrix n => Local.fourCycle (unrestrictedRefreshTable F A)) =
      ((2 : ℝ) ^ n) ^ 2 * Local.average (fun p : RefreshCycleInput n =>
        ∑ u₁ : Refreshing.Vector n, ∑ u₂ : Refreshing.Vector n,
          prescribedLinearProbability ![p.1.1.val, p.1.2.val] ![p.2.1.2, p.2.2.2]
            ![u₁, u₂] ![p.2.1.1.val, p.2.2.1.val] *
          extendedCycleProduct F p.1.1 p.1.2 u₁ u₂ p.2.1.1 p.2.2.1 p.2.1.2 p.2.2.2) := by
  classical
  calc
    _ = Local.average (fun A : BinaryMatrix n => Local.average (fun p : RefreshCycleInput n =>
        unrestrictedRefreshTable F A p.1.1 p.2.1 * unrestrictedRefreshTable F A p.1.1 p.2.2 *
        unrestrictedRefreshTable F A p.1.2 p.2.1 * unrestrictedRefreshTable F A p.1.2 p.2.2)) := by
      apply Local.average_congr
      intro A
      exact Local.fourCycle_as_product _
    _ = Local.average (fun p : RefreshCycleInput n => Local.average (fun A : BinaryMatrix n =>
        unrestrictedRefreshTable F A p.1.1 p.2.1 * unrestrictedRefreshTable F A p.1.1 p.2.2 *
        unrestrictedRefreshTable F A p.1.2 p.2.1 * unrestrictedRefreshTable F A p.1.2 p.2.2)) :=
      Local.average_comm _
    _ = _ := by
      rw [← Local.average_smul]
      apply Local.average_congr
      intro p
      calc
        _ = ((2 : ℝ) ^ n) ^ 2 * Local.average (fun A : BinaryMatrix n =>
            if A *ᵥ p.2.1.2 = p.2.1.1.val ∧ A *ᵥ p.2.2.2 = p.2.2.1.val then
              extendedCycleProduct F p.1.1 p.1.2 (p.1.1.val ᵥ* A) (p.1.2.val ᵥ* A)
                p.2.1.1 p.2.2.1 p.2.1.2 p.2.2.2 else 0) := by
          rw [← Local.average_smul]
          apply Local.average_congr
          intro A
          rw [unrestrictedRefreshTable_cycle_product]
          split_ifs <;> simp
        _ = _ := by rw [average_cycle_columns]

/-- Recover a counting sum from the normalized finite average. -/
theorem sum_eq_card_mul_average {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) :
    (∑ x, f x) = (Fintype.card X : ℝ) * Local.average f := by
  have hc : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold Local.average
  field_simp

/-- Two inserted unrestricted rows contribute exactly Q² to normalization. -/
theorem sum_vector_pair_eq {n : ℕ} (f : Refreshing.Vector n → Refreshing.Vector n → ℝ) :
    (∑ u₁ : Refreshing.Vector n, ∑ u₂ : Refreshing.Vector n, f u₁ u₂) =
      ((2 : ℝ) ^ n) ^ 2 * Local.average (fun u₁ => Local.average (f u₁)) := by
  have hcard : (Fintype.card (Refreshing.Vector n) : ℝ) = (2 : ℝ) ^ n := by
    simp [Refreshing.Vector, Bit, ZMod.card]
  simp_rw [sum_eq_card_mul_average, hcard]
  rw [Local.average_smul]
  ring

/-- Reorder the eight independent indices into the four grouped coordinates. -/
def prescribedCycleIndexEquiv (n : ℕ) :
    (RefreshCycleInput n × (Refreshing.Vector n × Refreshing.Vector n)) ≃
      ((ExtendedSharePair n × ExtendedSharePair n) × (ExtendedSharePair n × ExtendedSharePair n)) where
  toFun z := (((z.1.1.1, z.2.1), (z.1.1.2, z.2.2)), z.1.2)
  invFun z := (((z.1.1.1, z.1.2.1), z.2), (z.1.1.2, z.1.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual prescribed-matrix event probability for four grouped coordinates. -/
def cyclePrescriptionProbability {n : ℕ}
    (x₁ x₂ y₁ y₂ : ExtendedSharePair n) : ℝ :=
  prescribedLinearProbability ![x₁.1.val, x₂.1.val] ![y₁.2, y₂.2]
    ![x₁.2, x₂.2] ![y₁.1.val, y₂.1.val]

/-- The paper's exact prescribed-matrix expansion, with all eight variables independent and uniformly averaged over their specified domains. -/
theorem unrestricted_fourCycle_prescribed_expansion {n : ℕ}
    (F : Local.Table (ExtendedSharePair n) (ExtendedSharePair n)) :
    Local.average (fun A : BinaryMatrix n => Local.fourCycle (unrestrictedRefreshTable F A)) =
      ((2 : ℝ) ^ n) ^ 4 * Local.average (fun z :
          (ExtendedSharePair n × ExtendedSharePair n) × (ExtendedSharePair n × ExtendedSharePair n) =>
        cyclePrescriptionProbability z.1.1 z.1.2 z.2.1 z.2.2 *
          (F z.1.1 z.2.1 * F z.1.1 z.2.2 * F z.1.2 z.2.1 * F z.1.2 z.2.2)) := by
  rw [unrestricted_fourCycle_prescribed_sum]
  simp_rw [sum_vector_pair_eq]
  rw [Local.average_smul]
  let H := fun z : (ExtendedSharePair n × ExtendedSharePair n) ×
      (ExtendedSharePair n × ExtendedSharePair n) =>
    cyclePrescriptionProbability z.1.1 z.1.2 z.2.1 z.2.2 *
      (F z.1.1 z.2.1 * F z.1.1 z.2.2 * F z.1.2 z.2.1 * F z.1.2 z.2.2)
  have hperm : Local.average (fun p : RefreshCycleInput n =>
      Local.average (fun u₁ : Refreshing.Vector n => Local.average (fun u₂ : Refreshing.Vector n =>
        prescribedLinearProbability ![p.1.1.val, p.1.2.val] ![p.2.1.2, p.2.2.2]
          ![u₁, u₂] ![p.2.1.1.val, p.2.2.1.val] *
        extendedCycleProduct F p.1.1 p.1.2 u₁ u₂ p.2.1.1 p.2.2.1 p.2.1.2 p.2.2.2))) =
      Local.average H := by
    calc
      _ = Local.average (fun z : RefreshCycleInput n ×
          (Refreshing.Vector n × Refreshing.Vector n) => H (prescribedCycleIndexEquiv n z)) := by
        conv_rhs => rw [Local.average_product]
        apply Local.average_congr
        intro p
        conv_rhs => rw [Local.average_product]
        apply Local.average_congr
        intro u₁
        apply Local.average_congr
        intro u₂
        rfl
      _ = Local.average H := Local.average_equiv (prescribedCycleIndexEquiv n) H
  rw [hperm]
  change ((2 : ℝ) ^ n) ^ 2 * (((2 : ℝ) ^ n) ^ 2 * Local.average H) =
    ((2 : ℝ) ^ n) ^ 4 * Local.average H
  ring

/-- At a nonzero signed four-cycle, zero extension forces both new columns nonzero, and consistency support enforces all four pairing constraints. -/
theorem cyclePrescriptionProbability_of_nonzero_cycle {n : ℕ}
    (F : Local.Table (ExtendedSharePair n) (ExtendedSharePair n))
    (hz : ∀ x y, y.2 = 0 → F x y = 0)
    (hs : ∀ x y, x.1.val ⬝ᵥ y.1.val ≠ x.2 ⬝ᵥ y.2 → F x y = 0)
    (x₁ x₂ y₁ y₂ : ExtendedSharePair n)
    (hC : F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂ ≠ 0) :
    cyclePrescriptionProbability x₁ x₂ y₁ y₂ =
      if (x₁.1 ≠ x₂.1 ∨ x₁ = x₂) ∧ (y₁.2 ≠ y₂.2 ∨ y₁ = y₂) then
        (2 : ℝ) ^ ((if x₁.1 = x₂.1 then 1 else 2) * (if y₁.2 = y₂.2 then 1 else 2)) /
          ((2 : ℝ) ^ n) ^ ((if x₁.1 = x₂.1 then 1 else 2) +
            (if y₁.2 = y₂.2 then 1 else 2)) else 0 := by
  classical
  have h₁₁ : F x₁ y₁ ≠ 0 := by intro h; exact hC (by simp [h])
  have h₁₂ : F x₁ y₂ ≠ 0 := by intro h; exact hC (by simp [h])
  have h₂₁ : F x₂ y₁ ≠ 0 := by intro h; exact hC (by simp [h])
  have h₂₂ : F x₂ y₂ ≠ 0 := by intro h; exact hC (by simp [h])
  have hv₁ : y₁.2 ≠ 0 := fun h => h₁₁ (hz x₁ y₁ h)
  have hv₂ : y₂.2 ≠ 0 := fun h => h₁₂ (hz x₁ y₂ h)
  have hc₁₁ : x₁.2 ⬝ᵥ y₁.2 = x₁.1.val ⬝ᵥ y₁.1.val := by
    by_contra h
    exact h₁₁ (hs x₁ y₁ (Ne.symm h))
  have hc₁₂ : x₁.2 ⬝ᵥ y₂.2 = x₁.1.val ⬝ᵥ y₂.1.val := by
    by_contra h
    exact h₁₂ (hs x₁ y₂ (Ne.symm h))
  have hc₂₁ : x₂.2 ⬝ᵥ y₁.2 = x₂.1.val ⬝ᵥ y₁.1.val := by
    by_contra h
    exact h₂₁ (hs x₂ y₁ (Ne.symm h))
  have hc₂₂ : x₂.2 ⬝ᵥ y₂.2 = x₂.1.val ⬝ᵥ y₂.1.val := by
    by_contra h
    exact h₂₂ (hs x₂ y₂ (Ne.symm h))
  let v₁ : Share n := ⟨y₁.2, hv₁⟩
  let v₂ : Share n := ⟨y₂.2, hv₂⟩
  have hp := prescribedLinearProbability_nonzeroPairs x₁.1 x₂.1 v₁ v₂
    ![x₁.2, x₂.2] ![y₁.1.val, y₂.1.val]
  have hrow : (x₁.1 = x₂.1 → x₁.2 = x₂.2) ↔ (x₁.1 ≠ x₂.1 ∨ x₁ = x₂) := by
    constructor
    · intro h
      by_cases he : x₁.1 = x₂.1
      · exact Or.inr (Prod.ext he (h he))
      · exact Or.inl he
    · rintro (hne | he) h
      · exact False.elim (hne h)
      · exact congrArg Prod.snd he
  have hcol : (y₁.2 = y₂.2 → y₁.1 = y₂.1) ↔ (y₁.2 ≠ y₂.2 ∨ y₁ = y₂) := by
    constructor
    · intro h
      by_cases he : y₁.2 = y₂.2
      · exact Or.inr (Prod.ext (h he) he)
      · exact Or.inl he
    · rintro (hne | he) h
      · exact False.elim (hne h)
      · exact congrArg Prod.fst he
  have hval : (y₁.1.val = y₂.1.val) ↔ y₁.1 = y₂.1 :=
    ⟨Subtype.ext, congrArg Subtype.val⟩
  simpa [cyclePrescriptionProbability, nonzeroPairCompatible, nonzeroPairRank,
    v₁, v₂, Fin.forall_fin_two, hc₁₁, hc₁₂, hc₂₁, hc₂₂, hval, hrow, hcol] using hp

/-- Exact separation into the four rank cases. The entire signed four-cycle product is retained in each case; no pointwise absolute-value bound is used. -/
theorem cyclePrescription_four_rank_identity {n : ℕ}
    (F : Local.Table (ExtendedSharePair n) (ExtendedSharePair n))
    (hz : ∀ x y, y.2 = 0 → F x y = 0)
    (hs : ∀ x y, x.1.val ⬝ᵥ y.1.val ≠ x.2 ⬝ᵥ y.2 → F x y = 0)
    (x₁ x₂ y₁ y₂ : ExtendedSharePair n) :
    ((2 : ℝ) ^ n) ^ 4 * cyclePrescriptionProbability x₁ x₂ y₁ y₂ *
        (F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂) =
      (if x₁.1 ≠ x₂.1 ∧ y₁.2 ≠ y₂.2 then
        16 * (F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂) else 0) +
      (if x₁ = x₂ ∧ y₁.2 ≠ y₂.2 then
        4 * (2 : ℝ) ^ n * (F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂) else 0) +
      (if x₁.1 ≠ x₂.1 ∧ y₁ = y₂ then
        4 * (2 : ℝ) ^ n * (F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂) else 0) +
      (if x₁ = x₂ ∧ y₁ = y₂ then
        2 * ((2 : ℝ) ^ n) ^ 2 * (F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂) else 0) := by
  classical
  by_cases hC : F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂ = 0
  · simp [hC]
  rw [cyclePrescriptionProbability_of_nonzero_cycle F hz hs x₁ x₂ y₁ y₂ hC]
  by_cases hL : x₁.1 = x₂.1 <;> by_cases hV : y₁.2 = y₂.2 <;>
    by_cases hX : x₁ = x₂ <;> by_cases hY : y₁ = y₂
  all_goals first
    | exact False.elim (hL (congrArg Prod.fst hX))
    | exact False.elim (hV (congrArg Prod.snd hY))
    | simp [hL, hV, hX, hY]
      <;> field_simp
      <;> norm_num
      <;> ring

/-- After rank separation, the two mixed-rank restrictions can be dropped because their complete contributions are products of squares. -/
theorem cyclePrescription_four_rank_le {n : ℕ}
    (F : Local.Table (ExtendedSharePair n) (ExtendedSharePair n))
    (hz : ∀ x y, y.2 = 0 → F x y = 0)
    (hs : ∀ x y, x.1.val ⬝ᵥ y.1.val ≠ x.2 ⬝ᵥ y.2 → F x y = 0)
    (x₁ x₂ y₁ y₂ : ExtendedSharePair n) :
    ((2 : ℝ) ^ n) ^ 4 * cyclePrescriptionProbability x₁ x₂ y₁ y₂ *
        (F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂) ≤
      16 * (if x₁.1 ≠ x₂.1 ∧ y₁.2 ≠ y₂.2 then
        F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂ else 0) +
      (4 * (2 : ℝ) ^ n) * (if x₁ = x₂ then F x₁ y₁ ^ 2 * F x₁ y₂ ^ 2 else 0) +
      (4 * (2 : ℝ) ^ n) * (if y₁ = y₂ then F x₁ y₁ ^ 2 * F x₂ y₁ ^ 2 else 0) +
      (2 * ((2 : ℝ) ^ n) ^ 2) * (if x₁ = x₂ ∧ y₁ = y₂ then F x₁ y₁ ^ 4 else 0) := by
  classical
  rw [cyclePrescription_four_rank_identity F hz hs]
  have hmain : (if x₁.1 ≠ x₂.1 ∧ y₁.2 ≠ y₂.2 then
      16 * (F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂) else 0) =
      16 * (if x₁.1 ≠ x₂.1 ∧ y₁.2 ≠ y₂.2 then
        F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂ else 0) := by
    split_ifs <;> simp
  have hrow : (if x₁ = x₂ ∧ y₁.2 ≠ y₂.2 then
      4 * (2 : ℝ) ^ n * (F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂) else 0) ≤
      (4 * (2 : ℝ) ^ n) * (if x₁ = x₂ then F x₁ y₁ ^ 2 * F x₁ y₂ ^ 2 else 0) := by
    by_cases hX : x₁ = x₂
    · subst x₂
      by_cases hV : y₁.2 ≠ y₂.2
      · simp [hV, pow_two, mul_assoc, mul_left_comm, mul_comm]
      · simp only [hV, and_false, ite_false, ite_true]
        positivity
    · simp [hX]
  have hcol : (if x₁.1 ≠ x₂.1 ∧ y₁ = y₂ then
      4 * (2 : ℝ) ^ n * (F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂) else 0) ≤
      (4 * (2 : ℝ) ^ n) * (if y₁ = y₂ then F x₁ y₁ ^ 2 * F x₂ y₁ ^ 2 else 0) := by
    by_cases hY : y₁ = y₂
    · subst y₂
      by_cases hL : x₁.1 ≠ x₂.1
      · simp [hL, pow_two, mul_assoc, mul_left_comm, mul_comm]
      · simp only [hL, false_and, ite_false, ite_true]
        positivity
    · simp [hY]
  have hcorner : (if x₁ = x₂ ∧ y₁ = y₂ then
      2 * ((2 : ℝ) ^ n) ^ 2 * (F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂) else 0) =
      (2 * ((2 : ℝ) ^ n) ^ 2) * (if x₁ = x₂ ∧ y₁ = y₂ then F x₁ y₁ ^ 4 else 0) := by
    by_cases hX : x₁ = x₂ <;> by_cases hY : y₁ = y₂
    all_goals simp only [hX, hY, and_self, and_true, and_false, true_and, false_and,
      ite_true, ite_false] <;> first | subst_vars; ring | ring
  rw [hmain, hcorner]
  linarith

/-- Uniform averages commute with a constant zero-padded condition. -/
theorem average_ite_zero {X : Type*} [Fintype X] (p : Prop) [Decidable p] (f : X → ℝ) :
    Local.average (fun x => if p then f x else 0) = if p then Local.average f else 0 := by
  by_cases hp : p <;> simp [hp, Local.average]

/-- A grouped four-index average, without unfolding the grouped coordinate types. -/
theorem average_cycle_indices {X Y : Type*} [Fintype X] [Fintype Y]
    (f : (X × X) × (Y × Y) → ℝ) :
    Local.average f = Local.average (fun x₁ => Local.average (fun x₂ =>
      Local.average (fun y₁ => Local.average (fun y₂ => f ((x₁, x₂), (y₁, y₂)))))) := by
  simp only [Local.average_product]

/-- Exact normalization after a complete row collision. -/
theorem average_full_row_collision {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
    (F : Local.Table X Y) :
    Local.average (fun x₁ => Local.average (fun x₂ => Local.average (fun y₁ => Local.average (fun y₂ =>
      if x₁ = x₂ then F x₁ y₁ ^ 2 * F x₁ y₂ ^ 2 else 0)))) =
      (Fintype.card X : ℝ)⁻¹ * Local.average (fun x => (Local.average (fun y => F x y ^ 2)) ^ 2) := by
  classical
  simp only [average_ite_zero, Local.average_eq_indicator]
  rw [Local.average_smul]
  congr 1
  apply Local.average_congr
  intro x
  rw [pow_two, Local.average_mul_average]

/-- Exact normalization after a complete column collision. -/
theorem average_full_column_collision {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (F : Local.Table X Y) :
    Local.average (fun x₁ => Local.average (fun x₂ => Local.average (fun y₁ => Local.average (fun y₂ =>
      if y₁ = y₂ then F x₁ y₁ ^ 2 * F x₂ y₁ ^ 2 else 0)))) =
      (Fintype.card Y : ℝ)⁻¹ * Local.average (fun y => (Local.average (fun x => F x y ^ 2)) ^ 2) := by
  classical
  simp only [Local.average_eq_indicator, Local.average_smul]
  congr 1
  calc
    _ = Local.average (fun xx : X × X => Local.average (fun y =>
        F xx.1 y ^ 2 * F xx.2 y ^ 2)) := by
      conv_rhs => rw [Local.average_product]
    _ = Local.average (fun y => Local.average (fun xx : X × X =>
        F xx.1 y ^ 2 * F xx.2 y ^ 2)) := Local.average_comm _
    _ = _ := by
      apply Local.average_congr
      intro y
      rw [Local.average_product, pow_two, Local.average_mul_average]

/-- Exact normalization after both complete row and column collisions. -/
theorem average_full_corner_collision {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] (F : Local.Table X Y) :
    Local.average (fun x₁ => Local.average (fun x₂ => Local.average (fun y₁ => Local.average (fun y₂ =>
      if x₁ = x₂ ∧ y₁ = y₂ then F x₁ y₁ ^ 4 else 0)))) =
      (Fintype.card X : ℝ)⁻¹ * (Fintype.card Y : ℝ)⁻¹ *
        Local.average (fun x => Local.average (fun y => F x y ^ 4)) := by
  classical
  simp only [ite_and, average_ite_zero, Local.average_eq_indicator, Local.average_smul]
  ring

end RefreshingProof
