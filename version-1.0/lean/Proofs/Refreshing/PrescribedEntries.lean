import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Counting independent binary entry prescriptions

The coordinate-counting step behind the prescribed rows and columns lemma. The reduction from arbitrary independent linear constraints to these coordinate prescriptions is a separate change-of-basis argument.
-/

noncomputable section

namespace RefreshingProof

/-- A function whose prescribed coordinates are fixed is exactly a free function on the remaining coordinates. This is an explicit bijection. -/
def fixedCoordinatesEquiv {I A : Type*} [DecidableEq I] (s : Finset I) (a : I → A) :
    {f : I → A // ∀ i ∈ s, f i = a i} ≃ ({i : I // i ∉ s} → A) where
  toFun f i := f.val i.val
  invFun g := ⟨fun i => if hi : i ∈ s then a i else g ⟨i, hi⟩, by
    intro i hi
    simp [hi]⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · simp [hi, f.property i hi]
    · simp [hi]
  right_inv g := by
    funext i
    simp [i.property]

/-- Each unprescribed bit is independent: there are exactly 2^(|I|-|s|) binary assignments satisfying a fixed set of coordinate prescriptions. -/
theorem card_fixed_binary_coordinates {I : Type*} [Fintype I] [DecidableEq I]
    (s : Finset I) (a : I → ZMod 2) :
    Fintype.card {f : I → ZMod 2 // ∀ i ∈ s, f i = a i} =
      2 ^ (Fintype.card I - s.card) := by
  rw [Fintype.card_congr (fixedCoordinatesEquiv s a), Fintype.card_fun]
  simp [Fintype.card_subtype_compl, ZMod.card]

/-- Fixing rows R and columns C leaves precisely the rectangle Rᶜ×Cᶜ free. -/
def fixedRowsColumnsEquiv {I J A : Type*} [DecidableEq I] [DecidableEq J]
    (rows : Finset I) (cols : Finset J) (a : I → J → A) :
    {M : I → J → A // ∀ i j, i ∈ rows ∨ j ∈ cols → M i j = a i j} ≃
      ({i : I // i ∉ rows} → {j : J // j ∉ cols} → A) where
  toFun M i j := M.val i.val j.val
  invFun f := ⟨fun i j => if hi : i ∈ rows then a i j
      else if hj : j ∈ cols then a i j else f ⟨i, hi⟩ ⟨j, hj⟩, by
    intro i j h
    rcases h with hi | hj
    · simp [hi]
    · simp [hj]⟩
  left_inv M := by
    apply Subtype.ext
    funext i j
    by_cases hi : i ∈ rows
    · simp [hi, M.property i j (Or.inl hi)]
    · by_cases hj : j ∈ cols
      · simp [hi, hj, M.property i j (Or.inr hj)]
      · simp [hi, hj]
  right_inv f := by
    funext i j
    simp [i.property, j.property]

/-- Exactly (|I|-|R|)(|J|-|C|) binary matrix entries remain free after prescribing compatible complete rows and complete columns. -/
theorem card_fixed_binary_rows_columns {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (rows : Finset I) (cols : Finset J) (a : I → J → ZMod 2) :
    Fintype.card {M : I → J → ZMod 2 //
      ∀ i j, i ∈ rows ∨ j ∈ cols → M i j = a i j} =
      2 ^ ((Fintype.card I - rows.card) * (Fintype.card J - cols.card)) := by
  rw [Fintype.card_congr (fixedRowsColumnsEquiv rows cols a)]
  simp [Fintype.card_subtype_compl, ZMod.card, ← pow_mul, mul_comm]

end RefreshingProof
