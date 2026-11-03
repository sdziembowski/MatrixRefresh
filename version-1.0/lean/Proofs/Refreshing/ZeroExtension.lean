import Proofs.Refreshing.LocalSVD
import Proofs.Refreshing.GramVariance
import Mathlib.Data.Fintype.BigOperators

/-!
# Probability normalization under extension by zero

These exact identities account for the factors q/Q when nonzero shares are extended to unrestricted binary vectors in the four-cycle calculation.
-/

noncomputable section
open scoped BigOperators

namespace RefreshingProof.Local

/-- A finite uniform average is unchanged by an equivalence of its carrier. -/
theorem average_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) : average (fun a => f (e a)) = average f := by
  unfold average
  rw [Fintype.card_congr e, Equiv.sum_comp e f]

/-- The squared normalized L₂ norm of a table is the uniform mean of its squared entries on the product carrier. -/
theorem normSq_as_product {X Y : Type*} [Fintype X] [Fintype Y] (F : Table X Y) :
    normSq F = average (fun xy : X × Y => F xy.1 xy.2 ^ 2) := by
  rw [average_product]
  simp only [normSq, pairing, pow_two]

/-- The four-cycle quantity is the uniform mean of the product of its four corner entries. -/
theorem fourCycle_as_product {X Y : Type*} [Fintype X] [Fintype Y] (F : Table X Y) :
    fourCycle F = average (fun p : (X × X) × (Y × Y) =>
      F p.1.1 p.2.1 * F p.1.1 p.2.2 * F p.1.2 p.2.1 * F p.1.2 p.2.2) := by
  simp only [average_product, fourCycle]

/-- The squared normalized L₂ norm is unchanged by independent equivalences of the row and column carriers. -/
theorem normSq_reindex {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (e : A ≃ B) (f : C ≃ D) (F : Table B D) :
    normSq (fun a c => F (e a) (f c)) = normSq F := by
  rw [normSq_as_product, normSq_as_product]
  exact average_equiv (e.prodCongr f) (fun xy : B × D => F xy.1 xy.2 ^ 2)

/-- The four-cycle quantity is unchanged by independent equivalences of the row and column carriers. -/
theorem fourCycle_reindex {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (e : A ≃ B) (f : C ≃ D) (F : Table B D) :
    fourCycle (fun a c => F (e a) (f c)) = fourCycle F := by
  rw [fourCycle_as_product, fourCycle_as_product]
  exact average_equiv ((e.prodCongr e).prodCongr (f.prodCongr f))
    (fun p : (B × B) × (D × D) =>
      F p.1.1 p.2.1 * F p.1.1 p.2.2 * F p.1.2 p.2.1 * F p.1.2 p.2.2)

/-- A grouped nonzero-coordinate subtype is the product of the old-coordinate type and the nonzero new-coordinate type. -/
def nonzeroSecondEquiv (L V : Type*) [Zero V] :
    {x : L × V // x.2 ≠ 0} ≃ L × {v : V // v ≠ 0} where
  toFun x := (x.val.1, ⟨x.val.2, x.property⟩)
  invFun x := ⟨(x.1, x.2.val), x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Extend a function from a predicate-defined subset by assigning zero outside that subset. -/
def extendZero {A : Type*} (p : A → Prop) [DecidablePred p]
    (f : {a // p a} → ℝ) (a : A) : ℝ := if h : p a then f ⟨a, h⟩ else 0

/-- The sum of a zero-extended function equals the sum over its original subset. -/
theorem sum_extendZero {A : Type*} [Fintype A] (p : A → Prop) [DecidablePred p]
    (f : {a // p a} → ℝ) : (∑ a, extendZero p f a) = ∑ a : {a // p a}, f a := by
  symm
  calc
    _ = ∑ a : {a // p a}, extendZero p f a.val := by
      apply Finset.sum_congr rfl
      intro a _
      simp [extendZero, a.property]
    _ = ∑ a ∈ Finset.univ.filter p, extendZero p f a :=
      (Finset.sum_subtype _ (by simp) _).symm
    _ = ∑ a, extendZero p f a := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro a _ hn
      have hp : ¬p a := by simpa using hn
      simp [extendZero, hp]

/-- The average of a zero extension equals the original average times the subset’s relative cardinality. -/
theorem average_extendZero {A : Type*} [Fintype A] [Nonempty A]
    (p : A → Prop) [DecidablePred p] [Nonempty {a // p a}]
    (f : {a // p a} → ℝ) :
    average (extendZero p f) =
      ((Fintype.card {a // p a} : ℝ) / Fintype.card A) * average f := by
  have hp : (Fintype.card {a // p a} : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold average
  rw [sum_extendZero]
  field_simp

/-- Extend a table by zero outside its allowed row and column subsets. -/
def extendTableZero {A B : Type*} (p : A → Prop) (q : B → Prop)
    [DecidablePred p] [DecidablePred q] (F : Table {a // p a} {b // q b}) : Table A B :=
  fun a b => if ha : p a then if hb : q b then F ⟨a, ha⟩ ⟨b, hb⟩ else 0 else 0

/-- A table’s zero extension has mean equal to its original mean times the two subset densities. -/
theorem average_extendTableZero {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (p : A → Prop) (q : B → Prop)
    [DecidablePred p] [DecidablePred q] [Nonempty {a // p a}] [Nonempty {b // q b}]
    (F : Table {a // p a} {b // q b}) :
    average (fun a => average (extendTableZero p q F a)) =
      ((Fintype.card {a // p a} : ℝ) / Fintype.card A) *
        ((Fintype.card {b // q b} : ℝ) / Fintype.card B) *
          average (fun a => average (F a)) := by
  have hin (a : A) : average (extendTableZero p q F a) =
      extendZero p (fun a' =>
        ((Fintype.card {b // q b} : ℝ) / Fintype.card B) * average (F a')) a := by
    by_cases ha : p a
    · simp only [extendZero, ha, dite_true]
      have heq : extendTableZero p q F a = extendZero q (F ⟨a, ha⟩) := by
        funext b
        simp [extendTableZero, extendZero, ha]
      rw [heq]
      exact average_extendZero q (F ⟨a, ha⟩)
    · simp [extendTableZero, extendZero, ha, average]
  simp_rw [hin]
  rw [average_extendZero]
  simp only [average_smul]
  ring

/-- Squaring a zero-extended table equals zero-extending its squared entries. -/
theorem extendTableZero_square {A B : Type*} (p : A → Prop) (q : B → Prop)
    [DecidablePred p] [DecidablePred q] (F : Table {a // p a} {b // q b}) (a : A) (b : B) :
    extendTableZero p q F a b ^ 2 = extendTableZero p q (fun x y => F x y ^ 2) a b := by
  by_cases ha : p a <;> by_cases hb : q b <;> simp [extendTableZero, ha, hb]

/-- Squared L2 mass picks up one support-density factor on each side. -/
theorem normSq_extendTableZero {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (p : A → Prop) (q : B → Prop)
    [DecidablePred p] [DecidablePred q] [Nonempty {a // p a}] [Nonempty {b // q b}]
    (F : Table {a // p a} {b // q b}) :
    normSq (extendTableZero p q F) =
      ((Fintype.card {a // p a} : ℝ) / Fintype.card A) *
        ((Fintype.card {b // q b} : ℝ) / Fintype.card B) * normSq F := by
  simp only [normSq, pairing, ← pow_two, extendTableZero_square]
  exact average_extendTableZero p q (fun x y => F x y ^ 2)

/-- The column-averaged Gram entry of a zero extension equals its original Gram entry times the column density when both rows are allowed, and zero otherwise. -/
theorem extendTableZero_gram {A B : Type*} [Fintype B] [Nonempty B]
    (p : A → Prop) (q : B → Prop) [DecidablePred p] [DecidablePred q]
    [Nonempty {b // q b}] (F : Table {a // p a} {b // q b}) (a₁ a₂ : A) :
    average (fun b => extendTableZero p q F a₁ b * extendTableZero p q F a₂ b) =
      if h₁ : p a₁ then if h₂ : p a₂ then
        ((Fintype.card {b // q b} : ℝ) / Fintype.card B) *
          average (fun b => F ⟨a₁, h₁⟩ b * F ⟨a₂, h₂⟩ b) else 0 else 0 := by
  by_cases h₁ : p a₁ <;> by_cases h₂ : p a₂
  · simp only [h₁, h₂, dite_true]
    have heq (b : B) : extendTableZero p q F a₁ b * extendTableZero p q F a₂ b =
        extendZero q (fun b' => F ⟨a₁, h₁⟩ b' * F ⟨a₂, h₂⟩ b') b := by
      by_cases hb : q b <;> simp [extendTableZero, extendZero, h₁, h₂, hb]
    simp_rw [heq]
    exact average_extendZero q _
  all_goals simp [extendTableZero, h₁, h₂, average]

/-- Four-cycle mass picks up two support-density factors on each side. -/
theorem fourCycle_extendTableZero {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (p : A → Prop) (q : B → Prop)
    [DecidablePred p] [DecidablePred q] [Nonempty {a // p a}] [Nonempty {b // q b}]
    (F : Table {a // p a} {b // q b}) :
    fourCycle (extendTableZero p q F) =
      ((Fintype.card {a // p a} : ℝ) / Fintype.card A) ^ 2 *
        ((Fintype.card {b // q b} : ℝ) / Fintype.card B) ^ 2 * fourCycle F := by
  let rb : ℝ := (Fintype.card {b // q b} : ℝ) / Fintype.card B
  have hp (a₁ a₂ : A) :
      (average (fun b => extendTableZero p q F a₁ b * extendTableZero p q F a₂ b)) ^ 2 =
        extendTableZero p p (fun x₁ x₂ => rb ^ 2 *
          (average (fun y => F x₁ y * F x₂ y)) ^ 2) a₁ a₂ := by
    rw [extendTableZero_gram]
    by_cases h₁ : p a₁ <;> by_cases h₂ : p a₂ <;>
      simp [extendTableZero, h₁, h₂, rb, mul_pow]
  rw [fourCycle_gram]
  simp_rw [hp]
  rw [average_extendTableZero]
  simp only [average_smul]
  rw [← fourCycle_gram F]
  dsimp [rb]
  ring

end RefreshingProof.Local
