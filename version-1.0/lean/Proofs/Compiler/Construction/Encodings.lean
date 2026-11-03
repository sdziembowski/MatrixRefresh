import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.Construction.Namespaces
/-!
# Nonzero inner-product encodings

Vectors, nonzero shares, secret fibers, and exact finite cardinalities used by initialization and refreshing.

This module is part of the constructive compiler model; it imports no compiler proof theorem. The public source and execution interfaces are in Compiler.Direct and Compiler.Stateful.
-/
set_option backward.isDefEq.respectTransparency false
section
/-!
# Encodings

Definitions used by the headline security statements. The construction facts are included in this self-contained model.
-/
/-!
## Notation
-/
section
set_option autoImplicit false
namespace Refresh
/-- The field size, which may be any prime power rather than only a prime. -/

def fieldCard (F : Type*) [Fintype F] : ℕ := Fintype.card F
/-- The number of vectors in the `n`-dimensional finite-field space. -/

def vectorCard (F : Type*) [Fintype F] (n : ℕ) : ℕ := fieldCard F ^ n
/-- The number of nonzero vectors, obtained by removing the zero vector. -/

def shareCard (F : Type*) [Fintype F] (n : ℕ) : ℕ := vectorCard F n - 1
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Equality of encoding states is decided by comparing their left and right shares. -/
instance stateDecidableEq (n : ℕ) : DecidableEq (State F n) := fun x y =>
  decidable_of_iff ((stateLeftShare x) = (stateLeftShare y) ∧ (stateRightShare x) = (stateRightShare y)) (by
    constructor
    · rintro ⟨hL, hR⟩; exact State.ext hL hR
    · rintro rfl; exact ⟨rfl, rfl⟩)
end Refresh
end
/-!
## MatrixAction
-/
section
set_option autoImplicit false
namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end Refresh
end
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
namespace Refresh
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- A finite field has at least two elements, since zero and one are distinct. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

2 ≤ |F|.
-/
theorem fieldCard_ge_two : 2 ≤ fieldCard F :=
  Fintype.one_lt_card
/-- The cardinality of a finite field is positive. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

0 < |F|.
-/
theorem fieldCard_pos : 0 < fieldCard F :=
  Fintype.card_pos
/-- Pairing any vector with the zero vector gives zero. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; l ∈ V(F, n), we have

(l · 0) = 0.
-/
@[simp] lemma dot_zero_right {n : ℕ} (l : V F n) : dot l 0 = 0 := by
  simp [dot]
/-- The existence of a nonzero vector forces the ambient dimension to be positive. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; l ∈ U(F, n), we have

1 ≤ n.
-/
lemma one_le_of_nonzero_vector {n : ℕ} (l : U F n) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    exact absurd (funext fun i => absurd i.isLt (by omega)) l.property
  · exact h
/-- There are exactly `(fieldCard F)^n` vectors in an `n`-dimensional space over the finite field. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, we have

|V(F, n)| = (|F|)ⁿ.
-/
theorem vector_card (n : ℕ) : Fintype.card (V F n) = fieldCard F ^ n := by
  simp [V, fieldCard]
/-- There are exactly `(fieldCard F)^n - 1` nonzero vectors. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, we have

|U(F, n)| = (|F|)ⁿ - 1.
-/
theorem nonzero_vector_card (n : ℕ) : Fintype.card (U F n) = fieldCard F ^ n - 1 := by
  have h := Fintype.card_subtype_compl (α := V F n) (p := fun v => v = 0)
  rw [Fintype.card_subtype_eq (0 : V F n), vector_card] at h
  exact h
end Refresh
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
namespace Refresh
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Translation identifies every two fibers of a nonzero functional. -/

noncomputable def dotFiberTranslate {n : ℕ} (l : U F n) (s t : F) :
    {r : V F n // dot l.val r = s} ≃ {r : V F n // dot l.val r = t} := by
  let w := Classical.choose (exists_dot_one l)
  have hw : dot l.val w = 1 := Classical.choose_spec (exists_dot_one l)
  refine ⟨fun r => ⟨r.val + (t - s) • w, ?_⟩,
    fun r => ⟨r.val - (t - s) • w, ?_⟩, ?_, ?_⟩
  · rw [dot_add_right, dot_smul_right, hw, mul_one, r.property]
    ring
  · rw [dot_sub_right, dot_smul_right, hw, mul_one, r.property]
    ring
  · intro r; apply Subtype.ext; simp
  · intro r; apply Subtype.ext; simp
end Refresh
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
namespace Refresh
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- All fibers of pairing with a fixed nonzero row have the same cardinality, regardless of the prescribed field value. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; l ∈ U(F, n); s, t ∈ F, we have

|{r ∈ V(F, n) | (l · r) = s}| = |{r ∈ V(F, n) | (l · r) = t}|.
-/
lemma dot_fiber_card_eq {n : ℕ} (l : U F n) (s t : F) :
    Fintype.card {r : V F n // dot l.val r = s} =
      Fintype.card {r : V F n // dot l.val r = t} :=
  Fintype.card_congr (dotFiberTranslate l s t)
/-- In positive dimension, the number of vectors factors as the field size times `(fieldCard F)^(n-1)`. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, assume 1 ≤ n. Then

(|F|)ⁿ = |F| · (|F|)^(n − 1).
-/
lemma fieldCard_pow_pred {n : ℕ} (hn : 1 ≤ n) : fieldCard F ^ n = fieldCard F * fieldCard F ^ (n - 1) := by
  have heq : n = (n - 1) + 1 := by omega
  conv_lhs => rw [heq, pow_succ]
  ring
/-- A prescribed inner product with a nonzero row has exactly `(fieldCard F)^(n-1)` solutions when the zero vector is allowed. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; l ∈ U(F, n); s ∈ F, we have

|{r ∈ V(F, n) | (l · r) = s}| = (|F|)^(n − 1).
-/
theorem full_dot_fiber_card {n : ℕ} (l : U F n) (s : F) :
    Fintype.card {r : V F n // dot l.val r = s} = fieldCard F ^ (n - 1) := by
  have hsum : ∑ t : F, Fintype.card {r : V F n // dot l.val r = t} = fieldCard F ^ n := by
    rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv (fun r : V F n => dot l.val r))]
    exact vector_card n
  simp_rw [dot_fiber_card_eq l _ s] at hsum
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  change fieldCard F * _ = fieldCard F ^ n at hsum
  rw [fieldCard_pow_pred (one_le_of_nonzero_vector l)] at hsum
  exact Nat.eq_of_mul_eq_mul_left fieldCard_pos hsum
/-- Counting nonzero partner vectors as a subtype gives the same count as imposing nonzeroness inside the full vector space. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; l ∈ U(F, n); s ∈ F, we have

|{r ∈ U(F, n) | (l · r) = s}| = |{r ∈ V(F, n) | r ≠ 0 ∧ (l · r) = s}|.
-/
lemma nonzero_fiber_card_eq {n : ℕ} (l : U F n) (s : F) :
    Fintype.card {r : U F n // dot l.val r.val = s} =
      Fintype.card {r : V F n // r ≠ 0 ∧ dot l.val r = s} :=
  Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun v : V F n => v ≠ 0) (fun v : V F n => dot l.val v = s))
/-- For a nonzero prescribed inner product, every partner is already nonzero, so there are `(fieldCard F)^(n-1)` partners. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; l ∈ U(F, n); s ∈ F, assume s ≠ 0. Then

|{r ∈ U(F, n) | (l · r) = s}| = (|F|)^(n − 1).
-/
theorem nonzero_dot_fiber_card_of_ne_zero {n : ℕ} (l : U F n) (s : F) (hs : s ≠ 0) :
    Fintype.card {r : U F n // dot l.val r.val = s} = fieldCard F ^ (n - 1) := by
  rw [nonzero_fiber_card_eq l s]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight
    (p := fun r : V F n => r ≠ 0 ∧ dot l.val r = s)
    (q := fun r : V F n => dot l.val r = s)
    (fun r => ⟨fun h => h.2, fun h => ⟨by rintro rfl; exact hs (by simpa using h.symm), h⟩⟩))]
  exact full_dot_fiber_card l s
/-- For inner product zero, excluding the zero partner leaves exactly `(fieldCard F)^(n-1) - 1` partners. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; l ∈ U(F, n), we have

|{r ∈ U(F, n) | (l · r) = 0}| = (|F|)^(n − 1) - 1.
-/
theorem nonzero_dot_fiber_card_zero {n : ℕ} (l : U F n) :
    Fintype.card {r : U F n // dot l.val r.val = 0} = fieldCard F ^ (n - 1) - 1 := by
  classical
  rw [nonzero_fiber_card_eq l 0]
  have hcongr : Fintype.card {r : V F n // r ≠ 0 ∧ dot l.val r = 0} =
      Fintype.card {r : {v : V F n // dot l.val v = 0} // ¬ (r = ⟨0, dot_zero_right _⟩)} :=
    Fintype.card_congr (Equiv.symm
      { toFun := fun r => ⟨r.1.1, ⟨fun h => r.2 (Subtype.ext h), r.1.2⟩⟩
        invFun := fun r => ⟨⟨r.1, r.2.2⟩, fun h => r.2.1 (congrArg Subtype.val h)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
  rw [hcongr, Fintype.card_subtype_compl, Fintype.card_subtype_eq, full_dot_fiber_card l 0]
end Refresh
end
section
/-!
# EncodingCoordinates

Definitions used by the headline security statements. The construction facts are included in this self-contained model.
-/
/-!
## StateEquivProd
-/
section
set_option autoImplicit false
namespace Refresh
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- A secret fiber can be enumerated by first choosing its nonzero left share and then a compatible nonzero right share. -/

def fiberEquivSigma (n : ℕ) (s : F) :
    Fiber F n s ≃ Σ l : U F n, {r : U F n // dot l.val r.val = s} :=
  (Equiv.subtypeEquiv (stateEquivProd F n) (fun _ => Iff.rfl)).trans
    (Equiv.subtypeProdEquivSigmaSubtype (fun l r : U F n => dot l.val r.val = s))
end Refresh
end
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
namespace Refresh
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- The size of a secret fiber is the sum, over all nonzero left shares, of their compatible-partner counts. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, we have

|Fiber(F, n, s)| = ∑_(l ∈ U(F, n)) (|{r ∈ U(F, n) | (l · r) = s}|).
-/
lemma fiber_card_eq_sum (n : ℕ) (s : F) :
    Fintype.card (Fiber F n s) = ∑ l : U F n, Fintype.card {r : U F n // dot l.val r.val = s} := by
  rw [Fintype.card_congr (fiberEquivSigma n s), Fintype.card_sigma]
/-- The zero-secret fiber has `((fieldCard F)^n - 1)((fieldCard F)^(n-1) - 1)` encodings: the zero right partner is excluded for each left share. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, we have

|Fiber(F, n, 0)| = ((|F|)ⁿ - 1) · ((|F|)^(n − 1) - 1).
-/
theorem fiber_card_zero (n : ℕ) :
    Fintype.card (Fiber F n 0) = (fieldCard F ^ n - 1) * (fieldCard F ^ (n - 1) - 1) := by
  rw [fiber_card_eq_sum n 0, Finset.sum_congr rfl (fun l _ => nonzero_dot_fiber_card_zero l)]
  simp [nonzero_vector_card n]
/-- A nonzero-secret fiber has `((fieldCard F)^n - 1)(fieldCard F)^(n-1)` encodings. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, assume s ≠ 0. Then

|Fiber(F, n, s)| = ((|F|)ⁿ - 1) · (|F|)^(n − 1).
-/
theorem fiber_card_of_ne_zero (n : ℕ) (s : F) (hs : s ≠ 0) :
    Fintype.card (Fiber F n s) = (fieldCard F ^ n - 1) * fieldCard F ^ (n - 1) := by
  rw [fiber_card_eq_sum n s, Finset.sum_congr rfl (fun l _ => nonzero_dot_fiber_card_of_ne_zero l s hs)]
  simp [nonzero_vector_card n]
/-- The exact encoding count distinguishes the zero secret, whose partner count is smaller by one. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, we have

|Fiber(F, n, s)| = ((|F|)ⁿ - 1) · ({ (|F|)^(n − 1) - 1 if s = 0,; (|F|)^(n − 1) otherwise }).
-/
theorem fiber_card (n : ℕ) (s : F) :
    Fintype.card (Fiber F n s) =
      (fieldCard F ^ n - 1) * (if s = 0 then fieldCard F ^ (n - 1) - 1 else fieldCard F ^ (n - 1)) := by
  by_cases hs : s = 0
  · subst s; simpa using fiber_card_zero (F := F) n
  · simpa [hs] using fiber_card_of_ne_zero n s hs
/-- In dimension at least two, each unrestricted pairing fiber has at least two vectors. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, assume 2 ≤ n. Then

2 ≤ (|F|)^(n − 1).
-/
lemma two_le_pow_pred {n : ℕ} (hn : 2 ≤ n) : 2 ≤ fieldCard F ^ (n - 1) := by
  calc
    2 ≤ fieldCard F := fieldCard_ge_two
    _ = fieldCard F ^ 1 := by simp
    _ ≤ fieldCard F ^ (n - 1) := Nat.pow_le_pow_right (by have := fieldCard_ge_two (F := F); omega) (by omega)
/-- In dimension at least two, the full vector space has at least four vectors. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, assume 2 ≤ n. Then

4 ≤ (|F|)ⁿ.
-/
lemma four_le_pow {n : ℕ} (hn : 2 ≤ n) : 4 ≤ fieldCard F ^ n := by
  have hq := fieldCard_ge_two (F := F)
  have hpow : fieldCard F ^ 2 ≤ fieldCard F ^ n := Nat.pow_le_pow_right (by omega) hn
  have hbase : 4 ≤ fieldCard F ^ 2 := by rw [pow_two]; nlinarith
  exact hbase.trans hpow
/-- Every secret has a positive number of legal nonzero-share encodings in dimension at least two. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, assume 2 ≤ n. Then

0 < |Fiber(F, n, s)|.
-/
theorem fiber_card_pos {n : ℕ} (hn : 2 ≤ n) (s : F) : 0 < Fintype.card (Fiber F n s) := by
  have h1 := two_le_pow_pred (F := F) hn
  have h2 := four_le_pow (F := F) hn
  rw [fiber_card]
  split <;> exact Nat.mul_pos (by omega) (by omega)
end Refresh
end
