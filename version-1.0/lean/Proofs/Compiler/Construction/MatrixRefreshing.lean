import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.Construction.FiniteProbability
/-!
# The physical matrix refresh

Invertible actions preserve the represented secret and act transitively on its nonzero encoding fiber. The module also defines the local rectangle masks.

This module is part of the constructive compiler model; it imports no compiler proof theorem. The public source and execution interfaces are in Compiler.Direct and Compiler.Stateful.
-/
set_option backward.isDefEq.respectTransparency false
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end Refresh
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end Refresh
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end Refresh
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end Refresh
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
namespace Refresh
/-- The density multiplier on the secret fiber when uniform encodings are compared with two independent uniform nonzero shares. -/

noncomputable def densityWeight (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) (s : F) : ℝ :=
  (shareCard F n : ℝ) ^ 2 / (Fintype.card (Fiber F n s) : ℝ)
end Refresh
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- The field size remains strictly positive when viewed as a real number. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

0 < |F|.
-/
theorem fieldCard_cast_pos : 0 < (fieldCard F : ℝ) := by
  exact_mod_cast (fieldCard_pos (F := F))
/-- The real-valued field size is at least two. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

2 ≤ |F|.
-/
theorem fieldCard_cast_ge_two : 2 ≤ (fieldCard F : ℝ) := by
  exact_mod_cast (fieldCard_ge_two (F := F))
/-- The real-valued nonzero-vector count is the full vector count minus one. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, we have

(|F|ⁿ-1) = |F|ⁿ - 1.
-/
theorem shareCard_cast_real (n : ℕ) : (shareCard F n : ℝ) = (vectorCard F n : ℝ) - 1 := by
  simp only [shareCard, vectorCard, Nat.cast_sub (Nat.one_le_pow _ _ (fieldCard_pos (F := F))), Nat.cast_one]
/-- Dimension at least two gives at least four vectors, expressed in real arithmetic. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, assume 2 ≤ n. Then

4 ≤ |F|ⁿ.
-/
theorem vectorCard_real_ge_four {n : ℕ} (hn : 2 ≤ n) : 4 ≤ (vectorCard F n : ℝ) := by
  exact_mod_cast (four_le_pow (F := F) hn)
/-- Dimension at least two makes the vector count at least the square of the field size. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, assume 2 ≤ n. Then

(|F|)² ≤ |F|ⁿ.
-/
theorem vectorCard_real_ge_fieldCard_sq {n : ℕ} (hn : 2 ≤ n) :
    (fieldCard F : ℝ) ^ 2 ≤ (vectorCard F n : ℝ) := by
  have h : fieldCard F ^ 2 ≤ vectorCard F n := Nat.pow_le_pow_right (by have := fieldCard_ge_two (F := F); omega) hn
  exact_mod_cast h
/-- Dimension at least two makes the vector count at least twice the field size. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, assume 2 ≤ n. Then

2 · |F| ≤ |F|ⁿ.
-/
theorem vectorCard_real_ge_two_mul_fieldCard {n : ℕ} (hn : 2 ≤ n) :
    2 * (fieldCard F : ℝ) ≤ (vectorCard F n : ℝ) := by
  have hq := fieldCard_cast_ge_two (F := F)
  have hN := vectorCard_real_ge_fieldCard_sq (F := F) hn
  nlinarith
/-- The nonzero-vector count is strictly positive in dimension at least two. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, assume 2 ≤ n. Then

0 < (|F|ⁿ-1).
-/
theorem nonzeroCard_real_pos {n : ℕ} (hn : 2 ≤ n) : 0 < (shareCard F n : ℝ) := by
  rw [shareCard_cast_real]
  have hN := vectorCard_real_ge_four (F := F) hn
  linarith
/-- In dimension at least two, `(vectorCard F n) - (fieldCard F)` is positive, so the zero-secret density denominator does not vanish. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, assume 2 ≤ n. Then

0 < |F|ⁿ - |F|.
-/
theorem zeroFiber_denominator_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < (vectorCard F n : ℝ) - (fieldCard F : ℝ) := by
  have hN := vectorCard_real_ge_two_mul_fieldCard (F := F) hn
  have hq := fieldCard_cast_pos (F := F)
  linarith
/-- For dimension at least two, the real-valued vector count factors as `(fieldCard F)` times `(fieldCard F)^(n-1)`. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, assume 2 ≤ n. Then

(|F|)ⁿ = |F| · (|F|)^(n − 1).
-/
theorem pow_pred_real {n : ℕ} (hn : 2 ≤ n) :
    (fieldCard F : ℝ) ^ n = (fieldCard F : ℝ) * (fieldCard F : ℝ) ^ (n - 1) := by
  exact_mod_cast (fieldCard_pow_pred (F := F) (show 1 ≤ n by omega))
/-- The zero-secret encoding count equals `(shareCard F n) * ((vectorCard F n) - (fieldCard F)) / (fieldCard F)` in real arithmetic. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, assume 2 ≤ n. Then

|Fiber(F, n, 0)| = (|F|ⁿ-1) · (|F|ⁿ - |F|) / |F|.
-/
theorem fiber_card_zero_real {n : ℕ} (hn : 2 ≤ n) :
    (Fintype.card (Fiber F n 0) : ℝ) =
      (shareCard F n : ℝ) * ((vectorCard F n : ℝ) - (fieldCard F : ℝ)) / (fieldCard F : ℝ) := by
  rw [fiber_card_zero]
  have hpred : 1 ≤ fieldCard F ^ (n - 1) := Nat.one_le_pow _ _ fieldCard_pos
  have hbase : 1 ≤ fieldCard F ^ n := Nat.one_le_pow _ _ fieldCard_pos
  have hq : (fieldCard F : ℝ) ≠ 0 := ne_of_gt fieldCard_cast_pos
  simp only [Nat.cast_mul, Nat.cast_sub hbase, Nat.cast_sub hpred, Nat.cast_one,
    Nat.cast_pow, shareCard_cast_real, vectorCard]
  rw [pow_pred_real (F := F) hn]
  field_simp
/-- For a nonzero secret, the encoding count equals `(shareCard F n) * (vectorCard F n) / (fieldCard F)` in real arithmetic. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, assume 2 ≤ n; s ≠ 0. Then

|Fiber(F, n, s)| = (|F|ⁿ-1) · |F|ⁿ / |F|.
-/
theorem fiber_card_of_ne_zero_real {n : ℕ} (hn : 2 ≤ n) (s : F) (hs : s ≠ 0) :
    (Fintype.card (Fiber F n s) : ℝ) = (shareCard F n : ℝ) * (vectorCard F n : ℝ) / (fieldCard F : ℝ) := by
  rw [fiber_card_of_ne_zero n s hs]
  have hbase : 1 ≤ fieldCard F ^ n := Nat.one_le_pow _ _ fieldCard_pos
  have hq : (fieldCard F : ℝ) ≠ 0 := ne_of_gt fieldCard_cast_pos
  simp only [Nat.cast_mul, Nat.cast_sub hbase, Nat.cast_one, Nat.cast_pow, shareCard_cast_real, vectorCard]
  rw [pow_pred_real (F := F) hn]
  field_simp
/-- In dimension at least two, the density multiplier for secret zero is exactly `(fieldCard F) * (shareCard F n) / ((vectorCard F n) - (fieldCard F))`. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, assume 2 ≤ n. Then

densityWeight(F, n, 0) = |F| · (|F|ⁿ-1) / (|F|ⁿ - |F|).
-/
theorem densityWeight_zero {n : ℕ} (hn : 2 ≤ n) :
    densityWeight F n 0 = (fieldCard F : ℝ) * (shareCard F n : ℝ) / ((vectorCard F n : ℝ) - (fieldCard F : ℝ)) := by
  rw [densityWeight, fiber_card_zero_real hn]
  have hd : (shareCard F n : ℝ) ≠ 0 := ne_of_gt (nonzeroCard_real_pos hn)
  have hN : (vectorCard F n : ℝ) - (fieldCard F : ℝ) ≠ 0 := ne_of_gt (zeroFiber_denominator_pos hn)
  have hq : (fieldCard F : ℝ) ≠ 0 := ne_of_gt fieldCard_cast_pos
  field_simp
/-- In dimension at least two, every nonzero secret has density multiplier exactly `(fieldCard F) * (shareCard F n) / (vectorCard F n)`. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, assume 2 ≤ n; s ≠ 0. Then

densityWeight(F, n, s) = |F| · (|F|ⁿ-1) / |F|ⁿ.
-/
theorem densityWeight_of_ne_zero {n : ℕ} (hn : 2 ≤ n) (s : F) (hs : s ≠ 0) :
    densityWeight F n s = (fieldCard F : ℝ) * (shareCard F n : ℝ) / (vectorCard F n : ℝ) := by
  rw [densityWeight, fiber_card_of_ne_zero_real hn s hs]
  have hd : (shareCard F n : ℝ) ≠ 0 := ne_of_gt (nonzeroCard_real_pos hn)
  have hN : (vectorCard F n : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (vectorCard_real_ge_four hn))
  have hq : (fieldCard F : ℝ) ≠ 0 := ne_of_gt fieldCard_cast_pos
  field_simp
/-- Every secret has a strictly positive density multiplier in dimension at least two. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, assume 2 ≤ n. Then

0 < densityWeight(F, n, s).
-/
theorem densityWeight_pos {n : ℕ} (hn : 2 ≤ n) (s : F) : 0 < densityWeight F n s := by
  apply div_pos
  · exact pow_pos (nonzeroCard_real_pos hn) 2
  · exact_mod_cast fiber_card_pos hn s
/-- In dimension at least two, the uniform encoding density multiplier is at most twice the field cardinality for every secret. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, assume 2 ≤ n. Then

densityWeight(F, n, s) ≤ 2 · |F|.
-/
theorem densityWeight_le_two_mul_q {n : ℕ} (hn : 2 ≤ n) (s : F) :
    densityWeight F n s ≤ 2 * (fieldCard F : ℝ) := by
  have hq := fieldCard_cast_pos (F := F)
  have hN := vectorCard_real_ge_two_mul_fieldCard (F := F) hn
  by_cases hs : s = 0
  · subst s
    rw [densityWeight_zero hn]
    apply (div_le_iff₀ (zeroFiber_denominator_pos hn)).2
    rw [shareCard_cast_real]
    have h := mul_nonneg hq.le (show 0 ≤ (vectorCard F n : ℝ) - 2 * (fieldCard F : ℝ) from sub_nonneg.mpr hN)
    nlinarith
  · rw [densityWeight_of_ne_zero hn s hs]
    apply (div_le_iff₀ (show 0 < (vectorCard F n : ℝ) by linarith)).2
    rw [shareCard_cast_real]
    nlinarith
end Refresh
end
section
/-!
# Refreshing

Definitions used by the headline security statements. The construction facts are included in this self-contained model.
-/
/-!
## Mu
-/
section
set_option autoImplicit false
namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end Refresh
end
/-!
## Freshness
-/
section
set_option autoImplicit false
namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end Refresh
end
/-!
## RefreshBounds
-/
section
set_option autoImplicit false
open scoped BigOperators
namespace TableAnalysis
open MatrixRefresh Refresh
noncomputable section
variable {X G Z : Type*} [Fintype X] [Fintype G] [Fintype Z]
/-- A partition of transcript leaves for each old state and sampled refresh. The rectangle property is not needed for these norm bounds. -/

structure RoundPartition (X G Z : Type*) [Fintype Z] where
  weight : Z → G → X → ℝ
  nonneg : ∀ z g x, 0 ≤ weight z g x
  complete : ∀ g x, ∑ z, weight z g x = 1
end
end TableAnalysis
end
/-!
## RectangularRefresh
-/
section
set_option autoImplicit false
open scoped BigOperators Matrix Matrix.Norms.L2Operator
namespace TableAnalysis
open MatrixRefresh Refresh
noncomputable section
variable {X G Z : Type*} [Fintype X] [Fintype G] [Fintype Z]
/-- For each matrix, complete answers partition the two parties’ local inputs into rectangles. -/
structure TableRectanglePartition (X G Z : Type*) [Fintype Z] where
  left : Z → G → X → Bool
  right : Z → G → X → Bool
  complete : ∀ M l r, ∑ z,
    (if left z M l then (1 : ℝ) else 0) *
      (if right z M r then (1 : ℝ) else 0) = 1
/-- The real-valued indicator of the left local set for a fixed complete answer and matrix. -/
def TableRectanglePartition.leftIndicator (p : TableRectanglePartition X G Z)
    (z : Z) (M : G) (l : X) : ℝ := if p.left z M l then 1 else 0
/-- The real-valued indicator of the right local set for a fixed complete answer and matrix. -/
def TableRectanglePartition.rightIndicator (p : TableRectanglePartition X G Z)
    (z : Z) (M : G) (r : X) : ℝ := if p.right z M r then 1 else 0
/-- Read a rectangular answer partition as a normalized one-round answer distribution. -/
def TableRectanglePartition.toRoundPartition (p : TableRectanglePartition X G Z) :
    RoundPartition (X × X) G Z where
  weight z M x := p.leftIndicator z M x.1 * p.rightIndicator z M x.2
  nonneg z M x := by
    unfold TableRectanglePartition.leftIndicator TableRectanglePartition.rightIndicator
    split_ifs <;> norm_num
  complete M x := p.complete M x.1 x.2
end
end TableAnalysis
end
/-!
## StateDensity
-/
section
set_option autoImplicit false
open scoped BigOperators
namespace TableAnalysis
open MatrixRefresh Refresh
noncomputable section
variable {X G Z : Type*} [Fintype X] [Fintype G] [Fintype Z]
/-- The public answers observed at the first i chronological operations. -/
abbrev PublicHistory (Z : Type*) (i : ℕ) := Fin i → Z
end
end TableAnalysis
end
/-!
## RectangleTrees
-/
section
set_option autoImplicit false
open scoped BigOperators
namespace TableAnalysis
open MatrixRefresh Refresh
attribute [local instance] Classical.propDecidable
/-- A finite deterministic binary leakage tree. Its query function may read the entire common matrix; the node determines which share it can read. -/

inductive LocalQueryTree (X G : Type*) where
  | leaf : LocalQueryTree X G
  | alice (query : X → G → Bool) (zero one : LocalQueryTree X G) : LocalQueryTree X G
  | bob (query : X → G → Bool) (zero one : LocalQueryTree X G) : LocalQueryTree X G
namespace LocalQueryTree
variable {X G : Type*}
/-- Leaf positions, independent of whether a leaf can be reached. -/

def Leaves : LocalQueryTree X G → Type
  | .leaf => Unit
  | .alice _ zero one => Leaves zero ⊕ Leaves one
  | .bob _ zero one => Leaves zero ⊕ Leaves one
noncomputable instance leavesFintype (t : LocalQueryTree X G) : Fintype t.Leaves := by
  induction t with
  | leaf => exact inferInstanceAs (Fintype Unit)
  | alice _ _ _ ih₀ ih₁ | bob _ _ _ ih₀ ih₁ =>
      letI := ih₀
      letI := ih₁
      exact inferInstanceAs (Fintype (_ ⊕ _))
/-- Evaluate the adaptive local-query tree on the fixed matrix and the two parties’ local inputs. -/
def eval : (t : LocalQueryTree X G) → G → X → X → t.Leaves
  | .leaf, _, _, _ => ()
  | .alice query zero one, M, l, r =>
      if query l M then Sum.inr (eval one M l r) else Sum.inl (eval zero M l r)
  | .bob query zero one, M, l, r =>
      if query r M then Sum.inr (eval one M l r) else Sum.inl (eval zero M l r)
/-- The largest total number of binary local queries on any branch of the adaptive query tree. -/
def depth : LocalQueryTree X G → ℕ
  | .leaf => 0
  | .alice _ zero one => max zero.depth one.depth + 1
  | .bob _ zero one => max zero.depth one.depth + 1
/-- Maximum number of bits read from Alice along any path. -/

def aliceBits : LocalQueryTree X G → ℕ
  | .leaf => 0
  | .alice _ zero one => max zero.aliceBits one.aliceBits + 1
  | .bob _ zero one => max zero.aliceBits one.aliceBits
/-- Maximum number of bits read from Bob along any path. -/

def bobBits : LocalQueryTree X G → ℕ
  | .leaf => 0
  | .alice _ zero one => max zero.bobBits one.bobBits
  | .bob _ zero one => max zero.bobBits one.bobBits + 1
end LocalQueryTree
end TableAnalysis
end
end
