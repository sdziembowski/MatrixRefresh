import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Binary character cancellation

The elementary Walsh-character orthogonality underlying the discrepancy and consistency-sign estimates in the paper. These statements use all binary vectors; nonzero-share restrictions are handled separately in the analytic argument.
-/

open scoped BigOperators Matrix
set_option maxHeartbeats 800000

namespace RefreshingProof.Binary

/-- The binary field ℤ/2ℤ. -/
abbrev Bit := ZMod 2
/-- The n-dimensional vector space of binary coordinate functions. -/
abbrev Vec (n : ℕ) := Fin n → Bit

/-- The real binary character takes value 1 at zero and −1 at one. -/
def sign (a : Bit) : ℝ := if a = 0 then 1 else -1

/-- The binary character of zero equals one. -/
@[simp] theorem sign_zero : sign 0 = 1 := by norm_num [sign]

/-- The binary character of one equals minus one. -/
@[simp] theorem sign_one : sign 1 = -1 := by norm_num [sign]

/-- Every binary-field element is either zero or one. -/
theorem bit_cases (a : Bit) : a = 0 ∨ a = 1 := by
  fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- The binary character turns field addition into multiplication of real signs. -/
theorem sign_add (a b : Bit) : sign (a + b) = sign a * sign b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl
  all_goals simp [CharTwo.add_self_eq_zero]

/-- Adding one reverses a binary character’s sign. -/
@[simp] theorem sign_add_one (a : Bit) : sign (a + 1) = -sign a := by
  rw [sign_add, sign_one]
  ring

/-- Translation by a unit coordinate reverses a nontrivial binary character. -/
theorem character_flip {n : ℕ} (a v : Vec n) (i : Fin n) (hi : a i = 1) :
    sign (a ⬝ᵥ (v + Pi.single i 1)) = -sign (a ⬝ᵥ v) := by
  rw [dotProduct_add]
  simpa only [dotProduct_single, mul_one, hi] using sign_add_one (a ⬝ᵥ v)

/-- The sum of a nontrivial binary character vanishes exactly. -/
theorem character_sum_zero {n : ℕ} (a : Vec n) (ha : a ≠ 0) :
    ∑ v : Vec n, sign (a ⬝ᵥ v) = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    apply ha
    ext i
    simpa using not_exists.mp h i
  have hi' : a i = 1 := by
    exact (bit_cases (a i)).resolve_left hi
  have hneg : ∑ v : Vec n, sign (a ⬝ᵥ v) =
      -(∑ v : Vec n, sign (a ⬝ᵥ v)) := by
    rw [← Finset.sum_neg_distrib]
    apply Fintype.sum_equiv (Equiv.addRight (Pi.single i (1 : Bit) : Vec n))
    intro v
    change sign (a ⬝ᵥ v) = -sign (a ⬝ᵥ (v + Pi.single i 1))
    rw [character_flip a v i hi', neg_neg]
  linarith

/-- Orthogonality of any two distinct sign rows of the full binary matrix. -/
theorem character_rows_orthogonal {n : ℕ} (a b : Vec n) (hab : a ≠ b) :
    ∑ v : Vec n, sign (a ⬝ᵥ v) * sign (b ⬝ᵥ v) = 0 := by
  have hadd : a + b ≠ 0 := by
    intro h
    apply hab
    have h' := congrArg (fun w : Vec n => w + b) h
    have hbb : b + b = 0 := by ext j; exact CharTwo.add_self_eq_zero (b j)
    simpa only [add_assoc, hbb, add_zero, zero_add] using h'
  rw [← character_sum_zero (a + b) hadd]
  apply Finset.sum_congr rfl
  intro v _
  rw [add_dotProduct, sign_add]

/-- Every binary character has square one. -/
@[simp] theorem sign_mul_self (a : Bit) : sign a * sign a = 1 := by
  rcases bit_cases a with rfl | rfl <;> norm_num

/-- The full Walsh matrix has Gram matrix `2^n I`, without asymptotic error. -/
theorem character_gram {n : ℕ} (a b : Vec n) :
    (∑ v : Vec n, sign (a ⬝ᵥ v) * sign (b ⬝ᵥ v)) =
      if a = b then (2 : ℝ) ^ n else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    simp [Vec, Bit]
  · rw [ite_eq_right hab]
    exact character_rows_orthogonal a b hab

/-- The column version of the same Gram identity. -/
theorem character_column_gram {n : ℕ} (v w : Vec n) :
    (∑ a : Vec n, sign (a ⬝ᵥ v) * sign (a ⬝ᵥ w)) =
      if v = w then (2 : ℝ) ^ n else 0 := by
  simpa only [dotProduct_comm] using character_gram v w

/-- The exact unnormalized Parseval identity for the binary sign transform. -/
theorem character_parseval {n : ℕ} (f : Vec n → ℝ) :
    (∑ a : Vec n, (∑ v : Vec n, sign (a ⬝ᵥ v) * f v) ^ 2) =
      (2 : ℝ) ^ n * ∑ v : Vec n, f v ^ 2 := by
  classical
  calc
    _ = ∑ a : Vec n, ∑ v : Vec n, ∑ w : Vec n,
        sign (a ⬝ᵥ v) * sign (a ⬝ᵥ w) * f v * f w := by
      apply Finset.sum_congr rfl
      intro a _
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = ∑ v : Vec n, ∑ w : Vec n,
        (∑ a : Vec n, sign (a ⬝ᵥ v) * sign (a ⬝ᵥ w)) * f v * f w := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.sum_mul, Finset.sum_mul]
    _ = (2 : ℝ) ^ n * ∑ v : Vec n, f v ^ 2 := by
      simp only [character_column_gram]
      simp [ite_mul, Finset.mul_sum, pow_two, mul_assoc]

end RefreshingProof.Binary
