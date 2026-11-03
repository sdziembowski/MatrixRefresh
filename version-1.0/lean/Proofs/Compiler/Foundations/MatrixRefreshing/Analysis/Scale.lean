import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Notation



/-! Basic cardinality and logarithmic conversions for the security bounds. -/

set_option autoImplicit false

namespace MatrixRefresh

open Refresh

variable {F : Type*} [Field F] [Fintype F]

/-- Every finite field has at least two elements, since zero and one are distinct. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

2 ≤ |F|.
-/
theorem field_card_two_le : 2 ≤ fieldCard F :=
  Fintype.one_lt_card

-- Positivity of the field cardinality supplies the hypotheses for real powers, division, and monotonicity. Keep these casts out of the analytic arguments.
/-- The finite field's cardinality, viewed as a real number, is at least two. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

2 ≤ |F|.
-/
theorem fieldCard_cast_two_le : (2 : ℝ) ≤ fieldCard F := by
  exact_mod_cast (field_card_two_le (F := F))

/-- The real-valued field cardinality is strictly positive, allowing division and real powers. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

0 < |F|.
-/
theorem fieldCard_cast_pos : (0 : ℝ) < fieldCard F :=
  lt_of_lt_of_le (by norm_num) fieldCard_cast_two_le

/-- The real-valued field cardinality is at least one. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

1 ≤ |F|.
-/
theorem fieldCard_cast_one_le : (1 : ℝ) ≤ fieldCard F :=
  (by norm_num : (1 : ℝ) ≤ 2).trans fieldCard_cast_two_le

/-- Information length of an `n`-coordinate field vector, in bits. This real quantity need not be an integer when `(fieldCard F)` is not a power of two. -/
/-
Mathematical definition (normal notation): For F a set; n ∈ ℕ, assume F is finite. define

bitLength(n) := n · Real.logb(2, |F|).
-/
noncomputable def bitLength (F : Type*) [Fintype F] (n : ℕ) : ℝ :=
  (n : ℝ) * Real.logb 2 (fieldCard F : ℝ)

/-- The number of field vectors in any dimension is strictly positive when viewed as a real number. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, we have

0 < |F|ⁿ.
-/
theorem vectorCard_cast_pos (n : ℕ) : 0 < (vectorCard F n : ℝ) := by
  simpa only [vectorCard, Nat.cast_pow] using pow_pos (fieldCard_cast_pos (F := F)) n

/--
The complete binary answer alphabet has at least one element for every leakage length.

Uniform answer alphabets remain binary: this is unrelated to the share field.
-/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ℓ ∈ ℕ, we have

1 ≤ K(ℓ).
-/
theorem K_cast_one_le (ℓ : ℕ) : (1 : ℝ) ≤ (K ℓ : ℝ) := by
  exact_mod_cast (Nat.one_le_two_pow (n := 2 * ℓ))

/-- The complete binary answer alphabet of leakage length `ℓ` has real cardinality `2^(2 ℓ)`. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ℓ ∈ ℕ, we have

K(ℓ) = Real.rpow(2, (2 · ℓ)).
-/
theorem K_eq_rpow_two (ℓ : ℕ) : (K ℓ : ℝ) = Real.rpow 2 (2 * (ℓ : ℝ)) := by
  simpa only [K, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, Real.rpow_eq_pow] using
    (Real.rpow_natCast (2 : ℝ) (2 * ℓ)).symm

/-- Change a field-size power to base two, keeping the bit-length factor exact. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For x ∈ ℝ, we have

Real.rpow(|F|, x) = Real.rpow(2, (Real.logb(2, |F|) · x)).
-/
theorem fieldCard_rpow_eq_two (x : ℝ) :
    Real.rpow (fieldCard F : ℝ) x = Real.rpow 2 (Real.logb 2 (fieldCard F : ℝ) * x) := by
  change (fieldCard F : ℝ) ^ x = (2 : ℝ) ^ (Real.logb 2 (fieldCard F : ℝ) * x)
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) fieldCard_cast_pos]

end MatrixRefresh
