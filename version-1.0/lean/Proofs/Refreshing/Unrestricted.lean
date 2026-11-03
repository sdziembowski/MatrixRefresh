import Proofs.Refreshing.ModelFacts
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Data.Fin.Rev

/-!
# Comparing unrestricted binary matrices with uniform invertible matrices

The constant-density estimate is derived from the actual general-linear-group cardinality formula. No density or invertibility probability bound is assumed.
-/

noncomputable section
open scoped BigOperators Matrix ENNReal

namespace RefreshingProof
open Refreshing

/-- A square n × n matrix over the binary field, without an invertibility restriction. -/
abbrev BinaryMatrix (n : ℕ) := Matrix (Fin n) (Fin n) Bit

/-- The exact finite binary GL cardinality, as a product of real factors. -/
theorem card_refreshMatrix_real (n : ℕ) :
    (Fintype.card (RefreshMatrix n) : ℝ) =
      ∏ i : Fin n, ((2 : ℝ) ^ n - (2 : ℝ) ^ i.val) := by
  classical
  have hnat : Fintype.card (RefreshMatrix n) =
      ∏ i : Fin n, ((2 : ℕ) ^ n - (2 : ℕ) ^ i.val) := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using
      (Matrix.card_GL_field (𝔽 := Bit) n)
  rw [hnat, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [Nat.cast_sub (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt i.isLt))]
  norm_cast

/-- There are exactly 2^(n²) unrestricted binary square matrices. -/
theorem card_binaryMatrix_real (n : ℕ) :
    (Fintype.card (BinaryMatrix n) : ℝ) = (2 : ℝ) ^ (n * n) := by
  have hnat : Fintype.card (BinaryMatrix n) = (2 : ℕ) ^ (n * n) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, ZMod.card] using
      (Matrix.card_matrix (m := Fin n) (n := Fin n) (α := Bit))
  exact_mod_cast hnat

/-- The actual fraction of all binary matrices which are invertible. -/
def invertibleDensity (n : ℕ) : ℝ :=
  (Fintype.card (RefreshMatrix n) : ℝ) / (Fintype.card (BinaryMatrix n) : ℝ)

/-- The familiar finite product for the binary invertibility probability. -/
theorem invertibleDensity_product (n : ℕ) :
    invertibleDensity n = ∏ i : Fin n, (1 - (1 / 2 : ℝ) ^ (i.val + 1)) := by
  classical
  unfold invertibleDensity
  rw [card_refreshMatrix_real, card_binaryMatrix_real]
  have hden : (2 : ℝ) ^ (n * n) = ∏ i : Fin n, (2 : ℝ) ^ n := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [hden, ← Finset.prod_div_distrib]
  calc
    _ = ∏ i : Fin n, (1 - (1 / 2 : ℝ) ^ (n - i.val)) := by
      apply Finset.prod_congr rfl
      intro i _
      have hp : (2 : ℝ) ^ n = (2 : ℝ) ^ i.val * (2 : ℝ) ^ (n - i.val) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hp, div_pow, one_pow]
      field_simp
    _ = _ := by
      apply Fintype.prod_equiv Fin.revPerm
      intro i
      congr 2
      simp only [Fin.revPerm_apply, Fin.val_rev]
      omega

/-- A finite union bound in product form for numbers in [0,1]. -/
theorem one_sub_sum_le_prod_one_sub {α : Type*} (s : Finset α) (a : α → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  revert h0 h1
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    intro h0 h1
    have hi0 := h0 i (Finset.mem_insert_self _ _)
    have hi1 := h1 i (Finset.mem_insert_self _ _)
    have hs0 : ∀ j ∈ s, 0 ≤ a j := fun j hj => h0 j (Finset.mem_insert_of_mem hj)
    have hs1 : ∀ j ∈ s, a j ≤ 1 := fun j hj => h1 j (Finset.mem_insert_of_mem hj)
    have hs := ih hs0 hs1
    have hsum0 : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg hs0
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hm := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hi1)
    nlinarith [mul_nonneg hi0 hsum0]

/-- The tail geometric sum is strictly below one half. -/
theorem binary_tail_geometric_sum (n : ℕ) :
    (∑ i : Fin n, (1 / 2 : ℝ) ^ (i.val + 2)) =
      1 / 2 - (1 / 2 : ℝ) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    ring

/-- Uniform invertible matrices have probability strictly greater than 1/4 among all unrestricted binary square matrices, including dimension zero. -/
theorem one_quarter_lt_invertibleDensity (n : ℕ) :
    (1 / 4 : ℝ) < invertibleDensity n := by
  rw [invertibleDensity_product]
  cases n with
  | zero => norm_num
  | succ n =>
    rw [Fin.prod_univ_succ]
    simp only [Fin.val_zero, zero_add, pow_one, Fin.val_succ]
    have htail := one_sub_sum_le_prod_one_sub (Finset.univ : Finset (Fin n))
      (fun i => (1 / 2 : ℝ) ^ (i.val + 2))
      (fun _ _ => by positivity) (fun _ _ => pow_le_one₀ (by norm_num) (by norm_num))
    rw [binary_tail_geometric_sum] at htail
    have hp : 0 < (1 / 2 : ℝ) ^ (n + 1) := by positivity
    have he : (∏ i : Fin n, (1 - (1 / 2 : ℝ) ^ (i.val + 1 + 1))) =
        ∏ i : Fin n, (1 - (1 / 2 : ℝ) ^ (i.val + 2)) := by
      apply Finset.prod_congr rfl
      intro i _
      congr 2
    rw [he]
    nlinarith

/-- Restricting a nonnegative sum to the injective image of matrix units can only decrease it. -/
theorem sum_invertible_le_sum_all (n : ℕ) (Z : BinaryMatrix n → ℝ)
    (hZ : ∀ A, 0 ≤ Z A) :
    (∑ M : RefreshMatrix n, Z (M : BinaryMatrix n)) ≤ ∑ A : BinaryMatrix n, Z A := by
  classical
  let e : RefreshMatrix n ↪ BinaryMatrix n := ⟨Units.val, Units.val_injective⟩
  have hsub : Finset.univ.map e ⊆ (Finset.univ : Finset (BinaryMatrix n)) :=
    Finset.subset_univ _
  calc
    _ = ∑ A ∈ Finset.univ.map e, Z A := by
      simp only [Finset.sum_map, e, Function.Embedding.coeFn_mk]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun A _ _ => hZ A)

/-- The actual uniform invertible average is at most four times the actual uniform unrestricted average, for every nonnegative binary-matrix function. -/
theorem average_invertible_le_four (n : ℕ) (Z : BinaryMatrix n → ℝ)
    (hZ : ∀ A, 0 ≤ Z A) :
    (Fintype.card (RefreshMatrix n) : ℝ)⁻¹ *
        (∑ M : RefreshMatrix n, Z (M : BinaryMatrix n)) ≤
      4 * ((Fintype.card (BinaryMatrix n) : ℝ)⁻¹ * ∑ A : BinaryMatrix n, Z A) := by
  have hG : 0 < (Fintype.card (RefreshMatrix n) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hA : 0 < (Fintype.card (BinaryMatrix n) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hden := one_quarter_lt_invertibleDensity n
  unfold invertibleDensity at hden
  have hcard : (Fintype.card (BinaryMatrix n) : ℝ) ≤
      4 * (Fintype.card (RefreshMatrix n) : ℝ) := by
    have h := (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 4) hA).1 hden
    linarith
  have hinv : (Fintype.card (RefreshMatrix n) : ℝ)⁻¹ ≤
      4 * (Fintype.card (BinaryMatrix n) : ℝ)⁻¹ := by
    have h : (1 : ℝ) / (Fintype.card (RefreshMatrix n) : ℝ) ≤
        4 / (Fintype.card (BinaryMatrix n) : ℝ) :=
      (div_le_div_iff₀ hG hA).2 (by simpa using hcard)
    simpa only [one_div, div_eq_mul_inv, one_mul] using h
  calc
    _ ≤ (Fintype.card (RefreshMatrix n) : ℝ)⁻¹ * ∑ A : BinaryMatrix n, Z A :=
      mul_le_mul_of_nonneg_left (sum_invertible_le_sum_all n Z hZ) (inv_nonneg.mpr hG.le)
    _ ≤ (4 * (Fintype.card (BinaryMatrix n) : ℝ)⁻¹) * ∑ A : BinaryMatrix n, Z A :=
      mul_le_mul_of_nonneg_right hinv (Finset.sum_nonneg (fun A _ => hZ A))
    _ = _ := by ring

/-- The same comparison written using the explicit point masses of both uniform PMFs. -/
theorem uniformPMF_invertible_le_four (n : ℕ) (Z : BinaryMatrix n → ℝ)
    (hZ : ∀ A, 0 ≤ Z A) :
    (∑ M : RefreshMatrix n, (uniformPMF (RefreshMatrix n) M).toReal * Z (M : BinaryMatrix n)) ≤
      4 * ∑ A : BinaryMatrix n, (uniformPMF (BinaryMatrix n) A).toReal * Z A := by
  simpa only [uniformPMF_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ← Finset.mul_sum] using average_invertible_le_four n Z hZ

end RefreshingProof
