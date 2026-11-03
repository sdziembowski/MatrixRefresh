import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.Construction.MatrixRefreshing
/-!
# Tensor features and matrix sampling

Tensor encoding maps and the finite rejection-sampling constructions for uniform invertible matrices.

This module is part of the constructive compiler model; it imports no compiler proof theorem. The public source and execution interfaces are in Compiler.Direct and Compiler.Stateful.
-/
set_option backward.isDefEq.respectTransparency false
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler
open Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end CircuitCompiler
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler
open Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end CircuitCompiler
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Sampling
open Refresh
variable {α β : Type*} [Fintype α] [Fintype β]
end CircuitCompiler.Sampling
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Sampling
open Refresh
variable {α β : Type*} [Fintype α] [Fintype β]
theorem acceptance_nonneg (P : FiniteDistribution α) (accept : α → Bool) :
    0 ≤ acceptance P accept := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact P.nonneg a
  · rfl
end CircuitCompiler.Sampling
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Sampling
open Refresh
variable {α β : Type*} [Fintype α] [Fintype β]
/-- The exact accepted distribution. Its existence needs positive acceptance. -/

noncomputable def accepted (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) : FiniteDistribution α where
  weight a := (if accept a then P.weight a else 0) / acceptance P accept
  nonneg a := div_nonneg (by split_ifs; exact P.nonneg a; rfl) hp.le
  total := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hp)
/-- One actual trial, retaining the supplied distribution only on rejection. -/

noncomputable def trial (P : FiniteDistribution α) (accept : α → Bool)
    (fallback : FiniteDistribution α) : FiniteDistribution α :=
  P.bind fun a => if accept a then FiniteDistribution.pure a else fallback
/-- At most `attempts` trials, then a specified fallback distribution. -/

noncomputable def capped (P : FiniteDistribution α) (accept : α → Bool)
    (fallback : FiniteDistribution α) : ℕ → FiniteDistribution α
  | 0 => fallback
  | attempts + 1 => trial P accept (capped P accept fallback attempts)
universe u
end CircuitCompiler.Sampling
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler
open Refresh Sampling
variable {Ω Y Z : Type*} [Fintype Ω] [Fintype Y] [Fintype Z] [DecidableEq Y]
/-- The original sample conditioned on a deterministic observed value. -/

noncomputable def conditional (P : FiniteDistribution Ω) (value : Ω → Y) (y : Y) : FiniteDistribution Ω :=
  if hp : 0 < acceptance P (fun ω => decide (value ω = y)) then
    accepted P (fun ω => decide (value ω = y)) hp else P
end CircuitCompiler
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
namespace MatrixRefresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
open Refresh Module
open scoped Classical
/-- There are `(fieldCard F)^(n^2)` unrestricted `n` by `n` matrices: each of the `n^2` entries is chosen independently from the field. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, we have

|F^({0,…,n−1} × {0,…,n−1})| = (|F|)^(n²).
-/
theorem card_all_matrices (n : ℕ) :
    Fintype.card (Matrix (Fin n) (Fin n) F) = fieldCard F ^ (n ^ 2) := by
  change Fintype.card (Fin n → Fin n → F) = _
  rw [Fintype.card_fun, Fintype.card_fun]
  simp [fieldCard, pow_mul, pow_two]
end MatrixRefresh
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
namespace MatrixRefresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
open Refresh
open scoped BigOperators
/-- Multiplying numbers in the unit interval loses at most the sum of their defects. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ι a set; s ∈ Finset(ι); f ∈ ι → ℝ, assume ∀ i ∈ s, 0 ≤ f(i); ∀ i ∈ s, f(i) ≤ 1. Then

1 - ∏_(i ∈ s) (f(i)) ≤ ∑_(i ∈ s) ((1 - f(i))).
-/
theorem product_defect_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf₀ : ∀ i ∈ s, 0 ≤ f i) (hf₁ : ∀ i ∈ s, f i ≤ 1) :
    1 - ∏ i ∈ s, f i ≤ ∑ i ∈ s, (1 - f i) := by
  classical
  revert hf₀ hf₁
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    intro hf₀ hf₁
    have hs₀ : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf₀ i (Finset.mem_insert_of_mem hi)
    have hs₁ : ∀ i ∈ s, f i ≤ 1 := fun i hi => hf₁ i (Finset.mem_insert_of_mem hi)
    have hp := Finset.prod_le_one₀ hs₀ hs₁
    have hi := ih hs₀ hs₁
    have hx := hf₁ a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hp)]
/-- The first `m` powers of two sum to `2^m - 1`. This evaluates the total defect of the binary invertibility factors. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ, we have

∑_(i ∈ {0,…,m−1}) (2ⁱ) = 2ᵐ - 1.
-/
theorem sum_two_pow (m : ℕ) : ∑ i ∈ Finset.range m, (2 : ℝ) ^ i = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
/-- A dimension-independent lower bound for the binary invertibility product. The last factor is exactly `1/2`; the defect estimate bounds the product of the earlier factors below by another `1/2`. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, we have

1 / 4 ≤ ∏_(i ∈ {0,…,n−1}) ((1 - 2ⁱ / 2ⁿ)).
-/
theorem binary_invertibility_product_ge (n : ℕ) :
    (1 / 4 : ℝ) ≤ ∏ i ∈ Finset.range n, (1 - (2 : ℝ) ^ i / 2 ^ n) := by
  cases n with
  | zero => norm_num
  | succ m =>
    have hf₀ : ∀ i ∈ Finset.range m, 0 ≤ 1 - (2 : ℝ) ^ i / 2 ^ (m + 1) := by
      intro i hi
      apply sub_nonneg.mpr
      apply (div_le_one (by positivity)).mpr
      have him : i < m := Finset.mem_range.mp hi
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : i ≤ m + 1)
    have hf₁ : ∀ i ∈ Finset.range m, 1 - (2 : ℝ) ^ i / 2 ^ (m + 1) ≤ 1 := by
      intro i _
      exact sub_le_self _ (by positivity)
    have hprod := product_defect_le (Finset.range m)
      (fun i => 1 - (2 : ℝ) ^ i / 2 ^ (m + 1)) hf₀ hf₁
    have hsum : (∑ i ∈ Finset.range m, (2 : ℝ) ^ i / 2 ^ (m + 1)) ≤ 1 / 2 := by
      rw [← Finset.sum_div, sum_two_pow, pow_succ]
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    simp only [sub_sub_cancel] at hprod
    have hlast : 1 - (2 : ℝ) ^ m / 2 ^ (m + 1) = 1 / 2 := by
      rw [pow_succ]
      field_simp
      norm_num
    rw [Finset.prod_range_succ, hlast]
    linarith
/-- The binary field gives the smallest factor at every position: for `i < n`, the loss is `Q^i / Q^n = Q^(-(n-i))`, which decreases as `Q` grows. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Q ∈ ℝ; n ∈ ℕ, assume 2 ≤ Q. Then

1 / 4 ≤ ∏_(i ∈ {0,…,n−1}) ((1 - Qⁱ / Qⁿ)).
-/
theorem invertibility_product_ge (Q : ℝ) (hQ : 2 ≤ Q) (n : ℕ) :
    (1 / 4 : ℝ) ≤ ∏ i ∈ Finset.range n, (1 - Q ^ i / Q ^ n) := by
  apply (binary_invertibility_product_ge n).trans
  apply Finset.prod_le_prod₀
  · intro i hi
    apply sub_nonneg.mpr
    apply (div_le_one (by positivity)).mpr
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Finset.mem_range.mp hi).le
  · intro i hi
    apply sub_le_sub_left
    have hin : i ≤ n := (Finset.mem_range.mp hi).le
    have hratio (a : ℝ) (ha : 0 < a) : a ^ i / a ^ n = (a ^ (n - i))⁻¹ := by
      conv_lhs => rw [← Nat.add_sub_of_le hin, pow_add]
      field_simp
    rw [hratio Q (by linarith), hratio 2 (by norm_num)]
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact pow_le_pow_left₀ (by norm_num) hQ _
/-- Count an ordered basis column by column: column `i` must avoid the span of its predecessors, leaving `(fieldCard F)^n - (fieldCard F)^i` choices. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, we have

|GLₙ(F)| = ∏_(i ∈ {0,…,n−1}) (((|F|)ⁿ - (|F|)ⁱ)).
-/
theorem card_GL (n : ℕ) :
    Fintype.card (Refresh.«GL» F n) = ∏ i ∈ Finset.range n, (fieldCard F ^ n - fieldCard F ^ i) := by
  have hc := Matrix.card_GL_field (𝔽 := F) n
  rw [Finset.prod_range]
  simpa [Nat.card_eq_fintype_card, fieldCard] using hc
/-- The proportion of all `n` by `n` matrices that are invertible is exactly the product of `1 - (fieldCard F)^i/(fieldCard F)^n` for `i = 0,...,n-1`. The numerator counts ordered bases; division by `(fieldCard F)^(n^2)` normalizes to the unrestricted matrix distribution. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, we have

|GLₙ(F)| / |F^({0,…,n−1} × {0,…,n−1})| = ∏_(i ∈ {0,…,n−1}) ((1 - (|F|)ⁱ / (|F|)ⁿ)).
-/
theorem invertibility_probability_eq_product (n : ℕ) :
    (Fintype.card (Refresh.«GL» F n) : ℝ) / Fintype.card (Matrix (Fin n) (Fin n) F) =
      ∏ i ∈ Finset.range n, (1 - (fieldCard F : ℝ) ^ i / (fieldCard F : ℝ) ^ n) := by
  rw [card_GL, card_all_matrices, Nat.cast_prod]
  have hcast : ∀ i ∈ Finset.range n,
      ((fieldCard F ^ n - fieldCard F ^ i : ℕ) : ℝ) = (fieldCard F : ℝ) ^ n - (fieldCard F : ℝ) ^ i := by
    intro i hi
    rw [Nat.cast_sub (Nat.pow_le_pow_right
      (show 0 < fieldCard F from Fintype.card_pos) (Finset.mem_range.mp hi).le)]
    simp
  rw [Finset.prod_congr rfl hcast]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hden : (fieldCard F : ℝ) ^ (n ^ 2) = ∏ _i ∈ Finset.range n, (fieldCard F : ℝ) ^ n := by
    simp [pow_mul, pow_two]
  rw [hden, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hqpos : (0 : ℝ) < fieldCard F := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  rw [sub_div, div_self (by positivity)]
/-- At least one quarter of all matrices are invertible, uniformly over finite fields. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, we have

1 / 4 ≤ |GLₙ(F)| / |F^({0,…,n−1} × {0,…,n−1})|.
-/
theorem invertibility_probability_ge_quarter (n : ℕ) :
    (1 / 4 : ℝ) ≤ (Fintype.card (Refresh.«GL» F n) : ℝ) /
      Fintype.card (Matrix (Fin n) (Fin n) F) := by
  rw [invertibility_probability_eq_product]
  apply invertibility_product_ge
  exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card F)
end MatrixRefresh
end
section
/-!
# GadgetEncodings

Definitions used by the headline security statements. The construction facts are included in this self-contained model.
-/
/-!
## GateDensity
-/
section
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler
open Refresh MatrixRefresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- A local party retains both old operands and its new long share. -/

abbrev GateSide (F : Type*) [Field F] (n m : ℕ) := (U F n × U F n) × U F m
end CircuitCompiler
end
/-!
## GateDimensions
-/
section
set_option autoImplicit false
open scoped BigOperators Matrix Matrix.Norms.L2Operator
namespace CircuitCompiler
open Refresh MatrixRefresh TableAnalysis Shortening
noncomputable section
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype A]
end
end CircuitCompiler
end
/-!
## AugmentedTensor
-/
section
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end CircuitCompiler.Rectangular
end
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Sampling
open Refresh
variable {α : Type*} [Fintype α] [Nonempty α]
theorem acceptance_uniform (accept : α → Bool) :
    acceptance (FiniteDistribution.uniform : FiniteDistribution α) accept =
      (Fintype.card {a : α // accept a = true} : ℝ) / Fintype.card α := by
  classical
  simp only [acceptance, FiniteDistribution.uniform, div_eq_mul_inv]
  rw [Fintype.card_subtype]
  have hpoint (a : α) :
      (if accept a then (Fintype.card α : ℝ)⁻¹ else 0) =
        (if accept a = true then (1 : ℝ) else 0) * (Fintype.card α : ℝ)⁻¹ := by
    split_ifs <;> simp_all
  simp_rw [hpoint]
  rw [← Finset.sum_mul, Finset.sum_boole]
/-- Conditioning a uniform proposal retains the uniform satisfying-input distribution. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For accept ∈ α → Bool, assume 0 < acceptance(𝒰_α, accept); {a ∈ α | accept(a) = true} ≠ ∅. Then

accepted(𝒰_α, accept) = (Subtype_*𝒰_({a ∈ α | accept(a) = true})).
-/
theorem accepted_uniform (accept : α → Bool)
    (hp : 0 < acceptance (FiniteDistribution.uniform : FiniteDistribution α) accept)
    [Nonempty {a : α // accept a = true}] :
    accepted (FiniteDistribution.uniform : FiniteDistribution α) accept hp =
      (FiniteDistribution.uniform : FiniteDistribution {a : α // accept a = true}).map Subtype.val := by
  classical
  have hα : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext a
  rw [FiniteDistribution.uniform_map_weight]
  have hc : Fintype.card {b : {a : α // accept a = true} // b.val = a} =
      if accept a then 1 else 0 := by
    cases ha : accept a
    · haveI : IsEmpty {b : {a : α // accept a = true} // b.val = a} :=
        ⟨fun b => by simpa [b.property, ha] using b.val.property⟩
      simp
    · letI : Unique {b : {a : α // accept a = true} // b.val = a} :=
        { default := ⟨⟨a, ha⟩, rfl⟩
          uniq := fun b => Subtype.ext (Subtype.ext b.property) }
      simp
  rw [hc]
  simp only [accepted]
  rw [acceptance_uniform]
  simp only [FiniteDistribution.uniform]
  cases accept a <;> simp [hα, div_eq_mul_inv]
end CircuitCompiler.Sampling
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Sampling
open Refresh
variable {α : Type*} [Fintype α] [Nonempty α]
section Matrix
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end Matrix
end CircuitCompiler.Sampling
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Sampling
open Refresh
variable {α : Type*} [Fintype α] [Nonempty α]
section Matrix
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
theorem matrix_acceptance_ge_quarter (n : ℕ) :
    (1 / 4 : ℝ) ≤ acceptance
      (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin n) (Fin n) F)) invertibleTest := by
  rw [acceptance_uniform, ← Fintype.card_congr (invertibleEquiv (F := F) n)]
  exact MatrixRefresh.invertibility_probability_ge_quarter n
end Matrix
end CircuitCompiler.Sampling
end
