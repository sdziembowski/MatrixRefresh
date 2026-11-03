import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.EncodingBounds
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.InitialDistribution



set_option autoImplicit false

namespace Refresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The operational initial distribution is the literal uniform fiber weight on the common carrier. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F; x ∈ State(F, n), assume 2 ≤ n. Then

μₛ(x) = { 1 / |Fiber(F, n, s)| if secret(x) = s,; 0 otherwise }.
-/
theorem mu_weight (n : ℕ) (hn : 2 ≤ n) (s : F) (x : State F n) :
    (mu F n hn s).weight x =
      if secret x = s then 1 / (Fintype.card (Fiber F n s) : ℝ) else 0 := by
  classical
  letI := fiber_nonempty F n hn s
  unfold mu
  rw [FiniteDistribution.uniform_map_weight]
  by_cases hx : secret x = s
  · have hcard : Fintype.card {a : Fiber F n s // a.val = x} = 1 := by
      have hiff (a : Fiber F n s) : a.val = x ↔ a = ⟨x, hx⟩ :=
        ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
      simpa using Fintype.card_congr (Equiv.subtypeEquivRight hiff)
    simp [hx, hcard]
  · haveI : IsEmpty {a : Fiber F n s // a.val = x} := ⟨by
      intro a
      apply hx
      rw [← a.property]
      exact a.val.property⟩
    simp [hx]

/-- A reference state formed from two independent uniform nonzero shares. -/
/-
Mathematical definition (normal notation): For F a set; n ∈ ℕ, assume F is a field; F is finite; 2 ≤ n. define

independentStateDistribution(n) := ((stateEquivProd(F, n))⁻¹_*(uniformShare(F, n) ⊗ uniformShare(F, n))).
-/
noncomputable def independentStateDistribution (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) (hn : 2 ≤ n) : FiniteDistribution (State F n) :=
  ((uniformShare F n hn).prod (uniformShare F n hn)).map (stateEquivProd F n).symm

/-- Every state receives mass `1 / (shareCard F n)²` under two independent uniform nonzero shares. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; x ∈ State(F, n), assume 2 ≤ n. Then

independentStateDistribution(F, n)(x) = 1 / (|F|ⁿ-1)².
-/
theorem independentStateDistribution_weight (n : ℕ) (hn : 2 ≤ n) (x : State F n) :
    (independentStateDistribution F n hn).weight x = 1 / (shareCard F n : ℝ) ^ 2 := by
  rw [independentStateDistribution, FiniteDistribution.map_equiv_weight]
  change (Fintype.card (U F n) : ℝ)⁻¹ * (Fintype.card (U F n) : ℝ)⁻¹ = _
  rw [nonzero_vector_card]
  simp [shareCard, vectorCard, pow_two, div_eq_mul_inv]

/-- The density formula refers to the actual initial sampling distribution. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F; x ∈ State(F, n), assume 2 ≤ n. Then

μₛ(x) = ({ densityWeight(F, n, s) if secret(x) = s,; 0 otherwise }) · independentStateDistribution(F, n)(x).
-/
theorem mu_weight_density (n : ℕ) (hn : 2 ≤ n) (s : F) (x : State F n) :
    (mu F n hn s).weight x =
      (if secret x = s then densityWeight F n s else 0) *
        (independentStateDistribution F n hn).weight x := by
  rw [mu_weight, independentStateDistribution_weight]
  by_cases hx : secret x = s
  · simp only [hx, if_true]
    unfold densityWeight
    have hd : (shareCard F n : ℝ) ≠ 0 := ne_of_gt (nonzeroCard_real_pos hn)
    have hF : (Fintype.card (Fiber F n s) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (fiber_card_pos hn s)
    field_simp
  · simp [hx]

/-- Pointwise density bound for every secret, relative to independent shares. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F; x ∈ State(F, n), assume 2 ≤ n. Then

μₛ(x) ≤ 2 · |F| · independentStateDistribution(F, n)(x).
-/
theorem mu_weight_le (n : ℕ) (hn : 2 ≤ n) (s : F) (x : State F n) :
    (mu F n hn s).weight x ≤ 2 * (fieldCard F : ℝ) * (independentStateDistribution F n hn).weight x := by
  rw [mu_weight_density]
  apply mul_le_mul_of_nonneg_right _ ((independentStateDistribution F n hn).nonneg x)
  split_ifs
  · exact densityWeight_le_two_mul_q hn s
  · positivity

/-- Arbitrary independently encoded secrets have density at most four (fieldCard F) squared. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; a, b ∈ F; x, y ∈ State(F, n), assume 2 ≤ n. Then

μₐ(x) · μ_b(y) ≤ (4 · (|F|)²) · (independentStateDistribution(F, n)(x) · independentStateDistribution(F, n)(y)).
-/
theorem mixed_state_density_le (n : ℕ) (hn : 2 ≤ n) (a b : F) (x y : State F n) :
    (mu F n hn a).weight x * (mu F n hn b).weight y ≤
      (4 * (fieldCard F : ℝ) ^ 2) *
        ((independentStateDistribution F n hn).weight x * (independentStateDistribution F n hn).weight y) := by
  have h := mul_le_mul (mu_weight_le n hn a x) (mu_weight_le n hn b y)
    ((mu F n hn b).nonneg y)
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * (fieldCard F : ℝ))
      ((independentStateDistribution F n hn).nonneg x))
  nlinarith

end Refresh
