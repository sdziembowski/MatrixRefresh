import Proofs.Compiler.Foundations.MatrixRefreshing.Probability.FiniteDistribution



/-!
# From scalar tests to statistical distance

The hybrid argument compares acceptance probabilities for each Boolean test. `statisticalDistance_le_iff_tests` turns those scalar estimates into a bound on the entire transcript distribution. Its converse is constructive at the level of finite events: choose the points where `P` assigns at least as much mass as `Q`.

The key normalization is that `P - Q` has total mass zero. Consequently its positive mass equals half its absolute mass, which explains the factor `1/2` in statistical distance and avoids a factor-of-two loss in the test bound.
-/

set_option autoImplicit false

open scoped BigOperators

namespace MatrixRefresh

open Refresh

variable {α : Type*} [Fintype α]

/-- The acceptance probability of a deterministic Boolean test. -/
/-
Mathematical definition (normal notation): For P ∈ 𝒟(α); test ∈ α → Bool, define

testExpectation(P, test) := 𝔼_(a ← P) [{ 1 if test(a),; 0 otherwise }].
-/
def testExpectation (P : FiniteDistribution α) (test : α → Bool) : ℝ :=
  P.expect (fun a => if test a then 1 else 0)

/-- The difference of two probability mass functions has total signed mass zero. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P, Q ∈ 𝒟(α), we have

(∑ₐ ((P(a) - Q(a)))) = 0.
-/
private theorem signed_mass_sum (P Q : FiniteDistribution α) :
    (∑ a, (P.weight a - Q.weight a)) = 0 := by
  rw [Finset.sum_sub_distrib, P.total, Q.total, sub_self]

/-- A difference of expectations is the sum of the function against the signed difference of the two probability weights. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P, Q ∈ 𝒟(α); f ∈ α → ℝ, we have

𝔼_(u ← P) [f(u)] - 𝔼_(v ← Q) [f(v)] = ∑ₐ ((P(a) - Q(a)) · f(a)).
-/
private theorem expect_difference (P Q : FiniteDistribution α) (f : α → ℝ) :
    P.expect f - Q.expect f = ∑ a, (P.weight a - Q.weight a) * f a := by
  simp [FiniteDistribution.expect, sub_mul, Finset.sum_sub_distrib]

/-- For a function valued in `[0,1]`, the expectation under `P` minus that under `Q` is at most their statistical distance. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P, Q ∈ 𝒟(α); f ∈ α → ℝ, assume ∀ a, 0 ≤ f(a); ∀ a, f(a) ≤ 1. Then

𝔼_(u ← P) [f(u)] - 𝔼_(v ← Q) [f(v)] ≤ δ(P, Q).
-/
theorem expect_sub_expect_le_statisticalDistance (P Q : FiniteDistribution α) (f : α → ℝ)
    (hf0 : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1) :
    P.expect f - Q.expect f ≤ statisticalDistance P Q := by
  -- Each contribution is bounded by the positive part of the signed mass. For negative mass, the test's lower bound is used; for positive mass, its upper bound is used. Summation cancels the remaining signed term.
  have hp (a : α) : (P.weight a - Q.weight a) * f a ≤
      (|P.weight a - Q.weight a| + (P.weight a - Q.weight a)) / 2 := by
    by_cases h : 0 ≤ P.weight a - Q.weight a
    · rw [abs_of_nonneg h]
      nlinarith [mul_le_mul_of_nonneg_left (hf1 a) h]
    · have hn : P.weight a - Q.weight a ≤ 0 := le_of_lt (lt_of_not_ge h)
      rw [abs_of_nonpos hn]
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hn (hf0 a)]
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hp a)
  rw [expect_difference]
  calc
    _ ≤ ∑ a, (|P.weight a - Q.weight a| + (P.weight a - Q.weight a)) / 2 := hs
    _ = statisticalDistance P Q := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, signed_mass_sum]
      simp [statisticalDistance, variationNorm, div_eq_mul_inv, mul_comm]

/-- Any test taking values in `[0,1]` distinguishes two distributions by at most their statistical distance, in absolute acceptance-probability difference. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P, Q ∈ 𝒟(α); f ∈ α → ℝ, assume ∀ a, 0 ≤ f(a); ∀ a, f(a) ≤ 1. Then

|𝔼_(u ← P) [f(u)] - 𝔼_(v ← Q) [f(v)]| ≤ δ(P, Q).
-/
theorem abs_expect_sub_expect_le_statisticalDistance (P Q : FiniteDistribution α) (f : α → ℝ)
    (hf0 : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1) :
    |P.expect f - Q.expect f| ≤ statisticalDistance P Q := by
  apply abs_le.mpr
  constructor
  · have h := expect_sub_expect_le_statisticalDistance Q P f hf0 hf1
    rw [statisticalDistance_symm Q P] at h
    linarith
  · exact expect_sub_expect_le_statisticalDistance P Q f hf0 hf1

/-- The acceptance probabilities of any Boolean test differ by at most the statistical distance of the input distributions. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P, Q ∈ 𝒟(α); test ∈ α → Bool, we have

|testExpectation(P, test) - testExpectation(Q, test)| ≤ δ(P, Q) .
-/
theorem testExpectation_sub_le_statisticalDistance (P Q : FiniteDistribution α) (test : α → Bool) :
    |testExpectation P test - testExpectation Q test| ≤ statisticalDistance P Q := by
  apply abs_expect_sub_expect_le_statisticalDistance
  · intro a
    split <;> norm_num
  · intro a
    split <;> norm_num

/-- The event on which `P` has at least as much mass as `Q` realizes the distance. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P, Q ∈ 𝒟(α), we have

∃ test ∈ α → Bool, testExpectation(P, test) - testExpectation(Q, test) = δ(P, Q).
-/
theorem exists_test_eq_statisticalDistance (P Q : FiniteDistribution α) :
    ∃ test : α → Bool,
      testExpectation P test - testExpectation Q test = statisticalDistance P Q := by
  classical
  -- This event attains the positive mass exactly, including ties harmlessly.
  refine ⟨fun a => decide (Q.weight a ≤ P.weight a), ?_⟩
  unfold testExpectation
  rw [expect_difference]
  calc
    _ = ∑ a, (|P.weight a - Q.weight a| + (P.weight a - Q.weight a)) / 2 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : Q.weight a ≤ P.weight a
      · simp [h, abs_of_nonneg (sub_nonneg.mpr h)]
      · simp [h, abs_of_nonpos (sub_nonpos.mpr (le_of_lt (lt_of_not_ge h)))]
    _ = statisticalDistance P Q := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, signed_mass_sum]
      simp [statisticalDistance, variationNorm, div_eq_mul_inv, mul_comm]

/-- Public interface for the transcript hybrids: it is sufficient to bound every Boolean distinguisher with the same scalar `c`. No sign assumption on `c` is needed; the maximizing test supplies the reverse implication. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P, Q ∈ 𝒟(α); c ∈ ℝ, we have

δ(P, Q) ≤ c ⇔ ∀ test ∈ α → Bool, |testExpectation(P, test) - testExpectation(Q, test)| ≤ c.
-/
theorem statisticalDistance_le_iff_tests (P Q : FiniteDistribution α) (c : ℝ) :
    statisticalDistance P Q ≤ c ↔
      ∀ test : α → Bool, |testExpectation P test - testExpectation Q test| ≤ c := by
  constructor
  · intro h test
    exact (testExpectation_sub_le_statisticalDistance P Q test).trans h
  · intro h
    obtain ⟨test, ht⟩ := exists_test_eq_statisticalDistance P Q
    have hb := h test
    rwa [ht, abs_of_nonneg (statisticalDistance_nonneg P Q)] at hb

/-- If `P` contains at least a fraction `c ≤ 1` of `Q` pointwise, their statistical distance is at most the remaining mass `1 - c`. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A a set; P, Q ∈ 𝒟(A); c ∈ ℝ, assume A is finite; c ≤ 1; ∀ a, c · Q(a) ≤ P(a). Then

δ(P, Q) ≤ 1 - c.
-/
theorem statisticalDistance_le_one_sub_of_weight_ge {A : Type*} [Fintype A]
    (P Q : FiniteDistribution A) (c : ℝ) (hc : c ≤ 1)
    (hweight : ∀ a, c * Q.weight a ≤ P.weight a) : statisticalDistance P Q ≤ 1 - c := by
  have hpoint (a : A) : |P.weight a - Q.weight a| ≤ P.weight a + Q.weight a - 2 * c * Q.weight a := by
    by_cases h : P.weight a ≤ Q.weight a
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      linarith [hweight a]
    · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt (lt_of_not_ge h)))]
      nlinarith [mul_le_mul_of_nonneg_right hc (Q.nonneg a)]
  unfold statisticalDistance variationNorm
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hpoint a)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, P.total, Q.total] at hsum
  linarith

/-- Uniform conditioning onto an embedded finite subset loses at most its omitted mass. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A,B a set; e ∈ A ↪ B, assume A is finite; B is finite; A ≠ ∅; B ≠ ∅. Then

δ(𝒰_B, (e_*𝒰_A)) ≤ 1 - |A| / |B|.
-/
theorem uniform_embedding_statisticalDistance {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (e : A ↪ B) :
    statisticalDistance (FiniteDistribution.uniform : FiniteDistribution B) ((FiniteDistribution.uniform : FiniteDistribution A).map e) ≤
      1 - (Fintype.card A : ℝ) / Fintype.card B := by
  classical
  have ha : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hb : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hcard : (Fintype.card A : ℝ) ≤ Fintype.card B := by
    exact_mod_cast Fintype.card_le_of_injective e e.injective
  apply statisticalDistance_le_one_sub_of_weight_ge _ _ _ ((div_le_one hb).2 hcard)
  intro b
  have hmass : ((FiniteDistribution.uniform : FiniteDistribution A).map e).weight b ≤ 1 / (Fintype.card A : ℝ) := by
    rw [FiniteDistribution.uniform_map_weight]
    letI : Subsingleton {a : A // e a = b} := ⟨fun a a' => Subtype.ext (e.injective (a.property.trans a'.property.symm))⟩
    have hc : (Fintype.card {a : A // e a = b} : ℝ) ≤ 1 := by
      exact_mod_cast Fintype.card_le_one_iff_subsingleton.mpr (inferInstance : Subsingleton {a : A // e a = b})
    exact div_le_div_of_nonneg_right hc ha.le
  calc
    _ ≤ ((Fintype.card A : ℝ) / Fintype.card B) * (1 / (Fintype.card A : ℝ)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (FiniteDistribution.uniform : FiniteDistribution B).weight b := by
      simp only [FiniteDistribution.uniform]
      field_simp

end MatrixRefresh
