import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Discrepancy
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.EncodingMeasure



set_option autoImplicit false

open scoped BigOperators

namespace Refresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The normalized square-sum norm on nonzero shares; it is their L2 norm under the uniform distribution when the carrier is nonempty. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; a ∈ U(F, n) → ℝ, define

shareL2(a) := √((1 / (|F|ⁿ-1)) · ∑_(l ∈ U(F, n)) ((a(l))²)).
-/
noncomputable def shareL2 {n : ℕ} (a : U F n → ℝ) : ℝ :=
  Real.sqrt ((1 / (shareCard F n : ℝ)) * ∑ l : U F n, a l ^ 2)

/-- A uniform discrepancy coefficient for any pair of field-valued secrets. -/
/-
Mathematical definition (normal notation): For F a set; n ∈ ℕ, assume F is finite. define

zeta(n) := 2 · |F| / √(|F|ⁿ).
-/
noncomputable def zeta (F : Type*) [Fintype F] (n : ℕ) : ℝ :=
  2 * (fieldCard F : ℝ) / Real.sqrt (vectorCard F n : ℝ)

/-- In dimension at least two, the explicit uniform-share norm is the square root of the second moment under the uniform distribution. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; a ∈ U(F, n) → ℝ, assume 2 ≤ n. Then

‖ a‖₂ = √(𝔼_(l ← uniformShare(F, n)) [(a(l))²]).
-/
theorem shareL2_eq_sqrt_expect {n : ℕ} (hn : 2 ≤ n) (a : U F n → ℝ) :
    shareL2 a = Real.sqrt ((uniformShare F n hn).expect (fun l => a l ^ 2)) := by
  unfold shareL2
  congr 1
  change (1 / (shareCard F n : ℝ)) * ∑ l : U F n, a l ^ 2 =
    ∑ l : U F n, (Fintype.card (U F n) : ℝ)⁻¹ * a l ^ 2
  rw [← Finset.mul_sum, nonzero_vector_card]
  simp [shareCard, vectorCard, one_div]

/-- The share norm and the incidence-matrix root mean square use exactly the same normalization. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; a ∈ U(F, n) → ℝ, we have

‖ a‖₂ = incidenceRms(a).
-/
theorem shareL2_eq_incidenceRms {n : ℕ} (a : U F n → ℝ) : shareL2 a = incidenceRms a := by
  unfold shareL2 incidenceRms
  rw [shareCard_cast_real]

/-- An expectation on the state carrier can be expanded as nested sums over the two nonzero shares. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; P ∈ 𝒟(State(F, n)); f ∈ State(F, n) → ℝ, we have

𝔼_(u ← P) [f(u)] = ∑_(l ∈ U(F, n)) (∑_(r ∈ U(F, n)) (P((l, r)) · f((l, r)))).
-/
private theorem expect_state_sum {n : ℕ} (P : FiniteDistribution (State F n)) (f : State F n → ℝ) :
    P.expect f = ∑ l : U F n, ∑ r : U F n, P.weight ⟨l, r⟩ * f ⟨l, r⟩ := by
  calc
    P.expect f = ∑ p : U F n × U F n, P.weight ⟨p.1, p.2⟩ * f ⟨p.1, p.2⟩ :=
      Fintype.sum_equiv (stateEquivProd F n) _ _ (fun x => by cases x; rfl)
    _ = _ := by rw [Fintype.sum_prod_type]

/-- In dimension at least two, the encoding-fiber size is the number of nonzero rows times the incidence degree. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, assume 2 ≤ n. Then

|Fiber(F, n, s)| = (|F|ⁿ - 1) · incidenceDegree(F, n, s).
-/
theorem fiber_card_eq_incidenceDegree {n : ℕ} (hn : 2 ≤ n) (s : F) :
    (Fintype.card (Fiber F n s) : ℝ) = ((vectorCard F n : ℝ) - 1) * incidenceDegree F n s := by
  have hq : (fieldCard F : ℝ) ≠ 0 := ne_of_gt (fieldCard_cast_pos (F := F))
  by_cases hs : s = 0
  · subst s
    rw [fiber_card_zero_real hn, shareCard_cast_real]
    simp [incidenceDegree]
    field_simp
  · rw [fiber_card_of_ne_zero_real hn s hs, shareCard_cast_real]
    simp only [incidenceDegree, if_neg hs, sub_zero]
    ring

/-- The incidence formula is the expectation under the actual uniform encoding distribution. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F; a, b ∈ U(F, n) → ℝ, assume 2 ≤ n. Then

𝔼_(x ← μₛ) [a(L(x)) · b(R(x))] = incidenceMean(s, a, b).
-/
theorem mu_expect_eq_incidenceMean {n : ℕ} (hn : 2 ≤ n) (s : F) (a b : U F n → ℝ) :
    (mu F n hn s).expect (fun x => a (stateLeftShare x) * b (stateRightShare x)) = incidenceMean s a b := by
  classical
  rw [expect_state_sum]
  unfold incidenceMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [mu_weight, fiber_card_eq_incidenceDegree hn s]
  by_cases h : dot l.val r.val = s <;> simp [secret, incidence, h]

/-- Static discrepancy for arbitrary field values under the actual initial distributions. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s, t ∈ F; a, b ∈ U(F, n) → ℝ, assume 2 ≤ n. Then

|𝔼_(x ← μₛ) [a(L(x)) · b(R(x))] - 𝔼_(x ← μₜ) [a(L(x)) · b(R(x))]| ≤ zeta(F, n) · ‖ a‖₂ · ‖ b‖₂.
-/
theorem innerProduct_discrepancy {n : ℕ} (hn : 2 ≤ n) (s t : F) (a b : U F n → ℝ) :
    |(mu F n hn s).expect (fun x => a (stateLeftShare x) * b (stateRightShare x)) -
      (mu F n hn t).expect (fun x => a (stateLeftShare x) * b (stateRightShare x))| ≤
      zeta F n * shareL2 a * shareL2 b := by
  rw [mu_expect_eq_incidenceMean hn s a b, mu_expect_eq_incidenceMean hn t a b,
    shareL2_eq_incidenceRms a, shareL2_eq_incidenceRms b]
  exact discrepancy_bound hn s t a b

end Refresh
