import Proofs.Compiler.GateApproximation.MatrixPhase.RejectionPrefix
import Proofs.Compiler.Foundations.Sampling.UnboundedSamplingCost



/-!
# Work bounds conditional on a sampler's returned value

The independent rejected-prefix factorization permits nested retry costs to be bounded even when the surrounding computation fixes the returned value. The bound does not assume independence of the cost and the returned value.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace CircuitCompiler.Sampling.Unbounded

open Refresh

noncomputable section

variable {α : Type*} [Fintype α]

/-
Mathematical definition (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; cost ∈ α → ℝ; a ∈ α; k ∈ ℕ, define

conditionalLengthCost(P, accept, cost, a, k) := ∑_(t ∈ Tape(α, k)) ((prefixWeight(P, accept, k, t) · acceptance(P, accept)) · traceCost(cost, joinPrefix((k, t), a))).
-/
def conditionalLengthCost (P : FiniteDistribution α) (accept : α → Bool)
    (cost : α → ℝ) (a : α) (k : ℕ) : ℝ :=
  ∑ t : Tape α k, (prefixWeight P accept k t * acceptance P accept) *
    traceCost cost (joinPrefix ⟨k,t⟩ a)

/-- Exact expected work of the rejected-prefix distribution followed by a fixed returned proposal. This is the sampler's conditional complete tape. -/
/- Mathematical definition (normal notation): The expected total proposal cost conditional on a specified accepted value is the sum, over all possible rejected-prefix lengths, of the corresponding conditional length-cost contributions. -/
def conditionalExpectedCost (P : FiniteDistribution α) (accept : α → Bool)
    (cost : α → ℝ) (a : α) : ℝ :=
  ∑' k : ℕ, conditionalLengthCost P accept cost a k

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; cost ∈ α → ℝ; a ∈ α; k ∈ ℕ, assume ∀ a, 0 ≤ cost(a). Then

0 ≤ conditionalLengthCost(P, accept, cost, a, k).
-/
theorem conditionalLengthCost_nonneg (P : FiniteDistribution α) (accept : α → Bool)
    (cost : α → ℝ) (hc : ∀ a,0 ≤ cost a) (a : α) (k : ℕ) :
    0 ≤ conditionalLengthCost P accept cost a k := by
  apply Finset.sum_nonneg
  intro t _
  exact mul_nonneg (mul_nonneg (prefixWeight_nonneg P accept _ _) (acceptance_nonneg P accept))
    (traceCost_nonneg cost hc _)

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; cost ∈ α → ℝ; C ∈ ℝ; a ∈ α; k ∈ ℕ, assume ∀ a, cost(a) ≤ C. Then

conditionalLengthCost(P, accept, cost, a, k) ≤ C · (k + 1) · ProbabilityTheory.geometricPMFReal(acceptance(P, accept), k).
-/
theorem conditionalLengthCost_le (P : FiniteDistribution α) (accept : α → Bool)
    (cost : α → ℝ) (C : ℝ) (hc : ∀ a,cost a ≤ C) (a : α) (k : ℕ) :
    conditionalLengthCost P accept cost a k ≤
      C*((k:ℝ)+1)*ProbabilityTheory.geometricPMFReal (acceptance P accept) k := by
  calc
    _ ≤ ∑ t : Tape α k, (prefixWeight P accept k t * acceptance P accept) * (((k:ℝ)+1)*C) := by
      apply Finset.sum_le_sum
      intro t _
      exact mul_le_mul_of_nonneg_left (traceCost_le cost C hc _)
        (mul_nonneg (prefixWeight_nonneg P accept _ _) (acceptance_nonneg P accept))
    _ = _ := by
      rw [← Finset.sum_mul,← Finset.sum_mul,prefixWeight_sum]
      simp only [ProbabilityTheory.geometricPMFReal]
      ring

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; cost ∈ α → ℝ; a ∈ α, assume ∀ a, 0 ≤ cost(a). Then

0 ≤ conditionalExpectedCost(P, accept, cost, a).
-/
theorem conditionalExpectedCost_nonneg (P : FiniteDistribution α) (accept : α → Bool)
    (cost : α → ℝ) (hc : ∀ a,0 ≤ cost a) (a : α) :
    0 ≤ conditionalExpectedCost P accept cost a :=
  tsum_nonneg (conditionalLengthCost_nonneg P accept cost hc a)

/-- The same `C/p` bound holds after fixing any accepted proposal, including rare accepted outputs. Thus nesting does not introduce inverse output masses. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; cost ∈ α → ℝ; C ∈ ℝ; a ∈ α, assume 0 < acceptance(P, accept); ∀ a, 0 ≤ cost(a); ∀ a, cost(a) ≤ C. Then

conditionalExpectedCost(P, accept, cost, a) ≤ C / acceptance(P, accept).
-/
theorem conditionalExpectedCost_le (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (cost : α → ℝ) (C : ℝ)
    (hc0 : ∀ a,0 ≤ cost a) (hc : ∀ a,cost a ≤ C) (a : α) :
    conditionalExpectedCost P accept cost a ≤ C/acceptance P accept := by
  have hg := (expected_attempts P accept hp).mul_left C
  have hgeom : HasSum (fun k : ℕ => C*((k:ℝ)+1)*
      ProbabilityTheory.geometricPMFReal (acceptance P accept) k)
      (C/acceptance P accept) := by
    convert hg using 1
    · ext k
      rw [count_distribution]
      change _ = C*(((k:ℝ)+1)*(ENNReal.ofReal _).toReal)
      rw [ENNReal.toReal_ofReal
        (ProbabilityTheory.geometricPMFReal_nonneg hp (acceptance_le_one P accept))]
      ring
    · ring
  have hs : Summable (conditionalLengthCost P accept cost a) :=
    Summable.of_nonneg_of_le (conditionalLengthCost_nonneg P accept cost hc0 a)
      (conditionalLengthCost_le P accept cost C hc a) hgeom.summable
  unfold conditionalExpectedCost
  exact (hs.tsum_le_tsum (conditionalLengthCost_le P accept cost C hc a)
    hgeom.summable).trans_eq hgeom.tsum_eq

/-- The finite-length definition uses exactly the actual rejected-prefix PMF. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; cost ∈ α → ℝ; a ∈ α; k ∈ ℕ, assume 0 < acceptance(P, accept). Then

conditionalLengthCost(P, accept, cost, a, k) = ∑_(t ∈ Tape(α, k)) (toReal(prefixDistribution(P, accept, (k, t))) · traceCost(cost, joinPrefix((k, t), a))).
-/
theorem conditionalLengthCost_eq_prefixDistribution (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (cost : α → ℝ) (a : α) (k : ℕ) :
    conditionalLengthCost P accept cost a k =
      ∑ t : Tape α k, (prefixDistribution P accept hp ⟨k,t⟩).toReal *
        traceCost cost (joinPrefix ⟨k,t⟩ a) := by
  apply Finset.sum_congr rfl
  intro t _
  rw [prefixDistribution_apply,ENNReal.toReal_ofReal
    (mul_nonneg (prefixWeight_nonneg P accept _ _) hp.le)]

end

end CircuitCompiler.Sampling.Unbounded
