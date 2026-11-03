import Proofs.Compiler.GateApproximation.Shortening.RectangularUnboundedSampling



/-!
# Expected work of the actual unbounded rejection loop

The cost is the sum of proposal costs along its complete stopped tape. The geometric estimate is applied to this trace cost, rather than declaring a sampler to have an arbitrary constant running time.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace CircuitCompiler.Sampling.Unbounded

open Refresh

noncomputable section

variable {α : Type*} [Fintype α]

/-- Sum of work on the rejected prefix. -/
/- Mathematical definition (normal notation): Sum the supplied real proposal costs over the rejected prefix. The empty prefix has total cost zero. -/
def prefixCost (cost : α → ℝ) : (k : ℕ) → Tape α k → ℝ
  | 0,_ => 0
  | k+1,t => cost t.1 + prefixCost cost k t.2

/-- Every attempted proposal, including the accepted one, incurs its cost. -/
/-
Mathematical definition (normal notation): For cost ∈ α → ℝ; t ∈ StoppedTape(α), define

traceCost(cost, t) := prefixCost(cost, (t)₁, ((t)₂)₁) + cost(((t)₂)₂).
-/
def traceCost (cost : α → ℝ) (t : StoppedTape α) : ℝ :=
  prefixCost cost t.1 t.2.1 + cost t.2.2

omit [Fintype α] in
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For cost ∈ α → ℝ; t ∈ StoppedTape(α), assume ∀ a, 0 ≤ cost(a). Then

0 ≤ traceCost(cost, t).
-/
theorem traceCost_nonneg (cost : α → ℝ) (hc : ∀ a, 0 ≤ cost a)
    (t : StoppedTape α) : 0 ≤ traceCost cost t := by
  have hp : ∀ (k : ℕ) (p : Tape α k), 0 ≤ prefixCost cost k p := by
    intro k
    induction k with
    | zero => intro p; exact le_refl 0
    | succ k ih => intro p; exact add_nonneg (hc p.1) (ih p.2)
  exact add_nonneg (hp _ _) (hc _)

omit [Fintype α] in
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For cost ∈ α → ℝ; C ∈ ℝ; t ∈ StoppedTape(α), assume ∀ a, cost(a) ≤ C. Then

traceCost(cost, t) ≤ ((t)₁ + 1) · C.
-/
theorem traceCost_le (cost : α → ℝ) (C : ℝ) (hc : ∀ a, cost a ≤ C)
    (t : StoppedTape α) : traceCost cost t ≤ ((t.1:ℝ)+1)*C := by
  have hp : ∀ (k : ℕ) (p : Tape α k), prefixCost cost k p ≤ (k:ℝ)*C := by
    intro k
    induction k with
    | zero => intro p; simp [prefixCost]
    | succ k ih =>
      intro p
      have h := add_le_add (hc p.1) (ih p.2)
      simpa only [prefixCost,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm] using h
  have h := add_le_add (hp t.1 t.2.1) (hc t.2.2)
  simpa only [traceCost,add_mul,one_mul] using h

/-- The cost expectation over executions of a fixed finite length. -/
/-
Mathematical definition (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; cost ∈ α → ℝ; k ∈ ℕ, define

lengthCost(P, accept, cost, k) := ∑_(t ∈ Tape(α, k) × α) (traceWeight(P, accept, (k, t)) · traceCost(cost, (k, t))).
-/
def lengthCost (P : FiniteDistribution α) (accept : α → Bool) (cost : α → ℝ) (k : ℕ) : ℝ :=
  ∑ t : Tape α k × α, traceWeight P accept ⟨k,t⟩ * traceCost cost ⟨k,t⟩

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; cost ∈ α → ℝ; k ∈ ℕ, assume ∀ a, 0 ≤ cost(a). Then

0 ≤ lengthCost(P, accept, cost, k).
-/
theorem lengthCost_nonneg (P : FiniteDistribution α) (accept : α → Bool)
    (cost : α → ℝ) (hc : ∀ a, 0 ≤ cost a) (k : ℕ) :
    0 ≤ lengthCost P accept cost k := by
  apply Finset.sum_nonneg
  intro t _
  exact mul_nonneg (traceWeight_nonneg P accept _) (traceCost_nonneg cost hc _)

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; cost ∈ α → ℝ; C ∈ ℝ; k ∈ ℕ, assume ∀ a, cost(a) ≤ C. Then

lengthCost(P, accept, cost, k) ≤ C · (k + 1) · ProbabilityTheory.geometricPMFReal(acceptance(P, accept), k).
-/
theorem lengthCost_le (P : FiniteDistribution α) (accept : α → Bool)
    (cost : α → ℝ) (C : ℝ) (hc : ∀ a, cost a ≤ C) (k : ℕ) :
    lengthCost P accept cost k ≤
      C*((k:ℝ)+1)*ProbabilityTheory.geometricPMFReal (acceptance P accept) k := by
  calc
    _ ≤ ∑ t : Tape α k × α, traceWeight P accept ⟨k,t⟩ * (((k:ℝ)+1)*C) := by
      apply Finset.sum_le_sum
      intro t _
      exact mul_le_mul_of_nonneg_left (traceCost_le cost C hc _) (traceWeight_nonneg P accept _)
    _ = _ := by rw [← Finset.sum_mul,traceWeight_sum]; ring

/-- Actual expected work, grouped by the finite stopped-tape length. -/
/-
Mathematical definition (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; cost ∈ α → ℝ, define

expectedCost(P, accept, cost) := ∑_(k ∈ ℕ) (lengthCost(P, accept, cost, k)).
-/
def expectedCost (P : FiniteDistribution α) (accept : α → Bool) (cost : α → ℝ) : ℝ :=
  ∑' k : ℕ, lengthCost P accept cost k

/-- A uniform bound on one proposal yields the expected-work bound `C/p`. The cost may depend on the proposal and on whether it is accepted. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; cost ∈ α → ℝ; C ∈ ℝ, assume 0 < acceptance(P, accept); 0 ≤ C; ∀ a, 0 ≤ cost(a); ∀ a, cost(a) ≤ C. Then

expectedCost(P, accept, cost) ≤ C / acceptance(P, accept).
-/
theorem expectedCost_le (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (cost : α → ℝ) (C : ℝ)
    (_hC : 0 ≤ C) (hc0 : ∀ a, 0 ≤ cost a) (hc : ∀ a, cost a ≤ C) :
    expectedCost P accept cost ≤ C / acceptance P accept := by
  have hg := (expected_attempts P accept hp).mul_left C
  have hgeom : HasSum (fun k : ℕ => C*((k:ℝ)+1)*
      ProbabilityTheory.geometricPMFReal (acceptance P accept) k)
      (C/acceptance P accept) := by
    convert hg using 1
    · ext k
      rw [count_distribution]
      change _ = C * (((k:ℝ)+1) * (ENNReal.ofReal _).toReal)
      rw [ENNReal.toReal_ofReal (ProbabilityTheory.geometricPMFReal_nonneg hp (acceptance_le_one P accept))]
      ring
    · ring
  have hs : Summable (lengthCost P accept cost) :=
    Summable.of_nonneg_of_le (lengthCost_nonneg P accept cost hc0)
      (lengthCost_le P accept cost C hc) hgeom.summable
  unfold expectedCost
  exact (hs.tsum_le_tsum (lengthCost_le P accept cost C hc) hgeom.summable).trans_eq hgeom.tsum_eq

end

end CircuitCompiler.Sampling.Unbounded
