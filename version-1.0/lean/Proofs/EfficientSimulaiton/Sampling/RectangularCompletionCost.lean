import Proofs.Compiler.GateApproximation.Shortening.RectangularCompletionCount
import Proofs.Compiler.GateApproximation.Shortening.RectangularCompletionSampler



/-!
# Constant expected completion trials

The count bounds concern the actual independent-free-entry sampler and its complete unbounded stopped tape. The rank predicate is not charged unit cost in a claim about field operations.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace CircuitCompiler.Rectangular.CompletionSampler

open Refresh MatrixRefresh Sampling

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [DecidableEq F] in
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; j ∈ {0,…,n-1}, we have

|FreeRows(F, n, m, j)| = (|F|)^((n − 1) · m).
-/
theorem freeRows_card {n m : ℕ} (j : Fin n) :
    Fintype.card (FreeRows F n m j) = fieldCard F ^ ((n-1)*m) := by
  have hc : Fintype.card {i : Fin n // i ≠ j} = n-1 := by
    simp [Fintype.card_subtype_compl]
  simp only [FreeRows,Fintype.card_fun,Fintype.card_fin,hc,fieldCard,← pow_mul]
  rw [Nat.mul_comm]

/-- Uniform free entries, followed by the rank test, accept with probability at least one quarter for every pair of nonzero constrained rows. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; u ∈ U(F, (n + t)); a ∈ U(F, n), we have

1 / 4 ≤ acceptance(𝒰_(FreeRows(F, n, (n + t), pivot(a))), accept(u, a)) .
-/
theorem acceptance_ge_quarter {n t : ℕ} (u : U F (n+t)) (a : U F n) :
    (1/4 : ℝ) ≤ acceptance
      (FiniteDistribution.uniform : FiniteDistribution (FreeRows F n (n+t) (pivot a))) (accept u a) := by
  rw [acceptance_uniform,Fintype.card_congr (acceptedEquiv u a),freeRows_card]
  push_cast
  exact completion_probability_ge_quarter (by omega) u a

/-- No cap: the complete sampler takes at most four trials in expectation. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; u ∈ U(F, (n + t)); a ∈ U(F, n), we have

(∑_(k ∈ ℕ) ((k + 1) · toReal(map(tapeDistribution(u, a))((Sigma)₁, k)))) ≤ 4.
-/
theorem expected_attempts_le_four {n t : ℕ} (u : U F (n+t)) (a : U F n) :
    (∑' k : ℕ, ((k:ℝ)+1) *
      (((tapeDistribution u a).map Sigma.fst) k).toReal) ≤ 4 := by
  have h := Unbounded.expected_attempts
    (FiniteDistribution.uniform : FiniteDistribution (FreeRows F n (n+t) (pivot a)))
      (accept u a) (acceptance_pos u a)
  change (∑' k : ℕ, ((k:ℝ)+1) *
    (((Unbounded.distribution _ _ _).map Sigma.fst) k).toReal) ≤ 4
  rw [h.tsum_eq]
  apply (div_le_iff₀ (acceptance_pos u a)).mpr
  have hp := acceptance_ge_quarter u a
  linarith

end

end CircuitCompiler.Rectangular.CompletionSampler
