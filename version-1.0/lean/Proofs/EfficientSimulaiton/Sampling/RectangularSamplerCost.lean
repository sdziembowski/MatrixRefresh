import Proofs.EfficientSimulaiton.Sampling.ConditionalSamplingCost
import Proofs.Compiler.GateApproximation.MatrixPhase.EncodingSampling
import Proofs.Compiler.Foundations.Sampling.GaussianAlgebraCost
import Proofs.EfficientSimulaiton.Sampling.RectangularCompletionCost
import Proofs.Compiler.Foundations.Sampling.UnboundedSamplingCost
import Proofs.Compiler.Construction.Parameters



/-!
# Concrete polynomial expected work of rectangular compiler samplers

The acceptance tests are refined to executable Gaussian elimination. Costs sum actual counted operations over every rejected proposal and the accepted proposal. Random-field-coordinate counts are separate from arithmetic counts; for the binary field each sampled coordinate is one unbiased random bit.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace CircuitCompiler.Rectangular.SamplerCost

open Refresh MatrixRefresh Sampling Gaussian

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
/-- The executable Gaussian test implements the original square-matrix test. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; H ∈ F^({0,…,m−1} × {0,…,m−1}), we have

rankTest(H) = Sampling.invertibleTest(H).
-/
theorem gaussian_eq_invertibleTest {m : ℕ} (H : Matrix (Fin m) (Fin m) F) :
    rankTest H = Sampling.invertibleTest H := by
  apply Bool.eq_iff_iff.mpr
  rw [rankTest_correct,fullRowRank_iff_linearIndependent]
  change LinearIndependent F H.row ↔ _
  rw [Matrix.linearIndependent_rows_iff_isUnit,Matrix.isUnit_iff_isUnit_det]
  simp [Sampling.invertibleTest,isUnit_iff_ne_zero]

/-- The executable Gaussian test implements the exact affine completion test. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; u ∈ U(F, m); a ∈ U(F, n); w ∈ CompletionSampler.FreeRows(F, n, m, CompletionSampler.pivot(a)), we have

rankTest(CompletionSampler.fill(u, a, w)) = CompletionSampler.accept(u, a, w).
-/
theorem gaussian_eq_completionAccept {n m : ℕ} (u : U F m) (a : U F n)
    (w : CompletionSampler.FreeRows F n m (CompletionSampler.pivot a)) :
    rankTest (CompletionSampler.fill u a w) = CompletionSampler.accept u a w := by
  apply Bool.eq_iff_iff.mpr
  simp [rankTest_correct,CompletionSampler.accept]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; u ∈ U(F, m); a ∈ U(F, n); w ∈ CompletionSampler.FreeRows(F, n, m, CompletionSampler.pivot(a)), we have

value(completionProposal(u, a, w)) = CompletionSampler.accept(u, a, w).
-/
@[simp] theorem completionProposal_value {n m : ℕ} (u : U F m) (a : U F n)
    (w : CompletionSampler.FreeRows F n m (CompletionSampler.pivot a)) :
    (completionProposal u a w).value = CompletionSampler.accept u a w := by
  apply Bool.eq_iff_iff.mpr
  simp only [completionProposal,Counted.bind,check_correct]
  have he : entries (fillData (Vector.ofFn u.val) (Vector.ofFn a.val)
      (CompletionSampler.pivot a) w).value = CompletionSampler.fill u a w := by
    funext i k
    simp only [fillData_entries,CompletionSampler.fill,get_ofFn]
  rw [he,← fullRowRank_iff_linearIndependent]
  simp [CompletionSampler.accept]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; u ∈ U(F, m); a ∈ U(F, n); w ∈ CompletionSampler.FreeRows(F, n, m, CompletionSampler.pivot(a)), we have

operations(completionProposal(u, a, w)) ≤ 5 · (n + 1)² · (m + 1).
-/
theorem completionProposal_operations_le {n m : ℕ} (u : U F m) (a : U F n)
    (w : CompletionSampler.FreeRows F n m (CompletionSampler.pivot a)) :
    (completionProposal u a w).operations ≤ 5*(n+1)^2*(m+1) := by
  have hf := fillData_operations_le (Vector.ofFn u.val) (Vector.ofFn a.val)
    (CompletionSampler.pivot a) w
  have hr := check_operations_le n
    (fillData (Vector.ofFn u.val) (Vector.ofFn a.val) (CompletionSampler.pivot a) w).value
  simp only [completionProposal,Counted.bind]
  nlinarith

/-- Expected scalar arithmetic and zero tests of uniform-GL rejection sampling. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ, we have

Unbounded.expectedCost(𝒰_(F^({0,…,m−1} × {0,…,m−1})), Sampling.invertibleTest, ((H ↦ operations(check(m, materialize(H)))))) ≤ 12 · (m + 1)³.
-/
theorem matrix_expected_operations_le (m : ℕ) :
    Unbounded.expectedCost
      (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin m) (Fin m) F)) Sampling.invertibleTest
      (fun H => ((check m (materialize H)).operations : ℝ)) ≤ 12*(m+1)^3 := by
  have hp := matrix_acceptance_ge_quarter (F := F) m
  have hp0 : 0 < acceptance
      (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin m) (Fin m) F)) Sampling.invertibleTest :=
    lt_of_lt_of_le (by norm_num) hp
  have h := Unbounded.expectedCost_le _ _ hp0
    (fun H => ((check m (materialize H)).operations : ℝ))
    (3*((m:ℝ)+1)^3) (by positivity) (fun _ => Nat.cast_nonneg _)
    (fun H => by
      have hc : ((check m (materialize H)).operations : ℝ) ≤
          3*((m:ℝ)+1)^2*((m:ℝ)+1) := by exact_mod_cast rankTest_operations_le H
      simpa only [pow_succ,mul_assoc] using hc)
  apply h.trans
  apply (div_le_iff₀ hp0).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (by positivity : 0 ≤ ((m:ℝ)+1)^3)]

/-- Expected number of random field coordinates used to sample a uniform GL matrix. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ, we have

Unbounded.expectedCost(𝒰_(F^({0,…,m−1} × {0,…,m−1})), Sampling.invertibleTest, ((x₁ ↦ m²))) ≤ 4 · m².
-/
theorem matrix_expected_coordinates_le (m : ℕ) :
    Unbounded.expectedCost
      (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin m) (Fin m) F)) Sampling.invertibleTest
      (fun _ => (m:ℝ)^2) ≤ 4*(m:ℝ)^2 := by
  have hp := matrix_acceptance_ge_quarter (F := F) m
  have hp0 : 0 < acceptance
      (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin m) (Fin m) F)) Sampling.invertibleTest :=
    lt_of_lt_of_le (by norm_num) hp
  have h := Unbounded.expectedCost_le _ _ hp0 (fun _ => (m:ℝ)^2) ((m:ℝ)^2)
    (by positivity) (fun _ => by positivity) (fun _ => le_rfl)
  apply h.trans
  apply (div_le_iff₀ hp0).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg (m:ℝ))]

/-- Every free-entry trial has polynomial counted arithmetic, and at most four trials are needed in expectation. The selected pivot is computed once outside this loop and costs at most `n` additional zero tests. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; u ∈ U(F, (n + t)); a ∈ U(F, n), we have

Unbounded.expectedCost(𝒰_(CompletionSampler.FreeRows(F, n, (n + t), CompletionSampler.pivot(a))), CompletionSampler.accept(u, a), ((w ↦ operations(completionProposal(u, a, w))))) ≤ 20 · (n + 1)² · (n + t + 1).
-/
theorem completion_expected_operations_le {n t : ℕ} (u : U F (n+t)) (a : U F n) :
    Unbounded.expectedCost
      (FiniteDistribution.uniform : FiniteDistribution (CompletionSampler.FreeRows F n (n+t) (CompletionSampler.pivot a)))
      (CompletionSampler.accept u a) (fun w => ((completionProposal u a w).operations : ℝ)) ≤
      20*((n:ℝ)+1)^2*((n+t:ℕ)+1) := by
  have hp := CompletionSampler.acceptance_ge_quarter u a
  have hp0 := CompletionSampler.acceptance_pos u a
  have h := Unbounded.expectedCost_le _ _ hp0
    (fun w => ((completionProposal u a w).operations : ℝ))
    (5*((n:ℝ)+1)^2*((n+t:ℕ)+1)) (by positivity) (fun _ => Nat.cast_nonneg _)
    (fun w => by exact_mod_cast completionProposal_operations_le u a w)
  apply h.trans
  apply (div_le_iff₀ hp0).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hp)
    (by positivity : 0 ≤ ((n:ℝ)+1)^2*((n+t:ℕ)+1))]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; u ∈ U(F, (n + t)); a ∈ U(F, n), we have

Unbounded.expectedCost(𝒰_(CompletionSampler.FreeRows(F, n, (n + t), CompletionSampler.pivot(a))), CompletionSampler.accept(u, a), ((x₁ ↦ (n - 1) · (n + t)))) ≤ 4 · (n - 1) · (n + t).
-/
theorem completion_expected_coordinates_le {n t : ℕ} (u : U F (n+t)) (a : U F n) :
    Unbounded.expectedCost
      (FiniteDistribution.uniform : FiniteDistribution (CompletionSampler.FreeRows F n (n+t) (CompletionSampler.pivot a)))
      (CompletionSampler.accept u a) (fun _ => ((n-1)*(n+t):ℕ)) ≤
      4*((n-1)*(n+t):ℕ) := by
  have hp := CompletionSampler.acceptance_ge_quarter u a
  have hp0 := CompletionSampler.acceptance_pos u a
  have h := Unbounded.expectedCost_le _ _ hp0
    (fun _ => (((n-1)*(n+t):ℕ):ℝ)) (((n-1)*(n+t):ℕ):ℝ)
    (by positivity) (fun _ => by positivity) (fun _ => le_rfl)
  apply h.trans
  apply (div_le_iff₀ hp0).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hp)
    (by positivity : (0:ℝ) ≤ ((n-1)*(n+t):ℕ))]

omit [Fintype F] in
/-- The explicit scan implements the nonzero-share acceptance predicate. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; v ∈ V(F, n), we have

value(scanNonzero(Vector.ofFn(v))) = Sampling.nonzeroTest(v).
-/
theorem scan_eq_nonzeroTest {n : ℕ} (v : V F n) :
    (scanNonzero (Vector.ofFn v)).value = Sampling.nonzeroTest v := by
  apply Bool.eq_iff_iff.mpr
  simp [scanNonzero_correct,get_ofFn,Sampling.nonzeroTest]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, assume 1 ≤ n. Then

Unbounded.expectedCost(𝒰_(V(F, n)), Sampling.nonzeroTest, ((v ↦ operations(scanNonzero(Vector.ofFn(v)))))) ≤ 2 · n.
-/
theorem nonzero_expected_operations_le {n : ℕ} (hn : 1 ≤ n) :
    Unbounded.expectedCost (FiniteDistribution.uniform : FiniteDistribution (V F n)) Sampling.nonzeroTest
      (fun v => ((scanNonzero (Vector.ofFn v)).operations : ℝ)) ≤ 2*n := by
  have hp := Sampling.nonzero_acceptance_ge_half (F := F) hn
  have hp0 : 0 < acceptance (FiniteDistribution.uniform : FiniteDistribution (V F n)) Sampling.nonzeroTest :=
    lt_of_lt_of_le (by norm_num) hp
  have h := Unbounded.expectedCost_le _ _ hp0
    (fun v => ((scanNonzero (Vector.ofFn v)).operations : ℝ)) (n:ℝ)
    (by positivity) (fun _ => Nat.cast_nonneg _)
    (fun v => by exact_mod_cast scanNonzero_operations_le (Vector.ofFn v))
  apply h.trans
  apply (div_le_iff₀ hp0).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (Nat.cast_nonneg n : (0:ℝ) ≤ n)]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, assume 1 ≤ n. Then

Unbounded.expectedCost(𝒰_(V(F, n)), Sampling.nonzeroTest, ((x₁ ↦ n))) ≤ 2 · n.
-/
theorem nonzero_expected_coordinates_le {n : ℕ} (hn : 1 ≤ n) :
    Unbounded.expectedCost (FiniteDistribution.uniform : FiniteDistribution (V F n)) Sampling.nonzeroTest
      (fun _ => (n:ℝ)) ≤ 2*n := by
  have hp := Sampling.nonzero_acceptance_ge_half (F := F) hn
  have hp0 : 0 < acceptance (FiniteDistribution.uniform : FiniteDistribution (V F n)) Sampling.nonzeroTest :=
    lt_of_lt_of_le (by norm_num) hp
  have h := Unbounded.expectedCost_le _ _ hp0 (fun _ => (n:ℝ)) (n:ℝ)
    (by positivity) (fun _ => by positivity) (fun _ => le_rfl)
  apply h.trans
  apply (div_le_iff₀ hp0).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (Nat.cast_nonneg n : (0:ℝ) ≤ n)]

/-- Fixing the accepted short row does not increase its expected scan work. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; a ∈ U(F, n), assume 1 ≤ n. Then

Unbounded.conditionalExpectedCost(𝒰_(V(F, n)), Sampling.nonzeroTest, ((v ↦ operations(scanNonzero(Vector.ofFn(v))))), a) ≤ 2 · n.
-/
theorem nonzero_conditional_operations_le {n : ℕ} (hn : 1 ≤ n) (a : U F n) :
    Unbounded.conditionalExpectedCost (FiniteDistribution.uniform : FiniteDistribution (V F n)) Sampling.nonzeroTest
      (fun v => ((scanNonzero (Vector.ofFn v)).operations : ℝ)) a.val ≤ 2*n := by
  have hp := Sampling.nonzero_acceptance_ge_half (F := F) hn
  have hp0 : 0 < acceptance (FiniteDistribution.uniform : FiniteDistribution (V F n)) Sampling.nonzeroTest :=
    lt_of_lt_of_le (by norm_num) hp
  have h := Unbounded.conditionalExpectedCost_le _ _ hp0
    (fun v => ((scanNonzero (Vector.ofFn v)).operations : ℝ)) (n:ℝ)
    (fun _ => Nat.cast_nonneg _)
    (fun v => by exact_mod_cast scanNonzero_operations_le (Vector.ofFn v)) a.val
  apply h.trans
  apply (div_le_iff₀ hp0).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (Nat.cast_nonneg n : (0:ℝ) ≤ n)]

/-- The inner completion bound is uniform in the accepted matrix, which is what permits summing the work of nested outer shortening retries. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; u ∈ U(F, (n + t)); a ∈ U(F, n); H ∈ Completion(u, a), we have

Unbounded.conditionalExpectedCost(𝒰_(CompletionSampler.FreeRows(F, n, (n + t), CompletionSampler.pivot(a))), CompletionSampler.accept(u, a), ((w ↦ operations(completionProposal(u, a, w)))), (CompletionSampler.acceptedEquiv(u, a))⁻¹(H)) ≤ 20 · (n + 1)² · (n + t + 1).
-/
theorem completion_conditional_operations_le {n t : ℕ} (u : U F (n+t)) (a : U F n)
    (H : Completion u a) :
    Unbounded.conditionalExpectedCost
      (FiniteDistribution.uniform : FiniteDistribution (CompletionSampler.FreeRows F n (n+t) (CompletionSampler.pivot a)))
      (CompletionSampler.accept u a) (fun w => ((completionProposal u a w).operations : ℝ))
      ((CompletionSampler.acceptedEquiv u a).symm H).val ≤
      20*((n:ℝ)+1)^2*((n+t:ℕ)+1) := by
  have hp := CompletionSampler.acceptance_ge_quarter u a
  have hp0 := CompletionSampler.acceptance_pos u a
  have h := Unbounded.conditionalExpectedCost_le _ _ hp0
    (fun w => ((completionProposal u a w).operations : ℝ))
    (5*((n:ℝ)+1)^2*((n+t:ℕ)+1)) (fun _ => Nat.cast_nonneg _)
    (fun w => by exact_mod_cast completionProposal_operations_le u a w)
    ((CompletionSampler.acceptedEquiv u a).symm H).val
  apply h.trans
  apply (div_le_iff₀ hp0).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hp)
    (by positivity : 0 ≤ ((n:ℝ)+1)^2*((n+t:ℕ)+1))]

end

end CircuitCompiler.Rectangular.SamplerCost
