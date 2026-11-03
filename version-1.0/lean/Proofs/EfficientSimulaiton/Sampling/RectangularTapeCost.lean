import Proofs.EfficientSimulaiton.Sampling.GaussianSolveCost
import Proofs.EfficientSimulaiton.Sampling.RectangularSamplerCost
import Proofs.Compiler.GateApproximation.Shortening.RectangularTapedSampler
import Proofs.EfficientSimulaiton.Sampling.SamplerPMFCost
import Proofs.Compiler.Construction.Parameters



/-!
# Actual nested shortening tape costs

The natural-valued counters read every raw row and free-entry proposal in all outer attempts. Their expectation is taken under the complete marked sampler distribution. A proved tower identity supplies the polynomial bound.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal

namespace CircuitCompiler.Rectangular.Taped

open Refresh MatrixRefresh Sampling Sampling.Unbounded Gaussian

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

variable {n t : ℕ}

omit [Fintype F] in
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u, v ∈ U(F, (n + t)); p ∈ Attempt(n = n, u), we have

attemptOutputWork(u, v, p) ≤ 2 · n · (n + t) + n.
-/
theorem attemptOutputWork_le (u v : U F (n+t)) (p : Attempt (n := n) u) :
    attemptOutputWork u v p ≤ 2*n*(n+t)+n := by
  have h := scanNonzero_operations_le
    (mulVecData (materialize p.val.2.val) (Vector.ofFn v.val)).value
  simpa only [attemptOutputWork,Counted.bind,mulVecData_operations] using
    Nat.add_le_add_left h (2*n*(n+t))

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u, v ∈ U(F, (n + t)); p ∈ Attempt(n = n, u); mark ∈ AttemptSampler.Mark(m = n + t, (p)₁), we have

markedAttemptWork(u, v, p, ((p)₁, mark)) = internalWork(u, v, p, mark).
-/
@[simp] theorem markedAttemptWork_tagged (u v : U F (n+t)) (p : Attempt (n := n) u)
    (mark : AttemptSampler.Mark (m := n+t) p.val.1) :
    markedAttemptWork u v p ⟨p.val.1,mark⟩ = internalWork u v p mark := by
  simp [markedAttemptWork]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u, v ∈ U(F, (n + t)); z ∈ MarkedTape(Attempt(n = n, u), Mark(F, n, (n + t))), we have

shorteningWork(u, v, z) = markedTraceWork(((p, mark ↦ markedAttemptWork(u, v, p, mark))), z).
-/
@[simp] theorem shorteningWork_cast (u v : U F (n+t))
    (z : MarkedTape (Attempt (n := n) u) (Mark F n (n+t))) :
    (shorteningWork u v z : ℝ≥0∞) =
      markedTraceWork (fun p mark => (markedAttemptWork u v p mark : ℝ≥0∞)) z := by
  have h : ∀ (k : ℕ) (a : Tape (Attempt (n := n) u) k) (b : Tape (Mark F n (n+t)) k),
      (prefixShorteningWork u v k a b : ℝ≥0∞) =
        markedPrefixWork (fun p mark => (markedAttemptWork u v p mark : ℝ≥0∞)) k a b := by
    intro k
    induction k with
    | zero => intro a b; simp [prefixShorteningWork,markedPrefixWork]
    | succ k ih => intro a b; simp only [prefixShorteningWork,markedPrefixWork,Nat.cast_add,ih]
  simp only [shorteningWork,markedTraceWork,Nat.cast_add,h]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 1 ≤ n. Then

ENNReal.ofReal((1 / acceptance(𝒰_(V(F, n)), nonzeroTest))) ≤ 2.
-/
private theorem inv_acceptance_le_two (hn : 1 ≤ n) :
    ENNReal.ofReal (1/acceptance (FiniteDistribution.uniform : FiniteDistribution (V F n)) nonzeroTest) ≤ 2 := by
  have hp := nonzero_acceptance_ge_half (F := F) hn
  have hp0 := AttemptSampler.row_acceptance_pos (F := F) hn
  have h : 1/acceptance (FiniteDistribution.uniform : FiniteDistribution (V F n)) nonzeroTest ≤ (2:ℝ) := by
    apply (div_le_iff₀ hp0).mpr
    linarith
  simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal h

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u ∈ U(F, (n + t)); a ∈ U(F, n), we have

ENNReal.ofReal((1 / acceptance(𝒰_(CompletionSampler.FreeRows(F, n, (n + t), CompletionSampler.pivot(a))), CompletionSampler.accept(u, a)))) ≤ 4.
-/
private theorem inv_completion_acceptance_le_four (u : U F (n+t)) (a : U F n) :
    ENNReal.ofReal (1/acceptance (FiniteDistribution.uniform : FiniteDistribution
      (CompletionSampler.FreeRows F n (n+t) (CompletionSampler.pivot a)))
      (CompletionSampler.accept u a)) ≤ 4 := by
  have hp := CompletionSampler.acceptance_ge_quarter u a
  have h : 1/acceptance (FiniteDistribution.uniform : FiniteDistribution
      (CompletionSampler.FreeRows F n (n+t) (CompletionSampler.pivot a)))
      (CompletionSampler.accept u a) ≤ (4:ℝ) := by
    apply (div_le_iff₀ (CompletionSampler.acceptance_pos u a)).mpr
    linarith
  simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal h

/-- Uniform bound on the actual private inner work, even after fixing `(A,H)`. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u, v ∈ U(F, (n + t)); p ∈ Attempt(n = n, u), assume 2 ≤ n. Then

workExpectation(AttemptSampler.markDistribution(, u, (p)₁), ((mark ↦ internalWork(u, v, p, mark)))) ≤ 20 · (n + 1)² · (n + t + 1) + 4 · n + 2 · n · (n + t).
-/
theorem internalWork_expected_le (hn : 2 ≤ n) (u v : U F (n+t)) (p : Attempt (n := n) u) :
    workExpectation (AttemptSampler.markDistribution (by omega : 1 ≤ n) u p.val.1)
      (fun mark => (internalWork u v p mark : ℝ≥0∞)) ≤
      20*(n+1)^2*(n+t+1)+4*n+2*n*(n+t) := by
  have hrow := prefixDistribution_traceWork_le (FiniteDistribution.uniform : FiniteDistribution (V F n)) nonzeroTest
    (AttemptSampler.row_acceptance_pos (by omega : 1 ≤ n))
    (fun row => ((scanNonzero (Vector.ofFn row)).operations : ℝ≥0∞)) (n:ℝ≥0∞)
    (fun row => by exact_mod_cast scanNonzero_operations_le (Vector.ofFn row)) p.val.1.val
  have hcomp := prefixDistribution_traceWork_le
    (FiniteDistribution.uniform : FiniteDistribution (CompletionSampler.FreeRows F n (n+t) (CompletionSampler.pivot p.val.1)))
    (CompletionSampler.accept u p.val.1) (CompletionSampler.acceptance_pos u p.val.1)
    (fun w => ((SamplerCost.completionProposal u p.val.1 w).operations : ℝ≥0∞))
    (5*(n+1)^2*(n+t+1))
    (fun w => by exact_mod_cast SamplerCost.completionProposal_operations_le u p.val.1 w)
    (CompletionSampler.acceptedBackward u p.val.1 ⟨p.val.2,p.property⟩).val
  have hr := hrow.trans (mul_le_mul_left (inv_acceptance_le_two (F := F) (by omega : 1 ≤ n)) _)
  have hc := hcomp.trans (mul_le_mul_left (inv_completion_acceptance_le_four u p.val.1) _)
  have hpivot : ((CompletionSampler.pivotSearch p.val.1).operations : ℝ≥0∞) ≤ n := by
    exact_mod_cast CompletionSampler.pivotSearch_operations_le p.val.1
  have hout : (attemptOutputWork u v p : ℝ≥0∞) ≤ 2*n*(n+t)+n := by
    exact_mod_cast attemptOutputWork_le u v p
  unfold AttemptSampler.markDistribution
  rw [workExpectation_bind]
  simp_rw [workExpectation_map,internalWork,Nat.cast_add,workExpectation_add,
    workExpectation_const,traceNatWork_cast,AttemptSampler.reconstructRow,CompletionSampler.reconstruct,
    AttemptSampler.rowRejectedDistribution,CompletionSampler.rejectedDistribution]
  have hh := add_le_add (add_le_add (add_le_add hr hc) hpivot) hout
  convert hh using 1 <;> push_cast <;> ring

/-- The complete outer sampler, including every internal rejected proposal, has polynomial expected scalar work. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u, v ∈ U(F, (n + t)), assume 2 ≤ n. Then

workExpectation(fullTapeDistribution(u, v), ((z ↦ shorteningWork(u, v, z)))) ≤ 2 · (20 · (n + 1)² · (n + t + 1) + 4 · n + 2 · n · (n + t)).
-/
theorem shorteningWork_expected_le (hn : 2 ≤ n) (u v : U F (n+t)) :
    workExpectation (fullTapeDistribution hn u v) (fun z => (shorteningWork u v z : ℝ≥0∞)) ≤
      2*(20*(n+1)^2*(n+t+1)+4*n+2*n*(n+t)) := by
  simp_rw [shorteningWork_cast]
  have h := markedDistribution_work_le (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0))
    (attempt_acceptance_pos hn u v) (fun p => markDistribution hn u p.val.1)
    (fun p mark => (markedAttemptWork u v p mark : ℝ≥0∞))
    (20*(n+1)^2*(n+t+1)+4*n+2*n*(n+t)) (fun p => by
      rw [markDistribution,workExpectation_map]
      simp only [markedAttemptWork_tagged]
      exact internalWork_expected_le hn u v p)
  have hp : ENNReal.ofReal (1/acceptance (attemptDistribution hn u)
      (fun p => decide (rightOutput v p ≠ 0))) ≤ 2 := by
    have hreal : 1/acceptance (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0)) ≤ (2:ℝ) := by
      apply (div_le_iff₀ (attempt_acceptance_pos hn u v)).mpr
      have ha := attempt_acceptance_ge_half hn u v
      linarith
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hreal
  exact h.trans (mul_le_mul_left hp _)

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u ∈ U(F, (n + t)); p ∈ Attempt(n = n, u); mark ∈ AttemptSampler.Mark(m = n + t, (p)₁), we have

markedAttemptRandomWork(u, p, ((p)₁, mark)) = internalRandomWork(u, p, mark).
-/
@[simp] theorem markedAttemptRandomWork_tagged (u : U F (n+t)) (p : Attempt (n := n) u)
    (mark : AttemptSampler.Mark (m := n+t) p.val.1) :
    markedAttemptRandomWork u p ⟨p.val.1,mark⟩ = internalRandomWork u p mark := by
  simp [markedAttemptRandomWork]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u ∈ U(F, (n + t)); z ∈ MarkedTape(Attempt(n = n, u), Mark(F, n, (n + t))), we have

shorteningRandomWork(u, z) = markedTraceWork(((p, mark ↦ markedAttemptRandomWork(u, p, mark))), z) .
-/
@[simp] theorem shorteningRandomWork_cast (u : U F (n+t))
    (z : MarkedTape (Attempt (n := n) u) (Mark F n (n+t))) :
    (shorteningRandomWork u z : ℝ≥0∞) =
      markedTraceWork (fun p mark => (markedAttemptRandomWork u p mark : ℝ≥0∞)) z := by
  have h : ∀ (k : ℕ) (a : Tape (Attempt (n := n) u) k) (b : Tape (Mark F n (n+t)) k),
      (prefixRandomWork u k a b : ℝ≥0∞) =
        markedPrefixWork (fun p mark => (markedAttemptRandomWork u p mark : ℝ≥0∞)) k a b := by
    intro k
    induction k with
    | zero => intro a b; simp [prefixRandomWork,markedPrefixWork]
    | succ k ih => intro a b; simp only [prefixRandomWork,markedPrefixWork,Nat.cast_add,ih]
  simp only [shorteningRandomWork,markedTraceWork,Nat.cast_add,h]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u ∈ U(F, (n + t)); p ∈ Attempt(n = n, u), assume 2 ≤ n. Then

workExpectation(AttemptSampler.markDistribution(, u, (p)₁), ((mark ↦ internalRandomWork(u, p, mark)))) ≤ 2 · n + 4 · (n - 1) · (n + t).
-/
theorem internalRandomWork_expected_le (hn : 2 ≤ n) (u : U F (n+t)) (p : Attempt (n := n) u) :
    workExpectation (AttemptSampler.markDistribution (by omega : 1 ≤ n) u p.val.1)
      (fun mark => (internalRandomWork u p mark : ℝ≥0∞)) ≤
      2*n+4*((n-1)*(n+t):ℕ) := by
  have hr := prefixDistribution_traceWork_le (FiniteDistribution.uniform : FiniteDistribution (V F n)) nonzeroTest
    (AttemptSampler.row_acceptance_pos (by omega : 1 ≤ n))
    (fun _ => (n:ℝ≥0∞)) n (fun _ => le_rfl) p.val.1.val
  have hc := prefixDistribution_traceWork_le
    (FiniteDistribution.uniform : FiniteDistribution (CompletionSampler.FreeRows F n (n+t) (CompletionSampler.pivot p.val.1)))
    (CompletionSampler.accept u p.val.1) (CompletionSampler.acceptance_pos u p.val.1)
    (fun _ => (((n-1)*(n+t):ℕ):ℝ≥0∞)) (((n-1)*(n+t):ℕ):ℝ≥0∞) (fun _ => le_rfl)
    (CompletionSampler.acceptedBackward u p.val.1 ⟨p.val.2,p.property⟩).val
  have hrow := hr.trans (mul_le_mul_left (inv_acceptance_le_two (F := F) (by omega : 1 ≤ n)) _)
  have hcomp := hc.trans (mul_le_mul_left (inv_completion_acceptance_le_four u p.val.1) _)
  unfold AttemptSampler.markDistribution
  rw [workExpectation_bind]
  simp_rw [workExpectation_map,internalRandomWork,Nat.cast_add,workExpectation_add,
    workExpectation_const,traceNatWork_cast,AttemptSampler.reconstructRow,CompletionSampler.reconstruct]
  exact add_le_add hrow hcomp

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u, v ∈ U(F, (n + t)), assume 2 ≤ n. Then

workExpectation(fullTapeDistribution(u, v), ((z ↦ shorteningRandomWork(u, z)))) ≤ 2 · (2 · n + 4 · (n - 1) · (n + t)).
-/
theorem shorteningRandomWork_expected_le (hn : 2 ≤ n) (u v : U F (n+t)) :
    workExpectation (fullTapeDistribution hn u v) (fun z => (shorteningRandomWork u z : ℝ≥0∞)) ≤
      2*(2*n+4*((n-1)*(n+t):ℕ)) := by
  simp_rw [shorteningRandomWork_cast]
  have h := markedDistribution_work_le (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0))
    (attempt_acceptance_pos hn u v) (fun p => markDistribution hn u p.val.1)
    (fun p mark => (markedAttemptRandomWork u p mark : ℝ≥0∞))
    (2*n+4*((n-1)*(n+t):ℕ)) (fun p => by
      rw [markDistribution,workExpectation_map]
      simp only [markedAttemptRandomWork_tagged]
      exact internalRandomWork_expected_le hn u p)
  have hp : ENNReal.ofReal (1/acceptance (attemptDistribution hn u)
      (fun p => decide (rightOutput v p ≠ 0))) ≤ 2 := by
    have hreal : 1/acceptance (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0)) ≤ (2:ℝ) := by
      apply (div_le_iff₀ (attempt_acceptance_pos hn u v)).mpr
      have ha := attempt_acceptance_ge_half hn u v
      linarith
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hreal
  exact h.trans (mul_le_mul_left hp _)

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u, v ∈ U(F, (n + t)), assume 2 ≤ n. Then

workExpectation(fullTapeDistribution(u, v), ((z ↦ shorteningTotalWork(u, v, z)))) ≤ 64 · (n + 1)² · (n + t + 1).
-/
theorem shorteningTotalWork_expected_le (hn : 2 ≤ n) (u v : U F (n+t)) :
    workExpectation (fullTapeDistribution hn u v) (fun z => (shorteningTotalWork u v z : ℝ≥0∞)) ≤
      64*(n+1)^2*(n+t+1) := by
  simp only [shorteningTotalWork,Nat.cast_add,workExpectation_add]
  have h := add_le_add (shorteningWork_expected_le hn u v) (shorteningRandomWork_expected_le hn u v)
  apply h.trans
  have hsub : n-1 ≤ n := Nat.sub_le _ _
  have hprod : (n-1)*(n+t) ≤ n*(n+t) := Nat.mul_le_mul_right _ hsub
  have hsq : n ≤ (n+1)^2 := by nlinarith
  have hnB : n ≤ (n+1)^2*(n+t+1) :=
    hsq.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hnmB : n*(n+t) ≤ (n+1)^2*(n+t+1) :=
    Nat.mul_le_mul hsq (by omega)
  exact_mod_cast (show
    2*(20*(n+1)^2*(n+t+1)+4*n+2*n*(n+t))+2*(2*n+4*((n-1)*(n+t))) ≤
      64*(n+1)^2*(n+t+1) by nlinarith only [hprod,hnB,hnmB])

end

end CircuitCompiler.Rectangular.Taped
