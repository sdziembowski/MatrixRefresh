import Proofs.Compiler.GateApproximation.Shortening.RectangularFullyTapedProgram
import Proofs.Compiler.GateApproximation.Shortening.RectangularRawRetryDistribution
import Proofs.Compiler.Construction.Parameters



/-!
# Gate execution directly from complete raw-record retry distributions

This presentation of the implementation uses countable iid rejection on raw row/completion records directly. Exact equalities connect it to the marked analytic representation, without changing any privacy or runtime parameter.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2200000

open scoped Classical

namespace CircuitCompiler.Rectangular

open Refresh MatrixRefresh TableAnalysis Shortening RefreshAnalysis

open Composition Composition.TopologicalExecution Sampling Sampling.Unbounded

noncomputable section

variable {F O A BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [Fintype A] [Fintype BL] [Fintype BR] {n t : ℕ}

namespace Taped

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u ∈ U(F, (n + t)); z ∈ MarkedTape(Attempt(n = n, u), Mark(F, n, (n + t))), we have

rawRightView(u, rawTrace(u, z)) = rightView((z)₁).
-/
@[simp] theorem rawRightView_rawTrace (u : U F (n+t))
    (z : MarkedTape (Attempt (n := n) u) (Mark F n (n+t))) :
    rawRightView u (rawTrace u z) = rightView z.1 := by
  rw [rawRightView,map_rawTrace]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u ∈ U(F, (n + t)); z ∈ MarkedTape(Attempt(n = n, u), Mark(F, n, (n + t))), we have

AttemptSampler.returned(u, (2)₂(rawTrace(u, z))) = (((z)₁)₂)₂.
-/
@[simp] theorem rawTrace_last_returned (u : U F (n+t))
    (z : MarkedTape (Attempt (n := n) u) (Mark F n (n+t))) :
    AttemptSampler.returned u (rawTrace u z).2.2 = z.1.2.2 := by
  exact rawAttempt_returned u _ _

/-- The direct iid raw-loop observation equals the marked sampler observation for every local leakage function, including functions reading all failures. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F; fallback ∈ Fiber(F, n, s); left ∈ A → O → ∏_(u ∈ U(F, (n + t))) StoppedTape(AttemptSampler.Record(n = n, u)) → BL; right ∈ A → O → U(F, (n + t)) → RightView(F, n, (n + t)) → BR; o ∈ O × O; x ∈ Fiber(F, (n + t), s); α ∈ A, assume 2 ≤ n. Then

rawShorteningExecution(fallback, left, right, o, x, α) = rawShorteningDirect(fallback, left, right, o, x, α).
-/
theorem rawShorteningExecution_eq_direct {s : F} (hn : 2 ≤ n) (fallback : Fiber F n s)
    (left : A → O → (u : U F (n+t)) → StoppedTape (AttemptSampler.Record (n := n) u) → BL)
    (right : A → O → U F (n+t) → RightView F n (n+t) → BR)
    (o : O × O) (x : Fiber F (n+t) s) (α : A) :
    rawShorteningExecution hn fallback left right o x α =
      rawShorteningDirect hn fallback left right o x α := by
  unfold rawShorteningDirect
  rw [← fullTapeDistribution_rawTrace,PMF.map_comp]
  unfold rawShorteningExecution
  congr 1
  congr 1
  funext z
  simp only [Function.comp_def,rawTrace_last_returned,rawRightView_rawTrace]

end Taped

namespace FullyTapedStrategy

variable {ML MR : Type*} [Fintype ML] [Fintype MR] {inputs : ℕ} {hdim : n*n+1 = n+t}

/-- Equality of full gate distributions, preserving correlations among the returned encoding, matrix leakage, and complete shortening-tape leakage. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ FullyTapedStrategy(F, ML, MR, BL, BR, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → (ML × MR) × (BL × BR); left, right ∈ State(F, n), assume 2 ≤ n. Then

strategy.rawExecution(i, gate, history, left, right) = strategy.directRawExecution(i, gate, history, left, right).
-/
theorem rawExecution_eq_direct (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → (ML × MR) × (BL × BR)) (left right : State F n) :
    strategy.rawExecution hn i gate history left right =
      strategy.directRawExecution hn i gate history left right := by
  unfold rawExecution directRawExecution
  simp only [Taped.rawShorteningExecution_eq_direct]

end FullyTapedStrategy

end

end CircuitCompiler.Rectangular
