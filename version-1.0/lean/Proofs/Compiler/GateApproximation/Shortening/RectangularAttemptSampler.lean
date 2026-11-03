import Proofs.Compiler.GateApproximation.MatrixPhase.EncodingSampling
import Proofs.Compiler.GateApproximation.Shortening.RectangularCompletionLeakage
import Proofs.Compiler.Construction.Parameters



/-!
# All internal randomness in one rectangular proposal

The short nonzero row is sampled by rejecting zero raw vectors. For that row, the completion sampler uses independent raw field entries and rejects rank failures. These are actual unbounded stopped tapes. The equivalent marked proposal distribution is derived, including its local dependence on the long left share.
-/
set_option autoImplicit false

set_option maxHeartbeats 2400000

open scoped BigOperators Classical

namespace CircuitCompiler.Rectangular.AttemptSampler

open Refresh MatrixRefresh Sampling Sampling.Unbounded

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ RowPrefix(F, n); a ∈ U(F, n), assume 1 ≤ n. Then

rowReturned((2)₂(reconstructRow(p, a))) = a.
-/
@[simp] theorem rowReturned_reconstruct {n : ℕ} (hn : 1 ≤ n)
    (p : RowPrefix F n) (a : U F n) : rowReturned hn (reconstructRow p a).2.2 = a :=
  rowReturned_nonzero hn a

/-- Forgetting every internal coin gives the exact existing primitive attempt distribution. No security or approximation premise is involved. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; u ∈ U(F, (n + t)), assume 2 ≤ n. Then

(returned(u)_*sequentialDistribution(, u)) = toPMF(attemptDistribution(u)) .
-/
theorem returned_distribution {n t : ℕ} (hn : 2 ≤ n) (u : U F (n+t)) :
    (sequentialDistribution (by omega : 1 ≤ n) u).map (returned u) = toPMF (attemptDistribution hn u) := by
  rw [sequentialDistribution_eq_marked hn,PMF.map_bind]
  simp only [PMF.map_comp,Function.comp_def,returned_reconstruct]
  have h (p : Attempt (n := n) u) :
      ((markDistribution (by omega : 1 ≤ n) u p.val.1).map (fun _ => p)) = PMF.pure p :=
    PMF.map_const _ _
  simp only [h,PMF.bind_pure]

end

end CircuitCompiler.Rectangular.AttemptSampler
