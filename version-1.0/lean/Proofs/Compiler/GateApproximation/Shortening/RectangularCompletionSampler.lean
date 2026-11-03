import Proofs.Compiler.Foundations.Sampling.GaussianRankCost
import Proofs.Compiler.GateApproximation.Shortening.RectangularUnbounded
import Proofs.Compiler.GateApproximation.MatrixPhase.RejectionPrefix
import Proofs.Compiler.GateApproximation.MatrixPhase.UniformSampling
import Proofs.Compiler.Construction.Parameters



/-!
# A completion sampler with explicit internal proposal tapes

To sample a full-row-rank matrix subject to `A H = U`, independently sample all non-pivot entries, solve one pivot row for the linear constraint, and reject if the resulting matrix lacks full row rank. Every rejected proposal is retained in the stopped tape. This implements the same uniform completion distribution as the primitive sampler, using a different rejection schedule from the paper's sequential row-completion description.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators Classical

namespace CircuitCompiler.Rectangular.CompletionSampler

open Refresh MatrixRefresh Sampling

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

instance affineFintype {n m : ℕ} (u : U F m) (a : U F n) :
    Fintype (AffineCompletion u a) := Fintype.ofFinite _

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; a ∈ U(F, n), we have

operations(pivotSearch(a)) ≤ n.
-/
theorem pivotSearch_operations_le {n : ℕ} (a : U F n) :
    (pivotSearch a).operations ≤ n :=
  Gaussian.findPivot_operations_le _

instance affineNonempty {n m : ℕ} (u : U F m) (a : U F n) :
    Nonempty (AffineCompletion u a) := ⟨affineEquiv u a 0⟩

/-- The actual accepted free entries return exactly a uniform completion. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): Condition a uniform free-row proposal on its filled matrix having full row rank. The returned matrix is then uniform over all full-row-rank solutions of a · H = u. -/
theorem accepted_returned_uniform {n t : ℕ} (u : U F (n+t)) (a : U F n) :
    letI := completion_nonempty u a
    (accepted FiniteDistribution.uniform (accept u a) (acceptance_pos u a)).map (returned u a) =
      (FiniteDistribution.uniform : FiniteDistribution (Completion u a)) := by
  letI := completion_nonempty u a
  rw [accepted_uniform,FiniteDistribution.map_map]
  convert uniform_equiv (acceptedEquiv u a) using 1
  congr 1
  funext w
  exact returned_accepted u a w

/-- Internal field rejection implements the primitive uniform matrix distribution. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): Repeat uniform free-row proposals until their filled matrix has full row rank. The matrix returned by this unbounded rejection sampler is exactly uniform over the full-row-rank completions satisfying a · H = u. -/
theorem returned_uniform {n t : ℕ} (u : U F (n+t)) (a : U F n) :
    letI := completion_nonempty u a
    Unbounded.observe FiniteDistribution.uniform (accept u a) (acceptance_pos u a)
      (fun tape => returned u a tape.2.2) =
      (FiniteDistribution.uniform : FiniteDistribution (Completion u a)) := by
  letI := completion_nonempty u a
  rw [Unbounded.observe_last]
  exact accepted_returned_uniform u a

end

end CircuitCompiler.Rectangular.CompletionSampler
