import Proofs.Compiler.GateApproximation.Shortening.RectangularAttemptSampler
import Proofs.Compiler.GateApproximation.Shortening.RectangularTapedLocal
import Proofs.Compiler.Construction.Parameters



/-!
# Concrete marked shortening executions

Every mark consists of the actual rejected row proposals and the actual rejected free-entry matrices. Its conditional distribution is obtained from the two implemented samplers and depends on the local long share and row. The outer marked rejection distribution retains these marks at every attempt.
-/
set_option autoImplicit false

set_option maxHeartbeats 2200000

open scoped BigOperators ENNReal

namespace CircuitCompiler.Rectangular.Taped

open Refresh MatrixRefresh Sampling Sampling.Unbounded

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

variable {n t : ℕ}

/-- Forgetting all private internal tapes recovers the proved outer sampler. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u, v ∈ U(F, (n + t)), assume 2 ≤ n. Then

((Sigma)₁_*fullTapeDistribution(u, v)) = Rectangular.fullTapeDistribution(u, v).
-/
theorem fullTapeDistribution_forget (hn : 2 ≤ n) (u v : U F (n+t)) :
    (fullTapeDistribution hn u v).map Sigma.fst = Rectangular.fullTapeDistribution hn u v :=
  markedDistribution_forget _ _ _ _

/-- The probability of a valid complete tape is the product of the actual marked proposal probabilities. This is the iid implementation, including both levels of unbounded internal rejection. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u, v ∈ U(F, (n + t)); base ∈ FullTape(n = n, u); marks ∈ Tape(Mark(F, n, (n + t)), (base)₁) × Mark(F, n, (n + t)), assume 2 ≤ n; AllRejected(((p ↦ decide((rightOutput(v, p) ≠ 0)))), (base)₁, ((base)₂)₁); rightOutput(v, ((base)₂)₂) ≠ 0. Then

fullTapeDistribution(u, v, (base, marks)) = enrichedPrefixWeight(attemptDistribution(u), ((p ↦ markDistribution(u, (p)₁))), (base)₁, ((base)₂)₁, (marks)₁) · (toPMF(attemptDistribution(u), ((base)₂)₂) · markDistribution(u, (((base)₂)₂)₁, (marks)₂)).
-/
theorem fullTapeDistribution_iid (hn : 2 ≤ n) (u v : U F (n+t))
    (base : FullTape (n := n) u) (marks : Tape (Mark F n (n+t)) base.1 × Mark F n (n+t))
    (hprefix : AllRejected (fun p => decide (rightOutput v p ≠ 0)) base.1 base.2.1)
    (hlast : rightOutput v base.2.2 ≠ 0) :
    fullTapeDistribution hn u v ⟨base,marks⟩ =
      enrichedPrefixWeight (attemptDistribution hn u) (fun p => markDistribution hn u p.val.1)
        base.1 base.2.1 marks.1 *
      (toPMF (attemptDistribution hn u) base.2.2 * markDistribution hn u base.2.2.val.1 marks.2) :=
  markedDistribution_eq_iid _ _ _ _ base marks hprefix (by simp [hlast])

/-- Every raw proposal in the reconstruction has exactly its original primitive result, including those whose right output triggered another retry. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u ∈ U(F, (n + t)); k ∈ ℕ; a ∈ Tape(Attempt(n = n, u), k); b ∈ Tape(Mark(F, n, (n + t)), k), we have

mapTape(AttemptSampler.returned(u), k, rawPrefix(u, k, a, b)) = a.
-/
theorem map_rawPrefix (u : U F (n+t)) (k : ℕ)
    (a : Tape (Attempt (n := n) u) k) (b : Tape (Mark F n (n+t)) k) :
    mapTape (AttemptSampler.returned u) k (rawPrefix u k a b) = a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rawPrefix,mapTape,rawAttempt_returned,ih]
    cases a
    rfl

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u ∈ U(F, (n + t)); z ∈ MarkedTape(Attempt(n = n, u), Mark(F, n, (n + t))), we have

mapStopped(AttemptSampler.returned(u), rawTrace(u, z)) = (z)₁.
-/
@[simp] theorem map_rawTrace (u : U F (n+t))
    (z : MarkedTape (Attempt (n := n) u) (Mark F n (n+t))) :
    mapStopped (AttemptSampler.returned u) (rawTrace u z) = z.1 := by
  rcases z with ⟨⟨k,a,p⟩,b,m⟩
  simp only [mapStopped,rawTrace,map_rawPrefix,rawAttempt_returned]

end

end CircuitCompiler.Rectangular.Taped
