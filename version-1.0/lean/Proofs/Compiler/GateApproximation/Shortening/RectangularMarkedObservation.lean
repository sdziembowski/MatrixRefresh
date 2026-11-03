import Proofs.Compiler.GateApproximation.MatrixPhase.MarkedRejection
import Proofs.Compiler.GateApproximation.Shortening.RectangularPhysicalStochastic
import Proofs.Compiler.Construction.Parameters



/-!
# Observing the actual marked rejection sampler

The stochastic observation distribution is obtained by averaging the actual internal marks of each outer proposal. This equality preserves all rejected marks.
-/
set_option autoImplicit false

set_option maxHeartbeats 1800000

open scoped BigOperators ENNReal

namespace CircuitCompiler.Sampling.Unbounded

open Refresh

noncomputable section

/-- The explicit joint mass and sequential dependent sampling agree. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): For a probability mass function P on I and conditional mass functions Qᵢ on sets Jᵢ, the joint distribution on pairs (i,j) is obtained by first sampling i from P, then j from Qᵢ. Its mass at (i,j) is P(i) · Qᵢ(j). -/
theorem sigmaPMF_eq_bind {I : Type*} {J : I → Type*} (P : PMF I) (Q : ∀ i, PMF (J i)) :
    sigmaPMF P Q = P.bind (fun i => (Q i).map (Sigma.mk i)) := by
  classical
  apply PMF.ext
  intro ⟨i,j⟩
  rw [PMF.bind_apply,tsum_eq_single i]
  · rw [PMF.map_apply]
    simp
    try rw [tsum_eq_single j (fun a ha => if_neg (Ne.symm ha)),if_pos rfl]
  · intro k hk
    rw [PMF.map_apply]
    have hne (x : J k) : (⟨i,j⟩ : Sigma J) ≠ ⟨k,x⟩ := by
      intro h
      exact hk (congrArg Sigma.fst h).symm
    simp [hne]

variable {α β Z : Type*} [Fintype α] [Fintype Z]

/-- A deterministic observation of every internal mark becomes a conditional answer distribution given the outer tape by exact averaging over those marks. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; R ∈ α → PMF(β); f ∈ MarkedTape(α, β) → Z, assume 0 < acceptance(P, accept). Then

toFinite((f_*markedDistribution(P, accept, R))) = observeDistribution(P, accept, ((t ↦ toFinite((((m ↦ f((t, m))))_*traceMarks(R, t)))))).
-/
theorem marked_observe_eq_distribution (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (R : α → PMF β)
    (f : MarkedTape α β → Z) :
    toFinite ((markedDistribution P accept hp R).map f) =
      observeDistribution P accept hp (fun t => toFinite ((traceMarks R t).map (fun m => f ⟨t,m⟩))) := by
  unfold markedDistribution observeDistribution
  rw [sigmaPMF_eq_bind,PMF.map_bind]
  simp only [PMF.map_comp,Function.comp_def,toPMF_toFinite]

end

end CircuitCompiler.Sampling.Unbounded
