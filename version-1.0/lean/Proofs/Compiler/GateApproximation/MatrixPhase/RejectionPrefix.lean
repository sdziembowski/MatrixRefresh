import Proofs.Compiler.GateApproximation.Shortening.RectangularUnboundedSampling
import Proofs.Compiler.GateApproximation.MatrixPhase.UniformSampling
import Proofs.Compiler.Construction.Parameters



/-!
# Rejected proposals are independent of the accepted sample

The complete rejection-sampling tape splits into a failed prefix and the final accepted proposal. The former has a distribution depending on the proposal distribution and acceptance predicate, but not on the particular accepted proposal. This retains rejected randomness when replacing a sampler by its uniform output.
-/
set_option autoImplicit false

open scoped BigOperators ENNReal

namespace CircuitCompiler.Sampling.Unbounded

open Refresh

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]

/-- A finite leakage observation can read every rejected proposal. Conditional on the prefix, only an independent accepted proposal remains to be sampled. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; f ∈ StoppedTape(α) → β, assume 0 < acceptance(P, accept). Then

observe(P, accept, f) = toFinite(bind(prefixDistribution(P, accept), ((t ↦ toPMF((((a ↦ f(joinPrefix(t, a))))_*accepted(P, accept))))))).
-/
theorem observe_eq_prefix_bind (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (f : StoppedTape α → β) :
    observe P accept hp f = toFinite ((prefixDistribution P accept hp).bind
      (fun t => toPMF ((accepted P accept hp).map (fun a => f (joinPrefix t a))))) := by
  unfold observe
  rw [distribution_eq_prefix_bind, PMF.map_bind]
  simp only [toPMF_map, PMF.map_comp, Function.comp_def]

section Uniform

variable [Nonempty α]

/-- Uniform rejection may be implemented using an independent rejected prefix and a uniform satisfying input, with exactly the same complete tape distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For accept ∈ α → Bool; f ∈ StoppedTape(α) → β, assume 0 < acceptance(𝒰_α, accept); {a ∈ α | accept(a) = true} ≠ ∅. Then

observe(FiniteDistribution.uniform, accept, f) = toFinite(bind(prefixDistribution(FiniteDistribution.uniform, accept), ((t ↦ toPMF((((a ↦ f(joinPrefix(t, a))))_*𝒰_({a ∈ α | accept(a) = true}))))))).
-/
theorem uniform_observe_eq_prefix_bind (accept : α → Bool)
    (hp : 0 < acceptance (FiniteDistribution.uniform : FiniteDistribution α) accept)
    [Nonempty {a : α // accept a = true}] (f : StoppedTape α → β) :
    observe FiniteDistribution.uniform accept hp f =
      toFinite ((prefixDistribution FiniteDistribution.uniform accept hp).bind (fun t =>
        toPMF ((FiniteDistribution.uniform : FiniteDistribution {a : α // accept a = true}).map
          (fun a => f (joinPrefix t a.val))))) := by
  rw [observe_eq_prefix_bind, accepted_uniform]
  simp only [FiniteDistribution.map_map, Function.comp_def]

end Uniform

end

end CircuitCompiler.Sampling.Unbounded
