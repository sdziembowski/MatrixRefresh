import Proofs.EfficientSimulaiton.Direct.Runtime
import Proofs.EfficientSimulaiton.Direct.Parameters
import Proofs.Compiler.Direct.Theorem52

/-!
# Efficient dummy-input simulation of the actual direct compiler

The simulator's marginal is the real zero-private-input execution with its hidden output shares discarded and its supplied plaintext appended. The proved direct privacy bound gives its error. Initialization, all sampler retries and output copying satisfy the concrete polynomial work bound; arbitrary correlated callback costs remain separately accounted for.
-/

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace EfficientSimulation.Direct

/-- One concrete counted simulator has the exact dummy-input marginal, polynomial expected sampler work, explicit callback accounting, and exponentially small error at a logarithmic share-length threshold. -/
theorem theorem_simulation :
    ∃ C : ℝ, 1≤C ∧
      ∀ (n ml sl P U T k : ℕ) (hn : 2≤n)
        (source : Compiler.Direct.Source P U T k) (adversary : Adversary source n ml sl),
        ∃ S : Simulator source n ml sl,
          S=simulator source adversary hn ∧
          (∀ (aux : AuxiliaryInput) (y : Fin k → Compiler.Bit),
            viewLaw (S aux y)=Compiler.Direct.simulatedView (adversary aux) hn y ∧
            expectedWork (S aux y)≤(workBound source n:ℝ≥0∞) ∧
            (∀ R : ℕ, expectedWork (chargeOracleBudget (S aux y) (oracleCalls source) R)≤
              (runtimeBound source n R:ℝ≥0∞)) ∧
            (∀ accounting : AccountingLaw (Compiler.Direct.View source ml sl),
              AccountsFor (S aux y) accounting→expectedWork (totalRun accounting)≤
                (workBound source n:ℝ≥0∞)+additionalExpectedWork accounting)) ∧
          (∀ (κ : ℝ) (_hκ : 1≤κ) (aux : AuxiliaryInput) (input : Fin P → Compiler.Bit),
            C*(κ+((ml+sl:ℕ):ℝ)+Real.log ((source.operationCount:ℝ)+2))≤(n:ℝ)→
            Compiler.statisticalDistance (Compiler.Direct.realView (adversary aux) hn input)
              (viewLaw (S aux (source.outputValues input)))≤Real.rpow 2 (-κ)) := by
  refine ⟨12000,by norm_num,?_⟩
  intro n ml sl P U T k hn source adversary
  refine ⟨simulator source adversary hn,rfl,?_,?_⟩
  · intro aux y
    have hw := EfficientSimulationProof.Direct.simulator_expected_le source adversary hn aux y
    refine ⟨EfficientSimulationProof.Direct.simulator_marginal source adversary hn aux y,hw,?_,?_⟩
    · intro R
      exact EfficientSimulationProof.Direct.simulator_oracle_budget source adversary hn aux y R
    · intro accounting haccounting
      exact EfficientSimulationProof.totalRun_expected_le _ accounting haccounting hw
  · intro κ hκ aux input hsize
    rw [EfficientSimulationProof.Direct.simulator_marginal]
    exact (Compiler.Direct.theorem_direct source (adversary aux) hn input).trans
      (EfficientSimulationProof.Direct.direct_bound_le hn hκ hsize)

end EfficientSimulation.Direct
