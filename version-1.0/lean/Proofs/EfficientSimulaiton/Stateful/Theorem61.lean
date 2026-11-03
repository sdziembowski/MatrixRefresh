import Proofs.EfficientSimulaiton.Stateful.Runtime
import Proofs.Compiler.Stateful.Theorem61
import Proofs.Compiler.Stateful.Parameters

/-!
# Efficient continual stateful simulation

The simulator is quantified before the actual private initial state. Its explicit polynomial counts physical sampling and preparation; adversary and ideal-oracle computation are separate. The statement includes the binary 18λ−n/27 rate and a uniform logarithmic share-length threshold.
-/

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace EfficientSimulation.Stateful

/-- One initial-state-independent oracle simulator has the exact physical dummy-run marginal, polynomial expected sampler work, the exact local-answer budget, and the stateful privacy bounds. -/
theorem theorem_simulation {m d c g k n ml sl : ℕ} (circuit : Compiler.Stateful.Circuit m d c g k)
    (T : ℕ) (adversary : Compiler.Stateful.Adversary m d k n ml sl) (hn : 2 ≤ n) :
    ∃ simulate : Compiler.Stateful.Oracle d k → PMF (circuit.View T ml sl × ℕ),
      simulate = simulator circuit T adversary hn ∧
      (∀ oracle,
        viewLaw (simulate oracle) = circuit.simulatedView T adversary hn oracle ∧
        expectedWork (simulate oracle) ≤ (workBound circuit T n:ℝ≥0∞) ∧
        ∀ R : ℕ, expectedWork (chargeOracleBudget (simulate oracle) (circuit.callbackCount T) R) ≤
          (runtimeBound circuit T n R:ℝ≥0∞)) ∧
      (circuit.privacyBound T n ml sl ≤
        2000000*(circuit.operationCount T:ℝ)*(2:ℝ)^(18*((ml+sl:ℕ):ℝ)-(n:ℝ)/27)) ∧
      (∀ initial : Fin m → Compiler.Bit,
        Refresh.statisticalDistance (circuit.realView T adversary hn initial)
          (viewLaw (simulate (circuit.oracle initial))) ≤ min 1 (circuit.privacyBound T n ml sl) ∧
        ∀ (κ : ℝ) (_hκ : 1 ≤ κ),
          12000*(κ+((ml+sl:ℕ):ℝ)+Real.log ((circuit.operationCount T:ℝ)+2)) ≤ n →
          Refresh.statisticalDistance (circuit.realView T adversary hn initial)
            (viewLaw (simulate (circuit.oracle initial))) ≤ (2:ℝ)^(-κ)) := by
  refine ⟨simulator circuit T adversary hn,rfl,?_,circuit.privacyBound_binary T hn,?_⟩
  · intro oracle
    exact ⟨simulator_marginal circuit T adversary hn oracle,
      simulator_expected_le circuit T adversary hn oracle,
      simulator_callback_budget circuit T adversary hn oracle⟩
  · rcases Compiler.Stateful.theorem_stateful circuit T adversary hn with ⟨simulate,hs,hsecurity⟩
    subst simulate
    intro initial
    rw [simulator_marginal]
    refine ⟨hsecurity initial,?_⟩
    intro κ hκ hsize
    exact ((hsecurity initial).trans (min_le_right _ _)).trans
      (circuit.privacyBound_logarithmic T hn hκ hsize)

end EfficientSimulation.Stateful
