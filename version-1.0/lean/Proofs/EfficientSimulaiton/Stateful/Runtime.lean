import Proofs.EfficientSimulaiton.Model
import Proofs.EfficientSimulaiton.Adaptive.Runtime
import Proofs.EfficientSimulaiton.Accounting
import Proofs.Compiler.Stateful.Resources

/-!
# Stateful simulator marginal and expected work

Counter erasure gives the very same online dummy-state physical experiment used in the privacy proof. Uniform single-operation bounds control expected work for adaptive inputs as well as fixed ones. The exact callback count comes from the compiled syntax, including each invocation's public samplers and both input-port refreshes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped ENNReal
namespace EfficientSimulation.Stateful
open Compiler Compiler.Stateful CircuitCompiler.Sampling.Unbounded
variable {m d c g k n ml sl : ℕ}

/-- The counted oracle simulator has exactly the visible distribution used by the stateful security theorem. -/
theorem simulator_marginal (circuit : Circuit m d c g k) (T : ℕ)
    (adversary : Compiler.Stateful.Adversary m d k n ml sl) (hn : 2 ≤ n)
    (oracle : Oracle d k) :
    viewLaw (simulator circuit T adversary hn oracle) =
      circuit.simulatedView T adversary hn oracle := by
  unfold viewLaw simulator Compiler.Stateful.Circuit.simulatedView Compiler.Stateful.Circuit.runState
  rw [PMF.map_comp]
  change toFinite ((EfficientSimulation.Adaptive.execution _ _ _ _ _).map
    ((fun state => circuit.observe T adversary oracle state.2) ∘ Prod.fst)) = _
  rw [←PMF.map_comp, EfficientSimulation.Adaptive.execution_marginal,
    ←toPMF_map, toFinite_toPMF]

/-- The expected work counter is bounded by an explicit polynomial, with only the initial registers encoded by trusted setup. -/
theorem simulator_expected_le (circuit : Circuit m d c g k) (T : ℕ)
    (adversary : Compiler.Stateful.Adversary m d k n ml sl) (hn : 2 ≤ n)
    (oracle : Oracle d k) :
    expectedWork (simulator circuit T adversary hn oracle) ≤ (workBound circuit T n:ℝ≥0∞) := by
  change workExpectation (simulator circuit T adversary hn oracle) (fun z => (z.2:ℝ≥0∞)) ≤ _
  rw [simulator, workExpectation_map]
  simp only [Nat.cast_add, workExpectation_add, workExpectation_const]
  have h := EfficientSimulation.Adaptive.execution_expected_le
    (circuit.unrolling T).schedule.compile.program (adversary.strategy c g T oracle) hn
    (circuit.sampleValues T adversary oracle) (fun _ => 0)
  rw [congrArg (fun S => EfficientSimulation.Adaptive.workBound m S n)
    (circuit.unrolled_operationCount T)] at h
  simpa only [workBound, Nat.cast_add, add_assoc, add_comm, add_left_comm] using add_le_add_left h ((m:ℝ≥0∞)+(T*k:ℕ))

/-- Charging an arbitrary uniform amount R for each of the actual local-answer evaluations gives the displayed relative runtime bound. -/
theorem simulator_callback_budget (circuit : Circuit m d c g k) (T : ℕ)
    (adversary : Compiler.Stateful.Adversary m d k n ml sl) (hn : 2 ≤ n)
    (oracle : Oracle d k) (R : ℕ) :
    expectedWork (chargeOracleBudget (simulator circuit T adversary hn oracle)
      (circuit.callbackCount T) R) ≤ (runtimeBound circuit T n R:ℝ≥0∞) := by
  rw [EfficientSimulationProof.expectedWork_chargeOracleBudget]
  simpa only [runtimeBound, Nat.cast_add] using
    add_le_add (simulator_expected_le circuit T adversary hn oracle)
      (le_refl ((circuit.callbackCount T*R:ℕ):ℝ≥0∞))

end EfficientSimulation.Stateful
