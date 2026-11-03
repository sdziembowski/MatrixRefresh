import Proofs.EfficientSimulaiton.Model
import Proofs.EfficientSimulaiton.Sampling.Execution
import Proofs.EfficientSimulaiton.Accounting
import Proofs.Compiler.Direct.Resources

/-!
# Concrete direct-simulator marginal and expected work

The counted runner and the uncounted physical protocol are the same sampler after erasing its work counter. Preparing the zero private input and copying the supplied plaintext output are explicitly charged preparation operations. Thus the simulation never needs a private input yielding the authorized output and never samples an approximation or signed measure.
-/

set_option autoImplicit false
noncomputable section
open scoped ENNReal BigOperators

namespace EfficientSimulationProof.Direct
open EfficientSimulation EfficientSimulation.Direct Compiler Compiler.Direct
  CircuitCompiler CircuitCompiler.Sampling.Unbounded CircuitCompiler.Rectangular.Gaussian

variable {P U T k n ml sl : ℕ}

/-- Each prepared private source input is exactly zero. -/
@[simp] theorem preparation_get (i : Fin P) :
    (preparation P).value.get i=0 := by
  simp [preparation]

/-- Materializing P zero private values costs exactly P indexed writes. -/
@[simp] theorem preparation_operations : (preparation P).operations=P := by
  simp [preparation,tabulate_operations]

/-- Reporting the supplied authorized output preserves every designated output position and repetition. -/
@[simp] theorem outputPreparation_get (output : Fin k → Bit) (j : Fin k) :
    (outputPreparation output).value.get j=output j := by
  simp [outputPreparation]

/-- Copying the supplied output tuple costs exactly k primitive output writes. -/
@[simp] theorem outputPreparation_operations (output : Fin k → Bit) :
    (outputPreparation output).operations=k := by
  simp [outputPreparation,tabulate_operations]

/-- The counted simulator's visible marginal is exactly the actual zero-input transcript followed by its supplied plaintext output, for every supplied tuple. -/
theorem simulator_marginal (source : Source P U T k)
    (adversary : Adversary source n ml sl) (hn : 2≤n)
    (aux : AuxiliaryInput) (output : Fin k → Bit) :
    viewLaw (EfficientSimulation.Direct.simulator source adversary hn aux output)=
      Compiler.Direct.simulatedView (adversary aux) hn output := by
  unfold viewLaw EfficientSimulation.Direct.simulator Compiler.Direct.simulatedView
    Compiler.Direct.transcript Compiler.Direct.runState
  rw [PMF.map_comp]
  simp only [preparation_get,outputPreparation_get]
  change toFinite ((CircuitCompiler.Operations.Counted.execution source.compiledProgram
    (adversary aux) hn (fun _=>0)).map
      ((fun state=>((Composition.answersEquiv _ _).symm state.2,output)) ∘ Prod.fst))=_
  rw [←PMF.map_comp,CircuitCompiler.Operations.Counted.execution_marginal,
    ←toPMF_map,toFinite_toPMF,Refresh.FiniteDistribution.map_map]
  rfl

/-- Initialization, all rejected proposals and retries, and plaintext reporting obey the explicit polynomial bound on the simplified work counter. -/
theorem simulator_expected_le (source : Source P U T k)
    (adversary : Adversary source n ml sl) (hn : 2≤n)
    (aux : AuxiliaryInput) (output : Fin k → Bit) :
    expectedWork (EfficientSimulation.Direct.simulator source adversary hn aux output)≤
      (workBound source n : ℝ≥0∞) := by
  change workExpectation (EfficientSimulation.Direct.simulator source adversary hn aux output)
    (fun z=>(z.2:ℝ≥0∞))≤_
  rw [EfficientSimulation.Direct.simulator,workExpectation_map]
  simp only [preparation_get,preparation_operations,outputPreparation_operations,
    Nat.cast_add,workExpectation_add,workExpectation_const]
  have hbinary : Refresh.fieldCard Bit=2 := by simp [Refresh.fieldCard,Bit]
  have h := CircuitCompiler.Operations.Counted.execution_expected_le source.compiledProgram
    (adversary aux) hbinary hn (fun _=>0)
  simpa only [EfficientSimulation.Direct.workBound,Nat.cast_add,add_assoc,add_comm,add_left_comm] using
    add_le_add_left h ((P:ℝ≥0∞)+k)

/-- The displayed callback count is derived from the actual physical instruction syntax. -/
theorem oracleCalls_actual (source : Source P U T k) :
    oracleCalls source=Compiler.Direct.Physical.callbacks source.compiledProgram := by
  exact source.callbacks_eq.symm

/-- A uniform charge per actual leakage evaluation adds exactly the stated relative callback budget. -/
theorem simulator_oracle_budget (source : Source P U T k)
    (adversary : Adversary source n ml sl) (hn : 2≤n)
    (aux : AuxiliaryInput) (output : Fin k → Bit) (R : ℕ) :
    expectedWork (chargeOracleBudget
      (EfficientSimulation.Direct.simulator source adversary hn aux output) (oracleCalls source) R)≤
        (runtimeBound source n R : ℝ≥0∞) := by
  rw [expectedWork_chargeOracleBudget]
  simpa [EfficientSimulation.Direct.runtimeBound,Nat.cast_add] using
    add_le_add (simulator_expected_le source adversary hn aux output)
      (le_refl (((oracleCalls source)*R:ℕ):ℝ≥0∞))

end EfficientSimulationProof.Direct
