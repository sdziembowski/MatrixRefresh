import Proofs.EfficientSimulaiton.Model
import Proofs.EfficientSimulaiton.Sampling.Execution

/-!
# Exact marginal and expected work for causal physical execution

The single-instruction marginal and expected-work theorems are uniform in the selected public bit, current state, and incoming history. They therefore apply at every node of an online execution, without any independence assumption on running times or leakage answers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open scoped BigOperators ENNReal Classical

namespace EfficientSimulation.Adaptive
open Refresh MatrixRefresh CircuitCompiler Compiler.Adaptive
  CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution
  CircuitCompiler.Sampling.Unbounded

variable {ML MR BL BR : Type*} [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
  [Nonempty ML] [Nonempty MR] [Nonempty BL] [Nonempty BR]
  {n t P S : ℕ} {hdim : n*n+1 = n+t}

/-- Erasing every work counter yields exactly the actual raw adaptive physical runner. -/
theorem runner_erase
    (strategy : CircuitCompiler.Operations.Strategy Compiler.Bit ML MR BL BR n t P hdim)
    (hn : 2 ≤ n) (program : CircuitCompiler.Operations.Program Compiler.Bit P S)
    (values : SampleValues Compiler.Bit (CircuitCompiler.Operations.Answer ML MR BL BR) S) :
    (runner strategy hn program values).erase =
      Compiler.Adaptive.realRunner (strategy.protocol hn) program values := by
  induction program with
  | nil => rfl
  | @snoc S prior instruction ih =>
    simp only [runner, CostedRunner.erase, Compiler.Adaptive.realRunner, ih]
    congr 1
    funext state
    exact CircuitCompiler.Operations.Counted.instruction_marginal strategy hn S
      (selectInstruction instruction (values (Fin.last _) state.2)) state.2 state.1

/-- The visible full-state marginal is exact, including every online public-input sampling operation. -/
theorem execution_marginal (program : CircuitCompiler.Operations.Program Compiler.Bit P S)
    (strategy : CircuitCompiler.Operations.Strategy Compiler.Bit ML MR BL BR n t P hdim)
    (hn : 2 ≤ n) (values : SampleValues Compiler.Bit (CircuitCompiler.Operations.Answer ML MR BL BR) S)
    (input : Fin P → Compiler.Bit) :
    (execution program strategy hn values input).map Prod.fst =
      toPMF (((Compiler.Adaptive.realRunner (strategy.protocol hn) program values).execute
        (toFinite (CircuitCompiler.Sampling.RawEncoding.initializeShares hn input)))) := by
  rw [execution, CostedRunner.execute_erase, runner_erase,
    CircuitCompiler.Sampling.RawEncoding.initializeSharesCosted_marginal]

/-- The expected sampling and scalar-operation counter stays polynomial in the total operation count, with one trusted initialization and all actual retries included. -/
theorem execution_expected_le (program : CircuitCompiler.Operations.Program Compiler.Bit P S)
    (strategy : CircuitCompiler.Operations.Strategy Compiler.Bit ML MR BL BR n t P hdim)
    (hn : 2 ≤ n) (values : SampleValues Compiler.Bit (CircuitCompiler.Operations.Answer ML MR BL BR) S)
    (input : Fin P → Compiler.Bit) :
    workExpectation (execution program strategy hn values input) (fun z => (z.2:ℝ≥0∞)) ≤
      (workBound P S n:ℝ≥0∞) := by
  have hbinary : fieldCard Compiler.Bit = 2 := by simp [fieldCard, Compiler.Bit]
  have hb : (runner strategy hn program values).Bounded ((100*(n*n+2)^3:ℕ):ℝ≥0∞) := by
    induction program with
    | nil => trivial
    | @snoc S prior instruction ih =>
      exact ⟨ih (fun i => values i.castSucc), fun state =>
        CircuitCompiler.Operations.Counted.instruction_expected_le strategy hbinary hn S
          (selectInstruction instruction (values (Fin.last _) state.2)) state.2 state.1⟩
  have h := CostedRunner.execute_work_le
    (CircuitCompiler.Sampling.RawEncoding.initializeSharesCosted hn input)
    (runner strategy hn program values) _ hb
  apply h.trans
  have hi := CircuitCompiler.Sampling.RawEncoding.initializeSharesCosted_work_le hn input
  rw [hbinary] at hi
  simpa only [workBound, show (8:ℕ)*2 = 16 by norm_num, Nat.cast_add,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
    add_le_add hi (le_refl ((S:ℝ≥0∞)*(100*(n*n+2)^3)))

end EfficientSimulation.Adaptive
