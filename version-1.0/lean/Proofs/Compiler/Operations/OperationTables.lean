import Proofs.Compiler.Operations.Execution

/-!
# Concrete instruction tables inside the global canonical network

The normalized global table at chronological position i is exactly the actual instruction's conditional distribution on its earlier operand slots and fresh output. This identity includes total completion of impossible histories and outputs.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace CircuitCompiler.Operations.Protocol
open Refresh _root_.CircuitCompiler.Composition _root_.CircuitCompiler.Composition.TopologicalExecution
variable {F E A : Type*} [Fintype E] [DecidableEq E] [Fintype A]
  {inputs S : ℕ}

/-- Read the actual conditional kernel at its typed chronological instruction. Only the old prefix is passed; the global future encodings are not arguments to any local leakage callback. -/
theorem operationAnswerDistribution_eq_instructionAt
    (protocol : Protocol F E A inputs) (defaultAnswer : A)
    (program : Operations.Program F inputs S) (i : Fin S) (history : List A)
    (encoding : Fin (inputs+S) → E) :
    protocol.operationAnswerDistribution defaultAnswer program i history encoding =
      protocol.answer i.val (program.instructionAt i)
        (GateProtocol.completeHistory defaultAnswer history i.val)
        (fun w => encoding (Fin.castLE (by have := i.isLt; omega) w))
        (encoding (Fin.natAdd inputs i)) := by
  induction program with
  | nil => exact Fin.elim0 i
  | @snoc S prior instruction ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [operationAnswerDistribution,Fin.lastCases_last,
        Operations.Program.instructionAt]
      rfl
    · simp only [operationAnswerDistribution,Fin.lastCases_castSucc,
        Operations.Program.instructionAt]
      rw [ih]
      rfl

end CircuitCompiler.Operations.Protocol
