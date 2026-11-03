import Proofs.Compiler.Operations.OperationTables

/-!
# Chronological ports of the direct compiler

The generic physical instruction array already excludes future memory locations from every operation. These identities expose its old ports and fresh output in the complete wire array. They connect the actual conditional answer kernels to local approximation certificates without changing any operation, probability, or leakage view.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace CompilerProof.Direct.Ports
open Refresh CircuitCompiler CircuitCompiler.Operations CircuitCompiler.Composition.TopologicalExecution

variable {F E A : Type*} {P S : ℕ}

/-- Embed an operation's strictly earlier memory port into the complete allocated wire array. -/
def oldWire (i : Fin S) (w : Fin (P+i.val)) : Fin (P+S) :=
  Fin.castLE (by have := i.isLt; omega) w

/-- The fresh output location allocated by the operation at chronological position i. -/
def newWire (i : Fin S) : Fin (P+S) := Fin.natAdd P i

/-- Different predecessor ports remain different in the complete wire array. -/
theorem oldWire_injective (i : Fin S) : Function.Injective (oldWire (P:=P) i) := by
  intro a b h
  exact Fin.ext (congrArg (fun w : Fin (P+S)=>w.val) h)

/-- No earlier input port is the fresh output slot of the same operation. -/
theorem oldWire_ne_newWire (i : Fin S) (w : Fin (P+i.val)) :
    oldWire i w ≠ newWire (P:=P) i := by
  intro h
  have he := congrArg Fin.val h
  have hw := w.isLt
  simp only [oldWire,newWire,Fin.val_castLE,Fin.val_natAdd] at he
  omega

/-- The fresh output is always in the full operation scope. -/
theorem newWire_mem (program : Operations.Program F P S) (i : Fin S) :
    newWire (P:=P) i ∈ program.scope i := by
  exact Finset.mem_insert_self _ _

/-- Every actual predecessor input belongs to the full scope after chronological embedding. -/
theorem oldWire_mem (program : Operations.Program F P S) (i : Fin S) (w : Fin (P+i.val))
    (hw : w ∈ (program.instructionAt i).inputs) : oldWire i w ∈ program.scope i := by
  apply Finset.mem_insert_of_mem
  rw [Operations.Program.sourceInstruction_eq_at]
  let e : Fin (P+i.val) ↪ Fin (P+S) := ⟨oldWire i,oldWire_injective i⟩
  change oldWire i w ∈ ((program.instructionAt i).mapPorts e).inputs
  rw [Instruction.inputs_mapPorts]
  exact Finset.mem_map.mpr ⟨w,hw,rfl⟩

/-- A global valid labeling satisfies the ordinary equation on exactly the typed old ports and fresh output. -/
theorem valid_at [Mul F] [Sub F] (program : Operations.Program F P S) (i : Fin S)
    (label : Fin (P+S) → F) (hvalid : program.valid label i) :
    label (newWire i)=(program.instructionAt i).eval (fun w=>label (oldWire i w)) := by
  rw [Operations.Program.valid,Operations.Program.sourceInstruction_eq_at,Instruction.eval_mapPorts] at hvalid
  exact hvalid

/-- Ordinary program evaluation satisfies every local instruction equation, including refresh copies and fixed public samplers. -/
theorem evaluated_valid [Mul F] [Sub F] (program : Operations.Program F P S)
    (input : Fin P → F) (i : Fin S) : program.valid (program.eval input) i := by
  induction program with
  | nil => exact Fin.elim0 i
  | @snoc S prior instruction ih =>
    have hprefix : (prior.snoc instruction).eval input ∘ Fin.castSucc=prior.eval input :=
      funext (fun w=>Operations.Program.eval_snoc_old prior instruction input w)
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp only [Operations.Program.valid,Operations.Program.sourceInstruction_snoc_last,
        Instruction.eval_mapPorts]
      change (prior.snoc instruction).eval input (Fin.last _)=_
      rw [Operations.Program.eval_snoc_last,hprefix]
    · dsimp only [Operations.Program.valid]
      rw [Operations.Program.sourceInstruction_snoc_old,Instruction.eval_mapPorts]
      change (prior.snoc instruction).eval input (Fin.natAdd P j).castSucc =
        (prior.sourceInstruction j).eval ((prior.snoc instruction).eval input ∘ Fin.castSucc)
      rw [Operations.Program.eval_snoc_old,hprefix]
      exact ih j

/-- The global distinct-operand invariant holds at every selected chronological computation instruction. -/
theorem instructionAt_distinct (program : Operations.Program F P S) (hd : program.DistinctInputs)
    (i : Fin S) : (program.instructionAt i).DistinctInputs := by
  induction program with
  | nil => exact Fin.elim0 i
  | @snoc S prior instruction ih =>
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [Operations.Program.instructionAt,Fin.lastCases_last] using hd.2
    · simpa only [Operations.Program.instructionAt,Fin.lastCases_castSucc] using ih hd.1 j

/-- The actual global answer distribution is the same physical conditional kernel on its old local prefix and new output; the supplied history is completed at impossible prefixes. -/
theorem operation_distribution [Fintype E] [DecidableEq E] [Fintype A]
    (protocol : Protocol F E A P) (defaultAnswer : A) (program : Operations.Program F P S)
    (i : Fin S) (history : List A) (encoding : Fin (P+S) → E) :
    protocol.operationAnswerDistribution defaultAnswer program i history encoding =
      protocol.answer i.val (program.instructionAt i)
        (GateProtocol.completeHistory defaultAnswer history i.val)
        (fun w=>encoding (oldWire i w)) (encoding (newWire i)) := by
  exact protocol.operationAnswerDistribution_eq_instructionAt defaultAnswer program i history encoding

/-- In particular, each answer weight used by the canonical network is the weight of its actual local physical conditional distribution. -/
theorem operation_probability [Fintype E] [DecidableEq E] [Fintype A]
    (protocol : Protocol F E A P) (defaultAnswer : A) (program : Operations.Program F P S)
    (i : Fin S) (history : List A) (encoding : Fin (P+S) → E) (z : A) :
    (protocol.operationAnswerDistribution defaultAnswer program i history encoding).weight z =
      (protocol.answer i.val (program.instructionAt i)
        (GateProtocol.completeHistory defaultAnswer history i.val)
        (fun w=>encoding (oldWire i w)) (encoding (newWire i))).weight z := by
  rw [operation_distribution]

end CompilerProof.Direct.Ports
