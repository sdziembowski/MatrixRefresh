import Proofs.Compiler.Operations.Model

/-!
# Elementary identities for the mixed chronological program

These identities describe the chronological instruction array used by both compilers. They concern only ordinary evaluation and finite port renaming, without any privacy or sampling premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace CircuitCompiler.Operations

namespace Instruction
variable {F : Type*} {a b c : ℕ}

/-- Successive predecessor renamings compose as functions. -/
@[simp] theorem mapPorts_comp (instruction : Instruction F a)
    (e : Fin a → Fin b) (f : Fin b → Fin c) :
    (instruction.mapPorts e).mapPorts f = instruction.mapPorts (f ∘ e) := by
  cases instruction <;> rfl

/-- Renaming predecessor ports by the identity leaves an instruction unchanged. -/
@[simp] theorem mapPorts_id (instruction : Instruction F a) :
    instruction.mapPorts id = instruction := by cases instruction <;> rfl

/-- Instruction evaluation commutes with renaming its predecessor ports. -/
@[simp] theorem eval_mapPorts [Mul F] [Sub F] (instruction : Instruction F a)
    (e : Fin a → Fin b) (values : Fin b → F) :
    (instruction.mapPorts e).eval values = instruction.eval (values ∘ e) := by
  cases instruction <;> rfl

/-- Renaming predecessor ports maps the instruction’s active predecessor set. -/
@[simp] theorem inputs_mapPorts (instruction : Instruction F a) (e : Fin a ↪ Fin b) :
    (instruction.mapPorts e).inputs = instruction.inputs.map e := by
  cases instruction <;> simp [mapPorts,inputs]

end Instruction

namespace Program
variable {F : Type*} {inputs S : ℕ}

/-- Appending an instruction preserves the evaluated labels of all older wire slots. -/
@[simp] theorem eval_snoc_old [Mul F] [Sub F] (prior : Program F inputs S)
    (instruction : Instruction F (inputs+S)) (input : Fin inputs → F)
    (w : Fin (inputs+S)) :
    (prior.snoc instruction).eval input w.castSucc = prior.eval input w := by
  simp [eval]

/-- The fresh output slot contains the appended instruction’s evaluated result. -/
@[simp] theorem eval_snoc_last [Mul F] [Sub F] (prior : Program F inputs S)
    (instruction : Instruction F (inputs+S)) (input : Fin inputs → F) :
    (prior.snoc instruction).eval input (Fin.last _) = instruction.eval (prior.eval input) := by
  simp [eval]

/-- Trusted input labels keep their original slots throughout evaluation. -/
theorem eval_input [Mul F] [Sub F] (program : Program F inputs S) (input : Fin inputs → F)
    (i : Fin inputs) : program.eval input (Fin.castAdd S i) = input i := by
  induction program with
  | nil => rfl
  | @snoc S prior instruction ih =>
    have hi : Fin.castAdd (S+1) i = (Fin.castAdd S i).castSucc := Fin.ext rfl
    rw [hi,eval_snoc_old]
    exact ih

/-- Appending an instruction preserves the older instructions under the natural wire embedding. -/
@[simp] theorem sourceInstruction_snoc_old (prior : Program F inputs S)
    (instruction : Instruction F (inputs+S)) (i : Fin S) :
    (prior.snoc instruction).sourceInstruction i.castSucc =
      (prior.sourceInstruction i).mapPorts Fin.castSucc := by
  simp only [sourceInstruction,Fin.lastCases_castSucc]

/-- The final instruction of an appended program is the appended instruction on complete coordinates. -/
@[simp] theorem sourceInstruction_snoc_last (prior : Program F inputs S)
    (instruction : Instruction F (inputs+S)) :
    (prior.snoc instruction).sourceInstruction (Fin.last S) = instruction.mapPorts Fin.castSucc := by
  simp only [sourceInstruction,Fin.lastCases_last]

/-- Reading a position from an assembled array returns exactly that instruction, with its predecessor ports embedded in the final array. -/
theorem ofInstructions_sourceInstruction
    (instructions : (i : Fin S) → Instruction F (inputs+i.val)) (i : Fin S) :
    (ofInstructions instructions).sourceInstruction i =
      (instructions i).mapPorts (fun w => Fin.castLE (by have := i.isLt; omega) w) := by
  induction S with
  | zero => exact Fin.elim0 i
  | succ S ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [ofInstructions,sourceInstruction_snoc_last]
      cases instructions (Fin.last S) <;> rfl
    · simp only [ofInstructions,sourceInstruction_snoc_old,ih,Instruction.mapPorts_comp]
      cases instructions j.castSucc <;> rfl

/-- The typed instruction array is recovered exactly, before embedding ports. -/
theorem ofInstructions_instructionAt
    (instructions : (i : Fin S) → Instruction F (inputs+i.val)) (i : Fin S) :
    (ofInstructions instructions).instructionAt i = instructions i := by
  induction S with
  | zero => exact Fin.elim0 i
  | succ S ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [ofInstructions,instructionAt,Fin.lastCases_last]
    · simp only [ofInstructions,instructionAt,Fin.lastCases_castSucc,ih]

/-- Global port indices are precisely the embedding of the typed instruction's earlier ports. This identity connects actual execution and global scopes. -/
theorem sourceInstruction_eq_at (program : Program F inputs S) (i : Fin S) :
    program.sourceInstruction i = (program.instructionAt i).mapPorts
      (fun w => Fin.castLE (by have := i.isLt; omega) w) := by
  induction program with
  | nil => exact Fin.elim0 i
  | @snoc S prior instruction ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [sourceInstruction,instructionAt,Fin.lastCases_last]
      cases instruction <;> rfl
    · simp only [sourceInstruction,instructionAt,Fin.lastCases_castSucc,ih,
        Instruction.mapPorts_comp]
      cases prior.instructionAt j <;> rfl

/-- The last operation’s scope consists of its predecessor inputs and fresh output. -/
@[simp] theorem scope_snoc_last (prior : Program F inputs S)
    (instruction : Instruction F (inputs+S)) :
    (prior.snoc instruction).scope (Fin.last S) =
      insert (Fin.last (inputs+S)) (instruction.inputs.map Fin.castSuccEmb) := by
  rw [scope,sourceInstruction_snoc_last]
  change insert (Fin.last (inputs+S))
    (instruction.mapPorts Fin.castSuccEmb).inputs = _
  rw [Instruction.inputs_mapPorts]

/-- Appending an operation embeds every earlier scope without changing its named wires. -/
@[simp] theorem scope_snoc_old (prior : Program F inputs S)
    (instruction : Instruction F (inputs+S)) (i : Fin S) :
    (prior.snoc instruction).scope i.castSucc = (prior.scope i).map Fin.castSuccEmb := by
  rw [scope,sourceInstruction_snoc_old]
  change insert (Fin.natAdd inputs i).castSucc
    ((prior.sourceInstruction i).mapPorts Fin.castSuccEmb).inputs = _
  rw [Instruction.inputs_mapPorts,scope,Finset.map_insert]
  rfl

/-- Array construction preserves the explicit distinct-computation condition. -/
theorem ofInstructions_distinct
    (instructions : (i : Fin S) → Instruction F (inputs+i.val))
    (hd : ∀ i, (instructions i).DistinctInputs) : (ofInstructions instructions).DistinctInputs := by
  induction S with
  | zero => trivial
  | succ S ih => exact ⟨ih (fun i => instructions i.castSucc) (fun i => hd i.castSucc),hd (Fin.last S)⟩

end Program
end CircuitCompiler.Operations
