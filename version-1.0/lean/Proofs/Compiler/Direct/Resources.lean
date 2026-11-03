import Proofs.Compiler.Model

/-!
# Actual operation and callback counts

The counters below inspect the compiled physical instruction syntax, not an independent resource specification. Each source gate contributes one protected NAND and two ordinary refreshes. A public input contributes one sampler. Initialization consists only of the private input prefix.
-/

set_option autoImplicit false
noncomputable section

namespace Compiler.Direct.Physical
open CircuitCompiler

/-- Count the protected computation instructions in an actual physical program. -/
def computations {P : ℕ} : {S : ℕ} → Operations.Program Bit P S → ℕ
  | 0,.nil => 0
  | _+1,.snoc prior instruction => computations prior+
      match instruction with | .compute _ => 1 | _ => 0

/-- Count the ordinary dimension-n refresh instructions in an actual physical program. -/
def refreshes {P : ℕ} : {S : ℕ} → Operations.Program Bit P S → ℕ
  | 0,.nil => 0
  | _+1,.snoc prior instruction => refreshes prior+
      match instruction with | .refresh _ => 1 | _ => 0

/-- Count the leaky public-input sampling instructions in an actual physical program. -/
def samplers {P : ℕ} : {S : ℕ} → Operations.Program Bit P S → ℕ
  | 0,.nil => 0
  | _+1,.snoc prior instruction => samplers prior+
      match instruction with | .sample _ => 1 | _ => 0

/-- Four local answers are evaluated at a two-phase computation; the two single-phase instruction kinds evaluate two. -/
def callbacks {P : ℕ} : {S : ℕ} → Operations.Program Bit P S → ℕ
  | 0,.nil => 0
  | _+1,.snoc prior instruction => callbacks prior+
      match instruction with | .compute _ => 4 | _ => 2

/-- Every protected computation instruction in this program has fixed NAND kind; ordinary refreshes and public samplers carry no binary gate offset. -/
def NandOnly {P : ℕ} : {S : ℕ} → Operations.Program Bit P S → Prop
  | 0,.nil => True
  | _+1,.snoc prior instruction => NandOnly prior ∧
      match instruction with | .compute gate => gate.kind=.complement 1 | _ => True

/-- The actual callback count is the weighted sum of the three actual instruction counts. -/
theorem callbacks_eq {P S : ℕ} (program : Operations.Program Bit P S) :
    callbacks program=4*computations program+2*refreshes program+2*samplers program := by
  induction program with
  | nil => rfl
  | snoc prior instruction ih =>
    cases instruction <;> simp [callbacks,computations,refreshes,samplers,ih] <;> omega

/-- The public initialization prefix consists of exactly U sampling operations and no computation or refresh. -/
theorem public_counts {P U : ℕ} (values : Fin U → Bit) :
    computations (Compilation.publicProgram (P:=P) values)=0 ∧
    refreshes (Compilation.publicProgram (P:=P) values)=0 ∧
    samplers (Compilation.publicProgram (P:=P) values)=U := by
  induction U with
  | zero => simp [Compilation.publicProgram,computations,refreshes,samplers]
  | succ u ih =>
    simpa [Compilation.publicProgram,computations,refreshes,samplers] using ih (fun i=>values i.castSucc)

/-- Public samplers alone have no computation-operand restriction. -/
theorem public_distinct {P U : ℕ} (values : Fin U → Bit) :
    (Compilation.publicProgram (P:=P) values).DistinctInputs := by
  induction U with
  | zero => trivial
  | succ u ih => exact ⟨ih _,trivial⟩

/-- The public-sampling prefix satisfies the fixed-NAND computation predicate vacuously. -/
theorem public_nand {P U : ℕ} (values : Fin U → Bit) :
    NandOnly (Compilation.publicProgram (P:=P) values) := by
  induction U with
  | zero => trivial
  | succ u ih => exact ⟨ih _,trivial⟩

/-- Counting the compiled syntax gives one protected NAND, two input-port refreshes, and the fixed public-sampler prefix. -/
theorem compile_counts {P U T : ℕ} (program : NandProgram (P+U) T)
    (values : Fin U → Bit) :
    computations (program.compile values).program=T ∧
    refreshes (program.compile values).program=2*T ∧
    samplers (program.compile values).program=U := by
  induction program with
  | nil => simpa [NandProgram.compile,Compilation.initial] using public_counts (P:=P) values
  | @snoc t prior left right ih =>
    rcases ih with ⟨hc,hr,hs⟩
    change computations (prior.compile values).program+1=t+1 ∧
      refreshes (prior.compile values).program+1+1=2*(t+1) ∧
      samplers (prior.compile values).program=U
    omega

/-- The two physical NAND operands are distinct fresh refresh outputs even when the source operands are equal. -/
theorem compile_distinct {P U T : ℕ} (program : NandProgram (P+U) T)
    (values : Fin U → Bit) : (program.compile values).program.DistinctInputs := by
  induction program with
  | nil => exact public_distinct values
  | @snoc t prior left right ih =>
    refine ⟨⟨⟨ih,trivial⟩,trivial⟩,?_⟩
    change (Fin.last (P+(prior.compile values).operations)).castSucc ≠
      Fin.last (P+(prior.compile values).operations+1)
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc,Fin.val_last] at hv
    omega

/-- Every computation in the compiled syntax is NAND; the compiler adds no protected AND selector or encoded control. -/
theorem compile_nand {P U T : ℕ} (program : NandProgram (P+U) T)
    (values : Fin U → Bit) : NandOnly (program.compile values).program := by
  induction program with
  | nil => exact public_nand values
  | snoc prior left right ih => exact ⟨⟨⟨ih,trivial⟩,trivial⟩,rfl⟩

end Compiler.Direct.Physical

namespace Compiler.Direct.Source
variable {P U T k : ℕ} (source : Source P U T k)

/-- The direct compiler executes exactly S = 3T + U operations, including T = 0. -/
theorem operationCount_eq : source.operationCount=3*T+U := by
  have h := source.compilation.count
  unfold operationCount
  omega

/-- Exact resource counts are read from the actual compiled physical instruction syntax. -/
theorem resource_counts :
    Physical.computations source.compiledProgram=T ∧
    Physical.refreshes source.compiledProgram=2*T ∧
    Physical.samplers source.compiledProgram=U ∧ source.operationCount=3*T+U ∧
    source.wireCount=P+source.operationCount := by
  have h := Physical.compile_counts source.program source.publicValues
  exact ⟨h.1,h.2.1,h.2.2,source.operationCount_eq,rfl⟩

/-- The direct compiler calls the local answer functions exactly 8T + 2U times. -/
theorem callbacks_eq : Physical.callbacks source.compiledProgram=8*T+2*U := by
  rw [Physical.callbacks_eq]
  rcases source.resource_counts with ⟨hc,hr,hs,_,_⟩
  rw [hc,hr,hs]
  omega

/-- The actual compiled NAND instructions always receive distinct refreshed encoding locations. -/
theorem compiled_distinct : source.compiledProgram.DistinctInputs := by
  exact Physical.compile_distinct source.program source.publicValues

/-- The main protocol fixes every protected source computation to NAND. -/
theorem compiled_nand : Physical.NandOnly source.compiledProgram := by
  exact Physical.compile_nand source.program source.publicValues

end Compiler.Direct.Source
