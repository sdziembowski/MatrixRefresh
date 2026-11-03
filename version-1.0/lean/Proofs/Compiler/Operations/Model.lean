import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.Construction.Parameters
/-!
# Shared physical computation, refresh, and public sampling

Every instruction allocates one new encoding. A computation reads two earlier encodings and runs the existing matrix refresh and rectangular shortener with all retries. An ordinary refresh reads one old encoding and samples a new square matrix. A public sampler reads no old encoding and initializes its stated public bit by raw-pair rejection. No operation receives unrelated retained encodings.

The common answer type retains four strings. Computation uses its two ordered phases. Refresh and public sampling use one phase: each party returns its two strings together, with both functions selected before either answer is known. The per-party total answer length therefore has the same convention throughout. The direct and stateful NAND compilers share these physical kernels.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace CircuitCompiler.Operations
open Refresh MatrixRefresh TableAnalysis Sampling Sampling.Unbounded
  _root_.CircuitCompiler.Composition _root_.CircuitCompiler.Composition.TopologicalExecution
namespace Instruction
/-- Rename predecessor positions; the public sampling value is unchanged. -/
def mapPorts {F : Type*} {wires wires' : ℕ} (e : Fin wires → Fin wires') :
    Instruction F wires → Instruction F wires'
  | .compute gate => .compute ⟨gate.kind,e gate.left,e gate.right⟩
  | .refresh old => .refresh (e old)
  | .sample value => .sample value
/-- The ordinary plaintext meaning, independent of all leakage. -/
def eval {F : Type*} [Mul F] [Sub F] {wires : ℕ} :
    Instruction F wires → (Fin wires → F) → F
  | .compute gate, values => gate.eval values
  | .refresh old, values => values old
  | .sample value, _ => value
/-- Only these predecessor memory locations may be read by the operation. -/
def inputs {F : Type*} {wires : ℕ} : Instruction F wires → Finset (Fin wires)
  | .compute gate => {gate.left,gate.right}
  | .refresh old => {old}
  | .sample _ => ∅
/-- Computation operands are distinct. The other two instructions have fewer than two predecessor ports, so need no additional restriction. -/
def DistinctInputs {F : Type*} {wires : ℕ} : Instruction F wires → Prop
  | .compute gate => gate.left ≠ gate.right
  | .refresh _ => True
  | .sample _ => True
end Instruction
universe u
namespace Program
variable {F : Type*} {inputs S : ℕ}
/-- Assemble a program from its public chronological instruction array. -/
def ofInstructions : {S : ℕ} → ((i : Fin S) → Instruction F (inputs+i.val)) → Program F inputs S
  | 0, _ => .nil
  | s+1, instructions => (ofInstructions (fun i => instructions i.castSucc)).snoc
      (instructions (Fin.last s))
/-- Evaluate all trusted and newly allocated wire labels. -/
def eval [Mul F] [Sub F] (input : Fin inputs → F) :
    {S : ℕ} → Program F inputs S → Fin (inputs+S) → F
  | 0, .nil => input
  | _+1, .snoc prior instruction => Fin.snoc (prior.eval input)
      (instruction.eval (prior.eval input))
/-- The instruction at a chronological position, with predecessor ports embedded into the final wire array. -/
def instructionAt : {S : ℕ} → Program F inputs S → (i : Fin S) → Instruction F (inputs+i.val)
  | 0, .nil, i => Fin.elim0 i
  | _+1, .snoc prior instruction, i =>
      Fin.lastCases instruction (fun j => prior.instructionAt j) i
/-- The same instruction with its predecessor ports embedded in the complete final wire array, for the signed network's local scopes. -/
def sourceInstruction : {S : ℕ} → Program F inputs S → Fin S → Instruction F (inputs+S)
  | 0, .nil, i => Fin.elim0 i
  | _+1, .snoc prior instruction, i =>
      Fin.lastCases (instruction.mapPorts Fin.castSucc)
        (fun j => (prior.sourceInstruction j).mapPorts Fin.castSucc) i
/-- The ordinary local equation at each operation, including public sampling. -/
def valid [Mul F] [Sub F] (program : Program F inputs S)
    (label : Fin (inputs+S) → F) (i : Fin S) : Prop :=
  label (Fin.natAdd inputs i) = (program.sourceInstruction i).eval label
/-- The operation's full local scope: predecessor ports and its new output. -/
def scope (program : Program F inputs S) (i : Fin S) : Finset (Fin (inputs+S)) :=
  insert (Fin.natAdd inputs i) (program.sourceInstruction i).inputs
/-- Every computation in the chronological program has distinct operands. -/
def DistinctInputs : {S : ℕ} → Program F inputs S → Prop
  | 0, .nil => True
  | _+1, .snoc prior instruction => prior.DistinctInputs ∧ instruction.DistinctInputs
end Program
namespace Protocol
variable {F E A : Type*} [Fintype E] [DecidableEq E] [Fintype A] {inputs S : ℕ}
/-- The actual normalized answer distribution conditioned on the newly allocated pair. An impossible output receives the finite distribution's normalized fallback. -/
def answer (protocol : Protocol F E A inputs) (i : ℕ)
    (instruction : Instruction F (inputs+i)) (history : Fin i → A)
    (old : Fin (inputs+i) → E) (output : E) : FiniteDistribution A :=
  (conditional (protocol.real i instruction history old) Prod.fst output).map Prod.snd
end Protocol
/-- A finite answer renaming preserves its rectangular local masks. -/
def relabelPartition {X G A B : Type*} [Fintype A] [Fintype B]
    (p : TableRectanglePartition X G A) (e : A ≃ B) : TableRectanglePartition X G B where
  left z M x := p.left (e.symm z) M x
  right z M y := p.right (e.symm z) M y
  complete M x y := by
    exact (e.symm.sum_comp (fun z =>
      (if p.left z M x then (1:ℝ) else 0)*(if p.right z M y then (1:ℝ) else 0))).trans
        (p.complete M x y)
variable {F ML MR BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
  {n t inputs : ℕ} {hdim : n*n+1 = n+t}
namespace Strategy
end Strategy
/-- Fixing the independent rejected matrix prefixes leaves finite rectangle partitions, while preserving the exact public sampler and full H retry distribution. -/
structure FixedStrategy (F ML MR BL BR : Type*) [Field F] [Fintype F] [DecidableEq F]
    [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
    (n t inputs : ℕ) (hdim : n*n+1 = n+t) where
  compute : Rectangular.TapedAugmentedStrategy F (ML × MR) BL BR n t inputs hdim
  refresh : (i : ℕ) → Fin (inputs+i) → (Fin i → Answer ML MR BL BR) →
    TableRectanglePartition (U F n) (Refresh.«GL» F n) (Answer ML MR BL BR)
  publicLeft : (i : ℕ) → F → (Fin i → Answer ML MR BL BR) → PublicTape F n → ML × BL
  publicRight : (i : ℕ) → F → (Fin i → Answer ML MR BL BR) → U F n → MR × BR
namespace FixedStrategy
/-- The finite fixed-prefix transition retains actual normalized answers. -/
def protocol (strategy : FixedStrategy F ML MR BL BR n t inputs hdim) (hn : 2 ≤ n) :
    Protocol F (U F n × U F n) (Answer ML MR BL BR) inputs where
  real i instruction history old := match instruction with
    | .compute gate => (strategy.compute.shareProtocol hn).real i gate history (old gate.left) (old gate.right)
    | .refresh port =>
      ((FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F n)).joint
        (RefreshAnalysis.fixedMatrixAnswerDistribution (strategy.refresh i port history)
          (old port).1 (old port).2)).map fun ma =>
            ((rowRefresh (old port).1 ma.1,columnRefresh (old port).2 ma.1),ma.2)
    | .sample value =>
      toFinite ((RawEncoding.tapeDistribution hn value).map fun tape =>
        let output := (RawEncoding.returned hn value tape.2.2).val
        ((output.L,output.R),answerRegroup ML MR BL BR
          (strategy.publicLeft i value history tape,
           strategy.publicRight i value history output.R)))
end FixedStrategy
/-- Two independent prefixes cover computation's long matrix and a control refresh's short matrix. An instruction ignores the prefix it does not use. -/
abbrev Seed (F : Type*) (n t : ℕ) := MatrixPrefix F (n+t) × MatrixPrefix F n
/-- The fixed-prefix strategy uses the unchanged physical shortening and public sampling functions. Only rejected square-matrix prefixes have been externalized. -/
def Strategy.fixedPrefix (strategy : Strategy F ML MR BL BR n t inputs hdim)
    (seed : Seed F n t) : FixedStrategy F ML MR BL BR n t inputs hdim where
  compute := strategy.compute.fixedPrefix seed.1
  refresh i port history := relabelPartition
    (matrixTapePartition (strategy.refreshLeft i port history)
      (strategy.refreshRight i port history) seed.2) (answerRegroup ML MR BL BR)
  publicLeft := strategy.publicLeft
  publicRight := strategy.publicRight
end CircuitCompiler.Operations
