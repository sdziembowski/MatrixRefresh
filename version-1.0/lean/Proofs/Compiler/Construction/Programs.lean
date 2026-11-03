import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.Construction.CompletionSampling
/-!
# Topological circuit execution

Adaptive answer histories, source programs, distinct input ports, fanout, and the generic physical gate runner.

This module is part of the constructive compiler model; it imports no compiler proof theorem. The public source and execution interfaces are in Compiler.Direct and Compiler.Stateful.
-/
set_option backward.isDefEq.respectTransparency false
section
/-!
# Histories

Definitions used by the headline security statements. The construction facts are included in this self-contained model.
-/
/-!
## Composition
-/
section
set_option autoImplicit false
open scoped BigOperators
universe u
namespace CircuitCompiler.Composition
open Refresh
end CircuitCompiler.Composition
end
/-!
## AnswerVectors
-/
section
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Composition
open Refresh
universe u
end CircuitCompiler.Composition
end
/-!
## TopologicalExecution
-/
section
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Composition.TopologicalExecution
open Refresh
universe u v
variable {E : Type u} {A : Type v} [Fintype E] [Fintype A] {inputs T : ℕ}
end CircuitCompiler.Composition.TopologicalExecution
end
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
namespace CircuitCompiler
/-- Evaluate a product gate as s · t and a complement gate as c − s · t. -/
def GateKind.eval {F : Type*} [Mul F] [Sub F] : GateKind F → F → F → F
  | .product, s, t => s * t
  | .complement c, s, t => c - s * t
/-- Evaluate a binary gate on the values stored at its selected predecessor addresses. -/
def Gate.eval {F : Type*} [Mul F] [Sub F] {wires : ℕ}
    (gate : Gate F wires) (values : Fin wires → F) : F :=
  gate.kind.eval (values gate.left) (values gate.right)
universe u
/-- Appending a gate creates a new wire whose references are all earlier. -/

inductive Program (F : Type u) (inputs : ℕ) : ℕ → Type u where
  | nil : Program F inputs 0
  | snoc {T : ℕ} (prior : Program F inputs T) (gate : Gate F (inputs + T)) :
      Program F inputs (T + 1)
namespace Program
variable {F : Type u} [Mul F] [Sub F] {inputs T : ℕ}
/-- Evaluate the source program chronologically, retaining every input and gate-output value. -/
def eval : {T : ℕ} → Program F inputs T → (Fin inputs → F) → Fin (inputs + T) → F
  | 0, .nil, input => input
  | _ + 1, .snoc prior gate, input =>
      let old := prior.eval input
      Fin.snoc old (gate.eval old)
end Program
end CircuitCompiler
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
namespace CircuitCompiler
universe u
namespace Program
variable {F : Type u} [Mul F] [Sub F] {inputs T : ℕ}
@[simp] theorem eval_snoc_old (prior : Program F inputs T) (gate : Gate F (inputs + T))
    (input : Fin inputs → F) (i : Fin (inputs + T)) :
    (prior.snoc gate).eval input i.castSucc = prior.eval input i := by
  simp [eval]
@[simp] theorem eval_snoc_last (prior : Program F inputs T) (gate : Gate F (inputs + T))
    (input : Fin inputs → F) :
    (prior.snoc gate).eval input (Fin.last (inputs + T)) = gate.eval (prior.eval input) := by
  simp [eval]
end Program
end CircuitCompiler
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
namespace CircuitCompiler
universe u
namespace Program
variable {F : Type u} [Mul F] [Sub F] {inputs T : ℕ}
/-- The two operands of each gate are separate physical wires. -/

def DistinctInputs : {T : ℕ} → Program F inputs T → Prop
  | 0, .nil => True
  | _ + 1, .snoc prior gate => prior.DistinctInputs ∧ gate.left ≠ gate.right
/-- Count input-port occurrences of each wire, including two uses in one gate. -/

def uses : {T : ℕ} → Program F inputs T → Fin (inputs + T) → ℕ
  | 0, .nil => fun _ => 0
  | _ + 1, .snoc prior gate => Fin.snoc
      (fun i => prior.uses i + (if gate.left = i then 1 else 0) +
        (if gate.right = i then 1 else 0)) 0
/-- Every source wire is consumed by at most two binary-gate input ports. -/
def FanoutTwo (program : Program F inputs T) : Prop := ∀ w, program.uses w ≤ 2
end Program
end CircuitCompiler
end
section
/-!
# Execution

Definitions used by the headline security statements. The construction facts are included in this self-contained model.
-/
/-!
## ProgramExecution
-/
section
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Composition.TopologicalExecution
open Refresh
universe u v w
variable {F : Type u} {E : Type v} {A : Type w}
  [Mul F] [Sub F] [Fintype E] [Fintype A] {inputs T : ℕ}
/-- Gate leakage may adapt to all earlier answers. A local gate reads its two old operand encodings and allocates one new output encoding. -/

structure GateProtocol (F : Type u) (E : Type v) (A : Type w)
    [Fintype E] [Fintype A] (inputs : ℕ) where
  real : (t : ℕ) → Gate F (inputs + t) → (Fin t → A) → E → E → FiniteDistribution (E × A)
  answer : (t : ℕ) → Gate F (inputs + t) → (Fin t → A) → E → E → E → FiniteDistribution A
namespace GateProtocol
/-- Apply each physical gate kernel to its actual selected operands and preceding answer history. -/
noncomputable def realRunner (protocol : GateProtocol F E A inputs) :
    {T : ℕ} → Program F inputs T → Runner E A inputs T
  | 0, .nil => .nil
  | t + 1, .snoc prior gate => .snoc (protocol.realRunner prior) (fun state =>
      protocol.real t gate state.2 (state.1 gate.left) (state.1 gate.right))
end GateProtocol
end CircuitCompiler.Composition.TopologicalExecution
end
/-!
## ProtocolTransport
-/
section
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Composition.TopologicalExecution
open Refresh
variable {F E D A : Type*} [Fintype E] [Fintype D] [Fintype A] {inputs : ℕ}
namespace GateProtocol
/-- Operate the same actual protocol using another representation of complete wire encodings. Both operands and fresh outputs are transported together. -/

noncomputable def transport (protocol : GateProtocol F E A inputs) (e : E ≃ D) :
    GateProtocol F D A inputs where
  real i gate history left right :=
    (protocol.real i gate history (e.symm left) (e.symm right)).map (fun pair => (e pair.1, pair.2))
  answer i gate history left right output :=
    protocol.answer i gate history (e.symm left) (e.symm right) (e.symm output)
end GateProtocol
end CircuitCompiler.Composition.TopologicalExecution
end
/-!
## PhysicalProgram
-/
section
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler
open Refresh Shortening TableAnalysis Composition Composition.TopologicalExecution
variable {F Alpha Beta : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype Alpha] [Fintype Beta] {n t inputs T : ℕ}
end CircuitCompiler
end
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators
namespace CircuitCompiler.Composition.TopologicalExecution
open Refresh Sampling.Unbounded
noncomputable section
universe u v w
variable {Ω : Type u} {E : Type v} {A : Type w}
  [Countable Ω] [Fintype E] [Fintype A] {inputs T : ℕ}
namespace GateProtocol
variable {F : Type*} [Mul F] [Sub F]
/-- At each actual syntactic gate, draw its independent private seed and then run the corresponding local protocol. The canonical answer interface is averaged in the same way; the execution theorem concerns the real runner. -/

def mixSeeds (seed : ℕ → PMF Ω) (protocol : Ω → GateProtocol F E A inputs) :
    GateProtocol F E A inputs where
  real t gate history left right := countableMixture (seed t)
    (fun ω => (protocol ω).real t gate history left right)
  answer t gate history left right output := countableMixture (seed t)
    (fun ω => (protocol ω).answer t gate history left right output)
end GateProtocol
end
end CircuitCompiler.Composition.TopologicalExecution
end
