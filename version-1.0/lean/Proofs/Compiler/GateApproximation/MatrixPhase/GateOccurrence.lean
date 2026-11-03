import Proofs.Compiler.LocalComparisons.Framework.ProgramNetwork
import Proofs.Compiler.GateApproximation.MatrixPhase.TriplePorts



/-!
# Each circuit gate is an ordered occurrence of three physical ports
-/
set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler.Composition.TopologicalExecution

open Refresh

variable {F E A : Type*} [Mul F] [Sub F] [Fintype E] [Fintype A] {inputs T : ℕ}

/-- An occurrence records the original syntactic gate and its three ports inside the final wire set. The identities connect chronological execution, local validity, and the scope used in the signed-network proof. -/
/- Mathematical definition (normal notation): A descriptor of one actual program gate records its time, operation, and embedding of its earlier-wire context into the final wire set. It certifies that the three-port scope, gate-validity equation, and conditional answer distribution agree with the program-level definitions, and inherits distinct operands when assumed. -/
structure GateOccurrence (protocol : GateProtocol F E A inputs) (defaultAnswer : A)
    (program : Program F inputs T) (i : Fin T) where
  time : ℕ
  gate : Gate F (inputs + time)
  embedding : Fin (inputs + time + 1) ↪ Fin (inputs + T)
  scope_eq : program.scope i =
    {embedding gate.left.castSucc, embedding gate.right.castSucc, embedding (Fin.last (inputs + time))}
  valid_eq : ∀ label, program.gateValid label i ↔
    label (embedding (Fin.last (inputs + time))) =
      gate.kind.eval (label (embedding gate.left.castSucc)) (label (embedding gate.right.castSucc))
  answerDistribution_eq : ∀ history encoding,
    protocol.gateAnswerDistribution defaultAnswer program i history encoding =
      protocol.answer time gate (GateProtocol.completeHistory defaultAnswer history time)
        (encoding (embedding gate.left.castSucc)) (encoding (embedding gate.right.castSucc))
        (encoding (embedding (Fin.last (inputs + time))))
  distinct : program.DistinctInputs → gate.left ≠ gate.right

namespace GateProtocol

/-- This descriptor is constructed from the actual syntax, so the three-port reindexing introduces no abstract circuit-incidence assumptions. -/
/- Mathematical definition (normal notation): For gate i in a topological program, extract its earlier-wire context, operation, and embedding into the full wire set. The descriptor identifies its three-wire scope, validity equation, and conditional answer distribution with the corresponding program-level objects. Distinct inputs are inherited from the program's distinct-input assumption. -/
noncomputable def occurrence (protocol : GateProtocol F E A inputs) (defaultAnswer : A) :
    {T : ℕ} → (program : Program F inputs T) → (i : Fin T) →
      GateOccurrence protocol defaultAnswer program i
  | 0, .nil, i => Fin.elim0 i
  | t + 1, .snoc prior gate, i => Fin.lastCases
      { time := t
        gate := gate
        embedding := Function.Embedding.refl _
        scope_eq := by rw [Program.scope_last]; rfl
        valid_eq := by intro label; simp only [Program.gateValid, Fin.lastCases_last]; rfl
        answerDistribution_eq := by intro history encoding; simp only [gateAnswerDistribution, Fin.lastCases_last]; rfl
        distinct := fun h => h.2 }
      (fun j =>
        let old := protocol.occurrence defaultAnswer prior j
        { time := old.time
          gate := old.gate
          embedding := old.embedding.trans Fin.castSuccEmb
          scope_eq := by
            rw [Program.scope_old, old.scope_eq]
            simp only [Finset.map_insert, Finset.map_singleton]
            rfl
          valid_eq := by
            intro label
            simpa only [Program.gateValid, Fin.lastCases_castSucc, Function.Embedding.trans_apply,
              Fin.coe_castSuccEmb, Fin.init] using old.valid_eq (Fin.init label)
          answerDistribution_eq := by
            intro history encoding
            simpa only [gateAnswerDistribution, Fin.lastCases_castSucc,
              Function.Embedding.trans_apply, Fin.coe_castSuccEmb, Fin.init] using
              old.answerDistribution_eq history (Fin.init encoding)
          distinct := fun h => old.distinct h.1 }) i

end GateProtocol

namespace GateOccurrence

variable {protocol : GateProtocol F E A inputs} {defaultAnswer : A}
  {program : Program F inputs T} {i : Fin T}

/-
Mathematical definition (normal notation): For o ∈ GateOccurrence(protocol, defaultAnswer, program, i), define

left(o) := o.embedding(o.gate.left.castSucc).
-/
def left (o : GateOccurrence protocol defaultAnswer program i) := o.embedding o.gate.left.castSucc

/-
Mathematical definition (normal notation): For o ∈ GateOccurrence(protocol, defaultAnswer, program, i), define

right(o) := o.embedding(o.gate.right.castSucc).
-/
def right (o : GateOccurrence protocol defaultAnswer program i) := o.embedding o.gate.right.castSucc

/-
Mathematical definition (normal notation): For o ∈ GateOccurrence(protocol, defaultAnswer, program, i), define

output(o) := o.embedding(Fin.last((inputs + o.time))).
-/
def output (o : GateOccurrence protocol defaultAnswer program i) := o.embedding (Fin.last (inputs + o.time))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For o ∈ GateOccurrence(protocol, defaultAnswer, program, i), assume program.DistinctInputs. Then

o.left ≠ o.right.
-/
theorem left_ne_right (o : GateOccurrence protocol defaultAnswer program i)
    (hd : program.DistinctInputs) : o.left ≠ o.right := by
  intro h
  exact o.distinct hd (Fin.castSucc_injective _ (o.embedding.injective h))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For o ∈ GateOccurrence(protocol, defaultAnswer, program, i), we have

o.left ≠ o.output.
-/
theorem left_ne_output (o : GateOccurrence protocol defaultAnswer program i) : o.left ≠ o.output := by
  intro h
  exact Fin.castSucc_ne_last _ (o.embedding.injective h)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For o ∈ GateOccurrence(protocol, defaultAnswer, program, i), we have

o.right ≠ o.output.
-/
theorem right_ne_output (o : GateOccurrence protocol defaultAnswer program i) : o.right ≠ o.output := by
  intro h
  exact Fin.castSucc_ne_last _ (o.embedding.injective h)

/-- The exact ordered triple equivalence for each gate of a distinct-input program, including gates embedded under arbitrarily many later gates. -/
/- Mathematical definition (normal notation): For a gate with three distinct ports, identify an ordered triple (x_L,x_R,x_O) with its assignment of values to the gate's scoped wire set. The map follows the gate's actual embedding into the complete program. -/
noncomputable def portsEquiv {X : Type*}
    (o : GateOccurrence protocol defaultAnswer program i) (hd : program.DistinctInputs) :
    ((X × X) × X) ≃ ({w // w ∈ program.scope i} → X) :=
  (tripleScopeEquiv o.left o.right o.output (o.left_ne_right hd) o.left_ne_output o.right_ne_output).trans
    (Equiv.piCongrLeft' (fun _ => X) (Equiv.subtypeEquivRight (fun w => by rw [o.scope_eq]; rfl)))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For o ∈ GateOccurrence(protocol, defaultAnswer, program, i), we have

o.left ∈ program.scope(i).
-/
theorem left_mem (o : GateOccurrence protocol defaultAnswer program i) : o.left ∈ program.scope i := by
  rw [o.scope_eq]; exact Finset.mem_insert_self _ _

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For o ∈ GateOccurrence(protocol, defaultAnswer, program, i), we have

o.right ∈ program.scope(i).
-/
theorem right_mem (o : GateOccurrence protocol defaultAnswer program i) : o.right ∈ program.scope i := by
  rw [o.scope_eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For o ∈ GateOccurrence(protocol, defaultAnswer, program, i), we have

o.output ∈ program.scope(i).
-/
theorem output_mem (o : GateOccurrence protocol defaultAnswer program i) : o.output ∈ program.scope i := by
  rw [o.scope_eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X a set; o ∈ GateOccurrence(protocol, defaultAnswer, program, i); value ∈ {w | w ∈ program.scope(i)} → X, assume program.DistinctInputs. Then

(o.portsEquiv)⁻¹(value) = ((value((o.left, o.left_mem)), value((o.right, o.right_mem))), value((o.output, o.output_mem))).
-/
theorem portsEquiv_symm {X : Type*}
    (o : GateOccurrence protocol defaultAnswer program i) (hd : program.DistinctInputs)
    (value : {w // w ∈ program.scope i} → X) :
    (o.portsEquiv hd).symm value =
      ((value ⟨o.left, o.left_mem⟩, value ⟨o.right, o.right_mem⟩), value ⟨o.output, o.output_mem⟩) :=
  rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X a set; o ∈ GateOccurrence(protocol, defaultAnswer, program, i); value ∈ (X × X) × X, assume program.DistinctInputs. Then

o.portsEquiv(value, (o.left, o.left_mem)) = ((value)₁)₁.
-/
theorem portsEquiv_apply_left {X : Type*}
    (o : GateOccurrence protocol defaultAnswer program i) (hd : program.DistinctInputs)
    (value : (X × X) × X) : (o.portsEquiv hd value) ⟨o.left, o.left_mem⟩ = value.1.1 := by
  simp [portsEquiv, tripleScopeEquiv]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X a set; o ∈ GateOccurrence(protocol, defaultAnswer, program, i); value ∈ (X × X) × X, assume program.DistinctInputs. Then

o.portsEquiv(value, (o.right, o.right_mem)) = ((value)₁)₂.
-/
theorem portsEquiv_apply_right {X : Type*}
    (o : GateOccurrence protocol defaultAnswer program i) (hd : program.DistinctInputs)
    (value : (X × X) × X) : (o.portsEquiv hd value) ⟨o.right, o.right_mem⟩ = value.1.2 := by
  simp [portsEquiv, tripleScopeEquiv, Ne.symm (o.left_ne_right hd)]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X a set; o ∈ GateOccurrence(protocol, defaultAnswer, program, i); value ∈ (X × X) × X, assume program.DistinctInputs. Then

o.portsEquiv(value, (o.output, o.output_mem)) = (value)₂.
-/
theorem portsEquiv_apply_output {X : Type*}
    (o : GateOccurrence protocol defaultAnswer program i) (hd : program.DistinctInputs)
    (value : (X × X) × X) : (o.portsEquiv hd value) ⟨o.output, o.output_mem⟩ = value.2 := by
  simp [portsEquiv, tripleScopeEquiv, Ne.symm o.left_ne_output, Ne.symm o.right_ne_output]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X a set; o ∈ GateOccurrence(protocol, defaultAnswer, program, i); wireDistribution ∈ {0,…,(inputs + T)-1} → 𝒟(X), assume X is finite; program.DistinctInputs. Then

((o.portsEquiv)⁻¹_*independentDistribution(((w ∈ {w | w ∈ program.scope(i)} ↦ wireDistribution(w))))) = ((wireDistribution(o.left) ⊗ wireDistribution(o.right)) ⊗ wireDistribution(o.output)).
-/
theorem portsEquiv_product_distribution {X : Type*} [Fintype X]
    (o : GateOccurrence protocol defaultAnswer program i) (hd : program.DistinctInputs)
    (wireDistribution : Fin (inputs + T) → FiniteDistribution X) :
    (independentDistribution (fun w : {w // w ∈ program.scope i} => wireDistribution w)).map (o.portsEquiv hd).symm =
      ((wireDistribution o.left).prod (wireDistribution o.right)).prod (wireDistribution o.output) := by
  let e : Fin 3 ≃ {w // w ∈ program.scope i} :=
    (threePortEquiv o.left o.right o.output (o.left_ne_right hd) o.left_ne_output o.right_ne_output).trans
      (Equiv.subtypeEquivRight (fun w => by rw [o.scope_eq]; rfl))
  ext value
  rw [map_equiv_weight]
  change (∏ w : {w // w ∈ program.scope i}, (wireDistribution w).weight (o.portsEquiv hd value w)) =
    ((wireDistribution o.left).weight value.1.1 * (wireDistribution o.right).weight value.1.2) *
      (wireDistribution o.output).weight value.2
  rw [← Equiv.prod_comp e]
  simp only [Fin.prod_univ_three]
  change (wireDistribution o.left).weight (o.portsEquiv hd value ⟨o.left, o.left_mem⟩) *
      (wireDistribution o.right).weight (o.portsEquiv hd value ⟨o.right, o.right_mem⟩) *
      (wireDistribution o.output).weight (o.portsEquiv hd value ⟨o.output, o.output_mem⟩) = _
  rw [portsEquiv_apply_left, portsEquiv_apply_right, portsEquiv_apply_output]

end GateOccurrence

end CircuitCompiler.Composition.TopologicalExecution
