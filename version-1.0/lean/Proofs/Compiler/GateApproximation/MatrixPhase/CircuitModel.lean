import Proofs.Compiler.Construction.Parameters



/-!
# Topologically ordered circuits over the stated gate basis

The syntax permits only references to inputs and earlier gate outputs. Evaluation is an ordinary terminating program. Valid complete wire labels, input-port occurrence counts, and the distinct-input condition are defined separately, so fanout is never confused with resampling an encoding.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1200000

namespace CircuitCompiler

universe u

namespace Program

variable {F : Type u} [Mul F] [Sub F] {inputs T : ℕ}

/-- Every gate equation is satisfied by this complete assignment of wire labels. -/
/- Mathematical definition (normal notation): A complete wire labeling is valid exactly when every gate-output label equals its gate operation applied to its two input labels. -/
def Valid : {T : ℕ} → Program F inputs T → (Fin (inputs + T) → F) → Prop
  | 0, .nil, _ => True
  | t + 1, .snoc prior gate, values =>
      prior.Valid (Fin.init values) ∧ values (Fin.last (inputs + t)) = gate.eval (Fin.init values)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For program ∈ Program(F, inputs, T); input ∈ {0,…,inputs-1} → F, we have

program.Valid(program.eval(input)) .
-/
theorem eval_valid (program : Program F inputs T) (input : Fin inputs → F) :
    program.Valid (program.eval input) := by
  induction program with
  | nil => trivial
  | snoc prior gate ih => simpa [Valid, eval] using ih

/-- Computing a gate never changes the labels of earlier wires. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For prior ∈ Program(F, inputs, T); gate ∈ Gate(F, (inputs + T)); input ∈ {0,…,inputs-1} → F, we have

Fin.init(eval(prior.snoc(gate))(input)) = prior.eval(input).
-/
theorem eval_prior (prior : Program F inputs T) (gate : Gate F (inputs + T))
    (input : Fin inputs → F) :
    Fin.init ((prior.snoc gate).eval input) = prior.eval input := by
  simp [eval]

end Program

/- Mathematical definition (normal notation): A circuit consists of a topologically ordered program together with an ordered list of designated output-wire indices. -/
structure Circuit (F : Type*) (inputs gates outputs : ℕ) where
  program : Program F inputs gates
  output : Fin outputs → Fin (inputs + gates)

/- Mathematical definition (normal notation): Evaluate the program on its input, then return the values at the designated output-wire indices in their specified order. -/
def Circuit.eval {F : Type*} [Mul F] [Sub F] {inputs gates outputs : ℕ}
    (circuit : Circuit F inputs gates outputs) (input : Fin inputs → F) : Fin outputs → F :=
  fun i => circuit.program.eval input (circuit.output i)

end CircuitCompiler
