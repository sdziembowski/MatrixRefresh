import Proofs.Compiler.GateApproximation.MatrixPhase.GateLabelError
import Proofs.Compiler.LocalComparisons.Framework.OccurrenceTables
import Proofs.Compiler.GateApproximation.MatrixPhase.PhysicalShares
import Proofs.Compiler.Foundations.LinearAlgebra.FiniteCarrier



/-!
# Exact passage from ordered rectangular-gate tables to circuit scopes

This is only a change of coordinates and an exchange of finite sums. In particular it does not assume a local approximation, gate correctness, or a security theorem. It permits the proved accepted-gate error bound to be used on `GateProtocol.localOriginal` once its answer distribution is identified on valid ports.
-/
set_option autoImplicit false

set_option maxHeartbeats 1500000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.Rectangular

open Refresh MatrixRefresh TableAnalysis Composition Composition.TopologicalExecution

noncomputable section

variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype A]

variable {n inputs T : ℕ}

/-- Ordered side tables and the actual original scope table have exactly the same summed absolute error under the corresponding wire distributions. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For protocol ∈ GateProtocol(F, (U(F, n) × U(F, n)), A, inputs); defaultAnswer ∈ A; defaultEncoding ∈ U(F, n) × U(F, n); program ∈ Program(F, inputs, T); i ∈ {0,…,T-1}; o ∈ GateOccurrence(protocol, defaultAnswer, program, i); history ∈ A*; label ∈ {0,…,(inputs + T)-1} → F; G ∈ A → ℝ^(GateSide(F, n, n) × GateSide(F, n, n)), assume program.DistinctInputs; 2 ≤ n. Then

(∑_z (𝔼_(xy ← LocalApproximationData.portDistribution(scope = program.scope, ((w ↦ encodingDistribution(label(w)))), i)) [|protocol.localOriginal(defaultAnswer, defaultEncoding, program, i, history, z, (xy)₁, (xy)₂) - reindexTable(G(z), o.portsEquiv, o.portsEquiv, (xy)₁, (xy)₂)|])) = 𝔼_(op ← (oldLabelDistribution(label(o.left), label(o.right)) ⊗ μ_(label(o.output)))) [∑_z (|protocol.answer(o.time, o.gate, GateProtocol.completeHistory(defaultAnswer, history, o.time), ((((op)₁)₁)₁, (((op)₁)₂)₁), ((((op)₁)₁)₂, (((op)₁)₂)₂), (op.2.L, op.2.R))(z) - G(z, (((op)₁)₁, op.2.L), (((op)₁)₂, op.2.R))|)].
-/
theorem scope_error_eq_port_error
    (protocol : GateProtocol F (U F n × U F n) A inputs)
    (defaultAnswer : A) (defaultEncoding : U F n × U F n)
    (program : Program F inputs T) (hd : program.DistinctInputs) (i : Fin T)
    (o : GateOccurrence protocol defaultAnswer program i)
    (history : List A) (hn : 2 ≤ n) (label : Fin (inputs+T) → F)
    (G : A → Matrix (GateSide F n n) (GateSide F n n) ℝ) :
    (∑ z, (LocalApproximationData.portDistribution (scope := program.scope)
      (fun w => encodingDistribution hn (label w)) i).expect (fun xy =>
        |protocol.localOriginal defaultAnswer defaultEncoding program i history z xy.1 xy.2 -
          reindexTable (G z) (o.portsEquiv hd) (o.portsEquiv hd) xy.1 xy.2|)) =
    ((oldLabelDistribution hn (label o.left) (label o.right)).prod
      (mu F n hn (label o.output))).expect (fun op => ∑ z,
        |(protocol.answer o.time o.gate (GateProtocol.completeHistory defaultAnswer history o.time)
          (op.1.1.1,op.1.2.1) (op.1.1.2,op.1.2.2) (op.2.L,op.2.R)).weight z -
            G z (op.1.1,op.2.L) (op.1.2,op.2.R)|) := by
  have hencoding (s : F) :
      encodingDistribution hn s = (mu F n hn s).map (stateEquivProd F n) := rfl
  simp_rw [o.portDistribution_expect hd, hencoding, expect_prod, expect_map]
  simp only [oldLabelDistribution, expect_prod, expect_map]
  simp_rw [expect_sum]
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg (mu F n hn (label o.left)).expect
  funext left
  apply congrArg (mu F n hn (label o.right)).expect
  funext right
  apply congrArg (mu F n hn (label o.output)).expect
  funext output
  rw [o.localOriginal_ports hd]
  simp only [reindexTable, Equiv.symm_apply_apply]
  rfl

end

end CircuitCompiler.Rectangular
