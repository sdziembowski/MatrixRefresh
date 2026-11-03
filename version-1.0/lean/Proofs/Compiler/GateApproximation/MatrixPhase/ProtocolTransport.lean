import Proofs.Compiler.LocalComparisons.Framework.ProgramExecution
import Proofs.Compiler.Construction.Parameters



/-!
# Changing the representation of each complete wire encoding
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler.Composition.TopologicalExecution

open Refresh

variable {F E D A : Type*} [Fintype E] [Fintype D] [Fintype A] {inputs : ℕ}

/-- Transport the fresh encoding of a joint gate distribution along an equivalence. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(E); answer ∈ E → 𝒟(A); e ∈ E ≃ D, we have

(((pair ↦ (e((pair)₁), (pair)₂)))_*P.joint(answer)) = joint((e_*P))(((output ↦ answer((e)⁻¹(output))))) .
-/
theorem map_joint_encoding (P : FiniteDistribution E) (answer : E → FiniteDistribution A) (e : E ≃ D) :
    (P.joint answer).map (fun pair => (e pair.1, pair.2)) =
      (P.map e).joint (fun output => answer (e.symm output)) := by
  ext pair
  change ((P.joint answer).map (Equiv.prodCongr e (Equiv.refl A))).weight pair = _
  rw [map_equiv_weight]
  change P.weight (e.symm pair.1) * (answer (e.symm pair.1)).weight pair.2 =
    (P.map e).weight pair.1 * (answer (e.symm pair.1)).weight pair.2
  rw [map_equiv_weight]

namespace GateProtocol

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For protocol ∈ GateProtocol(F, E, A, inputs); e ∈ E ≃ D; decode ∈ E → F; wireDistribution ∈ F → 𝒟(E); τ ∈ ℝ; t ∈ ℕ; gate ∈ Gate(F, (inputs + t)); history ∈ {0,…,t-1} → A, assume Mul(F); Sub(F); ∀ t, gate, history, left, right, δ(protocol.real(t, gate, history, left, right), joint(wireDistribution(gate.kind.eval(decode(left), decode(right))))(protocol.answer(t, gate, history, left, right))) ≤ τ; D. Then

δ(real(protocol.transport(e))(t, gate, history), joint((e_*wireDistribution(gate.kind.eval(decode((e)⁻¹), decode((e)⁻¹)))))(answer(protocol.transport(e))(t, gate, history))) ≤ τ.
-/
theorem transport_local_coupling [Mul F] [Sub F]
    (protocol : GateProtocol F E A inputs) (e : E ≃ D)
    (decode : E → F) (wireDistribution : F → FiniteDistribution E) (τ : ℝ)
    (hgate : ∀ t gate history left right,
      statisticalDistance (protocol.real t gate history left right)
        ((wireDistribution (gate.kind.eval (decode left) (decode right))).joint
          (protocol.answer t gate history left right)) ≤ τ)
    (t : ℕ) (gate : Gate F (inputs + t)) (history : Fin t → A) (left right : D) :
    statisticalDistance ((protocol.transport e).real t gate history left right)
      (((wireDistribution (gate.kind.eval (decode (e.symm left)) (decode (e.symm right)))).map e).joint
        ((protocol.transport e).answer t gate history left right)) ≤ τ := by
  have h := (statisticalDistance_map_le
    (protocol.real t gate history (e.symm left) (e.symm right))
    ((wireDistribution (gate.kind.eval (decode (e.symm left)) (decode (e.symm right)))).joint
      (protocol.answer t gate history (e.symm left) (e.symm right)))
    (fun pair => (e pair.1, pair.2))).trans
      (hgate t gate history (e.symm left) (e.symm right))
  rw [map_joint_encoding] at h
  exact h

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): Suppose an encoding distribution for value s is supported on encodings decoding to s. After transporting encodings through a bijection e, the resulting distribution is supported on encodings whose inverse images under e decode to s. -/
theorem transport_encoding_support
    (decode : E → F) (wireDistribution : F → FiniteDistribution E) (e : E ≃ D)
    (hsupport : ∀ value, (wireDistribution value).Supports (fun encoding => decode encoding = value))
    (value : F) :
    ((wireDistribution value).map e).Supports (fun encoding => decode (e.symm encoding) = value) := by
  refine FiniteDistribution.map_supports (wireDistribution value) e _ _ (hsupport value) ?_
  intro encoding h
  simpa only [Equiv.symm_apply_apply] using h

end GateProtocol

end CircuitCompiler.Composition.TopologicalExecution
