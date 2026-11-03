import Proofs.Compiler.GateApproximation.MatrixPhase.GateOccurrence



/-!
# Exact transport between three-port tables and executable gate tables
-/
set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler.Composition.TopologicalExecution

open Refresh TableAnalysis

variable {F X Y A : Type*} [Mul F] [Sub F] [Fintype X] [Fintype Y] [Fintype A]
  {inputs T : ℕ} {protocol : GateProtocol F (X × Y) A inputs} {defaultAnswer : A}
  {program : Program F inputs T} {i : Fin T}

namespace GateOccurrence

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For o ∈ GateOccurrence(protocol, defaultAnswer, program, i); defaultEncoding ∈ X × Y; history ∈ A*; a ∈ A; x ∈ {w | w ∈ program.scope(i)} → X; y ∈ {w | w ∈ program.scope(i)} → Y, we have

protocol.localOriginal(defaultAnswer, defaultEncoding, program, i, history, a, x, y) = protocol.answer(o.time, o.gate, GateProtocol.completeHistory(defaultAnswer, history, o.time), (x((o.left, o.left_mem)), y((o.left, o.left_mem))), (x((o.right, o.right_mem)), y((o.right, o.right_mem))), (x((o.output, o.output_mem)), y((o.output, o.output_mem))))(a).
-/
theorem localOriginal_eq (o : GateOccurrence protocol defaultAnswer program i)
    (defaultEncoding : X × Y) (history : List A) (a : A)
    (x : {w // w ∈ program.scope i} → X) (y : {w // w ∈ program.scope i} → Y) :
    protocol.localOriginal defaultAnswer defaultEncoding program i history a x y =
      (protocol.answer o.time o.gate (GateProtocol.completeHistory defaultAnswer history o.time)
        (x ⟨o.left, o.left_mem⟩, y ⟨o.left, o.left_mem⟩)
        (x ⟨o.right, o.right_mem⟩, y ⟨o.right, o.right_mem⟩)
        (x ⟨o.output, o.output_mem⟩, y ⟨o.output, o.output_mem⟩)).weight a := by
  unfold GateProtocol.localOriginal
  rw [o.answerDistribution_eq]
  change (protocol.answer _ _ _ (joinScope _ _ _ o.left) (joinScope _ _ _ o.right)
    (joinScope _ _ _ o.output)).weight a = _
  rw [joinScope_of_mem _ _ _ o.left o.left_mem, joinScope_of_mem _ _ _ o.right o.right_mem,
    joinScope_of_mem _ _ _ o.output o.output_mem]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For o ∈ GateOccurrence(protocol, defaultAnswer, program, i); defaultEncoding ∈ X × Y; history ∈ A*; a ∈ A; x ∈ (X × X) × X; y ∈ (Y × Y) × Y, assume program.DistinctInputs. Then

protocol.localOriginal(defaultAnswer, defaultEncoding, program, i, history, a, o.portsEquiv(x), o.portsEquiv(y)) = protocol.answer(o.time, o.gate, GateProtocol.completeHistory(defaultAnswer, history, o.time), (((x)₁)₁, ((y)₁)₁), (((x)₁)₂, ((y)₁)₂), ((x)₂, (y)₂))(a).
-/
theorem localOriginal_ports (o : GateOccurrence protocol defaultAnswer program i)
    (hd : program.DistinctInputs) (defaultEncoding : X × Y) (history : List A) (a : A)
    (x : (X × X) × X) (y : (Y × Y) × Y) :
    protocol.localOriginal defaultAnswer defaultEncoding program i history a
      (o.portsEquiv hd x) (o.portsEquiv hd y) =
      (protocol.answer o.time o.gate (GateProtocol.completeHistory defaultAnswer history o.time)
        (x.1.1, y.1.1) (x.1.2, y.1.2) (x.2, y.2)).weight a := by
  rw [o.localOriginal_eq]
  simp only [portsEquiv_apply_left, portsEquiv_apply_right, portsEquiv_apply_output]

/-- Grouping share coordinates and ordering the ports commute exactly. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For o ∈ GateOccurrence(protocol, defaultAnswer, program, i); wireDistribution ∈ {0,…,(inputs + T)-1} → 𝒟((X × Y)), assume program.DistinctInputs. Then

LocalApproximationData.portDistribution(scope = program.scope, wireDistribution, i) = (((triple ↦ (o.portsEquiv((((((triple)₁)₁)₁, (((triple)₁)₂)₁), ((triple)₂)₁)), o.portsEquiv((((((triple)₁)₁)₂, (((triple)₁)₂)₂), ((triple)₂)₂)))))_*((wireDistribution(o.left) ⊗ wireDistribution(o.right)) ⊗ wireDistribution(o.output))).
-/
theorem portDistribution_eq (o : GateOccurrence protocol defaultAnswer program i)
    (hd : program.DistinctInputs) (wireDistribution : Fin (inputs + T) → FiniteDistribution (X × Y)) :
    LocalApproximationData.portDistribution (scope := program.scope) wireDistribution i =
      (((wireDistribution o.left).prod (wireDistribution o.right)).prod (wireDistribution o.output)).map
        (fun triple =>
          (o.portsEquiv hd ((triple.1.1.1, triple.1.2.1), triple.2.1),
           o.portsEquiv hd ((triple.1.1.2, triple.1.2.2), triple.2.2))) := by
  rw [← o.portsEquiv_product_distribution hd wireDistribution, FiniteDistribution.map_map]
  unfold LocalApproximationData.portDistribution
  congr 1
  funext inside
  apply Prod.ext
  · exact (o.portsEquiv hd).apply_symm_apply (fun w => (inside w).1) |>.symm
  · exact (o.portsEquiv hd).apply_symm_apply (fun w => (inside w).2) |>.symm

/-- Expectations of reindexed local tables are the ordered triple expectations used by the physical gate analysis. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For o ∈ GateOccurrence(protocol, defaultAnswer, program, i); wireDistribution ∈ {0,…,(inputs + T)-1} → 𝒟((X × Y)); f ∈ (({w | w ∈ program.scope(i)} → X) × ({w | w ∈ program.scope(i)} → Y)) → ℝ, assume program.DistinctInputs. Then

𝔼_(u ← LocalApproximationData.portDistribution(scope = program.scope, wireDistribution, i)) [f(u)] = 𝔼_(triple ← ((wireDistribution(o.left) ⊗ wireDistribution(o.right)) ⊗ wireDistribution(o.output))) [f((o.portsEquiv((((((triple)₁)₁)₁, (((triple)₁)₂)₁), ((triple)₂)₁)), o.portsEquiv((((((triple)₁)₁)₂, (((triple)₁)₂)₂), ((triple)₂)₂))))].
-/
theorem portDistribution_expect (o : GateOccurrence protocol defaultAnswer program i)
    (hd : program.DistinctInputs) (wireDistribution : Fin (inputs + T) → FiniteDistribution (X × Y))
    (f : (({w // w ∈ program.scope i} → X) × ({w // w ∈ program.scope i} → Y)) → ℝ) :
    (LocalApproximationData.portDistribution (scope := program.scope) wireDistribution i).expect f =
      (((wireDistribution o.left).prod (wireDistribution o.right)).prod (wireDistribution o.output)).expect
        (fun triple => f
          (o.portsEquiv hd ((triple.1.1.1, triple.1.2.1), triple.2.1),
           o.portsEquiv hd ((triple.1.1.2, triple.1.2.2), triple.2.2))) := by
  rw [o.portDistribution_eq hd, MatrixRefresh.expect_map]

end GateOccurrence

end CircuitCompiler.Composition.TopologicalExecution
