import Proofs.Compiler.GateApproximation.MatrixPhase.Disintegration



/-!
# Continuing a conditioned execution after erasing its random tape
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace CircuitCompiler

open Refresh

variable {Ω Y Z V : Type*} [Fintype Ω] [Fintype Y] [Fintype Z] [Fintype V]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(Ω); f ∈ Ω → Y; Q ∈ Y → 𝒟(V), we have

bind((f_*P), Q) = bind(P, ((ω ↦ Q(f(ω))))).
-/
theorem bind_after_map (P : FiniteDistribution Ω) (f : Ω → Y) (Q : Y → FiniteDistribution V) :
    (P.map f).bind Q = P.bind (fun ω => Q (f ω)) := by
  simp [FiniteDistribution.map, FiniteDistribution.bind_assoc]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(Ω); Q ∈ Ω → 𝒟(Z); R ∈ Ω → Z → 𝒟(V), we have

bind(P.joint(Q), ((pair ↦ R((pair)₁, (pair)₂)))) = bind(P, ((ω ↦ bind(Q(ω), R(ω))))).
-/
theorem bind_after_joint (P : FiniteDistribution Ω) (Q : Ω → FiniteDistribution Z)
    (R : Ω → Z → FiniteDistribution V) :
    (P.joint Q).bind (fun pair => R pair.1 pair.2) =
      P.bind (fun ω => (Q ω).bind (R ω)) := by
  ext v
  simp only [FiniteDistribution.bind, FiniteDistribution.joint, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- After erasure, the continuation may depend on the produced value and leakage answer. Conditioning preserves that complete continued execution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(Ω); value ∈ Ω → Y; answer ∈ Ω → 𝒟(Z); next ∈ Y → Z → 𝒟(V), we have

bind(P, ((ω ↦ bind(answer(ω), next(value(ω)))))) = bind((value_*P), ((y ↦ bind(bind(conditional(P, value, y), answer), next(y))))).
-/
theorem conditional_execution [DecidableEq Y] (P : FiniteDistribution Ω) (value : Ω → Y)
    (answer : Ω → FiniteDistribution Z) (next : Y → Z → FiniteDistribution V) :
    P.bind (fun ω => (answer ω).bind (next (value ω))) =
      (P.map value).bind (fun y =>
        ((conditional P value y).bind answer).bind (next y)) := by
  have h := congrArg (fun Q : FiniteDistribution (Y × Z) => Q.bind (fun yz => next yz.1 yz.2))
    (answer_joint_conditional P value answer)
  try dsimp only at h
  rw [bind_after_joint] at h
  rw [bind_after_map] at h
  rw [bind_after_map] at h
  change (P.bind (fun ω => ((conditional P value (value ω)).bind answer).bind
      (next (value ω)))) =
    (P.joint answer).bind (fun pair => next (value pair.1) pair.2) at h
  rw [bind_after_joint P answer (fun ω z => next (value ω) z)] at h
  rw [bind_after_map]
  exact h.symm

end CircuitCompiler
