import Proofs.Compiler.Model
import Proofs.Compiler.LocalComparisons.Framework.SupportedExecution

/-!
# Exact lazy canonical execution for online public inputs

The fresh encoding of each output is sampled using the bit determined by the incoming answer prefix. Supported physical prefixes decode to these induced labels. This gives an exact distribution identity, including the leakage answers, without assuming independence after observing a history.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open scoped BigOperators Classical

namespace Compiler.Adaptive
open Refresh MatrixRefresh CircuitCompiler CircuitCompiler.Operations
  CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution
  CircuitCompiler.AveragedEnergyComparison

variable {F E A : Type*} [Mul F] [Sub F] [Fintype E] [DecidableEq E] [Fintype A]
  {P S : ℕ}

/-- Dropping the final answer from a vector is exactly taking the earlier list prefix. -/
theorem ofFn_init (z : Fin (S+1) → A) :
    List.ofFn (Fin.init z) = (List.ofFn z).take S := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_take]
    rfl

/-- Completing the actual incoming history of the last operation recovers its original answer vector. -/
theorem complete_last (defaultAnswer : A) (z : Fin (S+1) → A) :
    GateProtocol.completeHistory defaultAnswer ((List.ofFn z).take S) S = Fin.init z := by
  rw [← ofFn_init]
  funext i
  unfold GateProtocol.completeHistory
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp

/-- The lazy plan uses the induced label's encoding distribution on every wire along the fixed formal transcript. -/
theorem canonical_wireLaws (protocol : Operations.Protocol F E A P)
    (law : F → FiniteDistribution E) (input : Fin P → F)
    (program : Operations.Program F P S) (values : SampleValues F A S) (z : Fin S → A) :
    (canonicalPlan protocol law input program values).wireLaws (fun i => law (input i)) z =
      fun w => law (evaluate input program values z w) := by
  induction program with
  | nil => rfl
  | snoc prior instruction ih =>
    funext w
    refine Fin.lastCases ?_ (fun j => ?_) w
    · simp [canonicalPlan, Plan.wireLaws, evaluate]
    · simp [canonicalPlan, Plan.wireLaws, evaluate, ih]

/-- The plan's conditional factors are the actual physical answer tables evaluated at the preceding formal prefix. -/
theorem canonical_factors (protocol : Operations.Protocol F E A P) (defaultAnswer : A)
    (law : F → FiniteDistribution E) (input : Fin P → F)
    (program : Operations.Program F P S) (values : SampleValues F A S)
    (e : Fin (P+S) → E) (z : Fin S → A) (i : Fin S) :
    (canonicalPlan protocol law input program values).factors e z i =
      (operationAnswer protocol defaultAnswer program values i
        ((List.ofFn z).take i.val) e).weight (z i) := by
  induction program with
  | nil => exact Fin.elim0 i
  | @snoc S prior instruction ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [canonicalPlan, Plan.factors, Fin.snoc_last, operationAnswer,
        Fin.lastCases_last, Fin.val_last, complete_last]
    · simp only [canonicalPlan, Plan.factors, Fin.snoc_castSucc, operationAnswer,
        Fin.lastCases_castSucc, Fin.val_castSucc]
      have ht : (List.ofFn (Fin.init z)).take j.val = (List.ofFn z).take j.val := by
        rw [ofFn_init, List.take_take]
        simp [Nat.min_eq_left (Nat.le_of_lt j.isLt)]
      rw [← ht]
      exact ih (fun i => values i.castSucc) (Fin.init e) (Fin.init z) j

/-- The actual online program has a causal realization in the signed-composition model. This certificate contains the concrete lazy sampler, not a security premise. -/
def canonicalRealization (protocol : Operations.Protocol F E A P) (hlocal : protocol.Local)
    (defaultAnswer : A) (law : F → FiniteDistribution E) (input : Fin P → F)
    (program : Operations.Program F P S) (values : SampleValues F A S) :
    Realization (probabilities protocol hlocal defaultAnswer program values) law
      (evaluate input program values) where
  inputs := P
  addresses := Equiv.refl _
  initial i := law (input i)
  plan := canonicalPlan protocol law input program values
  wire_laws z j := congrFun (canonical_wireLaws protocol law input program values z) j
  answer_factors e z i := canonical_factors protocol defaultAnswer law input program values e z i

/-- Nonzero canonical mass forces every retained wire to decode to the label induced by that same complete history. -/
theorem canonical_support (protocol : Operations.Protocol F E A P)
    (decode : E → F) (law : F → FiniteDistribution E)
    (hsupport : ∀ s, (law s).Supports (fun e => decode e = s))
    (input : Fin P → F) (program : Operations.Program F P S) (values : SampleValues F A S) :
    ((canonicalPlan protocol law input program values).runner.execute
      (independentDistribution (fun i => law (input i)))).Supports
      (fun state => ∀ w, decode (state.1 w) = evaluate input program values state.2 w) := by
  intro state hstate w
  have hm : (independentDistribution
      (fun w => law (evaluate input program values state.2 w))).weight state.1 ≠ 0 := by
    intro hz
    rw [Plan.execute_weight, canonical_wireLaws, hz, zero_mul] at hstate
    exact hstate rfl
  have hw : (law (evaluate input program values state.2 w)).weight (state.1 w) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp (show
      (∏ j, (law (evaluate input program values state.2 j)).weight (state.1 j)) ≠ 0 from hm))
        w (Finset.mem_univ _)
  exact hsupport _ _ hw

/-- Exact output freshness at each physical instruction gives equality with the causal canonical runner, even when public inputs are chosen online. -/
theorem real_eq_canonical (protocol : Operations.Protocol F E A P)
    (decode : E → F) (law : F → FiniteDistribution E)
    (hsupport : ∀ s, (law s).Supports (fun e => decode e = s))
    (hgate : ∀ i instruction history old,
      statisticalDistance (protocol.real i instruction history old)
        ((law (instruction.eval (fun w => decode (old w)))).joint
          (protocol.answer i instruction history old)) ≤ 0)
    (input : Fin P → F) (program : Operations.Program F P S) (values : SampleValues F A S) :
    (realRunner protocol program values).execute (independentDistribution (fun i => law (input i))) =
      (canonicalPlan protocol law input program values).runner.execute
        (independentDistribution (fun i => law (input i))) := by
  have hc : (realRunner protocol program values).CoupledOn
      (independentDistribution (fun i => law (input i))) 0
      (canonicalPlan protocol law input program values).runner := by
    induction program with
    | nil => trivial
    | @snoc S prior instruction ih =>
      refine ⟨ih (fun i => values i.castSucc), ?_⟩
      intro state hstate
      have hv := canonical_support protocol decode law hsupport input prior
        (fun i => values i.castSucc) state hstate
      have he : (fun w => decode (state.1 w)) =
          evaluate input prior (fun i => values i.castSucc) state.2 := funext hv
      simpa only [realRunner, canonicalPlan, Plan.runner, he] using
        hgate S (selectInstruction instruction (values (Fin.last _) state.2)) state.2 state.1
  apply CompilerProof.Canonical.eq_of_distance_nonpos
  simpa only [mul_zero] using Runner.execute_distance_on_support _ _ _ 0 hc

end Compiler.Adaptive
