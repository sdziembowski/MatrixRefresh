import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.Operations.Model
import Proofs.Compiler.LocalComparisons.Framework.TopologicalExecution
import Proofs.Compiler.DirectComposition.Model
import Proofs.Compiler.Operations.Execution
import Proofs.Compiler.Construction.Parameters
/-!
# Causal sampling constructions and their certificates

The forward sampling plans, canonical realizations, and online instruction kernels are defined in EfficientSimulation. This module proves their normalization and locality properties.
-/
section AdaptiveCanonical
/-!
## Sequential canonical sampling

An operation samples its new wire from a law selected by the preceding answers, and then samples its answer conditional on that wire. This is the lazy canonical experiment in Sec. 5.4.1. The density below keeps the wire laws indexed by the complete formal transcript; it does not move history-dependent samples before their labels have been chosen.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
namespace Compiler.Adaptive
open Refresh CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution
universe u v
namespace Plan
variable {E A : Type*} [Fintype E] [Fintype A] {P S : ℕ}
/-- The product of all conditional answer factors, with the labels fixed only along this formal transcript. -/
def historyWeight (plan : Plan E A P S) (e : Fin (P+S) → E) (z : Fin S → A) : ℝ :=
  ∏ i, plan.factors e z i
/-- Lazy sampling has the manuscript's joint density: multiply the transcript-dependent independent encoding weights by the conditional answer product. -/
theorem execute_weight (initial : Fin P → FiniteDistribution E)
    (plan : Plan E A P S) (state : RunState E A P S) :
    (plan.runner.execute (independentDistribution initial)).weight state =
      (independentDistribution (plan.wireLaws initial state.2)).weight state.1 *
        plan.historyWeight state.1 state.2 := by
  induction plan with
  | nil =>
    let e : (Fin P → E) ≃ RunState E A P 0 :=
      { toFun := fun encoding => (encoding, Fin.elim0)
        invFun := Prod.fst
        left_inv := fun _ => rfl
        right_inv := by intro pair; ext i <;> first | rfl | exact Fin.elim0 i }
    change ((independentDistribution initial).map e).weight state = _
    rw [map_equiv_weight]
    simp [e, wireLaws, historyWeight, factors]
  | @snoc S prior output answer ih =>
    change (((prior.runner.execute (independentDistribution initial)).joint
      (fun st => (output st.2).joint (answer st))).map appendEquiv).weight state = _
    rw [map_equiv_weight]
    simp only [appendEquiv, Equiv.coe_fn_symm_mk, splitState, FiniteDistribution.joint]
    rw [ih (Fin.init state.1, Fin.init state.2)]
    have hprod := Fin.prod_univ_castSucc (fun w : Fin (P+S+1) =>
      (Fin.snoc (α := fun _ => FiniteDistribution E)
        (prior.wireLaws initial (Fin.init state.2)) (output (Fin.init state.2)) w).weight
        (state.1 w))
    simp only [Fin.snoc_castSucc, Fin.snoc_last] at hprod
    simp only [wireLaws, historyWeight, factors, independentDistribution,
      Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    have hprod' :
        (∏ x, (Fin.snoc (α := fun _ => FiniteDistribution E)
          (prior.wireLaws initial (Fin.init state.2)) (output (Fin.init state.2)) x).weight
            (state.1 x)) =
        (∏ w, (prior.wireLaws initial (Fin.init state.2) w).weight (Fin.init state.1 w)) *
          (output (Fin.init state.2)).weight (state.1 (Fin.last (P+S))) := hprod
    calc
      _ = ((∏ w, (prior.wireLaws initial (Fin.init state.2) w).weight (Fin.init state.1 w)) *
          (output (Fin.init state.2)).weight (state.1 (Fin.last (P+S)))) *
          ((∏ i, prior.factors (Fin.init state.1) (Fin.init state.2) i) *
            (answer (Fin.init state.1,Fin.init state.2) (state.1 (Fin.last (P+S)))).weight
              (state.2 (Fin.last S))) := by ring
      _ = _ := congrArg (fun mass => mass *
        ((∏ i, prior.factors (Fin.init state.1) (Fin.init state.2) i) *
          (answer (Fin.init state.1,Fin.init state.2) (state.1 (Fin.last (P+S)))).weight
            (state.2 (Fin.last S)))) hprod'.symm
/-- Summing both the answers and their history-dependent encoding weights gives total mass one. -/
theorem total (initial : Fin P → FiniteDistribution E) (plan : Plan E A P S) :
    (∑ z : Fin S → A, ∑ e : Fin (P+S) → E,
      (independentDistribution (plan.wireLaws initial z)).weight e *
        plan.historyWeight e z) = 1 := by
  have hp (z : Fin S → A) (e : Fin (P+S) → E) :
      (independentDistribution (plan.wireLaws initial z)).weight e *
        plan.historyWeight e z =
      (plan.runner.execute (independentDistribution initial)).weight (e,z) :=
    (execute_weight initial plan (e,z)).symm
  simp_rw [hp]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type]
  exact FiniteDistribution.total _
variable [Nonempty A]
/-- Replace selected answers by independent uniform answers, preserving every causal encoding law and every remaining answer kernel. -/
def mask : {S : ℕ} → Plan E A P S → (Fin S → Bool) → Plan E A P S
  | 0, .nil, _ => .nil
  | _+1, .snoc prior output answer, selected =>
      .snoc (prior.mask (fun i => selected i.castSucc)) output
        (if selected (Fin.last _) then fun _ _ => FiniteDistribution.uniform else answer)
/-- Uniformizing answers does not change the wire law prescribed along any particular formal transcript. -/
theorem mask_wireLaws (plan : Plan E A P S) (selected : Fin S → Bool)
    (initial : Fin P → FiniteDistribution E) (z : Fin S → A) :
    (plan.mask selected).wireLaws initial z = plan.wireLaws initial z := by
  induction plan with
  | nil => rfl
  | snoc prior output answer ih =>
    simp only [mask, wireLaws, ih]
/-- Each selected factor becomes 1/K, and every unselected factor retains its original conditional probability. -/
theorem mask_factors (plan : Plan E A P S) (selected : Fin S → Bool)
    (e : Fin (P+S) → E) (z : Fin S → A) (i : Fin S) :
    (plan.mask selected).factors e z i =
      if selected i then (Fintype.card A : ℝ)⁻¹ else plan.factors e z i := by
  induction plan with
  | nil => exact Fin.elim0 i
  | snoc prior output answer ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · cases h : selected (Fin.last _) <;>
        simp [mask, factors, h, FiniteDistribution.uniform]
    · simpa only [mask, factors, Fin.snoc_castSucc] using
        ih (fun j => selected j.castSucc) (Fin.init e) (Fin.init z) j
/-- Deleting selected true answer factors costs exactly K per selected answer, even when all later encoding laws depend on earlier answers. This is the joint reverse-time normalization in the marked-term argument of Sec. 5.4. -/
theorem erased_mass (initial : Fin P → FiniteDistribution E)
    (plan : Plan E A P S) (selected : Fin S → Bool) :
    (∑ z : Fin S → A,
      (independentDistribution (plan.wireLaws initial z)).expect
        (fun e => ∏ i, if selected i then 1 else plan.factors e z i)) =
      ∏ i, if selected i then (Fintype.card A : ℝ) else 1 := by
  let C : ℝ := ∏ i, if selected i then (Fintype.card A : ℝ) else 1
  have hK : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hp (e : Fin (P+S) → E) (z : Fin S → A) :
      (∏ i, if selected i then 1 else plan.factors e z i) =
        C * (plan.mask selected).historyWeight e z := by
    simp only [C, historyWeight, ← Finset.prod_mul_distrib, mask_factors]
    apply Finset.prod_congr rfl
    intro i hi
    cases selected i <;> simp [hK]
  simp_rw [hp, FiniteDistribution.expect]
  simp_rw [mul_left_comm _ C, ← Finset.mul_sum]
  have ht := (plan.mask selected).total initial
  simp_rw [mask_wireLaws] at ht
  rw [ht, mul_one]
end Plan
end Compiler.Adaptive
end
end AdaptiveCanonical
section AdaptiveModel
/-!
## Causal labelings and canonical realizations

A labeling is indexed by the complete formal transcript, as in the induced labeling of Sec. 5.4.1. Causality is witnessed by a forward sampling plan: each wire law is selected before its producing operation returns an answer. The witness records exact sampling and factor identities, with no privacy or marked-term estimate as a hypothesis.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
namespace Compiler.Adaptive
open Refresh CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution
  CircuitCompiler.AveragedEnergyComparison CompilerProof.DirectComposition
variable {W E A F : Type*} [Fintype W] [DecidableEq W] [Fintype E] [Fintype A]
  {S : ℕ} {scope : Fin S → Finset W}
/-- The independent encoding expectation along a fixed formal transcript. Its labels may depend on the prefixes before their wires are produced, but the expectation is not a conditional law given that transcript. -/
def canonicalWeight (network : ScopedProbabilities (E := E) (A := A) scope)
    (law : F → FiniteDistribution E) (label : (Fin S → A) → W → F)
    (z : Fin S → A) : ℝ :=
  (independentDistribution (fun w => law (label z w))).expect
    (fun e => ∏ i, network.prob i ((List.ofFn z).take i.val) e (z i))
/-- Rename the indices of an encoding assignment bijectively. -/
def assignments {I J D : Type*} (e : I ≃ J) : (I → D) ≃ (J → D) where
  toFun f j := f (e.symm j)
  invFun f i := f (e i)
  left_inv f := by
    funext i
    simp
  right_inv f := by
    funext j
    simp
/-- Renaming wire locations preserves the expectation under their independent encoding laws. -/
theorem reindex_expect {I J D : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype D] (e : I ≃ J)
    (laws : J → FiniteDistribution D) (f : (J → D) → ℝ) :
    (independentDistribution (fun i => laws (e i))).expect
      (fun x => f (fun j => x (e.symm j))) =
      (independentDistribution laws).expect f := by
  unfold FiniteDistribution.expect independentDistribution
  rw [← Equiv.sum_comp (assignments (D := D) e).symm]
  simp only [assignments, Equiv.coe_fn_symm_mk, Equiv.apply_symm_apply]
  apply Finset.sum_congr rfl
  intro x hx
  exact congrArg (fun mass => mass * f x)
    (Equiv.prod_comp e (fun j => (laws j).weight (x j)))
namespace Realization
variable {network : ScopedProbabilities (E := E) (A := A) scope}
  {law : F → FiniteDistribution E} {label : (Fin S → A) → W → F}
/-- The forward sampler has exactly the history-dependent canonical transcript weight. -/
theorem transcript_weight (r : Realization network law label) (z : Fin S → A) :
    r.transcript.weight z = canonicalWeight network law label z := by
  rw [transcript, MatrixRefresh.map_snd_weight]
  simp_rw [r.plan.execute_weight r.initial]
  change (independentDistribution (r.plan.wireLaws r.initial z)).expect
    (fun e => r.plan.historyWeight e z) = _
  simp only [Plan.historyWeight, r.answer_factors]
  have hl : r.plan.wireLaws r.initial z = fun j => law (label z (r.addresses j)) :=
    funext (r.wire_laws z)
  rw [hl]
  exact reindex_expect r.addresses (fun w => law (label z w))
    (fun e => ∏ i, network.prob i ((List.ofFn z).take i.val) e (z i))
/-- After guard factors are deleted, summing both the causal encoding weights and all answers costs exactly K per guard. This replaces the fixed-encoding normalization used for nonadaptive labels. -/
theorem erased_mass [Nonempty A] (r : Realization network law label)
    (guards : Finset (Fin S)) :
    (∑ z : Fin S → A,
      (independentDistribution (fun w => law (label z w))).expect
        (fun e => ∏ i, if i ∈ guards then 1 else
          network.prob i ((List.ofFn z).take i.val) e (z i))) =
      (Fintype.card A : ℝ)^guards.card := by
  have h := r.plan.erased_mass r.initial (fun i => decide (i ∈ guards))
  have hp (z : Fin S → A) :
      (independentDistribution (r.plan.wireLaws r.initial z)).expect
        (fun e => ∏ i, if decide (i ∈ guards) then 1 else r.plan.factors e z i) =
      (independentDistribution (fun w => law (label z w))).expect
        (fun e => ∏ i, if i ∈ guards then 1 else
          network.prob i ((List.ofFn z).take i.val) e (z i)) := by
    simp only [r.answer_factors, decide_eq_true_eq]
    have hl : r.plan.wireLaws r.initial z = fun j => law (label z (r.addresses j)) :=
      funext (r.wire_laws z)
    rw [hl]
    exact reindex_expect r.addresses (fun w => law (label z w))
      (fun e => ∏ i, if i ∈ guards then 1 else
        network.prob i ((List.ofFn z).take i.val) e (z i))
  simp_rw [hp] at h
  simpa only [decide_eq_true_eq, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const_one, mul_one, Finset.prod_const] using h
end Realization
end Compiler.Adaptive
end
end AdaptiveModel
section AdaptiveProgram
/-!
## Programs with online public inputs

The chronological template fixes every operation and predecessor address. Only the plaintext value requested by a public sampler depends on the earlier answer vector. Refresh and NAND operations use exactly the same physical kernels as the single-evaluation compiler. Thus choosing public inputs online changes neither the scope graph nor the permitted local views.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
namespace Compiler.Adaptive
open Refresh CircuitCompiler CircuitCompiler.Operations
  CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution
  CircuitCompiler.AveragedEnergyComparison
variable {F E A : Type*} {P S : ℕ}
/-- Extract the exact incoming answer vector at one operation from a complete formal transcript. -/
def incomingVector (z : Fin S → A) (i : Fin S) : Fin i.val → A :=
  fun j => z (Fin.castLE (Nat.le_of_lt i.isLt) j)
/-- Online selection leaves the operation's active predecessor set unchanged. -/
@[simp] theorem selectInstruction_inputs {wires : ℕ}
    (instruction : Instruction F wires) (value : F) :
    (selectInstruction instruction value).inputs = instruction.inputs := by
  cases instruction <;> rfl
/-- Plaintext evaluation along a formal transcript, using each public value when its sampler is reached. The initial private values are fixed before any answer. -/
def evaluate [Mul F] [Sub F] (input : Fin P → F) :
    {S : ℕ} → Operations.Program F P S → SampleValues F A S →
      (Fin S → A) → Fin (P+S) → F
  | 0, .nil, _, _ => input
  | _+1, .snoc prior instruction, values, z =>
      let old := evaluate input prior (fun i => values i.castSucc) (Fin.init z)
      Fin.snoc old ((selectInstruction instruction (values (Fin.last _) (Fin.init z))).eval old)
/-- Freeze the public sampler values along a single formal history for ordinary plaintext reasoning. This operation is used only in the correctness proof, not to sample future online inputs early. -/
def specialize : {S : ℕ} → Operations.Program F P S → (Fin S → F) → Operations.Program F P S
  | 0, .nil, _ => .nil
  | _+1, .snoc prior instruction, values =>
      (specialize prior (Fin.init values)).snoc (selectInstruction instruction (values (Fin.last _)))
variable [Fintype E] [DecidableEq E] [Fintype A]
/-- The lazy canonical counterpart of that same physical execution. Only the fresh output law uses the induced plaintext labels. -/
def canonicalPlan [Mul F] [Sub F] (protocol : Operations.Protocol F E A P)
    (law : F → FiniteDistribution E) (input : Fin P → F) :
    {S : ℕ} → Operations.Program F P S → SampleValues F A S → Plan E A P S
  | 0, .nil, _ => .nil
  | _+1, .snoc prior instruction, values =>
      .snoc (canonicalPlan protocol law input prior (fun i => values i.castSucc))
        (fun h => law ((selectInstruction instruction (values (Fin.last _) h)).eval
          (evaluate input prior (fun i => values i.castSucc) h)))
        (fun state output => protocol.answer _
          (selectInstruction instruction (values (Fin.last _) state.2)) state.2 state.1 output)
/-- The complete conditional answer distribution at every operation and formal incoming history. Wrong-length histories are completed only to make the model total. -/
def operationAnswer (protocol : Operations.Protocol F E A P) (defaultAnswer : A) :
    {S : ℕ} → Operations.Program F P S → SampleValues F A S →
      Fin S → List A → (Fin (P+S) → E) → FiniteDistribution A
  | 0, .nil, _, i, _, _ => Fin.elim0 i
  | s+1, .snoc prior instruction, values, i, history, encoding => Fin.lastCases
      (let h := GateProtocol.completeHistory defaultAnswer history s
       protocol.answer s (selectInstruction instruction (values (Fin.last _) h))
         h (Fin.init encoding) (encoding (Fin.last _)))
      (fun j => operationAnswer protocol defaultAnswer prior (fun i => values i.castSucc)
        j history (Fin.init encoding)) i
/-- Changing the online public value preserves the physical locality of the complete conditional answer distribution. -/
theorem operationAnswer_scoped (protocol : Operations.Protocol F E A P) (hlocal : protocol.Local)
    (defaultAnswer : A) (program : Operations.Program F P S) (values : SampleValues F A S)
    (i : Fin S) (history : List A) (a : A) :
    Scoped (program.scope i) (fun e => (operationAnswer protocol defaultAnswer program values i history e).weight a) := by
  induction program with
  | nil => exact Fin.elim0 i
  | @snoc S prior instruction ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Operations.Program.scope_snoc_last]
      intro first second heq
      have ho := heq (Fin.last (P+S)) (by simp)
      have hi : ∀ w ∈ (selectInstruction instruction
          (values (Fin.last _) (GateProtocol.completeHistory defaultAnswer history S))).inputs,
          (Fin.init first) w = (Fin.init second) w := by
        intro w hw
        rw [selectInstruction_inputs] at hw
        exact heq w.castSucc (Finset.mem_insert_of_mem (Finset.mem_map_of_mem Fin.castSuccEmb hw))
      simp only [operationAnswer, Fin.lastCases_last, Operations.Protocol.answer]
      rw [hlocal S _ _ _ _ hi]
      exact congrArg (fun output => ((conditional (protocol.real S
        (selectInstruction instruction (values (Fin.last _) (GateProtocol.completeHistory defaultAnswer history S)))
        (GateProtocol.completeHistory defaultAnswer history S) (Fin.init second)) Prod.fst output).map
          Prod.snd).weight a) ho
    · rw [Operations.Program.scope_snoc_old]
      intro first second heq
      simp only [operationAnswer, Fin.lastCases_castSucc]
      apply ih (fun i => values i.castSucc) j
      intro w hw
      exact heq w.castSucc (Finset.mem_map_of_mem Fin.castSuccEmb hw)
/-- Actual online public sampling, refresh, and computation give a scoped normalized probability network on the original fixed port graph. -/
def probabilities (protocol : Operations.Protocol F E A P) (hlocal : protocol.Local)
    (defaultAnswer : A) (program : Operations.Program F P S) (values : SampleValues F A S) :
    ScopedProbabilities (E := E) (A := A) program.scope where
  prob i h e a := (operationAnswer protocol defaultAnswer program values i h e).weight a
  nonneg _ _ _ _ := FiniteDistribution.nonneg _ _
  total_le _ _ _ := (FiniteDistribution.total _).le
  locality := operationAnswer_scoped protocol hlocal defaultAnswer program values
end Compiler.Adaptive
end
end AdaptiveProgram
