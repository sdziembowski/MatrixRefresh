import Proofs.Compiler.LocalComparisons.Framework.ProgramExecution
import Proofs.Compiler.GateApproximation.Shortening.RectangularPhysicalStochastic
import Proofs.EfficientSimulaiton.Sampling.SamplerPMFCost
import Proofs.Compiler.Construction.Parameters



/-!
# Actual adaptive executions with accumulated work

Each transition returns its real output and a natural-number cost from the same probability distribution. Forgetting cost gives the ordinary runner. The expectation calculation is in extended nonnegative reals, so a divergent run has infinite expected work and cannot satisfy the polynomial bound.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

open scoped BigOperators ENNReal

namespace CircuitCompiler.Composition.TopologicalExecution

open Refresh Sampling.Unbounded

noncomputable section

universe u v

variable {E : Type u} {A : Type v} [Fintype E] [Fintype A] {inputs T : ℕ}

namespace CostedRunner

/-- Erasure forgets the cost of each actual transition; its output distribution is computed from that same transition PMF rather than supplied separately. -/
/- Mathematical definition (normal notation): Forget the work counter in each actual counted transition, retaining its exact output-state marginal. This produces the corresponding ordinary runner. -/
def erase : {T : ℕ} → CostedRunner E A inputs T → Runner E A inputs T
  | 0,.nil => .nil
  | _+1,.snoc prior gate => .snoc prior.erase
      (fun state => toFinite ((gate state).map Prod.fst))

/-- Keeping costs never changes the actual chronological output distribution. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For initial ∈ PMF((({0,…,inputs-1} → E) × ℕ)); runner ∈ CostedRunner(E, A, inputs, T), we have

((Prod)₁_*runner.execute(initial)) = toPMF(runner.erase.execute(toFinite(((Prod)₁_*initial)))) .
-/
theorem execute_erase (initial : PMF ((Fin inputs → E) × ℕ))
    (runner : CostedRunner E A inputs T) :
    (runner.execute initial).map Prod.fst =
      toPMF (runner.erase.execute (toFinite (initial.map Prod.fst))) := by
  induction runner with
  | nil =>
      simp only [execute,erase,Runner.execute,toPMF_map,toPMF_toFinite,PMF.map_comp]
      rfl
  | @snoc T prior gate ih =>
      simp only [execute,erase,Runner.execute_snoc,toPMF_bind,toPMF_map,toPMF_toFinite]
      rw [PMF.map_bind,← ih]
      simp only [PMF.bind_map,PMF.map_comp,Function.comp_def,appendEquiv,Equiv.coe_fn_mk]

/-- A uniform conditional bound permits arbitrary dependence on the prior encodings and answers; it does not assume independent running times. -/
/- Mathematical definition (normal notation): For every gate and every prior state, the conditional expected work of the next transition is at most C. The condition is imposed at all stages and does not require independent running times. -/
def Bounded (C : ℝ≥0∞) : {T : ℕ} → CostedRunner E A inputs T → Prop
  | 0,.nil => True
  | _+1,.snoc prior gate => prior.Bounded C ∧
      ∀ state, workExpectation (gate state) (fun result => (result.2 : ℝ≥0∞)) ≤ C

/-- Expected total work adds over actual adaptive transitions. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For initial ∈ PMF((({0,…,inputs-1} → E) × ℕ)); runner ∈ CostedRunner(E, A, inputs, T); C ∈ ℝ ≥ 0∞, assume runner.Bounded(C). Then

workExpectation(runner.execute(initial), ((result ↦ (result)₂))) ≤ workExpectation(initial, ((result ↦ (result)₂))) + T · C.
-/
theorem execute_work_le (initial : PMF ((Fin inputs → E) × ℕ))
    (runner : CostedRunner E A inputs T) (C : ℝ≥0∞) (h : runner.Bounded C) :
    workExpectation (runner.execute initial) (fun result => (result.2 : ℝ≥0∞)) ≤
      workExpectation initial (fun result => (result.2 : ℝ≥0∞)) + (T : ℝ≥0∞)*C := by
  induction runner with
  | nil => simp [execute,workExpectation_map]
  | @snoc T prior gate ih =>
      rcases h with ⟨hprior,hgate⟩
      have hstep :
          workExpectation ((prior.snoc gate).execute initial)
            (fun result => (result.2 : ℝ≥0∞)) ≤
          workExpectation (prior.execute initial) (fun result => (result.2 : ℝ≥0∞)) + C := by
        simp only [execute,workExpectation_bind,workExpectation_map,Nat.cast_add]
        simp_rw [workExpectation_add,workExpectation_const]
        exact add_le_add (le_refl _) ((workExpectation_mono (prior.execute initial)
          (fun before => hgate before.1)).trans_eq (workExpectation_const _ C))
      calc
        _ ≤ _ := hstep
        _ ≤ (workExpectation initial (fun result => (result.2 : ℝ≥0∞)) + (T:ℝ≥0∞)*C)+C :=
          add_le_add (ih hprior) (le_refl C)
        _ = _ := by simp only [Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_assoc]

/-- Any finite per-gate and initial expected-cost bounds give a finite total expectation. This is an expected-work statement about the actual PMF. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For initial ∈ PMF((({0,…,inputs-1} → E) × ℕ)); runner ∈ CostedRunner(E, A, inputs, T); C ∈ ℝ ≥ 0∞, assume runner.Bounded(C); workExpectation(initial, ((result ↦ (result)₂))) ≠ ⊤; C ≠ ⊤. Then

workExpectation(runner.execute(initial), ((result ↦ (result)₂))) ≠ ⊤.
-/
theorem execute_work_ne_top (initial : PMF ((Fin inputs → E) × ℕ))
    (runner : CostedRunner E A inputs T) (C : ℝ≥0∞) (h : runner.Bounded C)
    (hinitial : workExpectation initial (fun result => (result.2 : ℝ≥0∞)) ≠ ⊤)
    (hC : C ≠ ⊤) :
    workExpectation (runner.execute initial) (fun result => (result.2 : ℝ≥0∞)) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (execute_work_le initial runner C h)
  exact ENNReal.add_ne_top.mpr ⟨hinitial,ENNReal.mul_ne_top (by simp) hC⟩

end CostedRunner

namespace GateProtocol

variable {F : Type*} [Mul F] [Sub F]

/-- Local marginal identities lift structurally to the full actual runner; no whole-execution equality is assumed. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For protocol ∈ GateProtocol(F, E, A, inputs); implementation ∈ ∏_(t ∈ ℕ) Gate(F, (inputs + t)) → ({0,…,t-1} → A) → E → E → PMF(((E × A) × ℕ)); program ∈ Program(F, inputs, T), assume ∀ t, gate, history, left, right, toFinite(((Prod)₁_*implementation(t, gate, history, left, right))) = protocol.real(t, gate, history, left, right). Then

erase(costedRunner(implementation, program)) = protocol.realRunner(program).
-/
theorem costedRunner_erase
    (protocol : GateProtocol F E A inputs)
    (implementation : (t : ℕ) → Gate F (inputs+t) → (Fin t → A) → E → E → PMF ((E×A)×ℕ))
    (hmarginal : ∀ t gate history left right,
      toFinite ((implementation t gate history left right).map Prod.fst) =
        protocol.real t gate history left right)
    (program : Program F inputs T) :
    (costedRunner implementation program).erase = protocol.realRunner program := by
  induction program with
  | nil => rfl
  | snoc prior gate ih =>
      simp only [costedRunner,CostedRunner.erase,realRunner,ih,hmarginal]

/-- Uniform actual local expected work bounds lift to the stated program. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For implementation ∈ ∏_(t ∈ ℕ) Gate(F, (inputs + t)) → ({0,…,t-1} → A) → E → E → PMF(((E × A) × ℕ)); C ∈ ℝ ≥ 0∞; program ∈ Program(F, inputs, T), assume ∀ t, gate, history, left, right, workExpectation(implementation(t, gate, history, left, right), ((result ↦ (result)₂))) ≤ C. Then

Bounded(costedRunner(implementation, program))(C).
-/
theorem costedRunner_bounded
    (implementation : (t : ℕ) → Gate F (inputs+t) → (Fin t → A) → E → E → PMF ((E×A)×ℕ))
    (C : ℝ≥0∞)
    (hwork : ∀ t gate history left right,
      workExpectation (implementation t gate history left right) (fun result => (result.2 : ℝ≥0∞)) ≤ C)
    (program : Program F inputs T) :
    (costedRunner implementation program).Bounded C := by
  induction program with
  | nil => trivial
  | snoc prior gate ih => exact ⟨ih,fun state => hwork _ _ _ _ _⟩

/-- Exact implementation refinement for the output of the whole compiled program, retaining whatever work the concrete implementation performed. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For protocol ∈ GateProtocol(F, E, A, inputs); implementation ∈ ∏_(t ∈ ℕ) Gate(F, (inputs + t)) → ({0,…,t-1} → A) → E → E → PMF(((E × A) × ℕ)); program ∈ Program(F, inputs, T); initial ∈ PMF((({0,…,inputs-1} → E) × ℕ)), assume ∀ t, gate, history, left, right, toFinite(((Prod)₁_*implementation(t, gate, history, left, right))) = protocol.real(t, gate, history, left, right). Then

((Prod)₁_*execute(costedRunner(implementation, program))(initial)) = toPMF(execute(protocol.realRunner(program))(toFinite(((Prod)₁_*initial)))) .
-/
theorem costedRunner_execute_marginal
    (protocol : GateProtocol F E A inputs)
    (implementation : (t : ℕ) → Gate F (inputs+t) → (Fin t → A) → E → E → PMF ((E×A)×ℕ))
    (hmarginal : ∀ t gate history left right,
      toFinite ((implementation t gate history left right).map Prod.fst) =
        protocol.real t gate history left right)
    (program : Program F inputs T) (initial : PMF ((Fin inputs → E)×ℕ)) :
    ((costedRunner implementation program).execute initial).map Prod.fst =
      toPMF ((protocol.realRunner program).execute (toFinite (initial.map Prod.fst))) := by
  rw [CostedRunner.execute_erase,costedRunner_erase protocol implementation hmarginal]

end GateProtocol

end

end CircuitCompiler.Composition.TopologicalExecution
