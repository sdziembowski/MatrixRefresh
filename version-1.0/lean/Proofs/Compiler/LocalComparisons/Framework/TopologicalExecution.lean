import Proofs.Compiler.LocalComparisons.Framework.NetworkModes
import Proofs.Compiler.Construction.Parameters



/-!
# Topological execution with fresh wire allocation

The runner retains every earlier wire encoding and answer. A gate receives exactly that prefix and returns its new output encoding and full answer.
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler.Composition.TopologicalExecution

open Refresh

universe u v

variable {E : Type u} {A : Type v} [Fintype E] [Fintype A] {inputs T : ℕ}

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): Sampling X ∼ P, then Y from the transition distribution given X, and observing f(X,Y) gives the same distribution whether the joint pair is formed first or the observation is applied inside the conditional sampling. -/
theorem joint_map_eq_bind {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (P : FiniteDistribution X) (transition : X → FiniteDistribution Y) (observe : X × Y → Z) :
    (P.joint transition).map observe = P.bind (fun x => (transition x).map (fun y => observe (x, y))) := by
  ext z
  simp only [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.joint, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For initial ∈ 𝒟(({0,…,inputs-1} → E)); prior ∈ Runner(E, A, inputs, T); gate ∈ RunState(E, A, inputs, T) → 𝒟((E × A)), we have

execute(prior.snoc(gate))(initial) = bind(prior.execute(initial), ((state ↦ (((pair ↦ appendEquiv((state, pair))))_*gate(state))))) .
-/
theorem Runner.execute_snoc (initial : FiniteDistribution (Fin inputs → E))
    (prior : Runner E A inputs T) (gate : RunState E A inputs T → FiniteDistribution (E × A)) :
    (prior.snoc gate).execute initial = (prior.execute initial).bind
      (fun state => (gate state).map (fun pair => appendEquiv (state, pair))) :=
  joint_map_eq_bind _ _ _

/-- Local gate couplings include both the fresh output encoding and every answer; retaining the prefix and appending data preserves the coupling. -/
/- Mathematical definition (normal notation): At every gate and every prior state, the two corresponding transition distributions on fresh encoding-answer pairs have statistical distance at most ε. The condition holds recursively for all earlier gates. -/
def Runner.Coupled (error : ℝ) : {T : ℕ} → Runner E A inputs T → Runner E A inputs T → Prop
  | 0, .nil, .nil => True
  | _ + 1, .snoc real realGate, .snoc canonical canonicalGate =>
      real.Coupled error canonical ∧
        ∀ state, statisticalDistance (realGate state) (canonicalGate state) ≤ error

/-- The actual complete execution is at distance at most `T·τ` from its canonical execution, including every still-live encoding and all answers. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For initial ∈ 𝒟(({0,…,inputs-1} → E)); real, canonical ∈ Runner(E, A, inputs, T); error ∈ ℝ, assume real.Coupled(error, canonical). Then

δ(real.execute(initial), canonical.execute(initial)) ≤ T · error.
-/
theorem Runner.execute_distance (initial : FiniteDistribution (Fin inputs → E))
    (real canonical : Runner E A inputs T) (error : ℝ) (h : real.Coupled error canonical) :
    statisticalDistance (real.execute initial) (canonical.execute initial) ≤ (T : ℝ) * error := by
  induction real with
  | nil => cases canonical; simp [Runner.execute]
  | @snoc T real realGate ih =>
      cases canonical with
      | snoc canonical canonicalGate =>
          rcases h with ⟨hprior, hgate⟩
          rw [Runner.execute_snoc, Runner.execute_snoc]
          have hstep (state : RunState E A inputs T) :
              statisticalDistance
                ((realGate state).map (fun pair => appendEquiv (state, pair)))
                ((canonicalGate state).map (fun pair => appendEquiv (state, pair))) ≤ error :=
            (statisticalDistance_map_le _ _ _).trans (hgate state)
          have hbound := statisticalDistance_transition_le
            (real.execute initial) (canonical.execute initial) _ _ error hstep
          have hprev := ih canonical hprior
          push_cast
          nlinarith

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; initial ∈ 𝒟(({0,…,inputs-1} → E)); real, canonical ∈ Runner(E, A, inputs, T); error ∈ ℝ; observe ∈ RunState(E, A, inputs, T) → V, assume V is finite; real.Coupled(error, canonical). Then

δ((observe_*real.execute(initial)), (observe_*canonical.execute(initial))) ≤ T · error.
-/
theorem Runner.execute_observed_distance {V : Type*} [Fintype V]
    (initial : FiniteDistribution (Fin inputs → E))
    (real canonical : Runner E A inputs T) (error : ℝ) (h : real.Coupled error canonical)
    (observe : RunState E A inputs T → V) :
    statisticalDistance ((real.execute initial).map observe) ((canonical.execute initial).map observe) ≤
      (T : ℝ) * error :=
  (statisticalDistance_map_le _ _ _).trans (real.execute_distance initial canonical error h)

/-- Canonical gates sample their new wire independently, then sample from the conditional answer distribution for that exact output and all preceding data. -/
/- Mathematical definition (normal notation): A canonical plan specifies an independent fresh-encoding distribution for each new wire and a conditional answer distribution depending on that fresh encoding and the complete previous state. -/
inductive Canonical (E : Type u) (A : Type v) [Fintype E] [Fintype A] (inputs : ℕ) : ℕ → Type (max u v) where
  | nil : Canonical E A inputs 0
  | snoc {T : ℕ} (prior : Canonical E A inputs T) (outputDistribution : FiniteDistribution E)
      (answer : RunState E A inputs T → E → FiniteDistribution A) : Canonical E A inputs (T + 1)

/- Mathematical definition (normal notation): Execute a canonical plan by first sampling each new wire independently from its specified distribution, then sampling its answer conditioned on the old state and that exact new encoding. -/
noncomputable def Canonical.runner : {T : ℕ} → Canonical E A inputs T → Runner E A inputs T
  | 0, .nil => .nil
  | _ + 1, .snoc prior outputDistribution answer =>
      .snoc prior.runner (fun state => outputDistribution.joint (answer state))

/-- One independent encoding distribution for each input or gate-output wire. -/
/- Mathematical definition (normal notation): List the encoding distributions of all input wires followed by the independently specified output-wire distribution at each canonical gate. -/
def Canonical.wireDistributions (initial : Fin inputs → FiniteDistribution E) :
    {T : ℕ} → Canonical E A inputs T → Fin (inputs + T) → FiniteDistribution E
  | 0, .nil => initial
  | _ + 1, .snoc prior outputDistribution _ => Fin.snoc (prior.wireDistributions initial) outputDistribution

/-- Conditional transcript weight when every wire encoding has already been sampled. This is the product of the exact local answer tables. -/
/- Mathematical definition (normal notation): For a fixed complete encoding assignment, multiply the canonical conditional answer probabilities along the given history: w(z | X) = ∏ᵢ prob_(i,zᵢ)(z_(<i),X). The empty history has weight one. -/
def Canonical.historyWeight : {T : ℕ} → Canonical E A inputs T →
    (Fin (inputs + T) → E) → (Fin T → A) → ℝ
  | 0, .nil, _, _ => 1
  | _ + 1, .snoc prior _ answer, encoding, history =>
      prior.historyWeight (Fin.init encoding) (Fin.init history) *
        (answer (Fin.init encoding, Fin.init history) (encoding (Fin.last _))).weight (history (Fin.last _))

/-- The sequential canonical execution has exactly the same density as independently sampling every wire, then multiplying its adaptive answer answer tables. This proves the deferred-sampling step used by composition. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For initial ∈ {0,…,inputs-1} → 𝒟(E); canonical ∈ Canonical(E, A, inputs, T); state ∈ RunState(E, A, inputs, T), we have

canonical.runner.execute(independentDistribution(initial))(state) = independentDistribution(canonical.wireDistributions(initial))((state)₁) · canonical.historyWeight((state)₁, (state)₂).
-/
theorem Canonical.execute_weight (initial : Fin inputs → FiniteDistribution E)
    (canonical : Canonical E A inputs T) (state : RunState E A inputs T) :
    (canonical.runner.execute (independentDistribution initial)).weight state =
      (independentDistribution (canonical.wireDistributions initial)).weight state.1 *
        canonical.historyWeight state.1 state.2 := by
  induction canonical with
  | nil =>
      let e : (Fin inputs → E) ≃ RunState E A inputs 0 :=
        { toFun := fun encoding => (encoding, Fin.elim0)
          invFun := Prod.fst
          left_inv := fun _ => rfl
          right_inv := by intro pair; ext i <;> first | rfl | exact Fin.elim0 i }
      simp only [Canonical.runner, Runner.execute]
      change ((independentDistribution initial).map e).weight state = _
      rw [map_equiv_weight]
      simp only [e, Equiv.coe_fn_symm_mk, Canonical.wireDistributions, Canonical.historyWeight, mul_one]
  | @snoc T prior outputDistribution answer ih =>
      change (((prior.runner.execute (independentDistribution initial)).joint
        (fun st => outputDistribution.joint (answer st))).map appendEquiv).weight state = _
      rw [map_equiv_weight]
      simp only [appendEquiv, Equiv.coe_fn_symm_mk, splitState, FiniteDistribution.joint]
      rw [ih (Fin.init state.1, Fin.init state.2)]
      simp only [Canonical.historyWeight, Canonical.wireDistributions, independentDistribution]
      have hprod := Fin.prod_univ_castSucc (fun w : Fin (inputs + T + 1) =>
        (Fin.snoc (α := fun _ => FiniteDistribution E) (prior.wireDistributions initial) outputDistribution w).weight (state.1 w))
      simp only [Fin.snoc_castSucc, Fin.snoc_last] at hprod
      have hprod' : (∏ x, (Fin.snoc (α := fun _ => FiniteDistribution E) (prior.wireDistributions initial) outputDistribution x).weight (state.1 x)) =
          (∏ w, (prior.wireDistributions initial w).weight (Fin.init state.1 w)) *
            outputDistribution.weight (state.1 (Fin.last (inputs + T))) := hprod
      calc
        _ = ((∏ w, (prior.wireDistributions initial w).weight (Fin.init state.1 w)) *
              outputDistribution.weight (state.1 (Fin.last (inputs + T)))) *
            (prior.historyWeight (Fin.init state.1) (Fin.init state.2) *
              (answer (Fin.init state.1, Fin.init state.2) (state.1 (Fin.last (inputs + T)))).weight
                (state.2 (Fin.last T))) := by ring
        _ = _ := congrArg (fun mass => mass *
            (prior.historyWeight (Fin.init state.1) (Fin.init state.2) *
              (answer (Fin.init state.1, Fin.init state.2) (state.1 (Fin.last (inputs + T)))).weight
                (state.2 (Fin.last T)))) hprod'.symm

end CircuitCompiler.Composition.TopologicalExecution
