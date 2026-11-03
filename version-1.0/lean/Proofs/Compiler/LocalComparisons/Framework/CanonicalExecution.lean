import Proofs.Compiler.LocalComparisons.Framework.AnswerVectors
import Proofs.Compiler.LocalComparisons.Framework.SupportedExecution



/-!
# Equality between sequential canonical execution and the network composition distribution
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler.Composition.TopologicalExecution

open Refresh ErrorProcess

universe u v

variable {E : Type u} {A : Type v} [Fintype E] [Fintype A] {inputs T : ℕ}

/-- The exact chronological answer table induced by a sequential canonical plan. The last gate reads only its earlier wires, its output, and earlier answers. -/
/- Mathematical definition (normal notation): For a prefix h = (z₁,…,zᵢ), complete encoding assignment X, and next answer z, this table is the canonical plan's conditional probability of z at gate i+1, using the previous encodings and the new output encoding in X. It is the local factor in the chronological history product. -/
noncomputable def Canonical.answerTable : {T : ℕ} → Canonical E A inputs T →
    List A → (Fin (inputs + T) → E) → A → ℝ
  | 0, .nil, _, _, _ => 0
  | t + 1, .snoc prior _ answer, history, encoding, a =>
      if h : history.length = t then
        (answer (Fin.init encoding, fun i => history[i.val]'(by omega))
          (encoding (Fin.last _))).weight a
      else prior.answerTable history (Fin.init encoding) a

/-- The product used in the sequential density is exactly the adaptive chronological product over the induced local answer tables. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): For every complete encoding assignment X and history z = (z₁,…,z_T), the canonical plan's history weight is ∏ᵢ₌₁ ᵀprob_(i,zᵢ)(z_(<i),X). The two sides differ only in whether the product is built recursively with the plan or with answer vectors. -/
theorem Canonical.historyWeight_eq_vectorWeight
    (canonical : Canonical E A inputs T) (encoding : Fin (inputs + T) → E)
    (history : Fin T → A) :
    canonical.historyWeight encoding history = vectorWeight canonical.answerTable T [] history encoding := by
  induction canonical with
  | nil => rfl
  | @snoc T prior outputDistribution answer ih =>
      rw [Canonical.historyWeight, ih]
      have hprefix : vectorWeight prior.answerTable T [] (Fin.init history) (Fin.init encoding) =
          vectorWeight (prior.snoc outputDistribution answer).answerTable T [] (Fin.init history) encoding := by
        rw [← vectorWeight_map_state (fun enc : Fin (inputs + (T + 1)) → E => Fin.init enc) prior.answerTable]
        apply vectorWeight_congr
        intro h _ hlt a
        have hne : h.length ≠ T := by simpa using Nat.ne_of_lt hlt
        simp only [Canonical.answerTable, dif_neg hne]
      have hlast : (prior.snoc outputDistribution answer).answerTable (List.ofFn (Fin.init history)) encoding
          (history (Fin.last T)) =
          (answer (Fin.init encoding, Fin.init history) (encoding (Fin.last (inputs + T)))).weight
            (history (Fin.last T)) := by
        simp [Canonical.answerTable]
      have h := vectorWeight_snoc (prior.snoc outputDistribution answer).answerTable T []
        (Fin.init history) (history (Fin.last T)) encoding
      simp only [Fin.snoc_init_self, List.nil_append] at h
      rw [hprefix]
      exact (congrArg (fun z => vectorWeight (prior.snoc outputDistribution answer).answerTable T []
        (Fin.init history) encoding * z) hlast.symm).trans h.symm

/-- The finite answer vectors of a topological runner and the nested answers used by the forcing proof differ only by this explicit equivalence. -/
/- Mathematical definition (normal notation): Identify a pair consisting of the complete wire-encoding assignment and an answer vector (z₁,…,z_T) with the runner's state containing those same encodings and answers. This is a bijective reindexing, with no change of values. -/
def stateAnswerEquiv : ((Fin (inputs + T) → E) × Answers A T) ≃ RunState E A inputs T :=
  Equiv.prodCongr (Equiv.refl _) (answersEquiv A T)

/-- If the original network table is the local chronological answer table of the canonical runner, both constructions have exactly the same full joint distribution. -/

/- Mathematical statement (normal notation): Suppose each local answer probability of a canonical runner equals the corresponding local table of the network, for every prefix of length less than T. Then sequential execution has exactly the same joint distribution as: sample all wire encodings independently from their prescribed distributions, then sample the answer history with probability ∏ᵢ₌₁ ᵀ prob_(i,zᵢ)(hᵢ₋₁,X). The explicit reindexing only changes how finite answer vectors are represented. -/
theorem Canonical.execute_eq_network
    (initial : Fin inputs → FiniteDistribution E) (canonical : Canonical E A inputs T)
    {scope : Fin T → Finset (Fin (inputs + T))} {B : ℝ}
    (network : ScopedTables (E := E) (A := A) scope B)
    (hkernel : ∀ history, history.length < T → ∀ encoding a,
      network.answerTable (fun _ => .original) history encoding a = canonical.answerTable history encoding a) :
    canonical.runner.execute (independentDistribution initial) =
      ((independentDistribution (canonical.wireDistributions initial)).joint network.canonicalHistory).map stateAnswerEquiv := by
  ext state
  rw [canonical.execute_weight, map_equiv_weight]
  simp only [stateAnswerEquiv, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Equiv.refl_symm,
    Equiv.refl_apply, Prod.map, FiniteDistribution.joint, ScopedTables.canonicalHistory, ScopedTables.process,
    fromTables_vectorWeight, canonical.historyWeight_eq_vectorWeight]
  congr 1
  symm
  apply vectorWeight_congr
  intro history _ hlt a
  exact hkernel history (by simpa using hlt) state.1 a

/-- Observing the entire actual runner through any history/boundary map is close to precisely the canonicalDistribution used in the composition theorem. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): If every actual transition is within statistical distance τ of the corresponding canonical transition, and the canonical answer probabilities match the network tables, then every observation of a T-step actual run is within Tτ of the canonical network observation. Inputs are sampled independently from their stated encoding distributions. -/
theorem Runner.actual_canonical_network_distance {V : Type*} [Fintype V]
    (initial : Fin inputs → FiniteDistribution E) (real : Runner E A inputs T)
    (canonical : Canonical E A inputs T) (τ : ℝ) (hcoupling : real.Coupled τ canonical.runner)
    {scope : Fin T → Finset (Fin (inputs + T))} {B : ℝ}
    (network : ScopedTables (E := E) (A := A) scope B)
    (hkernel : ∀ history, history.length < T → ∀ encoding a,
      network.answerTable (fun _ => .original) history encoding a = canonical.answerTable history encoding a)
    (observe : Answers A T × (Fin (inputs + T) → E) → V) :
    statisticalDistance
      ((real.execute (independentDistribution initial)).map
        (fun state => observe ((answersEquiv A T).symm state.2, state.1)))
      (network.canonicalDistribution (canonical.wireDistributions initial) observe) ≤ (T : ℝ) * τ := by
  have h := real.execute_observed_distance (independentDistribution initial) canonical.runner τ hcoupling
    (fun state => observe ((answersEquiv A T).symm state.2, state.1))
  rw [canonical.execute_eq_network initial network hkernel, FiniteDistribution.map_map] at h
  simpa only [stateAnswerEquiv, Function.comp_def, Equiv.prodCongr_apply, Equiv.refl_apply, Prod.map,
    Equiv.symm_apply_apply, ScopedTables.canonicalDistribution] using h

/-- The same actual-to-network coupling needs local estimates only on correctly typed canonical prefixes, as provided by physical gate couplings. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): If the per-step actual/canonical distance is at most τ on supported canonical prefixes, and the canonical probabilities equal the network tables, then the observed actual and canonical-network executions have statistical distance at most Tτ. No transition assumption is required on unreachable prefixes. -/
theorem Runner.actual_canonical_network_distance_on_support {V : Type*} [Fintype V]
    (initial : Fin inputs → FiniteDistribution E) (real : Runner E A inputs T)
    (canonical : Canonical E A inputs T) (τ : ℝ)
    (hcoupling : real.CoupledOn (independentDistribution initial) τ canonical.runner)
    {scope : Fin T → Finset (Fin (inputs + T))} {B : ℝ}
    (network : ScopedTables (E := E) (A := A) scope B)
    (hkernel : ∀ history, history.length < T → ∀ encoding a,
      network.answerTable (fun _ => .original) history encoding a = canonical.answerTable history encoding a)
    (observe : Answers A T × (Fin (inputs + T) → E) → V) :
    statisticalDistance
      ((real.execute (independentDistribution initial)).map
        (fun state => observe ((answersEquiv A T).symm state.2, state.1)))
      (network.canonicalDistribution (canonical.wireDistributions initial) observe) ≤ (T : ℝ) * τ := by
  have h := real.execute_observed_distance_on_support (independentDistribution initial) canonical.runner τ hcoupling
    (fun state => observe ((answersEquiv A T).symm state.2, state.1))
  rw [canonical.execute_eq_network initial network hkernel, FiniteDistribution.map_map] at h
  simpa only [stateAnswerEquiv, Function.comp_def, Equiv.prodCongr_apply, Equiv.refl_apply, Prod.map,
    Equiv.symm_apply_apply, ScopedTables.canonicalDistribution] using h

end CircuitCompiler.Composition.TopologicalExecution
