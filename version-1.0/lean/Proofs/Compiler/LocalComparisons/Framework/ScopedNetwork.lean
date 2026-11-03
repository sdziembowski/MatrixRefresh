import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.LocalComparisons.Framework.CanonicalNetwork
import Proofs.Compiler.LocalComparisons.Framework.QueryTransport
/-!
# Scoped canonical network answer tables

This module defines the signed network views from their actual adaptive answer tables and independent wire distributions. Locality refers to the declared wire scope, not to independence of the adaptive answers.
-/
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Composition
open Refresh LabelPaths ErrorProcess
variable {W E A : Type*} [Fintype W] [DecidableEq W] [Fintype E] [Fintype A]
  {T : ℕ}
/-- Reassemble selected encodings and all other encodings. -/
/-
Mathematical definition (normal notation): For scope ∈ Finset(W); inside ∈ {w | w ∈ scope} → E; outside ∈ {w | w ∉ scope} → E, define

joinScope(scope, inside, outside) := (Equiv.piEquivPiSubtypeProd(((w ↦ w ∈ scope)), ((x₁ ↦ E))))⁻¹((inside, outside)).
-/
def joinScope (scope : Finset W) (inside : {w // w ∈ scope} → E)
    (outside : {w // w ∉ scope} → E) : W → E :=
  (Equiv.piEquivPiSubtypeProd (fun w => w ∈ scope) (fun _ => E)).symm (inside, outside)
theorem joinScope_of_mem (scope : Finset W) (inside : {w // w ∈ scope} → E)
    (outside : {w // w ∉ scope} → E) (w : W) (hw : w ∈ scope) :
    joinScope scope inside outside w = inside ⟨w, hw⟩ := by
  simp [joinScope, Equiv.piEquivPiSubtypeProd, hw]
theorem joinScope_of_not_mem (scope : Finset W) (inside : {w // w ∈ scope} → E)
    (outside : {w // w ∉ scope} → E) (w : W) (hw : w ∉ scope) :
    joinScope scope inside outside w = outside ⟨w, hw⟩ := by
  simp [joinScope, Equiv.piEquivPiSubtypeProd, hw]
/-- All gates whose local states can inspect any selected wire. -/
/-
Mathematical definition (normal notation): For scope ∈ {0,…,T-1} → Finset(W); selected ∈ Finset(W), define

touching(scope, selected) := Finset.univ.filter(((i ↦ ¬ (Disjoint(scope(i), selected))))).
-/
def touching (scope : Fin T → Finset W) (selected : Finset W) : Finset (Fin T) :=
  Finset.univ.filter (fun i => ¬ Disjoint (scope i) selected)
theorem touching_gate_eq_neighborhood (scope : Fin T → Finset W) (i : Fin T) :
    touching scope (scope i) = neighborhood scope i := by
  ext j
  simp only [touching, neighborhood, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.not_disjoint_iff, Finset.mem_biUnion, mem_incident]
  aesop
theorem touching_singleton_eq_incident (scope : Fin T → Finset W) (w : W) :
    touching scope {w} = incident scope w := by
  ext i
  simp [touching, Finset.disjoint_singleton_right]
/-- Fixing outside encodings makes a disjointly scoped answer table independent of the selected encodings, uniformly for every possible answer. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For scope, selected ∈ Finset(W); answerTable ∈ (W → E) → A → ℝ; outside ∈ {w | w ∉ selected} → E, assume E ≠ ∅; ∀ a, Scoped(scope, ((encoding ↦ answerTable(encoding, a)))); Disjoint(scope, selected). Then

∃ fixed ∈ A → ℝ, ∀ inside, a, answerTable(joinScope(selected, inside, outside), a) = fixed(a) .
-/
theorem scoped_table_independent [Nonempty E]
    (scope selected : Finset W) (answerTable : (W → E) → A → ℝ)
    (hlocal : ∀ a, Scoped scope (fun encoding => answerTable encoding a))
    (hdisjoint : Disjoint scope selected) (outside : {w // w ∉ selected} → E) :
    ∃ fixed : A → ℝ, ∀ inside a, answerTable (joinScope selected inside outside) a = fixed a := by
  let base : {w // w ∈ selected} → E := fun _ => Classical.choice (inferInstance : Nonempty E)
  refine ⟨fun a => answerTable (joinScope selected base outside) a, ?_⟩
  intro inside a
  apply hlocal a
  intro w hw
  have hwout : w ∉ selected := fun hs => Finset.disjoint_left.mp hdisjoint hw hs
  rw [joinScope_of_not_mem selected inside outside w hwout,
    joinScope_of_not_mem selected base outside w hwout]
/-- The three kinds of gate tables occurring in the composition proof. -/
/- Mathematical definition (normal notation): The three choices of a local hybrid factor are: original probability, cutoff probability, and signed approximation. -/
inductive AnswerTableKind where
  | original
  | real
  | signed
  deriving DecidableEq
/-- Local answer table data after common truncation. Each original gate is a probability table; each retained real gate is a subprobability table; signed gates obey their common absolute answer-sum budget. -/
/- Mathematical definition (normal notation): For every gate i, prefix h, and encoding assignment X, give three answer tables: normalized probabilities p_z ≥ 0 with ∑_z p_z = 1, cutoff probabilities r_z ≥ 0 with ∑_z r_z ≤ 1, and real signed tables g_z with ∑_z |g_z| ≤ B. Each table depends only on the encodings in gate i's scope. -/
structure ScopedTables (scope : Fin T → Finset W) (B : ℝ) where
  original : Fin T → List A → (W → E) → A → ℝ
  real : Fin T → List A → (W → E) → A → ℝ
  signed : Fin T → List A → (W → E) → A → ℝ
  original_nonneg : ∀ i h encoding a, 0 ≤ original i h encoding a
  original_total : ∀ i h encoding, (∑ a, original i h encoding a) = 1
  real_nonneg : ∀ i h encoding a, 0 ≤ real i h encoding a
  real_total_le : ∀ i h encoding, (∑ a, real i h encoding a) ≤ 1
  signed_budget : ∀ i h encoding, (∑ a, |signed i h encoding a|) ≤ B
  original_scoped : ∀ i h a, Scoped (scope i) (fun encoding => original i h encoding a)
  real_scoped : ∀ i h a, Scoped (scope i) (fun encoding => real i h encoding a)
  signed_scoped : ∀ i h a, Scoped (scope i) (fun encoding => signed i h encoding a)
namespace ScopedTables
variable {scope : Fin T → Finset W} {B : ℝ}
def choose (network : ScopedTables (E := E) (A := A) scope B) (kind : AnswerTableKind)
    (i : Fin T) (h : List A) (encoding : W → E) (a : A) : ℝ :=
  match kind with
  | .original => network.original i h encoding a
  | .real => network.real i h encoding a
  | .signed => network.signed i h encoding a
def kindBudget (B : ℝ) (kind : AnswerTableKind) : ℝ := if kind = .signed then B else 1
theorem choose_budget (network : ScopedTables (E := E) (A := A) scope B)
    (kind : AnswerTableKind) (i : Fin T) (h : List A) (encoding : W → E) :
    (∑ a, |network.choose kind i h encoding a|) ≤ kindBudget B kind := by
  cases kind with
  | original =>
      simpa [choose, kindBudget, abs_of_nonneg (network.original_nonneg _ _ _ _)] using
        le_of_eq (network.original_total i h encoding)
  | real =>
      simpa [choose, kindBudget, abs_of_nonneg (network.real_nonneg _ _ _ _)] using
        network.real_total_le i h encoding
  | signed => simpa [choose, kindBudget] using network.signed_budget i h encoding
theorem choose_scoped (network : ScopedTables (E := E) (A := A) scope B)
    (kind : AnswerTableKind) (i : Fin T) (h : List A) (a : A) :
    Scoped (scope i) (fun encoding => network.choose kind i h encoding a) := by
  cases kind with
  | original => exact network.original_scoped i h a
  | real => exact network.real_scoped i h a
  | signed => exact network.signed_scoped i h a
/-- Histories longer than the execution are harmlessly assigned a zero answer table. -/
/-
Mathematical definition (normal notation): For network ∈ ScopedTables(E = E, A = A, scope, B); mode ∈ {0,…,T-1} → AnswerTableKind; history ∈ A*; encoding ∈ W → E; a ∈ A, define

answerTable(network, mode, history, encoding, a) := { network.choose(mode((|history|, h)), (|history|, h), history, encoding, a) if |history| < T,; 0 otherwise }.
-/
def answerTable (network : ScopedTables (E := E) (A := A) scope B)
    (mode : Fin T → AnswerTableKind) (history : List A) (encoding : W → E) (a : A) : ℝ :=
  if h : history.length < T then network.choose (mode ⟨history.length, h⟩)
    ⟨history.length, h⟩ history encoding a else 0
def process (network : ScopedTables (E := E) (A := A) scope B)
    (mode : Fin T → AnswerTableKind) : ErrorProcess A (W → E) T :=
  fromTables (network.answerTable mode) (fun _ _ => 1) T []
noncomputable def view {V : Type*} [Fintype V]
    (network : ScopedTables (E := E) (A := A) scope B)
    (wireDistribution : W → FiniteDistribution E) (mode : Fin T → AnswerTableKind)
    (observe : Answers A T × (W → E) → V) : V → ℝ :=
  observedWeight (independentDistribution wireDistribution) (network.process mode) observe
def signedPositions (mode : Fin T → AnswerTableKind) : Finset (Fin T) :=
  Finset.univ.filter (fun i => mode i = .signed)
def timeBudget (mode : Fin T → AnswerTableKind) (B : ℝ) (time : ℕ) : ℝ :=
  if h : time < T then kindBudget B (mode ⟨time, h⟩) else 1
def timeLocal (positions : Finset (Fin T)) (time : ℕ) : Bool :=
  if h : time < T then decide (⟨time, h⟩ ∈ positions) else false
/-- The concrete mixed execution satisfies the forcing answer table hypotheses after all encodings outside the selected scope have been fixed. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For network ∈ ScopedTables(E = E, A = A, scope, B); mode ∈ {0,…,T-1} → AnswerTableKind; selected ∈ Finset(W); outside ∈ {w | w ∉ selected} → E, assume E ≠ ∅; 0 ≤ B. Then

TableControlled(precompose(((inside ↦ joinScope(selected, inside, outside))), network.process(mode)))(((i ↦ { B if i ∈ signedPositions(mode),; 1 otherwise })), ((i ↦ decide((i ∈ touching(scope, selected)))))).
-/
theorem process_tableControlled_scope [Nonempty E]
    (network : ScopedTables (E := E) (A := A) scope B) (hB : 0 ≤ B)
    (mode : Fin T → AnswerTableKind) (selected : Finset W)
    (outside : {w // w ∉ selected} → E) :
    (precompose (fun inside => joinScope selected inside outside) (network.process mode)).TableControlled
      (fun i => if i ∈ signedPositions mode then B else 1)
      (fun i => decide (i ∈ touching scope selected)) := by
  have hbudget (history : List A) (inside : {w // w ∈ selected} → E) :
      (∑ a, |network.answerTable mode history (joinScope selected inside outside) a|) ≤
        timeBudget mode B history.length := by
    by_cases h : history.length < T
    · simpa only [answerTable, timeBudget, dif_pos h] using
        network.choose_budget (mode ⟨history.length, h⟩) ⟨history.length, h⟩ history _
    · simp [answerTable, timeBudget, h]
  have hlocal (history : List A) (hflag : timeLocal (touching scope selected) history.length = false) :
      ∃ fixed : A → ℝ, ∀ inside a,
        network.answerTable mode history (joinScope selected inside outside) a = fixed a := by
    by_cases h : history.length < T
    · have hdisjoint : Disjoint (scope ⟨history.length, h⟩) selected := by
        simpa [timeLocal, h, touching] using hflag
      obtain ⟨fixed, hfixed⟩ := scoped_table_independent
        (scope ⟨history.length, h⟩) selected
        (fun encoding a => network.choose (mode ⟨history.length, h⟩) ⟨history.length, h⟩ history encoding a)
        (network.choose_scoped _ _ _) hdisjoint outside
      exact ⟨fixed, by simpa only [answerTable, dif_pos h] using hfixed⟩
    · exact ⟨fun _ => 0, by intros; simp [answerTable, h]⟩
  have h := fromTables_tableControlled
    (fun history inside => network.answerTable mode history (joinScope selected inside outside))
    (timeBudget mode B) (timeLocal (touching scope selected)) hbudget hlocal T []
  simpa [process, precompose_fromTables, timeBudget, timeLocal, kindBudget, signedPositions] using h
/-- A one-gate mode change leaves the adaptive continuation trees identical. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For network ∈ ScopedTables(E = E, A = A, scope, B); first, second ∈ {0,…,T-1} → AnswerTableKind; position ∈ {0,…,T-1}, assume ∀ i, (i ≠ position) ⇒ first(i) = second(i). Then

AgreeExceptAt(position, network.process(first), network.process(second)).
-/
theorem process_agreeExceptAt (network : ScopedTables (E := E) (A := A) scope B)
    (first second : Fin T → AnswerTableKind) (position : Fin T)
    (heq : ∀ i, i ≠ position → first i = second i) :
    AgreeExceptAt position.val (network.process first) (network.process second) := by
  apply fromTables_agreeExceptAt
  intro history hlength
  funext encoding a
  by_cases h : history.length < T
  · have hi : (⟨history.length, h⟩ : Fin T) ≠ position := by
      intro hi
      have hv := congrArg Fin.val hi
      exact hlength (by simpa using hv)
    simp only [answerTable, dif_pos h, heq _ hi]
  · simp [answerTable, h]
/-- The signed observed view is exactly the average of the views conditional on all encodings outside any selected scope. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; network ∈ ScopedTables(E = E, A = A, scope, B); wireDistribution ∈ W → 𝒟(E); mode ∈ {0,…,T-1} → AnswerTableKind; selected ∈ Finset(W); observe ∈ Answers(A, T) × (W → E) → V, assume V is finite. Then

network.view(wireDistribution, mode, observe) = (v ↦ 𝔼_(outside ← independentDistribution(((w ∈ {w | w ∉ selected} ↦ wireDistribution(w))))) [observedWeight(independentDistribution(((w ∈ {w | w ∈ selected} ↦ wireDistribution(w)))), precompose(((inside ↦ joinScope(selected, inside, outside))), network.process(mode)), ((hx ↦ observe(((hx)₁, joinScope(selected, (hx)₂, outside))))), v)]).
-/
theorem view_scope {V : Type*} [Fintype V]
    (network : ScopedTables (E := E) (A := A) scope B)
    (wireDistribution : W → FiniteDistribution E) (mode : Fin T → AnswerTableKind)
    (selected : Finset W) (observe : Answers A T × (W → E) → V) :
    network.view wireDistribution mode observe = fun v =>
      (independentDistribution (fun w : {w // w ∉ selected} => wireDistribution w)).expect (fun outside =>
        observedWeight (independentDistribution (fun w : {w // w ∈ selected} => wireDistribution w))
          (precompose (fun inside => joinScope selected inside outside) (network.process mode))
          (fun hx => observe (hx.1, joinScope selected hx.2 outside)) v) := by
  unfold view
  have hsplit := independentDistribution_split_reverse wireDistribution (fun w => w ∈ selected)
  have hinst : Subtype.fintype (fun w => w ∈ selected) = Finset.Subtype.fintype selected :=
    Subsingleton.elim _ _
  rw [hinst] at hsplit
  rw [hsplit]
  rw [observedWeight_map, observedWeight_prod]
  funext v
  apply congrArg (fun f => (independentDistribution (fun w : {w // w ∉ selected} => wireDistribution w)).expect f)
  funext outside
  simp only [observedWeight_eq_expect, weight_precompose, joinScope]
/-- A local gate approximation estimate is exactly the recursive error premise for the selected gate in the conditional execution tree. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For network ∈ ScopedTables(E = E, A = A, scope, B); first, second ∈ {0,…,T-1} → AnswerTableKind; position ∈ {0,…,T-1}; wireDistribution ∈ W → 𝒟(E); outside ∈ {w | w ∉ scope(position)} → E; η ∈ ℝ, assume 0 ≤ η; ∀ history, a, 𝔼_(inside ← independentDistribution(((w ∈ {w | w ∈ scope(position)} ↦ wireDistribution(w))))) [|network.choose(first(position), position, history, joinScope(scope(position), inside, outside), a) - network.choose(second(position), position, history, joinScope(scope(position), inside, outside), a)|] ≤ η. Then

DifferenceBound(independentDistribution(((w ∈ {w | w ∈ scope(position)} ↦ wireDistribution(w)))), η, position, precompose(((inside ↦ joinScope(scope(position), inside, outside))), network.process(first)), precompose(((inside ↦ joinScope(scope(position), inside, outside))), network.process(second))).
-/
theorem process_scope_differenceBound
    (network : ScopedTables (E := E) (A := A) scope B)
    (first second : Fin T → AnswerTableKind) (position : Fin T)
    (wireDistribution : W → FiniteDistribution E) (outside : {w // w ∉ scope position} → E)
    (η : ℝ) (hη : 0 ≤ η)
    (herror : ∀ history a,
      (independentDistribution (fun w : {w // w ∈ scope position} => wireDistribution w)).expect (fun inside =>
        |network.choose (first position) position history (joinScope (scope position) inside outside) a -
          network.choose (second position) position history (joinScope (scope position) inside outside) a|) ≤ η) :
    DifferenceBound (independentDistribution (fun w : {w // w ∈ scope position} => wireDistribution w)) η position.val
      (precompose (fun inside => joinScope (scope position) inside outside) (network.process first))
      (precompose (fun inside => joinScope (scope position) inside outside) (network.process second)) := by
  simp only [process, precompose_fromTables]
  apply fromTables_differenceBound _ η hη
  intro history hlength a
  have hlength' : history.length = position.val := by simpa using hlength
  have hlt : history.length < T := by simpa [hlength'] using position.isLt
  have hi : (⟨history.length, hlt⟩ : Fin T) = position := Fin.ext hlength'
  simpa only [answerTable, dif_pos hlt, hi] using herror history a
/-- One concrete answer table replacement in the actual signed network view. The local error is averaged only over the gate's scope; all remaining wire encodings and all terminal boundary observations are retained correctly. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; network ∈ ScopedTables(E = E, A = A, scope, B); wireDistribution ∈ W → 𝒟(E); first, second ∈ {0,…,T-1} → AnswerTableKind; position ∈ {0,…,T-1}; η ∈ ℝ; observe ∈ Answers(A, T) × (W → E) → V, assume E ≠ ∅; V is finite; 0 ≤ B; Nonempty(scope(position)); ∀ i, (i ≠ position) ⇒ first(i) = second(i); 0 ≤ η; ∀ outside ∈ {w | w ∉ scope(position)} → E, ∀ history, a, 𝔼_(inside ← independentDistribution(((w ∈ {w | w ∈ scope(position)} ↦ wireDistribution(w))))) [|network.choose(first(position), position, history, joinScope(scope(position), inside, outside), a) - network.choose(second(position), position, history, joinScope(scope(position), inside, outside), a)|] ≤ η. Then

variationNorm(((v ↦ network.view(wireDistribution, first, observe, v) - network.view(wireDistribution, second, observe, v)))) ≤ (|A|)^(|touching(scope, scope(position))|) · B^(|erase(signedPositions(first))(position)|) · η.
-/
theorem view_gate_switch [Nonempty E] {V : Type*} [Fintype V]
    (network : ScopedTables (E := E) (A := A) scope B) (hB : 0 ≤ B)
    (wireDistribution : W → FiniteDistribution E) (first second : Fin T → AnswerTableKind) (position : Fin T)
    (hscope : (scope position).Nonempty)
    (heq : ∀ i, i ≠ position → first i = second i)
    (η : ℝ) (hη : 0 ≤ η)
    (herror : ∀ outside : {w // w ∉ scope position} → E, ∀ history a,
      (independentDistribution (fun w : {w // w ∈ scope position} => wireDistribution w)).expect (fun inside =>
        |network.choose (first position) position history (joinScope (scope position) inside outside) a -
          network.choose (second position) position history (joinScope (scope position) inside outside) a|) ≤ η)
    (observe : Answers A T × (W → E) → V) :
    variationNorm (fun v => network.view wireDistribution first observe v - network.view wireDistribution second observe v) ≤
      (Fintype.card A : ℝ) ^ (touching scope (scope position)).card *
        B ^ ((signedPositions first).erase position).card * η := by
  have hposition : position ∈ touching scope (scope position) := by
    obtain ⟨w, hw⟩ := hscope
    simp only [touching, Finset.mem_filter, Finset.mem_univ, true_and, Finset.not_disjoint_iff]
    exact ⟨w, hw, hw⟩
  have hconditional (outside : {w // w ∉ scope position} → E) :=
    table_gate_switch_bound_pow
      (independentDistribution (fun w : {w // w ∈ scope position} => wireDistribution w)) position
      (precompose (fun inside => joinScope (scope position) inside outside) (network.process first))
      (precompose (fun inside => joinScope (scope position) inside outside) (network.process second))
      (precompose_agreeExceptAt _ _ _ _ (network.process_agreeExceptAt first second position heq))
      η B hη hB (signedPositions first) (touching scope (scope position)) hposition
      (network.process_tableControlled_scope hB first (scope position) outside)
      (network.process_scope_differenceBound first second position wireDistribution outside η hη (herror outside))
      (fun hx => observe (hx.1, joinScope (scope position) hx.2 outside))
  rw [network.view_scope wireDistribution first (scope position) observe,
    network.view_scope wireDistribution second (scope position) observe]
  have h := variationNorm_average_le
    (independentDistribution (fun w : {w // w ∉ scope position} => wireDistribution w))
    (fun outside v =>
      observedWeight (independentDistribution (fun w : {w // w ∈ scope position} => wireDistribution w))
        (precompose (fun inside => joinScope (scope position) inside outside) (network.process first))
        (fun hx => observe (hx.1, joinScope (scope position) hx.2 outside)) v -
      observedWeight (independentDistribution (fun w : {w // w ∈ scope position} => wireDistribution w))
        (precompose (fun inside => joinScope (scope position) inside outside) (network.process second))
        (fun hx => observe (hx.1, joinScope (scope position) hx.2 outside)) v)
    _ hconditional
  simpa only [MatrixRefresh.expect_sub] using h
end ScopedTables
end CircuitCompiler.Composition
