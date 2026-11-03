import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.LocalComparisons.Factorization
/-!
# Scoped probability tables and cut-free signed executions

There is deliberately no pointwise bound on a signed gate here. Only the unsigned answer tables are required to be probability distributions.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace CircuitCompiler.AveragedEnergyComparison
open Refresh MatrixRefresh Composition
noncomputable section
variable {W E A : Type*} [Fintype W] [DecidableEq W] [Fintype E] [Fintype A]
  {T : ℕ}
namespace ScopedProbabilities
variable {scope : Fin T → Finset W}
def outer (network : ScopedProbabilities (E := E) (A := A) scope)
    (signed : Finset (Fin T)) (h : List A) (e : W → E) (a : A) : ℝ :=
  if ht : h.length < T then
    if (⟨h.length,ht⟩ : Fin T) ∈ signed then 1 else network.prob ⟨h.length,ht⟩ h e a
  else 0
def inner (signedTable : Fin T → List A → (W → E) → A → ℝ)
    (signed : Finset (Fin T)) (h : List A) (e : W → E) (a : A) : ℝ :=
  if ht : h.length < T then
    if (⟨h.length,ht⟩ : Fin T) ∈ signed then signedTable ⟨h.length,ht⟩ h e a else 1
  else 1
def mixed (network : ScopedProbabilities (E := E) (A := A) scope)
    (signedTable : Fin T → List A → (W → E) → A → ℝ)
    (signed : Finset (Fin T)) (h : List A) (e : W → E) (a : A) : ℝ :=
  if ht : h.length < T then
    if (⟨h.length,ht⟩ : Fin T) ∈ signed then signedTable ⟨h.length,ht⟩ h e a
    else network.prob ⟨h.length,ht⟩ h e a
  else 0
theorem mixed_eq_outer_mul_inner
    (network : ScopedProbabilities (E := E) (A := A) scope)
    (signedTable : Fin T → List A → (W → E) → A → ℝ)
    (signed : Finset (Fin T)) (h : List A) (e : W → E) (a : A) :
    network.mixed signedTable signed h e a =
      network.outer signed h e a * inner signedTable signed h e a := by
  simp only [mixed, outer, inner]
  split_ifs <;> simp
def split (network : ScopedProbabilities (E := E) (A := A) scope)
    (signedTable : Fin T → List A → (W → E) → A → ℝ)
    (signed : Finset (Fin T)) (selected : Finset W)
    (outside : {w // w ∉ selected} → E) :
    SplitProcess A ({w // w ∈ selected} → E) T :=
  SplitProcess.fromTables
    (fun h inside => network.outer signed h (joinScope selected inside outside))
    (fun h inside => inner signedTable signed h (joinScope selected inside outside))
    (fun _ _ => 1) T []
def timeBudget (signed : Finset (Fin T)) (time : ℕ) : ℝ :=
  if ht : time < T then
    if (⟨time,ht⟩ : Fin T) ∈ signed then Fintype.card A else 1
  else 1
def timeGuard (signed : Finset (Fin T)) (selected : Finset W) (time : ℕ) : Bool :=
  if ht : time < T then decide ((⟨time,ht⟩ : Fin T) ∈ touching scope selected \ signed)
  else false
theorem outer_budget (network : ScopedProbabilities (E := E) (A := A) scope)
    (signed : Finset (Fin T)) (h : List A) (e : W → E) :
    (∑ a, |network.outer signed h e a|) ≤ timeBudget (A := A) signed h.length := by
  unfold outer timeBudget
  split_ifs with ht hs
  · simp
  · simp only [abs_of_nonneg (network.nonneg _ _ _ _)]
    exact network.total_le _ _ _
  · simp
theorem outer_independent [Nonempty E]
    (network : ScopedProbabilities (E := E) (A := A) scope)
    (signed : Finset (Fin T)) (selected : Finset W)
    (outside : {w // w ∉ selected} → E) (h : List A)
    (hg : timeGuard (scope := scope) signed selected h.length = false) :
    ∃ fixed : A → ℝ, ∀ inside a,
      network.outer signed h (joinScope selected inside outside) a = fixed a := by
  by_cases ht : h.length < T
  · by_cases hs : (⟨h.length,ht⟩ : Fin T) ∈ signed
    · exact ⟨fun _ => 1, by intros; simp [outer,ht,hs]⟩
    · have hd : Disjoint (scope ⟨h.length,ht⟩) selected := by
        simpa [timeGuard,ht,hs,touching] using hg
      obtain ⟨fixed,hfixed⟩ := scoped_table_independent (scope ⟨h.length,ht⟩) selected
        (fun e a => network.prob ⟨h.length,ht⟩ h e a) (network.locality _ _) hd outside
      exact ⟨fixed, by simpa only [outer,dif_pos ht,if_neg hs] using hfixed⟩
  · exact ⟨fun _ => 0, by intros; simp [outer,ht]⟩
theorem split_controlled [Nonempty E]
    (network : ScopedProbabilities (E := E) (A := A) scope)
    (signedTable : Fin T → List A → (W → E) → A → ℝ)
    (signed : Finset (Fin T)) (selected : Finset W)
    (outside : {w // w ∉ selected} → E) :
    (network.split signedTable signed selected outside).OuterControlled
      (fun i => if i ∈ signed then (Fintype.card A : ℝ) else 1)
      (fun i => decide (i ∈ touching scope selected \ signed)) := by
  have h := SplitProcess.fromTables_controlled
    (fun h inside => network.outer signed h (joinScope selected inside outside))
    (fun h inside => inner signedTable signed h (joinScope selected inside outside))
    (fun _ _ => 1) (timeBudget (A := A) signed)
    (timeGuard (scope := scope) signed selected)
    (fun h inside => network.outer_budget signed h _)
    (fun h hg => network.outer_independent signed selected outside h hg) T []
  simpa [split,timeBudget,timeGuard] using h
theorem split_full_weight
    (network : ScopedProbabilities (E := E) (A := A) scope)
    (signedTable : Fin T → List A → (W → E) → A → ℝ)
    (signed : Finset (Fin T)) (selected : Finset W)
    (outside : {w // w ∉ selected} → E) (history : Answers A T)
    (inside : {w // w ∈ selected} → E) :
    (network.split signedTable signed selected outside).full.weight history inside =
      (ErrorProcess.fromTables (network.mixed signedTable signed) (fun _ _ => 1) T []).weight
        history (joinScope selected inside outside) := by
  simp only [split,SplitProcess.full_fromTables, ← mixed_eq_outer_mul_inner]
  have h := ErrorProcess.weight_precompose (fun inside => joinScope selected inside outside)
    (ErrorProcess.fromTables (network.mixed signedTable signed) (fun _ _ => 1) T []) history inside
  simpa only [ErrorProcess.precompose_fromTables] using h
/-- Fixing the outside encodings turns the real adaptive execution into the proved split process. Its loss depends on the closed local neighborhood, not on the total number of gates. -/
-- Auxiliary lemma (hybrid comparison); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Fix the encodings outside a selected patch U, and sample its inside encodings from any distribution P. If every fixed answer history has expected absolute local product at most ε ≥ 0, then every finite observation of the weighted transcript and inside encodings has signed total mass bounded by

‖ν‖₁ ≤ K^(|S|+|touch(U) ∖ S|) · ε,

where S is the signed-gate set and K the answer-alphabet size.
-/
theorem observed_patch_bound [Nonempty E] {V : Type*} [Fintype V]
    (network : ScopedProbabilities (E := E) (A := A) scope)
    (signedTable : Fin T → List A → (W → E) → A → ℝ)
    (signed : Finset (Fin T)) (selected : Finset W)
    (outside : {w // w ∉ selected} → E)
    (P : FiniteDistribution ({w // w ∈ selected} → E)) (error : ℝ) (herror : 0 ≤ error)
    (hlocal : ∀ history : Answers A T, P.expect (fun inside =>
      |(network.split signedTable signed selected outside).localPart.weight history inside|) ≤ error)
    (observe : Answers A T × ({w // w ∈ selected} → E) → V) :
    variationNorm (fun v => ∑ hx : Answers A T × ({w // w ∈ selected} → E),
      P.weight hx.2 *
        (ErrorProcess.fromTables (network.mixed signedTable signed) (fun _ _ => 1) T []).weight
          hx.1 (joinScope selected hx.2 outside) * (FiniteDistribution.pure (observe hx)).weight v) ≤
      (Fintype.card A : ℝ)^(signed.card + (touching scope selected \ signed).card) * error := by
  have h := (network.split signedTable signed selected outside).observed_isolate
    P error herror signed (touching scope selected \ signed)
    (network.split_controlled signedTable signed selected outside) hlocal observe
  simpa only [split_full_weight] using h
/-- Split the independently sampled wire encodings into a selected patch and its complement. This is an equality of the actual signed observed views. -/
-- Auxiliary lemma (hybrid comparison); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; network ∈ ScopedProbabilities(E = E, A = A, scope); table ∈ {0,…,T-1} → A* → (W → E) → A → ℝ; signed ∈ Finset({0,…,T-1}); wireDistribution ∈ W → 𝒟(E); selected ∈ Finset(W); observe ∈ Answers(A, T) × (W → E) → V, assume V is finite. Then

ErrorProcess.observedWeight(independentDistribution(wireDistribution), ErrorProcess.fromTables(network.mixed(table, signed), ((x₁, x₂ ↦ 1)), T, []), observe) = ((v ↦ 𝔼_(outside ← independentDistribution(((w ∈ {w | w ∉ selected} ↦ wireDistribution(w))))) [ErrorProcess.observedWeight(independentDistribution(((w ∈ {w | w ∈ selected} ↦ wireDistribution(w)))), ErrorProcess.precompose(((inside ↦ joinScope(selected, inside, outside))), ErrorProcess.fromTables(network.mixed(table, signed), ((x₁, x₂ ↦ 1)), T, [])), ((hx ↦ observe(((hx)₁, joinScope(selected, (hx)₂, outside))))), v)])).
-/
theorem observed_scope {V : Type*} [Fintype V]
    (network : ScopedProbabilities (E := E) (A := A) scope)
    (table : Fin T → List A → (W → E) → A → ℝ)
    (signed : Finset (Fin T)) (wireDistribution : W → FiniteDistribution E)
    (selected : Finset W) (observe : Answers A T × (W → E) → V) :
    ErrorProcess.observedWeight (independentDistribution wireDistribution)
      (ErrorProcess.fromTables (network.mixed table signed) (fun _ _ => 1) T []) observe =
    (fun v => (independentDistribution (fun w : {w // w ∉ selected} => wireDistribution w)).expect (fun outside =>
      ErrorProcess.observedWeight (independentDistribution (fun w : {w // w ∈ selected} => wireDistribution w))
        (ErrorProcess.precompose (fun inside => joinScope selected inside outside)
          (ErrorProcess.fromTables (network.mixed table signed) (fun _ _ => 1) T []))
        (fun hx => observe (hx.1, joinScope selected hx.2 outside)) v)) := by
  have hsplit := independentDistribution_split_reverse wireDistribution (fun w => w ∈ selected)
  have hinst : Subtype.fintype (fun w => w ∈ selected) = Finset.Subtype.fintype selected :=
    Subsingleton.elim _ _
  rw [hinst] at hsplit
  rw [hsplit, ErrorProcess.observedWeight_map, ErrorProcess.observedWeight_prod]
  funext v
  apply congrArg (fun f => (independentDistribution (fun w : {w // w ∉ selected} => wireDistribution w)).expect f)
  funext outside
  simp only [ErrorProcess.observedWeight_eq_expect, ErrorProcess.weight_precompose, joinScope]
/-- Averaging the fixed outside encodings has no additional loss. -/
-- Auxiliary lemma (hybrid comparison); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Independently sample all wire encodings in a scoped network. Suppose that for every fixed outside encoding and full history, the expected absolute product of the factors local to a selected patch U is at most ε ≥ 0. Then any finite observation of the full weighted execution has signed L₁ mass at most

K^(|S|+|touch(U) ∖ S|) · ε.

Here S is the signed-gate set.
-/
theorem observed_network_bound [Nonempty E] {V : Type*} [Fintype V]
    (network : ScopedProbabilities (E := E) (A := A) scope)
    (table : Fin T → List A → (W → E) → A → ℝ)
    (signed : Finset (Fin T)) (wireDistribution : W → FiniteDistribution E)
    (selected : Finset W) (error : ℝ) (herror : 0 ≤ error)
    (hlocal : ∀ outside, ∀ history : Answers A T,
      (independentDistribution (fun w : {w // w ∈ selected} => wireDistribution w)).expect (fun inside =>
        |(network.split table signed selected outside).localPart.weight history inside|) ≤ error)
    (observe : Answers A T × (W → E) → V) :
    variationNorm (ErrorProcess.observedWeight (independentDistribution wireDistribution)
      (ErrorProcess.fromTables (network.mixed table signed) (fun _ _ => 1) T []) observe) ≤
      (Fintype.card A : ℝ)^(signed.card + (touching scope selected \ signed).card) * error := by
  rw [network.observed_scope table signed wireDistribution selected observe]
  apply variationNorm_average_le
  intro outside
  have h := network.observed_patch_bound table signed selected outside
    (independentDistribution (fun w : {w // w ∈ selected} => wireDistribution w)) error herror
    (hlocal outside) (fun hx => observe (hx.1,joinScope selected hx.2 outside))
  convert h using 1
  congr 1
  funext v
  simp only [ErrorProcess.observedWeight, ErrorProcess.weight_precompose]
/-- Signed positions and unsigned guards partition the closed patch. Hence its size, rather than their separate crude bounds, determines the exponent. -/

/-
Mathematical statement (normal notation): Choose a set of wires U in a scoped probability network. Suppose every signed gate touches U, and at most b gates touch U. For every fixed outside encoding and answer history, assume the absolute local product averaged over independently sampled encodings on U is at most ε ≥ 0. Then every finite observation of the full weighted network has signed L₁ mass at most

Kᵇ · ε,

where K is the answer-alphabet size.
-/
theorem observed_network_closed_bound [Nonempty E] [Nonempty A]
    {V : Type*} [Fintype V]
    (network : ScopedProbabilities (E := E) (A := A) scope)
    (table : Fin T → List A → (W → E) → A → ℝ)
    (signed : Finset (Fin T)) (wireDistribution : W → FiniteDistribution E)
    (selected : Finset W) (error : ℝ) (herror : 0 ≤ error) (bound : ℕ)
    (hcover : signed ⊆ touching scope selected)
    (hcard : (touching scope selected).card ≤ bound)
    (hlocal : ∀ outside, ∀ history : Answers A T,
      (independentDistribution (fun w : {w // w ∈ selected} => wireDistribution w)).expect (fun inside =>
        |(network.split table signed selected outside).localPart.weight history inside|) ≤ error)
    (observe : Answers A T × (W → E) → V) :
    variationNorm (ErrorProcess.observedWeight (independentDistribution wireDistribution)
      (ErrorProcess.fromTables (network.mixed table signed) (fun _ _ => 1) T []) observe) ≤
      (Fintype.card A : ℝ)^bound * error := by
  apply (network.observed_network_bound table signed wireDistribution selected error herror hlocal observe).trans
  apply mul_le_mul_of_nonneg_right _ herror
  have he : signed.card + (touching scope selected \ signed).card =
      (touching scope selected).card := by
    have h := Finset.card_sdiff_add_card_eq_card hcover
    omega
  rw [he]
  exact pow_le_pow_right₀ (by exact_mod_cast Fintype.card_pos (α := A)) hcard
end ScopedProbabilities
end
end CircuitCompiler.AveragedEnergyComparison
