import Proofs.Compiler.LocalComparisons.Framework.ScopedNetwork



/-!
# Concrete signed sets and real truncation of a canonical network
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace CircuitCompiler.Composition

open Refresh LabelPaths ErrorProcess

variable {W E A : Type*} [Fintype W] [DecidableEq W] [Fintype E] [Fintype A]
  {T : ℕ}

namespace ScopedTables

variable {scope : Fin T → Finset W} {B : ℝ}

/-- Use a designated gate kind on a selected set, and retained real answer tables at every other gate. -/
/-
Mathematical definition (normal notation): For kind ∈ AnswerTableKind; selected ∈ Finset({0,…,T-1}); i ∈ {0,…,T-1}, define

selectedMode(kind, selected, i) := { kind if i ∈ selected,; real otherwise }.
-/
def selectedMode (kind : AnswerTableKind) (selected : Finset (Fin T)) (i : Fin T) : AnswerTableKind :=
  if i ∈ selected then kind else .real

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For kind ∈ AnswerTableKind, we have

selectedMode(kind, ∅) = (x₁ ↦ real).
-/
@[simp] theorem selectedMode_empty (kind : AnswerTableKind) :
    selectedMode kind (∅ : Finset (Fin T)) = fun _ => .real := by
  funext i
  simp [selectedMode]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For kind ∈ AnswerTableKind, we have

selectedMode(kind, universe) = (x₁ ↦ kind).
-/
@[simp] theorem selectedMode_univ (kind : AnswerTableKind) :
    selectedMode kind (Finset.univ : Finset (Fin T)) = fun _ => kind := by
  funext i
  simp [selectedMode]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For selected ∈ Finset({0,…,T-1}), we have

signedPositions(signed(selectedMode)(selected)) = selected.
-/
@[simp] theorem signedPositions_selected_signed (selected : Finset (Fin T)) :
    signedPositions (selectedMode .signed selected) = selected := by
  ext i
  simp [signedPositions, selectedMode]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For selected ∈ Finset({0,…,T-1}), we have

signedPositions(original(selectedMode)(selected)) = ∅.
-/
@[simp] theorem signedPositions_selected_original (selected : Finset (Fin T)) :
    signedPositions (selectedMode .original selected) = ∅ := by
  ext i
  by_cases h : i ∈ selected <;> simp [signedPositions, selectedMode, h]

/-- Erasing a selected gate changes exactly that gate's kind. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For kind ∈ AnswerTableKind; selected ∈ Finset({0,…,T-1}); i, j ∈ {0,…,T-1}, assume j ≠ i. Then

selectedMode(kind, selected, j) = selectedMode(kind, selected.erase(i), j).
-/
theorem selectedMode_erase_away (kind : AnswerTableKind) (selected : Finset (Fin T))
    (i j : Fin T) (hne : j ≠ i) :
    selectedMode kind selected j = selectedMode kind (selected.erase i) j := by
  simp [selectedMode, Finset.mem_erase, hne]

/-- EnergyCompression signed-set switch in the concrete network view. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; network ∈ ScopedTables(E = E, A = A, scope, B); wireDistribution ∈ W → 𝒟(E); selected ∈ Finset({0,…,T-1}); i ∈ {0,…,T-1}; η ∈ ℝ; observe ∈ Answers(A, T) × (W → E) → V, assume E ≠ ∅; V is finite; 0 ≤ B; i ∈ selected; Nonempty(scope(i)); 0 ≤ η; ∀ outside ∈ {w | w ∉ scope(i)} → E, ∀ history, a, 𝔼_(inside ← independentDistribution(((w ∈ {w | w ∈ scope(i)} ↦ wireDistribution(w))))) [|network.signed(i, history, joinScope(scope(i), inside, outside), a) - network.real(i, history, joinScope(scope(i), inside, outside), a)|] ≤ η. Then

variationNorm(((v ↦ network.view(wireDistribution, signed(selectedMode)(selected), observe, v) - network.view(wireDistribution, signed(selectedMode)(selected.erase(i)), observe, v)))) ≤ (|A|)^(|neighborhood(scope, i)|) · B^(|selected.erase(i)|) · η.
-/
theorem view_signed_erase [Nonempty E] {V : Type*} [Fintype V]
    (network : ScopedTables (E := E) (A := A) scope B) (hB : 0 ≤ B)
    (wireDistribution : W → FiniteDistribution E) (selected : Finset (Fin T)) (i : Fin T) (hi : i ∈ selected)
    (hscope : (scope i).Nonempty) (η : ℝ) (hη : 0 ≤ η)
    (herror : ∀ outside : {w // w ∉ scope i} → E, ∀ history a,
      (independentDistribution (fun w : {w // w ∈ scope i} => wireDistribution w)).expect (fun inside =>
        |network.signed i history (joinScope (scope i) inside outside) a -
          network.real i history (joinScope (scope i) inside outside) a|) ≤ η)
    (observe : Answers A T × (W → E) → V) :
    variationNorm (fun v => network.view wireDistribution (selectedMode .signed selected) observe v -
      network.view wireDistribution (selectedMode .signed (selected.erase i)) observe v) ≤
      (Fintype.card A : ℝ) ^ (neighborhood scope i).card * B ^ (selected.erase i).card * η := by
  have h := network.view_gate_switch hB wireDistribution (selectedMode .signed selected)
    (selectedMode .signed (selected.erase i)) i hscope (selectedMode_erase_away _ _ i)
    η hη (by simpa [selectedMode, hi, choose] using herror) observe
  simpa only [signedPositions_selected_signed, touching_gate_eq_neighborhood] using h

/-- Replacing all original answer tables by their retained real answer tables costs one local truncation estimate per gate. No signed budget is charged. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; network ∈ ScopedTables(E = E, A = A, scope, B); wireDistribution ∈ W → 𝒟(E); r ∈ ℕ; β ∈ ℝ; observe ∈ Answers(A, T) × (W → E) → V, assume E ≠ ∅; A ≠ ∅; V is finite; 0 ≤ B; ∀ i, Nonempty(scope(i)); ∀ i, |neighborhood(scope, i)| ≤ r; 0 ≤ β; ∀ i, ∀ outside ∈ {w | w ∉ scope(i)} → E, ∀ history, a, 𝔼_(inside ← independentDistribution(((w ∈ {w | w ∈ scope(i)} ↦ wireDistribution(w))))) [|network.original(i, history, joinScope(scope(i), inside, outside), a) - network.real(i, history, joinScope(scope(i), inside, outside), a)|] ≤ β. Then

variationNorm(((v ↦ network.view(wireDistribution, ((x₁ ↦ original)), observe, v) - network.view(wireDistribution, ((x₁ ↦ real)), observe, v)))) ≤ T · ((|A|)ʳ · β).
-/
theorem view_truncation [Nonempty E] [Nonempty A] {V : Type*} [Fintype V]
    (network : ScopedTables (E := E) (A := A) scope B) (hB : 0 ≤ B)
    (wireDistribution : W → FiniteDistribution E) (r : ℕ) (hscope : ∀ i, (scope i).Nonempty)
    (hwidth : ∀ i, (neighborhood scope i).card ≤ r) (β : ℝ) (hβ : 0 ≤ β)
    (herror : ∀ i, ∀ outside : {w // w ∉ scope i} → E, ∀ history a,
      (independentDistribution (fun w : {w // w ∈ scope i} => wireDistribution w)).expect (fun inside =>
        |network.original i history (joinScope (scope i) inside outside) a -
          network.real i history (joinScope (scope i) inside outside) a|) ≤ β)
    (observe : Answers A T × (W → E) → V) :
    variationNorm (fun v => network.view wireDistribution (fun _ => .original) observe v -
      network.view wireDistribution (fun _ => .real) observe v) ≤
      (T : ℝ) * ((Fintype.card A : ℝ) ^ r * β) := by
  have hcard : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hswitch (selected : Finset (Fin T)) (i : Fin T) (hi : i ∈ selected) :
      variationNorm (fun v => network.view wireDistribution (selectedMode .original selected) observe v -
        network.view wireDistribution (selectedMode .original (selected.erase i)) observe v) ≤
        (Fintype.card A : ℝ) ^ r * β := by
    have h := network.view_gate_switch hB wireDistribution (selectedMode .original selected)
      (selectedMode .original (selected.erase i)) i (hscope i)
      (selectedMode_erase_away _ _ i) β hβ
      (by simpa [selectedMode, hi, choose] using herror i) observe
    simp only [signedPositions_selected_original, Finset.erase_empty, Finset.card_empty,
      pow_zero, mul_one, touching_gate_eq_neighborhood] at h
    exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hcard (hwidth i)) hβ)
  have h := signed_set_inclusion_bound
    (fun selected => network.view wireDistribution (selectedMode .original selected) observe)
    ∅ Finset.univ ((Fintype.card A : ℝ) ^ r * β) (Finset.empty_subset _)
    (fun selected _ _ i hi _ => hswitch selected i hi)
  simpa only [Finset.sdiff_empty, Finset.card_univ, Fintype.card_fin,
    selectedMode_empty, selectedMode_univ, variationNorm_sub_comm] using h

/-- Normalization only needs to hold at histories reachable before the final query; arbitrary longer histories are irrelevant. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X a set; answerTable ∈ A* → X → A → ℝ; n ∈ ℕ; history ∈ A*; x ∈ X, assume ∀ history, (|history| < T) ⇒ ∀ x, (∑ₐ (answerTable(history, x, a))) = 1; |history| + n ≤ T. Then

(∑ₕ (weight(fromTables(answerTable, ((x₁, x₂ ↦ 1)), n, history))(h, x))) = 1.
-/
theorem fromTables_weight_total_bounded {X : Type*}
    (answerTable : List A → X → A → ℝ)
    (htotal : ∀ history, history.length < T → ∀ x, (∑ a, answerTable history x a) = 1)
    (n : ℕ) (history : List A) (hlen : history.length + n ≤ T) (x : X) :
    (∑ h, (fromTables answerTable (fun _ _ => 1) n history).weight h x) = 1 := by
  induction n generalizing history with
  | zero => simp [fromTables, weight, Answers]
  | succ n ih =>
      have hnext (a : A) : (history ++ [a]).length + n ≤ T := by
        simp only [List.length_append, List.length_singleton]
        omega
      simp only [fromTables, weight, Answers, Fintype.sum_prod_type, ← Finset.mul_sum,
        ih _ (hnext _), mul_one]
      exact htotal history (by omega) x

/-- The complete canonical answer history, conditional on all wire encodings. -/
/- Mathematical definition (normal notation): Conditional on all wire encodings, use the original normalized answer probabilities at every gate. The probability of a complete answer history is their chronological product, giving the canonical transcript distribution. -/
noncomputable def canonicalHistory
    (network : ScopedTables (E := E) (A := A) scope B) (encoding : W → E) :
    FiniteDistribution (Answers A T) where
  weight h := (network.process (fun _ => .original)).weight h encoding
  nonneg h := fromTables_weight_nonneg _ (by
    intro history enc a
    by_cases h : history.length < T
    · simpa [answerTable, h, choose] using network.original_nonneg ⟨history.length, h⟩ history enc a
    · simp [answerTable, h]) T [] h encoding
  total := fromTables_weight_total_bounded (T := T) _ (by
    intro history h enc
    simpa [answerTable, h, choose] using network.original_total ⟨history.length, h⟩ history enc)
    T [] (by simp) encoding

/-- Sample all wire encodings, run the canonical adaptive answer tables, and disclose the designated function of history and boundary encodings. -/
/-
Mathematical definition (normal notation): For V a set; network ∈ ScopedTables(E = E, A = A, scope, B); wireDistribution ∈ W → 𝒟(E); observe ∈ Answers(A, T) × (W → E) → V, assume V is finite. define

canonicalDistribution(network, wireDistribution, observe) := (((eh ↦ observe(((eh)₂, (eh)₁))))_*joint(independentDistribution(wireDistribution))(network.canonicalHistory)) .
-/
noncomputable def canonicalDistribution {V : Type*} [Fintype V]
    (network : ScopedTables (E := E) (A := A) scope B)
    (wireDistribution : W → FiniteDistribution E) (observe : Answers A T × (W → E) → V) : FiniteDistribution V :=
  ((independentDistribution wireDistribution).joint network.canonicalHistory).map (fun eh => observe (eh.2, eh.1))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; network ∈ ScopedTables(E = E, A = A, scope, B); wireDistribution ∈ W → 𝒟(E); observe ∈ Answers(A, T) × (W → E) → V, assume V is finite. Then

weight(network.canonicalDistribution(wireDistribution, observe)) = network.view(wireDistribution, ((x₁ ↦ original)), observe).
-/
theorem canonicalDistribution_weight {V : Type*} [Fintype V]
    (network : ScopedTables (E := E) (A := A) scope B)
    (wireDistribution : W → FiniteDistribution E) (observe : Answers A T × (W → E) → V) :
    (network.canonicalDistribution wireDistribution observe).weight =
      network.view wireDistribution (fun _ => .original) observe := by
  funext v
  simp only [canonicalDistribution, FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.joint, canonicalHistory,
    view, observedWeight, Fintype.sum_prod_type]
  exact Finset.sum_comm

end ScopedTables

end CircuitCompiler.Composition
