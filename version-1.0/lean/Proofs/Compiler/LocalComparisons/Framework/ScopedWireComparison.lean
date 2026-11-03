import Proofs.Compiler.LocalComparisons.Framework.ScopedNetwork



/-!
# One-wire comparison for the concrete signed network view
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler.Composition

open Refresh LabelPaths ErrorProcess

variable {W E A : Type*} [Fintype W] [DecidableEq W] [Fintype E] [Fintype A]
  {T : ℕ}

/-- Insert the selected encoding among all fixed remaining wire encodings. -/
/-
Mathematical definition (normal notation): For wire ∈ W; encoding ∈ E; outside ∈ {w | w ≠ wire} → E, define

joinWire(wire, encoding, outside) := (Equiv.piSplitAt(wire, ((x₁ ↦ E))))⁻¹((encoding, outside)).
-/
def joinWire (wire : W) (encoding : E) (outside : {w // w ≠ wire} → E) : W → E :=
  (Equiv.piSplitAt wire (fun _ => E)).symm (encoding, outside)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For wire ∈ W; encoding ∈ E; outside ∈ {w | w ≠ wire} → E, we have

joinWire(wire, encoding, outside, wire) = encoding.
-/
theorem joinWire_at (wire : W) (encoding : E) (outside : {w // w ≠ wire} → E) :
    joinWire wire encoding outside wire = encoding := by
  simp [joinWire, Equiv.piSplitAt]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Insert the changed-wire value x into the outside assignment at wire w₀. At every other wire w ≠ w₀, the joined assignment is unchanged:

joinWire(w₀,x,outside)(w) = outside(w).

The domain of the outside assignment is the set of wires different from w₀; the proof of w ≠ w₀ merely establishes membership in that domain.
-/
theorem joinWire_away (wire w : W) (encoding : E) (outside : {w // w ≠ wire} → E)
    (hne : w ≠ wire) : joinWire wire encoding outside w = outside ⟨w, hne⟩ := by
  simp [joinWire, Equiv.piSplitAt, hne]

/-- The disclosed view does not expose a selected internal wire directly. -/
/-
Mathematical definition (normal notation): For V a set; wire ∈ W; observe ∈ Answers(A, T) × (W → E) → V, define

WireBlind(wire, observe) := ∀ history, first, second, (∀ w, (w ≠ wire) ⇒ first(w) = second(w)) → observe((history, first)) = observe((history, second)).
-/
def WireBlind {V : Type*} (wire : W) (observe : Answers A T × (W → E) → V) : Prop :=
  ∀ history first second, (∀ w, w ≠ wire → first w = second w) →
    observe (history, first) = observe (history, second)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; boundary ∈ Finset(W); wire ∈ W; observe ∈ Answers(A, T) × ({w | w ∈ boundary} → E) → V, assume wire ∉ boundary. Then

WireBlind(wire, ((hx ↦ observe(((hx)₁, (w ↦ (hx)₂(w))))))).
-/
theorem boundary_observation_wireBlind {V : Type*}
    (boundary : Finset W) (wire : W) (hwire : wire ∉ boundary)
    (observe : Answers A T × ({w // w ∈ boundary} → E) → V) :
    WireBlind wire (fun hx => observe (hx.1, fun w => hx.2 w)) := by
  intro history first second heq
  apply congrArg observe
  refine Prod.ext (by rfl) ?_
  funext w
  exact heq w (fun h => hwire (h ▸ w.property))

namespace ScopedTables

variable {scope : Fin T → Finset W} {B : ℝ}

/-- Decompose the actual signed view into one selected wire and its independent complement, without altering the observation map. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; network ∈ ScopedTables(E = E, A = A, scope, B); wireDistribution ∈ W → 𝒟(E); mode ∈ {0,…,T-1} → AnswerTableKind; wire ∈ W; observe ∈ Answers(A, T) × (W → E) → V, assume V is finite. Then

network.view(wireDistribution, mode, observe) = (v ↦ 𝔼_(outside ← independentDistribution(((w ∈ {w | w ≠ wire} ↦ wireDistribution(w))))) [observedWeight(wireDistribution(wire), precompose(((encoding ↦ joinWire(wire, encoding, outside))), network.process(mode)), ((hx ↦ observe(((hx)₁, joinWire(wire, (hx)₂, outside))))), v)]).
-/
theorem view_wire {V : Type*} [Fintype V]
    (network : ScopedTables (E := E) (A := A) scope B)
    (wireDistribution : W → FiniteDistribution E) (mode : Fin T → AnswerTableKind)
    (wire : W) (observe : Answers A T × (W → E) → V) :
    network.view wireDistribution mode observe = fun v =>
      (independentDistribution (fun w : {w // w ≠ wire} => wireDistribution w)).expect (fun outside =>
        observedWeight (wireDistribution wire)
          (precompose (fun encoding => joinWire wire encoding outside) (network.process mode))
          (fun hx => observe (hx.1, joinWire wire hx.2 outside)) v) := by
  unfold view
  rw [independentDistribution_splitAt_reverse wireDistribution wire]
  rw [observedWeight_map, observedWeight_prod]
  funext v
  apply congrArg (fun f => (independentDistribution (fun w : {w // w ≠ wire} => wireDistribution w)).expect f)
  funext outside
  simp only [observedWeight_eq_expect, weight_precompose, joinWire]

/-- At a nonincident gate, fixing the complementary wire encodings removes all dependence on the selected wire. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For network ∈ ScopedTables(E = E, A = A, scope, B); wire ∈ W; outside ∈ {w | w ≠ wire} → E; kind ∈ AnswerTableKind; i ∈ {0,…,T-1}; history ∈ A*, assume E ≠ ∅; i ∉ incident(scope, wire). Then

∃ fixed ∈ A → ℝ, (∀ encoding, a, network.choose(kind, i, history, joinWire(wire, encoding, outside), a) = fixed(a)) ∧ (∑ₐ (|fixed(a)|)) ≤ kindBudget(B, kind).
-/
theorem choose_independent_wire [Nonempty E]
    (network : ScopedTables (E := E) (A := A) scope B)
    (wire : W) (outside : {w // w ≠ wire} → E)
    (kind : AnswerTableKind) (i : Fin T) (history : List A) (hi : i ∉ incident scope wire) :
    ∃ fixed : A → ℝ, (∀ encoding a,
      network.choose kind i history (joinWire wire encoding outside) a = fixed a) ∧
      (∑ a, |fixed a|) ≤ kindBudget B kind := by
  let base : E := Classical.choice (inferInstance : Nonempty E)
  refine ⟨fun a => network.choose kind i history (joinWire wire base outside) a, ?_,
    network.choose_budget kind i history _⟩
  intro encoding a
  apply network.choose_scoped kind i history a
  intro w hw
  have hne : w ≠ wire := by
    intro heq
    subst w
    exact hi ((mem_incident scope wire i).mpr hw)
  rw [joinWire_away wire w encoding outside hne, joinWire_away wire w base outside hne]

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- A global left/right factorization restricts to the selected wire when the other complete encodings are fixed. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For network ∈ ScopedTables(E = X × Y, A = A, scope, B); wire ∈ W; outside ∈ {w | w ≠ wire} → X × Y; i ∈ {0,…,T-1}; history ∈ A*; a ∈ A, assume BoundedFactorization(((left ∈ W → X, right ∈ W → Y ↦ network.signed(i, history, ((w ↦ (left(w), right(w)))), a))), B) ≠ ∅. Then

BoundedFactorization(((x, y ↦ network.signed(i, history, joinWire(wire, (x, y), outside), a))), B) ≠ ∅.
-/
theorem signed_wire_factorization
    (network : ScopedTables (E := X × Y) (A := A) scope B)
    (wire : W) (outside : {w // w ≠ wire} → X × Y)
    (i : Fin T) (history : List A) (a : A)
    (hfactor : Nonempty (BoundedFactorization
      (fun (left : W → X) (right : W → Y) => network.signed i history
        (fun w => (left w, right w)) a) B)) :
    Nonempty (BoundedFactorization
      (fun x y => network.signed i history (joinWire wire (x, y) outside) a) B) := by
  obtain ⟨factor⟩ := hfactor
  let leftMap (x : X) : W → X := joinWire wire x (fun w => (outside w).1)
  let rightMap (y : Y) : W → Y := joinWire wire y (fun w => (outside w).2)
  have hjoin (x : X) (y : Y) :
      (fun w => (leftMap x w, rightMap y w)) = joinWire wire (x, y) outside := by
    funext w
    by_cases h : w = wire
    · subst w
      simp [leftMap, rightMap, joinWire_at]
    · simp [leftMap, rightMap, joinWire_away, h]
  simpa only [hjoin] using Nonempty.intro (factor.restrict leftMap rightMap)

/-- Every incident gate is signed; all other gates have a fixed answer table once the complementary encodings are fixed. These facts derive the complete adaptive tree's factorization premise. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For network ∈ ScopedTables(E = X × Y, A = A, scope, B); mode ∈ {0,…,T-1} → AnswerTableKind; wire ∈ W; outside ∈ {w | w ≠ wire} → X × Y, assume X ≠ ∅; Y ≠ ∅; ∀ i ∈ incident(scope, wire), mode(i) = signed; ∀ i, history, a, BoundedFactorization(((x, y ↦ network.signed(i, history, joinWire(wire, (x, y), outside), a))), B) ≠ ∅. Then

FactorControlled(precompose(((xy ↦ joinWire(wire, xy, outside))), network.process(mode)))(((i ↦ { B if i ∈ signedPositions(mode),; 1 otherwise })), ((i ↦ decide((i ∈ incident(scope, wire)))))).
-/
theorem process_factorControlled_wire [Nonempty X] [Nonempty Y]
    (network : ScopedTables (E := X × Y) (A := A) scope B)
    (mode : Fin T → AnswerTableKind) (wire : W)
    (hincident : ∀ i ∈ incident scope wire, mode i = .signed)
    (outside : {w // w ≠ wire} → X × Y)
    (hfactor : ∀ i history a, Nonempty (BoundedFactorization
      (fun x y => network.signed i history (joinWire wire (x, y) outside) a) B)) :
    (precompose (fun xy => joinWire wire xy outside) (network.process mode)).FactorControlled
      (fun i => if i ∈ signedPositions mode then B else 1)
      (fun i => decide (i ∈ incident scope wire)) := by
  have hf (history : List A) (hlocal : timeLocal (incident scope wire) history.length = true)
      (a : A) : Nonempty (BoundedFactorization
      (fun x y => network.answerTable mode history (joinWire wire (x, y) outside) a)
      (timeBudget mode B history.length)) := by
    by_cases h : history.length < T
    · have hi : (⟨history.length, h⟩ : Fin T) ∈ incident scope wire := by
        simpa [timeLocal, h] using hlocal
      simpa [answerTable, timeBudget, h, hincident _ hi, choose, kindBudget] using
        hfactor ⟨history.length, h⟩ history a
    · simp [timeLocal, h] at hlocal
  have hl (history : List A) (hlocal : timeLocal (incident scope wire) history.length = false) :
      ∃ fixed : A → ℝ, (∀ xy a,
        network.answerTable mode history (joinWire wire xy outside) a = fixed a) ∧
        (∑ a, |fixed a|) ≤ timeBudget mode B history.length := by
    by_cases h : history.length < T
    · have hi : (⟨history.length, h⟩ : Fin T) ∉ incident scope wire := by
        simpa [timeLocal, h] using hlocal
      simpa only [answerTable, timeBudget, dif_pos h] using
        network.choose_independent_wire wire outside (mode ⟨history.length, h⟩)
          ⟨history.length, h⟩ history hi
    · exact ⟨fun _ => 0, by intros; simp [answerTable, h], by simp [timeBudget, h]⟩
  have h := fromTables_factorControlled
    (fun history xy => network.answerTable mode history (joinWire wire xy outside))
    (timeBudget mode B) (timeLocal (incident scope wire)) hf hl T []
  simpa [process, precompose_fromTables, timeBudget, timeLocal, kindBudget, signedPositions] using h

/-- The actual network view changes by the one-wire discrepancy estimate. The observation can disclose arbitrary fixed boundary encodings. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; network ∈ ScopedTables(E = X × Y, A = A, scope, B); firstLaw, secondLaw ∈ W → 𝒟((X × Y)); mode ∈ {0,…,T-1} → AnswerTableKind; wire ∈ W; L ∈ 𝒟(X); R ∈ 𝒟(Y); δ ∈ ℝ; observe ∈ Answers(A, T) × (W → X × Y) → V, assume X ≠ ∅; Y ≠ ∅; V is finite; 0 ≤ B; ∀ w, (w ≠ wire) ⇒ firstLaw(w) = secondLaw(w); ∀ i ∈ incident(scope, wire), mode(i) = signed; 0 ≤ δ; ∀ a ∈ X → ℝ, ∀ b ∈ Y → ℝ, |𝔼_(xy ← firstLaw(wire)) [a((xy)₁) · b((xy)₂)] - 𝔼_(xy ← secondLaw(wire)) [a((xy)₁) · b((xy)₂)]| ≤ δ · √(𝔼_(x ← L) [(a(x))²]) · √(𝔼_(y ← R) [(b(y))²]); ∀ outside ∈ {w | w ≠ wire} → X × Y, ∀ i, history, a, BoundedFactorization(((x, y ↦ network.signed(i, history, joinWire(wire, (x, y), outside), a))), B) ≠ ∅; WireBlind(wire, observe). Then

variationNorm(((v ↦ network.view(firstLaw, mode, observe, v) - network.view(secondLaw, mode, observe, v)))) ≤ δ · (|A|)^(|incident(scope, wire)|) · B^(|signedPositions(mode)|).
-/
theorem view_one_wire [Nonempty X] [Nonempty Y] {V : Type*} [Fintype V]
    (network : ScopedTables (E := X × Y) (A := A) scope B) (hB : 0 ≤ B)
    (firstLaw secondLaw : W → FiniteDistribution (X × Y)) (mode : Fin T → AnswerTableKind) (wire : W)
    (hother : ∀ w, w ≠ wire → firstLaw w = secondLaw w)
    (hincident : ∀ i ∈ incident scope wire, mode i = .signed)
    (L : FiniteDistribution X) (R : FiniteDistribution Y) (δ : ℝ) (hδ : 0 ≤ δ)
    (hscalar : ∀ a : X → ℝ, ∀ b : Y → ℝ,
      |(firstLaw wire).expect (fun xy => a xy.1 * b xy.2) -
        (secondLaw wire).expect (fun xy => a xy.1 * b xy.2)| ≤
        δ * Real.sqrt (L.expect (fun x => a x ^ 2)) * Real.sqrt (R.expect (fun y => b y ^ 2)))
    (hfactor : ∀ outside : {w // w ≠ wire} → X × Y, ∀ i history a,
      Nonempty (BoundedFactorization
        (fun x y => network.signed i history (joinWire wire (x, y) outside) a) B))
    (observe : Answers A T × (W → X × Y) → V) (hblind : WireBlind wire observe) :
    variationNorm (fun v => network.view firstLaw mode observe v - network.view secondLaw mode observe v) ≤
      δ * (Fintype.card A : ℝ) ^ (incident scope wire).card * B ^ (signedPositions mode).card := by
  let base : X × Y := Classical.choice (inferInstance : Nonempty (X × Y))
  have hobs (outside : {w // w ≠ wire} → X × Y) (hx : Answers A T × (X × Y)) :
      observe (hx.1, joinWire wire hx.2 outside) = observe (hx.1, joinWire wire base outside) := by
    apply hblind
    intro w hw
    rw [joinWire_away wire w hx.2 outside hw, joinWire_away wire w base outside hw]
  have hconditional (outside : {w // w ≠ wire} → X × Y) :
      variationNorm (fun v =>
        observedWeight (firstLaw wire)
          (precompose (fun xy => joinWire wire xy outside) (network.process mode))
          (fun hx => observe (hx.1, joinWire wire hx.2 outside)) v -
        observedWeight (secondLaw wire)
          (precompose (fun xy => joinWire wire xy outside) (network.process mode))
          (fun hx => observe (hx.1, joinWire wire hx.2 outside)) v) ≤
        δ * (Fintype.card A : ℝ) ^ (incident scope wire).card * B ^ (signedPositions mode).card := by
    have hp := observedWeight_congr_observe (firstLaw wire)
      (precompose (fun xy => joinWire wire xy outside) (network.process mode))
      (fun hx => observe (hx.1, joinWire wire hx.2 outside))
      (fun hx => observe (hx.1, joinWire wire base outside)) (hobs outside)
    have hq := observedWeight_congr_observe (secondLaw wire)
      (precompose (fun xy => joinWire wire xy outside) (network.process mode))
      (fun hx => observe (hx.1, joinWire wire hx.2 outside))
      (fun hx => observe (hx.1, joinWire wire base outside)) (hobs outside)
    rw [hp, hq]
    rw [observedWeight_history (firstLaw wire)
      (precompose (fun xy => joinWire wire xy outside) (network.process mode))
      (fun history => observe (history, joinWire wire base outside)),
      observedWeight_history (secondLaw wire)
      (precompose (fun xy => joinWire wire xy outside) (network.process mode))
      (fun history => observe (history, joinWire wire base outside))]
    have h := one_wire_observed_bound (firstLaw wire) (secondLaw wire) L R δ hδ hscalar
      (precompose (fun xy => joinWire wire xy outside) (network.process mode))
      (fun i => if i ∈ signedPositions mode then B else 1)
      (fun i => decide (i ∈ incident scope wire))
      (fun i => by split_ifs <;> positivity)
      (network.process_factorControlled_wire mode wire hincident outside (hfactor outside))
      (fun history => observe (history, joinWire wire base outside))
    simpa only [observedWeight_history, localCount_mem, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const,
      Finset.sum_sub_distrib, sub_mul] using h
  have houtside : (fun w : {w // w ≠ wire} => firstLaw w) =
      (fun w : {w // w ≠ wire} => secondLaw w) := funext (fun w => hother w w.property)
  rw [network.view_wire firstLaw mode wire observe, network.view_wire secondLaw mode wire observe,
    ← houtside]
  have h := variationNorm_average_le
    (independentDistribution (fun w : {w // w ≠ wire} => firstLaw w)) _ _ hconditional
  simpa only [MatrixRefresh.expect_sub] using h

end ScopedTables

end CircuitCompiler.Composition
