import Mathlib.Data.Finset.Card
import Mathlib.Tactic



/-!
# Local validity and direct circuit-label paths

These lemmas use arbitrary finite gate scopes and arbitrary local gate predicates. They apply to product gates and complemented product gates alike. The direct path proves the general circuit bound; the sharper formula and depth-first constructions are not asserted here.
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler.LabelPaths

variable {W G F : Type*} [DecidableEq W] [Fintype G] [DecidableEq G]

/-- Adjacent labelings agree outside the selected wire. The selected label may also remain unchanged, allowing harmless repetitions in a path. -/
/-
Mathematical definition (normal notation): For s, t ∈ W → F; w ∈ W, define

DiffersOnly(s, t, w) := ∀ v, (v ≠ w) ⇒ s(v) = t(v).
-/
def DiffersOnly (s t : W → F) (w : W) : Prop := ∀ v, v ≠ w → s v = t v

/-- Gates whose validity condition may depend on a given wire. -/
/-
Mathematical definition (normal notation): For scope ∈ G → Finset(W); w ∈ W, define

incident(scope, w) := Finset.univ.filter(((i ↦ w ∈ scope(i)))).
-/
def incident (scope : G → Finset W) (w : W) : Finset G :=
  Finset.univ.filter (fun i => w ∈ scope i)

/-- Gates that are invalid under the supplied complete labeling. -/
/- Mathematical definition (normal notation): For a complete wire labeling s, define its cheating gates by defects(s) = {i:the validity equation at gate i fails under s}. -/
noncomputable def defects (valid : (W → F) → G → Prop) (s : W → F) : Finset G := by
  classical
  exact Finset.univ.filter (fun i => ¬ valid s i)

/-- A gate predicate reads only the labels in its scope. -/
/-
Mathematical definition (normal notation): For scope ∈ G → Finset(W); valid ∈ (W → F) → G → Prop, define

IsLocal(scope, valid) := ∀ s, t, i, (∀ w ∈ scope(i), s(w) = t(w)) → (valid(s, i) ⇔ valid(t, i)).
-/
def IsLocal (scope : G → Finset W) (valid : (W → F) → G → Prop) : Prop :=
  ∀ s t i, (∀ w ∈ scope i, s w = t w) → (valid s i ↔ valid t i)

omit [DecidableEq G] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For scope ∈ G → Finset(W); w ∈ W; i ∈ G, we have

i ∈ incident(scope, w) ⇔ w ∈ scope(i).
-/
@[simp] theorem mem_incident (scope : G → Finset W) (w : W) (i : G) :
    i ∈ incident scope w ↔ w ∈ scope i := by
  simp [incident]

omit [DecidableEq W] [DecidableEq G] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For valid ∈ (W → F) → G → Prop; s ∈ W → F; i ∈ G, we have

i ∈ defects(valid, s) ⇔ ¬ (valid(s, i)).
-/
@[simp] theorem mem_defects (valid : (W → F) → G → Prop) (s : W → F) (i : G) :
    i ∈ defects valid s ↔ ¬ valid s i := by
  classical simp [defects]

/-- Changing one wire cannot affect validity at a nonincident gate. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For scope ∈ G → Finset(W); valid ∈ (W → F) → G → Prop; s, t ∈ W → F; w ∈ W; i ∈ G, assume IsLocal(scope, valid); DiffersOnly(s, t, w); i ∉ incident(scope, w). Then

valid(s, i) ⇔ valid(t, i).
-/
theorem validity_unchanged (scope : G → Finset W) (valid : (W → F) → G → Prop)
    (hlocal : IsLocal scope valid) {s t : W → F} {w : W}
    (hchange : DiffersOnly s t w) {i : G} (hi : i ∉ incident scope w) :
    valid s i ↔ valid t i := by
  apply hlocal s t i
  intro v hv
  apply hchange v
  intro hvw
  subst v
  exact hi (by simpa using hv)

/-- The signed set for a one-wire step adds only incident gates to either endpoint's defect set. This bounds the number of required gate switches. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For scope ∈ G → Finset(W); valid ∈ (W → F) → G → Prop; s, t ∈ W → F; w ∈ W, assume IsLocal(scope, valid); DiffersOnly(s, t, w). Then

((defects(valid, s) ∪ defects(valid, t) ∪ incident(scope, w)) ∖ defects(valid, s)) ⊆ incident(scope, w).
-/
theorem added_gates_subset_incident
    (scope : G → Finset W) (valid : (W → F) → G → Prop)
    (hlocal : IsLocal scope valid) {s t : W → F} {w : W}
    (hchange : DiffersOnly s t w) :
    ((defects valid s ∪ defects valid t ∪ incident scope w) \ defects valid s)
      ⊆ incident scope w := by
  classical
  intro i hi
  by_contra hnot
  have hvalid : valid s i := by simpa using (Finset.mem_sdiff.mp hi).2
  have hvalid' := (validity_unchanged scope valid hlocal hchange hnot).mp hvalid
  rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hi).1 with hdef | hinc
  · rcases Finset.mem_union.mp hdef with hs | ht
    · exact (Finset.mem_sdiff.mp hi).2 hs
    · exact (mem_defects valid t i).mp ht hvalid'
  · exact hnot hinc

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For scope ∈ G → Finset(W); valid ∈ (W → F) → G → Prop; s, t ∈ W → F; w ∈ W, assume IsLocal(scope, valid); DiffersOnly(s, t, w). Then

|((defects(valid, s) ∪ defects(valid, t) ∪ incident(scope, w)) ∖ defects(valid, s))| ≤ |incident(scope, w)|.
-/
theorem added_gates_card_le
    (scope : G → Finset W) (valid : (W → F) → G → Prop)
    (hlocal : IsLocal scope valid) {s t : W → F} {w : W}
    (hchange : DiffersOnly s t w) :
    ((defects valid s ∪ defects valid t ∪ incident scope w) \ defects valid s).card
      ≤ (incident scope w).card :=
  Finset.card_le_card (added_gates_subset_incident scope valid hlocal hchange)

/-- A gate's neighborhood is the union of the incidence sets of its ports. -/
/-
Mathematical definition (normal notation): For scope ∈ G → Finset(W); i ∈ G, define

neighborhood(scope, i) := biUnion(scope(i))(incident(scope)) .
-/
def neighborhood (scope : G → Finset W) (i : G) : Finset G :=
  (scope i).biUnion (incident scope)

/-- Only earlier gates can affect a cutoff chosen from the incoming history. -/
/-
Mathematical definition (normal notation): For T ∈ ℕ; scope ∈ {0,…,T-1} → Finset(W); i ∈ {0,…,T-1}, define

earlierNeighborhood(scope, i) := filter(neighborhood(scope, i))(((j ↦ j < i))).
-/
def earlierNeighborhood {T : ℕ} (scope : Fin T → Finset W) (i : Fin T) :
    Finset (Fin T) :=
  (neighborhood scope i).filter (fun j => j < i)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For T ∈ ℕ; scope ∈ {0,…,T-1} → Finset(W); i, j ∈ {0,…,T-1}, we have

j ∈ earlierNeighborhood(scope, i) ⇔ j < i ∧ ∃ w ∈ scope(i), w ∈ scope(j).
-/
@[simp] theorem mem_earlierNeighborhood {T : ℕ} (scope : Fin T → Finset W)
    (i j : Fin T) :
    j ∈ earlierNeighborhood scope i ↔ j < i ∧ ∃ w ∈ scope i, w ∈ scope j := by
  simp only [earlierNeighborhood, Finset.mem_filter, neighborhood,
    Finset.mem_biUnion, mem_incident]
  tauto

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For scope ∈ G → Finset(W); i ∈ G; d ∈ ℕ, assume ∀ w, |incident(scope, w)| ≤ d. Then

|neighborhood(scope, i)| ≤ |scope(i)| · d.
-/
theorem neighborhood_card_le (scope : G → Finset W) (i : G) (d : ℕ)
    (hdegree : ∀ w, (incident scope w).card ≤ d) :
    (neighborhood scope i).card ≤ (scope i).card * d := by
  unfold neighborhood
  calc
    ((scope i).biUnion (incident scope)).card ≤
        ∑ w ∈ scope i, (incident scope w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ scope i, d := Finset.sum_le_sum (fun w _ => hdegree w)
    _ = (scope i).card * d := by simp

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For scope ∈ G → Finset(W); i ∈ G, assume |scope(i)| ≤ 3; ∀ w, |incident(scope, w)| ≤ 3. Then

|neighborhood(scope, i)| ≤ 9.
-/
theorem fanout_two_neighborhood_bound (scope : G → Finset W) (i : G)
    (hports : (scope i).card ≤ 3) (hdegree : ∀ w, (incident scope w).card ≤ 3) :
    (neighborhood scope i).card ≤ 9 := by
  have h := neighborhood_card_le scope i 3 hdegree
  omega

/-- Directly update every active wire to its target label. The resulting path has at most one update per active wire, and never touches a boundary wire. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For active, boundary ∈ Finset(W); s, t ∈ W → F, assume Disjoint(active, boundary); ∀ w, (w ∉ active) ⇒ s(w) = t(w). Then

∃ L ∈ ℕ, label ∈ ℕ → W → F, L ≤ |active| ∧ label(0) = s ∧ label(L) = t ∧ ∀ j, <, L, ∃ w ∈ active, w ∉ boundary ∧ DiffersOnly(label(j), label((j + 1)), w).
-/
theorem exists_direct_path (active boundary : Finset W)
    (hdisjoint : Disjoint active boundary) (s t : W → F)
    (houtside : ∀ w, w ∉ active → s w = t w) :
    ∃ (L : ℕ) (label : ℕ → W → F), L ≤ active.card ∧ label 0 = s ∧ label L = t ∧
      ∀ j < L, ∃ w ∈ active, w ∉ boundary ∧ DiffersOnly (label j) (label (j + 1)) w := by
  classical
  induction active using Finset.induction_on generalizing s with
  | empty =>
      have hst : s = t := funext (fun w => houtside w (by simp))
      refine ⟨0, fun _ => s, by simp, rfl, hst, ?_⟩
      omega
  | @insert w active hw ih =>
      let u := Function.update s w (t w)
      have hdisjoint' : Disjoint active boundary :=
        Finset.disjoint_of_subset_left (Finset.subset_insert w active) hdisjoint
      have houtside' : ∀ v, v ∉ active → u v = t v := by
        intro v hv
        by_cases hvw : v = w
        · subst v; simp [u]
        · simpa [u, Function.update_of_ne hvw] using
            houtside v (by simp [hv, hvw])
      obtain ⟨L, label, hL, hzero, hend, hsteps⟩ := ih hdisjoint' u houtside'
      let path : ℕ → W → F := fun j => if j = 0 then s else label (j - 1)
      refine ⟨L + 1, path, ?_, ?_, ?_, ?_⟩
      · simpa [Finset.card_insert_of_notMem hw] using Nat.add_le_add_right hL 1
      · simp [path]
      · simpa [path] using hend
      · intro j hj
        cases j with
        | zero =>
            refine ⟨w, by simp, ?_, ?_⟩
            · exact fun hwb => Finset.disjoint_left.mp hdisjoint (by simp) hwb
            · intro v hv
              simp [path, hzero, u, Function.update_of_ne hv]
        | succ j =>
            obtain ⟨v, hv, hvb, hchange⟩ := hsteps j (by omega)
            refine ⟨v, Finset.mem_insert_of_mem hv, hvb, ?_⟩
            simpa [path] using hchange

/-- Every signed set in the direct construction contains at most all gates. This is the general-circuit width bound `a ≤ T`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For scope ∈ G → Finset(W); valid ∈ (W → F) → G → Prop; s, t ∈ W → F; w ∈ W, we have

|(defects(valid, s) ∪ defects(valid, t) ∪ incident(scope, w))| ≤ |G|.
-/
theorem step_width_le_card (scope : G → Finset W)
    (valid : (W → F) → G → Prop) (s t : W → F) (w : W) :
    (defects valid s ∪ defects valid t ∪ incident scope w).card ≤ Fintype.card G :=
  Finset.card_le_univ _

/-- Only wires appearing in some gate can influence the gated transcript. -/
/-
Mathematical definition (normal notation): For scope ∈ G → Finset(W), define

activeWires(scope) := Finset.univ.biUnion(scope).
-/
def activeWires (scope : G → Finset W) : Finset W := Finset.univ.biUnion scope

omit [DecidableEq G] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For scope ∈ G → Finset(W), assume ∀ i, |scope(i)| ≤ 3. Then

|activeWires(scope)| ≤ 3 · |G| .
-/
theorem activeWires_card_le (scope : G → Finset W)
    (hports : ∀ i, (scope i).card ≤ 3) :
    (activeWires scope).card ≤ 3 * Fintype.card G := by
  unfold activeWires
  calc
    (Finset.univ.biUnion scope).card ≤ ∑ i, (scope i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : G, 3 := Finset.sum_le_sum (fun i _ => hports i)
    _ = 3 * Fintype.card G := by simp [Nat.mul_comm]

/-- The general circuit path has at most `3T` steps. Disclosed wire labels are fixed, and labels of inactive wires are assumed already identified. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For scope ∈ G → Finset(W); boundary ∈ Finset(W); s, t ∈ W → F, assume ∀ i, |scope(i)| ≤ 3; ∀ w ∈ boundary, s(w) = t(w); ∀ w, (w ∉ activeWires(scope)) ⇒ s(w) = t(w). Then

∃ L ∈ ℕ, label ∈ ℕ → W → F, L ≤ 3 · |G| ∧ label(0) = s ∧ label(L) = t ∧ ∀ j, <, L, ∃ w ∈ activeWires(scope), w ∉ boundary ∧ DiffersOnly(label(j), label((j + 1)), w).
-/
theorem exists_general_circuit_path (scope : G → Finset W)
    (hports : ∀ i, (scope i).card ≤ 3) (boundary : Finset W) (s t : W → F)
    (hboundary : ∀ w ∈ boundary, s w = t w)
    (hinactive : ∀ w, w ∉ activeWires scope → s w = t w) :
    ∃ (L : ℕ) (label : ℕ → W → F), L ≤ 3 * Fintype.card G ∧
      label 0 = s ∧ label L = t ∧
      ∀ j < L, ∃ w ∈ activeWires scope, w ∉ boundary ∧
        DiffersOnly (label j) (label (j + 1)) w := by
  classical
  have houtside : ∀ w, w ∉ activeWires scope \ boundary → s w = t w := by
    intro w hw
    by_cases hb : w ∈ boundary
    · exact hboundary w hb
    · apply hinactive w
      simpa [hb] using hw
  obtain ⟨L, label, hL, hstart, hend, hsteps⟩ :=
    exists_direct_path (activeWires scope \ boundary) boundary
      Finset.sdiff_disjoint s t houtside
  refine ⟨L, label, ?_, hstart, hend, ?_⟩
  · exact hL.trans ((Finset.card_le_card Finset.sdiff_subset).trans
      (activeWires_card_le scope hports))
  · intro j hj
    obtain ⟨w, hw, hwb, hchange⟩ := hsteps j hj
    exact ⟨w, (Finset.mem_sdiff.mp hw).1, hwb, hchange⟩

end CircuitCompiler.LabelPaths
