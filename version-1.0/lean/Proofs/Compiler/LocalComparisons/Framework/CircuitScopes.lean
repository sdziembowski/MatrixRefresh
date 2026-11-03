import Proofs.Compiler.GateApproximation.MatrixPhase.CircuitModel
import Proofs.Compiler.LocalComparisons.Framework.Labels



/-!
# Local scopes of the concrete circuit syntax

The three ports are the two earlier operands and the gate's fresh output. Fan-out counts are taken from the executable syntax, and imply incidence degree three, total intersecting-neighborhood size nine, and at most four earlier intersecting gates. The current cutoff proof uses the last bound.
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler.Program

open LabelPaths

variable {F : Type*} [Mul F] [Sub F] {inputs T : ℕ}

/-- The ports of each gate, embedded in the final wire carrier. -/
/- Mathematical definition (normal notation): For each gate i, its scope Sᵢ is the set containing its left input wire, right input wire, and output wire, all indexed in the complete program's wire set. -/
def scope : {T : ℕ} → Program F inputs T → Fin T → Finset (Fin (inputs + T))
  | 0, .nil, i => Fin.elim0 i
  | t + 1, .snoc prior gate, i => Fin.lastCases
      {gate.left.castSucc, gate.right.castSucc, Fin.last (inputs + t)}
      (fun j => (prior.scope j).map Fin.castSuccEmb) i

/-- An individual gate equation on a complete assignment of labels. -/
/- Mathematical definition (normal notation): A complete labeling satisfies gate i's validity predicate when the label of its output wire equals its specified gate operation on the two input-wire labels. -/
def gateValid : {T : ℕ} → Program F inputs T → (Fin (inputs + T) → F) → Fin T → Prop
  | 0, .nil, _, i => Fin.elim0 i
  | t + 1, .snoc prior gate, values, i => Fin.lastCases
      (values (Fin.last (inputs + t)) = gate.eval (Fin.init values))
      (fun j => prior.gateValid (Fin.init values) j) i

omit [Mul F] [Sub F] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): After appending a new gate, its scope is exactly the set of its two previous operand wires and its newly allocated output wire. -/
@[simp] theorem scope_last (prior : Program F inputs T) (gate : Gate F (inputs + T)) :
    (prior.snoc gate).scope (Fin.last T) =
      {gate.left.castSucc, gate.right.castSucc, Fin.last (inputs + T)} := by
  simp [scope]

omit [Mul F] [Sub F] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For prior ∈ Program(F, inputs, T); gate ∈ Gate(F, (inputs + T)); i ∈ {0,…,T-1}, we have

scope(prior.snoc(gate))(i.castSucc) = (Fin.castSuccEmb_*prior.scope(i)).
-/
@[simp] theorem scope_old (prior : Program F inputs T) (gate : Gate F (inputs + T))
    (i : Fin T) : (prior.snoc gate).scope i.castSucc =
      (prior.scope i).map Fin.castSuccEmb := by
  simp [scope]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For program ∈ Program(F, inputs, T); i ∈ {0,…,T-1}, we have

|program.scope(i)| ≤ 3.
-/
theorem scope_card_le (program : Program F inputs T) (i : Fin T) :
    (program.scope i).card ≤ 3 := by
  induction program with
  | nil => exact Fin.elim0 i
  | @snoc t prior gate ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [scope_last]
        exact Finset.card_le_three
      · simpa using ih j

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For program ∈ Program(F, inputs, T), we have

IsLocal(program.scope, program.gateValid).
-/
theorem gateValid_local (program : Program F inputs T) :
    IsLocal program.scope program.gateValid := by
  induction program with
  | nil => intro s t i; exact Fin.elim0 i
  | @snoc t prior gate ih =>
      intro s u i h
      revert h
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro h
        have ho := h (Fin.last (inputs + t)) (by simp)
        have hl := h gate.left.castSucc (by simp)
        have hr := h gate.right.castSucc (by simp)
        simpa [gateValid, Gate.eval, Fin.init] using
          congrArg₂ (fun a b => a = gate.kind.eval b (s gate.right.castSucc)) ho hl |>.trans
            (by rw [hr])
      · intro h
        simp only [gateValid, Fin.lastCases_castSucc]
        apply ih (Fin.init s) (Fin.init u) j
        intro w hw
        apply h w.castSucc
        rw [scope_old]
        exact Finset.mem_map_of_mem Fin.castSuccEmb hw

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For program ∈ Program(F, inputs, T); values ∈ {0,…,(inputs + T)-1} → F, we have

program.Valid(values) ⇔ ∀ i, program.gateValid(values, i).
-/
theorem valid_iff_all_gates (program : Program F inputs T) (values : Fin (inputs + T) → F) :
    program.Valid values ↔ ∀ i, program.gateValid values i := by
  induction program with
  | nil => simp [Valid, gateValid]
  | @snoc t prior gate ih =>
      simp only [Valid, ih]
      constructor
      · rintro ⟨hprior, hlast⟩ i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa [gateValid] using hlast
        · simpa [gateValid] using hprior j
      · intro h
        exact ⟨fun i => by simpa [gateValid] using h i.castSucc,
          by simpa [gateValid] using h (Fin.last t)⟩

omit [Mul F] [Sub F] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For program ∈ Program(F, inputs, T); w ∈ {0,…,(inputs + T)-1}, we have

|incident(program.scope, w)| = ∑ᵢ ({ 1 if w ∈ program.scope(i),; 0 otherwise }).
-/
private theorem incident_card_eq_sum (program : Program F inputs T)
    (w : Fin (inputs + T)) :
    (incident program.scope w).card = ∑ i, if w ∈ program.scope i then 1 else 0 := by
  simp only [incident, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- A wire is in at most its number of input occurrences plus one producing gate. This includes duplicate operands, without assuming they are distinct. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For program ∈ Program(F, inputs, T); w ∈ {0,…,(inputs + T)-1}, we have

|incident(program.scope, w)| ≤ program.uses(w) + 1.
-/
theorem incident_card_le_uses_add_one (program : Program F inputs T)
    (w : Fin (inputs + T)) : (incident program.scope w).card ≤ program.uses w + 1 := by
  induction program with
  | nil => simp [incident, uses]
  | @snoc t prior gate ih =>
      refine Fin.lastCases ?_ (fun v => ?_) w
      · rw [incident_card_eq_sum, Fin.sum_univ_castSucc]
        simp [uses, Fin.snoc]
      · rw [incident_card_eq_sum, Fin.sum_univ_castSucc]
        have h := ih v
        rw [incident_card_eq_sum] at h
        have hm (j : Fin t) : v.castSucc ∈ (prior.scope j).map Fin.castSuccEmb ↔
            v ∈ prior.scope j := Finset.mem_map' Fin.castSuccEmb
        have hvlast : v.castSucc ≠ Fin.last (inputs + t) := Fin.castSucc_ne_last v
        simp only [scope_old, scope_last, hm, Finset.mem_insert, Finset.mem_singleton,
          Fin.castSucc_inj, hvlast, or_false]
        simp only [uses, Fin.snoc_castSucc]
        by_cases hl : gate.left = v <;> by_cases hr : gate.right = v <;>
          simp only [eq_comm (a := v), hl, hr, if_true, if_false, or_false,
            or_true] <;> omega

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For program ∈ Program(F, inputs, T); w ∈ {0,…,(inputs + T)-1}, assume program.FanoutTwo. Then

|incident(program.scope, w)| ≤ 3.
-/
theorem fanout_two_incident (program : Program F inputs T) (hfanout : program.FanoutTwo)
    (w : Fin (inputs + T)) : (incident program.scope w).card ≤ 3 := by
  have h := incident_card_le_uses_add_one program w
  have hf := hfanout w
  omega

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For program ∈ Program(F, inputs, T); i ∈ {0,…,T-1}, assume program.FanoutTwo. Then

|neighborhood(program.scope, i)| ≤ 9.
-/
theorem fanout_two_neighborhood (program : Program F inputs T) (hfanout : program.FanoutTwo)
    (i : Fin T) : (neighborhood program.scope i).card ≤ 9 :=
  fanout_two_neighborhood_bound program.scope i (scope_card_le program i)
    (fanout_two_incident program hfanout)

/-- A gate meets at most four earlier gates: each operand has at most its producer and one earlier consumer. Its new output has no earlier incidence. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For program ∈ Program(F, inputs, T); i ∈ {0,…,T-1}, assume program.FanoutTwo. Then

|earlierNeighborhood(program.scope, i)| ≤ 4.
-/
theorem fanout_two_earlier_neighborhood (program : Program F inputs T)
    (hfanout : program.FanoutTwo) (i : Fin T) :
    (earlierNeighborhood program.scope i).card ≤ 4 := by
  induction program with
  | nil => exact Fin.elim0 i
  | @snoc t prior gate ih =>
      have hfprior : prior.FanoutTwo := by
        intro w
        have h := hfanout w.castSucc
        simp only [uses, Fin.snoc_castSucc] at h
        omega
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hsubset : earlierNeighborhood (prior.snoc gate).scope (Fin.last t) ⊆
            ((incident prior.scope gate.left) ∪ (incident prior.scope gate.right)).map
              Fin.castSuccEmb := by
          intro j hj
          obtain ⟨hjlt, w, hwlast, hwj⟩ := (mem_earlierNeighborhood _ _ _).mp hj
          obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last (ne_of_lt hjlt)
          simp only [scope_last, Finset.mem_insert, Finset.mem_singleton] at hwlast
          rcases hwlast with rfl | rfl | rfl
          · apply Finset.mem_map_of_mem
            apply Finset.mem_union_left
            rw [mem_incident]
            rw [scope_old] at hwj
            exact (Finset.mem_map' Fin.castSuccEmb).mp hwj
          · apply Finset.mem_map_of_mem
            apply Finset.mem_union_right
            rw [mem_incident]
            rw [scope_old] at hwj
            exact (Finset.mem_map' Fin.castSuccEmb).mp hwj
          · simp only [scope_old, Finset.mem_map] at hwj
            obtain ⟨v, _, hv⟩ := hwj
            exact (Fin.castSucc_ne_last v hv).elim
        have hl : (incident prior.scope gate.left).card ≤ 2 := by
          have hu := hfanout gate.left.castSucc
          simp [uses, Fin.snoc_castSucc] at hu
          have hi := incident_card_le_uses_add_one prior gate.left
          omega
        have hr : (incident prior.scope gate.right).card ≤ 2 := by
          have hu := hfanout gate.right.castSucc
          simp [uses, Fin.snoc_castSucc] at hu
          have hi := incident_card_le_uses_add_one prior gate.right
          omega
        calc
          _ ≤ (((incident prior.scope gate.left) ∪
              (incident prior.scope gate.right)).map Fin.castSuccEmb).card :=
            Finset.card_le_card hsubset
          _ = ((incident prior.scope gate.left) ∪ (incident prior.scope gate.right)).card :=
            Finset.card_map _
          _ ≤ (incident prior.scope gate.left).card +
              (incident prior.scope gate.right).card := Finset.card_union_le _ _
          _ ≤ 4 := by omega
      · have heq : earlierNeighborhood (prior.snoc gate).scope j.castSucc =
            (earlierNeighborhood prior.scope j).map Fin.castSuccEmb := by
          ext k
          refine Fin.lastCases ?_ (fun v => ?_) k
          · have hlast : ¬ Fin.last t < j.castSucc := not_lt_of_ge (Fin.le_last _)
            simp [mem_earlierNeighborhood, hlast, Finset.mem_map, Fin.castSuccEmb_apply]
          · have hm (s : Finset (Fin t)) : v.castSucc ∈ s.map Fin.castSuccEmb ↔ v ∈ s :=
              Finset.mem_map' Fin.castSuccEmb
            rw [hm]
            simp only [mem_earlierNeighborhood, Fin.castSucc_lt_castSucc_iff, scope_old]
            constructor
            · rintro ⟨hv, w, hw, hwv⟩
              obtain ⟨u, hu, he⟩ := Finset.mem_map.mp hw
              subst w
              exact ⟨hv, u, hu, (Finset.mem_map' Fin.castSuccEmb).mp hwv⟩
            · rintro ⟨hv, w, hw, hwv⟩
              exact ⟨hv, w.castSucc, Finset.mem_map_of_mem _ hw,
                Finset.mem_map_of_mem _ hwv⟩
        rw [heq, Finset.card_map]
        exact ih hfprior j

/-- Evaluation supplies a valid endpoint for the signed-label comparison. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For program ∈ Program(F, inputs, T); input ∈ {0,…,inputs-1} → F, we have

defects(program.gateValid, program.eval(input)) = ∅.
-/
theorem eval_defects_empty (program : Program F inputs T) (input : Fin inputs → F) :
    defects program.gateValid (program.eval input) = ∅ := by
  have h := (valid_iff_all_gates program _).mp (eval_valid program input)
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  exact (mem_defects _ _ _).mp hi (h i)

end CircuitCompiler.Program
