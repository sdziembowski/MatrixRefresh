import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.LocalComparisons.Framework.QueryExtraction
import Proofs.Compiler.LocalComparisons.Framework.WireComparison
/-!
# Canonical finite network executions

Wire encodings are sampled independently before the adaptive transcript. Signed tables are interpreted as finite signed weights; they are never treated as sampling procedures. Per-history local bounds imply the query-tree premises used by forcing and the one-wire comparison.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace CircuitCompiler.Composition
open Refresh
/-- Transport along a finite equivalence simply reads the inverse image. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X,Y a set; P ∈ 𝒟(X); e ∈ X ≃ Y; y ∈ Y, assume X is finite; Y is finite. Then

(e_*P)(y) = P((e)⁻¹(y)).
-/
theorem map_equiv_weight {X Y : Type*} [Fintype X] [Fintype Y]
    (P : FiniteDistribution X) (e : X ≃ Y) (y : Y) :
    (P.map e).weight y = P.weight (e.symm y) := by
  classical
  have heq : ∀ x, y = e x ↔ x = e.symm y := by
    intro x
    exact eq_comm.trans e.apply_eq_iff_eq_symm_apply
  simp [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.pure, heq]
/-- Separating selected wires from all remaining wires splits the independent distribution into a product. This is the independence fact used when forcing a scope. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For W,E a set; wireDistribution ∈ W → 𝒟(E); selected ∈ W → Prop, assume W is finite; E is finite; DecidablePred(selected). Then

(Equiv.piEquivPiSubtypeProd(selected, ((x₁ ↦ E)))_*independentDistribution(wireDistribution)) = (independentDistribution(((w ∈ {w | selected(w)} ↦ wireDistribution(w)))) ⊗ independentDistribution(((w ∈ {w | ¬ (selected(w))} ↦ wireDistribution(w))))).
-/
theorem independentDistribution_split {W E : Type*} [Fintype W] [DecidableEq W] [Fintype E]
    (wireDistribution : W → FiniteDistribution E) (selected : W → Prop) [DecidablePred selected] :
    (independentDistribution wireDistribution).map (Equiv.piEquivPiSubtypeProd selected (fun _ => E)) =
      (independentDistribution (fun w : {w // selected w} => wireDistribution w)).prod
        (independentDistribution (fun w : {w // ¬selected w} => wireDistribution w)) := by
  ext encoding
  rw [map_equiv_weight]
  change (∏ w, (wireDistribution w).weight
      ((Equiv.piEquivPiSubtypeProd selected (fun _ => E)).symm encoding w)) =
    (∏ w : {w // selected w}, (wireDistribution w).weight (encoding.1 w)) *
      ∏ w : {w // ¬selected w}, (wireDistribution w).weight (encoding.2 w)
  rw [← Fintype.prod_subtype_mul_prod_subtype selected]
  congr 1
  · apply Finset.prod_congr rfl
    intro w _
    simp [Equiv.piEquivPiSubtypeProd, w.property]

  · apply Finset.prod_congr rfl
    intro w _
    simp [Equiv.piEquivPiSubtypeProd, w.property]
/-- Products of coordinate functions factor under independent wire distributions. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For W,E a set; wireDistribution ∈ W → 𝒟(E); f ∈ W → E → ℝ, assume W is finite; E is finite. Then

𝔼_(encoding ← independentDistribution(wireDistribution)) [∏_w (f(w, encoding(w)))] = ∏_w (𝔼_(v ← wireDistribution(w)) [f(w, v)]).
-/
theorem independentDistribution_expect_prod {W E : Type*} [Fintype W] [DecidableEq W] [Fintype E]
    (wireDistribution : W → FiniteDistribution E) (f : W → E → ℝ) :
    (independentDistribution wireDistribution).expect (fun encoding => ∏ w, f w (encoding w)) =
      ∏ w, (wireDistribution w).expect (f w) := by
  simp only [independentDistribution, FiniteDistribution.expect, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun w e => (wireDistribution w).weight e * f w e)).symm
/-- Applying a separate deterministic map to each wire preserves independence. In particular, all left-share marginals and all right-share marginals are the products of their one-wire marginals, as common truncation requires. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For W,E,D a set; wireDistribution ∈ W → 𝒟(E), assume W is finite; E is finite; D is finite; W → E → D. Then

(((encoding, w ↦ f(w, encoding(w))))_*independentDistribution(wireDistribution)) = independentDistribution(((w ↦ map(wireDistribution(w))))).
-/
theorem independentDistribution_map {W E D : Type*} [Fintype W] [DecidableEq W]
    [Fintype E] [Fintype D] (wireDistribution : W → FiniteDistribution E) (f : W → E → D) :
    (independentDistribution wireDistribution).map (fun encoding w => f w (encoding w)) =
      independentDistribution (fun w => (wireDistribution w).map (f w)) := by
  letI : DecidableEq D := Classical.decEq D
  letI : DecidableEq (W → D) := Classical.decEq (W → D)
  ext output
  change ((independentDistribution wireDistribution).map (fun encoding w => f w (encoding w))).weight output =
    ∏ w, ((wireDistribution w).map (f w)).weight (output w)
  simp only [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.pure]
  change (independentDistribution wireDistribution).expect
      (fun encoding => if output = (fun w => f w (encoding w)) then 1 else 0) =
    ∏ w, (wireDistribution w).expect (fun e => if output w = f w e then 1 else 0)
  rw [← independentDistribution_expect_prod]
  congr 1
  funext encoding
  by_cases heq : output = (fun w => f w (encoding w))
  · simp [heq]
  · rw [if_neg heq]
    obtain ⟨w, hw⟩ := Function.ne_iff.mp heq
    exact (Finset.prod_eq_zero (Finset.mem_univ w) (by simp [hw])).symm
/-- A product of uniform distributions is the uniform distribution on the function carrier. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For W,E a set, assume W is finite; E is finite; E ≠ ∅. Then

independentDistribution(((xw ∈ W ↦ 𝒰_E))) = FiniteDistribution.uniform.
-/
theorem independentDistribution_uniform {W E : Type*} [Fintype W] [DecidableEq W]
    [Fintype E] [Nonempty E] :
    independentDistribution (fun _w : W => (FiniteDistribution.uniform : FiniteDistribution E)) = FiniteDistribution.uniform := by
  ext encoding
  simp [independentDistribution, FiniteDistribution.uniform]
/-- Uniform one-wire marginals give a uniform grouped marginal. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For W,E,D a set; wireDistribution ∈ W → 𝒟(E), assume W is finite; E is finite; D is finite; D ≠ ∅; W → E → D; ∀ w, map(wireDistribution(w)) = FiniteDistribution.uniform. Then

(((encoding, w ↦ f(w, encoding(w))))_*independentDistribution(wireDistribution)) = FiniteDistribution.uniform.
-/
theorem independentDistribution_map_uniform {W E D : Type*} [Fintype W] [DecidableEq W]
    [Fintype E] [Fintype D] [Nonempty D]
    (wireDistribution : W → FiniteDistribution E) (f : W → E → D)
    (hmarginal : ∀ w, (wireDistribution w).map (f w) = FiniteDistribution.uniform) :
    (independentDistribution wireDistribution).map (fun encoding w => f w (encoding w)) = FiniteDistribution.uniform := by
  rw [independentDistribution_map]
  simp_rw [hmarginal]
  exact independentDistribution_uniform
theorem groupedDistribution_left_marginal {W E D : Type*} [Fintype W] [DecidableEq W]
    [Fintype E] [Fintype D] [Nonempty D]
    (wireDistribution : W → FiniteDistribution E) (left right : E → D)
    (hmarginal : ∀ w, (wireDistribution w).map left = FiniteDistribution.uniform) :
    (groupedDistribution wireDistribution left right).map Prod.fst = FiniteDistribution.uniform := by
  rw [groupedDistribution, FiniteDistribution.map_map]
  exact independentDistribution_map_uniform wireDistribution (fun _ => left) hmarginal
theorem groupedDistribution_right_marginal {W E D : Type*} [Fintype W] [DecidableEq W]
    [Fintype E] [Fintype D] [Nonempty D]
    (wireDistribution : W → FiniteDistribution E) (left right : E → D)
    (hmarginal : ∀ w, (wireDistribution w).map right = FiniteDistribution.uniform) :
    (groupedDistribution wireDistribution left right).map Prod.snd = FiniteDistribution.uniform := by
  rw [groupedDistribution, FiniteDistribution.map_map]
  exact independentDistribution_map_uniform wireDistribution (fun _ => right) hmarginal
namespace ErrorProcess
variable {A X : Type*}
/-- Build the adaptive query tree. The full previous answer list chooses each answer table, so adaptivity both within and between gates can be represented. -/
/- Mathematical definition (normal notation): Construct the depth-n adaptive process from local answer tables: use the current prefix to select the next table, append its answer to that prefix, and recurse. At depth zero use the prescribed prefix-dependent terminal error. -/
def fromTables (answerTable : List A → X → A → ℝ) (terminal : List A → X → ℝ) :
    (n : ℕ) → List A → ErrorProcess A X n
  | 0, history => .stop (terminal history)
  | n + 1, history => .query (answerTable history)
      (fun a => fromTables answerTable terminal n (history ++ [a]))
/-- Answer tables that agree at every remaining position define identical adaptive continuation trees. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For first, second ∈ A* → X → A → ℝ; start ∈ ℕ; n ∈ ℕ; history ∈ A*, assume ∀ history, (start ≤ |history|) ⇒ first(history) = second(history); start ≤ |history|. Then

fromTables(first, ((x₁, x₂ ↦ 1)), n, history) = fromTables(second, ((x₁, x₂ ↦ 1)), n, history).
-/
theorem fromTables_eq_after (first second : List A → X → A → ℝ) (start : ℕ)
    (heq : ∀ history, start ≤ history.length → first history = second history)
    (n : ℕ) (history : List A) (hstart : start ≤ history.length) :
    fromTables first (fun _ _ => 1) n history =
      fromTables second (fun _ _ => 1) n history := by
  induction n generalizing history with
  | zero => rfl
  | succ n ih =>
      simp only [fromTables, heq history hstart]
      congr 1
      funext a
      exact ih (history ++ [a]) (by simp; omega)
/-- Replacing one gate changes only its query position, even though the shared continuations may depend arbitrarily on the answer at that gate. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For first, second ∈ A* → X → A → ℝ; n, position ∈ ℕ; history ∈ A*, assume ∀ h, (|h| ≠ |history| + position) ⇒ first(h) = second(h). Then

AgreeExceptAt(position, fromTables(first, ((x₁, x₂ ↦ 1)), n, history), fromTables(second, ((x₁, x₂ ↦ 1)), n, history)).
-/
theorem fromTables_agreeExceptAt (first second : List A → X → A → ℝ)
    (n position : ℕ) (history : List A)
    (heq : ∀ h, h.length ≠ history.length + position → first h = second h) :
    AgreeExceptAt position (fromTables first (fun _ _ => 1) n history)
      (fromTables second (fun _ _ => 1) n history) := by
  induction n generalizing position history with
  | zero => cases position <;> rfl
  | succ n ih =>
      cases position with
      | zero =>
          simp only [fromTables, AgreeExceptAt]
          funext a
          apply fromTables_eq_after first second (history.length + 1)
          · intro h hh
            apply heq h
            omega
          · simp
      | succ position =>
          simp only [fromTables, AgreeExceptAt]
          refine ⟨heq history (by omega), ?_⟩
          intro a
          apply ih
          intro h hh
          apply heq h
          simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
theorem fromTables_unitLeaves (answerTable : List A → X → A → ℝ)
    (n : ℕ) (history : List A) :
    (fromTables answerTable (fun _ _ => 1) n history).UnitLeaves := by
  induction n generalizing history with
  | zero => intro x; rfl
  | succ n ih => exact fun a => ih (history ++ [a])
/-- Answer table bounds for a complete canonical execution, before any local error is extracted from it. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For answerTable ∈ A* → X → A → ℝ; budget ∈ ℕ → ℝ; localQuery ∈ ℕ → Bool; n ∈ ℕ; history ∈ A*, assume A is finite; ∀ history, x, (∑ₐ (|answerTable(history, x, a)|)) ≤ budget(|history|); ∀ history, (localQuery(|history|) = false) ⇒ ∃ fixed ∈ A → ℝ, ∀ x, a, answerTable(history, x, a) = fixed(a). Then

TableControlled(fromTables(answerTable, ((x₁, x₂ ↦ 1)), n, history))(((i ↦ budget((|history| + i)))), ((i ↦ localQuery((|history| + i))))).
-/
theorem fromTables_tableControlled [Fintype A]
    (answerTable : List A → X → A → ℝ) (budget : ℕ → ℝ) (localQuery : ℕ → Bool)
    (hbudget : ∀ history x, (∑ a, |answerTable history x a|) ≤ budget history.length)
    (hlocal : ∀ history, localQuery history.length = false →
      ∃ fixed : A → ℝ, ∀ x a, answerTable history x a = fixed a)
    (n : ℕ) (history : List A) :
    (fromTables answerTable (fun _ _ => 1) n history).TableControlled
      (fun i => budget (history.length + i.val))
      (fun i => localQuery (history.length + i.val)) := by
  induction n generalizing history with
  | zero => trivial
  | succ n ih =>
      simp only [fromTables, TableControlled, Fin.val_zero, Nat.add_zero]
      refine ⟨hbudget history, hlocal history, ?_⟩
      intro a
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Fin.tail_def] using ih (history ++ [a])
/-- The paper's local approximation estimate, uniform in incoming histories, implies the recursive `DifferenceBound` needed for gate extraction. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(X); η ∈ ℝ; first, second ∈ A* → X → A → ℝ; n, position ∈ ℕ; history ∈ A*, assume X is finite; 0 ≤ η; ∀ h, (|h| = |history| + position) ⇒ ∀ a, 𝔼_(x ← P) [|first(h, x, a) - second(h, x, a)|] ≤ η. Then

DifferenceBound(P, η, position, fromTables(first, ((x₁, x₂ ↦ 1)), n, history), fromTables(second, ((x₁, x₂ ↦ 1)), n, history)).
-/
theorem fromTables_differenceBound [Fintype X]
    (P : FiniteDistribution X) (η : ℝ) (hη : 0 ≤ η)
    (first second : List A → X → A → ℝ) (n position : ℕ) (history : List A)
    (herror : ∀ h, h.length = history.length + position → ∀ a,
      P.expect (fun x => |first h x a - second h x a|) ≤ η) :
    DifferenceBound P η position (fromTables first (fun _ _ => 1) n history)
      (fromTables second (fun _ _ => 1) n history) := by
  induction n generalizing position history with
  | zero =>
      cases position <;> simpa [fromTables, DifferenceBound] using hη
  | succ n ih =>
      cases position with
      | zero =>
          simp only [fromTables, DifferenceBound]
          exact ⟨herror history (by omega), fun a =>
            fromTables_unitLeaves first n (history ++ [a])⟩
      | succ position =>
          simp only [fromTables, DifferenceBound]
          intro a
          apply ih
          intro h hh
          apply herror h
          simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
/-- Uniform local error estimates and history-indexed answer table bounds imply the concrete tree premise of adaptive forcing. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(X); η ∈ ℝ; answerTable ∈ A* → X → A → ℝ; terminal ∈ A* → X → ℝ; budget ∈ ℕ → ℝ; localQuery ∈ ℕ → Bool; n ∈ ℕ; history ∈ A*, assume A is finite; X is finite; ∀ history, 𝔼_(x ← P) [|terminal(history, x)|] ≤ η; ∀ history, x, (∑ₐ (|answerTable(history, x, a)|)) ≤ budget(|history|); ∀ history, (localQuery(|history|) = false) ⇒ ∃ fixed ∈ A → ℝ, ∀ x, a, answerTable(history, x, a) = fixed(a). Then

Controlled(fromTables(answerTable, terminal, n, history))(P, η, ((i ↦ budget((|history| + i)))), ((i ↦ localQuery((|history| + i))))).
-/
theorem fromTables_controlled [Fintype A] [Fintype X]
    (P : FiniteDistribution X) (η : ℝ) (answerTable : List A → X → A → ℝ)
    (terminal : List A → X → ℝ) (budget : ℕ → ℝ) (localQuery : ℕ → Bool)
    (hterminal : ∀ history, P.expect (fun x => |terminal history x|) ≤ η)
    (hbudget : ∀ history x, (∑ a, |answerTable history x a|) ≤ budget history.length)
    (hlocal : ∀ history, localQuery history.length = false →
      ∃ fixed : A → ℝ, ∀ x a, answerTable history x a = fixed a)
    (n : ℕ) (history : List A) :
    (fromTables answerTable terminal n history).Controlled P η
      (fun i => budget (history.length + i.val))
      (fun i => localQuery (history.length + i.val)) := by
  induction n generalizing history with
  | zero => exact hterminal history
  | succ n ih =>
      simp only [fromTables, Controlled, Fin.val_zero, Nat.add_zero]
      refine ⟨hbudget history, hlocal history, ?_⟩
      intro a
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Fin.tail_def] using ih (history ++ [a])
/-- Uniform factorization certificates and nonlocal answer-sum bounds imply the concrete tree premise of the adaptive one-wire comparison. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Y a set; answerTable ∈ A* → X × Y → A → ℝ; budget ∈ ℕ → ℝ; localQuery ∈ ℕ → Bool; n ∈ ℕ; history ∈ A*, assume A is finite; X is finite; Y is finite; ∀ history, (localQuery(|history|) = true) ⇒ ∀ a, BoundedFactorization(((x, y ↦ answerTable(history, (x, y), a))), budget(|history|)) ≠ ∅; ∀ history, (localQuery(|history|) = false) ⇒ ∃ fixed ∈ A → ℝ, (∀ xy, a, answerTable(history, xy, a) = fixed(a)) ∧ (∑ₐ (|fixed(a)|)) ≤ budget(|history|). Then

FactorControlled(fromTables(answerTable, ((x₁, x₂ ↦ 1)), n, history))(((i ↦ budget((|history| + i)))), ((i ↦ localQuery((|history| + i))))).
-/
theorem fromTables_factorControlled {Y : Type*}
    [Fintype A] [Fintype X] [Fintype Y]
    (answerTable : List A → X × Y → A → ℝ) (budget : ℕ → ℝ) (localQuery : ℕ → Bool)
    (hfactor : ∀ history, localQuery history.length = true → ∀ a,
      Nonempty (BoundedFactorization (fun x y => answerTable history (x, y) a)
        (budget history.length)))
    (hlocal : ∀ history, localQuery history.length = false → ∃ fixed : A → ℝ,
      (∀ xy a, answerTable history xy a = fixed a) ∧
        (∑ a, |fixed a|) ≤ budget history.length)
    (n : ℕ) (history : List A) :
    (fromTables answerTable (fun _ _ => 1) n history).FactorControlled
      (fun i => budget (history.length + i.val))
      (fun i => localQuery (history.length + i.val)) := by
  induction n generalizing history with
  | zero => intro xy; rfl
  | succ n ih =>
      simp only [fromTables, FactorControlled, Fin.val_zero, Nat.add_zero]
      refine ⟨hfactor history, hlocal history, ?_⟩
      intro a
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Fin.tail_def] using ih (history ++ [a])
/-- Positive normalized answer tables give positive complete-history weights. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For answerTable ∈ A* → X → A → ℝ; n ∈ ℕ; history ∈ A*; h ∈ Answers(A, n); x ∈ X, assume ∀ history, x, a, 0 ≤ answerTable(history, x, a). Then

0 ≤ weight(fromTables(answerTable, ((x₁, x₂ ↦ 1)), n, history))(h, x).
-/
theorem fromTables_weight_nonneg
    (answerTable : List A → X → A → ℝ) (hnonneg : ∀ history x a, 0 ≤ answerTable history x a)
    (n : ℕ) (history : List A) (h : Answers A n) (x : X) :
    0 ≤ (fromTables answerTable (fun _ _ => 1) n history).weight h x := by
  induction n generalizing history with
  | zero => exact zero_le_one
  | succ n ih =>
      exact mul_nonneg (hnonneg history x h.1) (ih (history ++ [h.1]) h.2)
/-- Normalized answer tables give total complete-history mass one despite adaptivity. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For answerTable ∈ A* → X → A → ℝ; n ∈ ℕ; history ∈ A*; x ∈ X, assume A is finite; ∀ history, x, (∑ₐ (answerTable(history, x, a))) = 1. Then

(∑ₕ (weight(fromTables(answerTable, ((x₁, x₂ ↦ 1)), n, history))(h, x))) = 1.
-/
theorem fromTables_weight_total [Fintype A]
    (answerTable : List A → X → A → ℝ)
    (htotal : ∀ history x, (∑ a, answerTable history x a) = 1)
    (n : ℕ) (history : List A) (x : X) :
    (∑ h, (fromTables answerTable (fun _ _ => 1) n history).weight h x) = 1 := by
  induction n generalizing history with
  | zero => simp [fromTables, weight, Answers, answersFintype]
  | succ n ih =>
      simp only [fromTables, weight, Answers, answersFintype, Fintype.sum_prod_type, ← Finset.mul_sum,
        ih, mul_one]
      exact htotal history x
/-- The conditional transcript distribution obtained from nonnegative tables normalized over answers. -/
/- Mathematical definition (normal notation): For fixed state x and initial prefix h, the probability of a length-n answer history is the product of its successive conditional answer probabilities. Pointwise nonnegativity and answer normalization make this a probability distribution. -/
noncomputable def historyDistribution [Fintype A]
    (answerTable : List A → X → A → ℝ)
    (hnonneg : ∀ history x a, 0 ≤ answerTable history x a)
    (htotal : ∀ history x, (∑ a, answerTable history x a) = 1)
    (n : ℕ) (history : List A) (x : X) : FiniteDistribution (Answers A n) where
  weight h := (fromTables answerTable (fun _ _ => 1) n history).weight h x
  nonneg h := fromTables_weight_nonneg answerTable hnonneg n history h x
  total := fromTables_weight_total answerTable htotal n history x
end ErrorProcess
/-- Observe any function of all wire encodings and the complete history. This allows terminal output encodings to be part of the same finite view. -/
/-
Mathematical definition (normal notation): For A,X,V a set; P ∈ 𝒟(X); answerTable ∈ A* → X → A → ℝ; n ∈ ℕ; observe ∈ X × Answers(A, n) → V, assume A is finite; X is finite; V is finite. define

signedView(P, answerTable, n, observe) := (v ↦ ∑_(xh ∈ X × Answers(A, n)) (P((xh)₁) · weight(ErrorProcess.fromTables(answerTable, ((x₁, x₂ ↦ 1)), n, []))((xh)₂, (xh)₁) · FiniteDistribution.pure(observe(xh))(v))) .
-/
noncomputable def signedView {A X V : Type*} [Fintype A] [Fintype X] [Fintype V]
    (P : FiniteDistribution X) (answerTable : List A → X → A → ℝ) (n : ℕ)
    (observe : X × Answers A n → V) : V → ℝ :=
  fun v => ∑ xh : X × Answers A n,
    P.weight xh.1 * (ErrorProcess.fromTables answerTable (fun _ _ => 1) n []).weight xh.2 xh.1 *
      (FiniteDistribution.pure (observe xh)).weight v
/-- When all answer tables are nonnegative and normalized over answers, the signed-view definition agrees with sampling the wire state, sampling its adaptive history, and observing it. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A,X,V a set; P ∈ 𝒟(X); answerTable ∈ A* → X → A → ℝ; n ∈ ℕ; observe ∈ X × Answers(A, n) → V, assume A is finite; X is finite; V is finite; ∀ history, x, a, 0 ≤ answerTable(history, x, a); ∀ history, x, (∑ₐ (answerTable(history, x, a))) = 1. Then

signedView(P, answerTable, n, observe) = weight((observe_*P.joint(ErrorProcess.historyDistribution(answerTable, n, [])))).
-/
theorem signedView_eq_actual {A X V : Type*} [Fintype A] [Fintype X] [Fintype V]
    (P : FiniteDistribution X) (answerTable : List A → X → A → ℝ) (n : ℕ)
    (hnonneg : ∀ history x a, 0 ≤ answerTable history x a)
    (htotal : ∀ history x, (∑ a, answerTable history x a) = 1)
    (observe : X × Answers A n → V) :
    signedView P answerTable n observe =
      ((P.joint (ErrorProcess.historyDistribution answerTable hnonneg htotal n [])).map observe).weight :=
  rfl
end CircuitCompiler.Composition
