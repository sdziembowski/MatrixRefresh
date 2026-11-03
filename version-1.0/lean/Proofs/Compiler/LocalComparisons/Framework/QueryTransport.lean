import Proofs.Compiler.LocalComparisons.Framework.NetworkExecution



/-!
# Transporting adaptive signed views through product decompositions
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler.Composition

open Refresh

namespace ErrorProcess

variable {A X Y : Type*}

/-- Substitute a deterministic encoding map at every query and every leaf. -/
/- Mathematical definition (normal notation): Substitute x = f(y) in every answer table and every terminal-error function of the adaptive process, leaving its branch structure unchanged. -/
def precompose (f : Y → X) : {n : ℕ} → ErrorProcess A X n → ErrorProcess A Y n
  | 0, .stop leaf => .stop (fun y => leaf (f y))
  | _ + 1, .query answerTable next =>
      .query (fun y a => answerTable (f y) a) (fun a => precompose f (next a))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; f ∈ Y → X; process ∈ ErrorProcess(A, X, n); h ∈ Answers(A, n); y ∈ Y, we have

weight(precompose(f, process))(h, y) = weight(process)(h, f(y)).
-/
theorem weight_precompose {n : ℕ} (f : Y → X) (process : ErrorProcess A X n)
    (h : Answers A n) (y : Y) :
    (precompose f process).weight h y = process.weight h (f y) := by
  induction process with
  | stop leaf => rfl
  | query answerTable next ih => simp only [precompose, weight, ih]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ Y → X; answerTable ∈ A* → X → A → ℝ; terminal ∈ A* → X → ℝ; n ∈ ℕ; history ∈ A*, we have

precompose(f, fromTables(answerTable, terminal, n, history)) = fromTables(((h, y ↦ answerTable(h, f(y)))), ((h, y ↦ terminal(h, f(y)))), n, history).
-/
theorem precompose_fromTables (f : Y → X) (answerTable : List A → X → A → ℝ)
    (terminal : List A → X → ℝ) (n : ℕ) (history : List A) :
    precompose f (fromTables answerTable terminal n history) =
      fromTables (fun h y => answerTable h (f y)) (fun h y => terminal h (f y)) n history := by
  induction n generalizing history with
  | zero => rfl
  | succ n ih => simp only [fromTables, precompose, ih]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; f ∈ Y → X; position ∈ ℕ; first, second ∈ ErrorProcess(A, X, n), assume AgreeExceptAt(position, first, second). Then

AgreeExceptAt(position, precompose(f, first), precompose(f, second)).
-/
theorem precompose_agreeExceptAt {n : ℕ} (f : Y → X) (position : ℕ)
    (first second : ErrorProcess A X n) (hagree : AgreeExceptAt position first second) :
    AgreeExceptAt position (precompose f first) (precompose f second) := by
  induction first generalizing position with
  | stop first =>
      cases second
      cases position <;> simpa [AgreeExceptAt, precompose] using congrArg (fun g y => g (f y)) hagree
  | query first firstNext ih =>
      cases second with
      | query second secondNext =>
          cases position with
          | zero =>
              simp only [AgreeExceptAt] at hagree
              subst secondNext
              rfl
          | succ position =>
              simp only [AgreeExceptAt] at hagree
              rcases hagree with ⟨hkernel, hnext⟩
              subst second
              exact ⟨rfl, fun a => ih a position (secondNext a) (hnext a)⟩

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; n ∈ ℕ; P ∈ 𝒟(X); process ∈ ErrorProcess(A, X, n); observe ∈ Answers(A, n) × X → V; v ∈ V, assume A is finite; X is finite; V is finite. Then

observedWeight(P, process, observe, v) = 𝔼_(x ← P) [∑ₕ (weight(process)(h, x) · FiniteDistribution.pure(observe((h, x)))(v))].
-/
theorem observedWeight_eq_expect [Fintype A] [Fintype X]
    {V : Type*} [Fintype V] {n : ℕ}
    (P : FiniteDistribution X) (process : ErrorProcess A X n)
    (observe : Answers A n × X → V) (v : V) :
    observedWeight P process observe v =
      P.expect (fun x => ∑ h, process.weight h x * (FiniteDistribution.pure (observe (h, x))).weight v) := by
  simp only [observedWeight, FiniteDistribution.expect, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- A deterministic change of coordinates can be applied either to the input distribution or to every answer table and observation. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; n ∈ ℕ; P ∈ 𝒟(Y); f ∈ Y → X; process ∈ ErrorProcess(A, X, n); observe ∈ Answers(A, n) × X → V, assume A is finite; X is finite; Y is finite; V is finite. Then

observedWeight((f_*P), process, observe) = observedWeight(P, precompose(f, process), ((hy ↦ observe(((hy)₁, f((hy)₂)))))).
-/
theorem observedWeight_map [Fintype A] [Fintype X] [Fintype Y]
    {V : Type*} [Fintype V] {n : ℕ}
    (P : FiniteDistribution Y) (f : Y → X) (process : ErrorProcess A X n)
    (observe : Answers A n × X → V) :
    observedWeight (P.map f) process observe =
      observedWeight P (precompose f process) (fun hy => observe (hy.1, f hy.2)) := by
  funext v
  rw [observedWeight_eq_expect, MatrixRefresh.expect_map, observedWeight_eq_expect]
  simp only [weight_precompose]

/-- Fixing the other encodings and then averaging their distribution gives precisely the same signed observed view as sampling both independent blocks at once. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; n ∈ ℕ; P ∈ 𝒟(X); Q ∈ 𝒟(Y); process ∈ ErrorProcess(A, (X × Y), n); observe ∈ Answers(A, n) × (X × Y) → V, assume A is finite; X is finite; Y is finite; V is finite. Then

observedWeight((P ⊗ Q), process, observe) = ((v ↦ 𝔼_(y ← Q) [observedWeight(P, precompose(((x ↦ (x, y))), process), ((hx ↦ observe(((hx)₁, ((hx)₂, y))))), v)])).
-/
theorem observedWeight_prod [Fintype A] [Fintype X] [Fintype Y]
    {V : Type*} [Fintype V] {n : ℕ}
    (P : FiniteDistribution X) (Q : FiniteDistribution Y) (process : ErrorProcess A (X × Y) n)
    (observe : Answers A n × (X × Y) → V) :
    observedWeight (P.prod Q) process observe =
      (fun v => Q.expect (fun y => observedWeight P
        (precompose (fun x => (x, y)) process)
        (fun hx => observe (hx.1, (hx.2, y))) v)) := by
  funext v
  rw [observedWeight_eq_expect, MatrixRefresh.expect_prod, MatrixRefresh.expect_comm]
  simp only [observedWeight_eq_expect, weight_precompose]

/-- If no selected encoding is disclosed, observation may be applied after averaging the signed history weights. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; n ∈ ℕ; P ∈ 𝒟(X); process ∈ ErrorProcess(A, X, n); observe ∈ Answers(A, n) → V, assume A is finite; X is finite; V is finite. Then

observedWeight(P, process, ((hx ↦ observe((hx)₁)))) = (v ↦ ∑ₕ (𝔼_(u ← P) [weight(process)(h, u)] · FiniteDistribution.pure(observe(h))(v))) .
-/
theorem observedWeight_history [Fintype A] [Fintype X]
    {V : Type*} [Fintype V] {n : ℕ}
    (P : FiniteDistribution X) (process : ErrorProcess A X n) (observe : Answers A n → V) :
    observedWeight P process (fun hx => observe hx.1) =
      fun v => ∑ h, P.expect (process.weight h) * (FiniteDistribution.pure (observe h)).weight v := by
  funext v
  simp only [observedWeight, Fintype.sum_prod_type, FiniteDistribution.expect, Finset.sum_mul]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; n ∈ ℕ; P ∈ 𝒟(X); process ∈ ErrorProcess(A, X, n); first, second ∈ Answers(A, n) × X → V, assume A is finite; X is finite; V is finite; ∀ hx, first(hx) = second(hx). Then

observedWeight(P, process, first) = observedWeight(P, process, second).
-/
theorem observedWeight_congr_observe [Fintype A] [Fintype X]
    {V : Type*} [Fintype V] {n : ℕ}
    (P : FiniteDistribution X) (process : ErrorProcess A X n)
    (first second : Answers A n × X → V) (heq : ∀ hx, first hx = second hx) :
    observedWeight P process first = observedWeight P process second := by
  exact congrArg (observedWeight P process) (funext heq)

end ErrorProcess

/-- Reassembling the two independent blocks returns the original wire distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For W,E a set; wireDistribution ∈ W → 𝒟(E); selected ∈ W → Prop, assume W is finite; E is finite; DecidablePred(selected). Then

independentDistribution(wireDistribution) = ((Equiv.piEquivPiSubtypeProd(selected, ((x₁ ↦ E))))⁻¹_*(independentDistribution(((w ∈ {w | selected(w)} ↦ wireDistribution(w)))) ⊗ independentDistribution(((w ∈ {w | ¬ (selected(w))} ↦ wireDistribution(w)))))).
-/
theorem independentDistribution_split_reverse {W E : Type*} [Fintype W] [DecidableEq W] [Fintype E]
    (wireDistribution : W → FiniteDistribution E) (selected : W → Prop) [DecidablePred selected] :
    independentDistribution wireDistribution =
      ((independentDistribution (fun w : {w // selected w} => wireDistribution w)).prod
        (independentDistribution (fun w : {w // ¬selected w} => wireDistribution w))).map
          (Equiv.piEquivPiSubtypeProd selected (fun _ => E)).symm := by
  let e := Equiv.piEquivPiSubtypeProd selected (fun _ => E)
  ext encoding
  rw [map_equiv_weight]
  have h := congrArg (fun P => P.weight (e encoding)) (independentDistribution_split wireDistribution selected)
  try dsimp only at h
  rw [map_equiv_weight] at h
  simpa only [e, Equiv.symm_apply_apply, Equiv.symm_symm] using h

/-- Separate one complete wire encoding from the independent remaining wires. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For W,E a set; wireDistribution ∈ W → 𝒟(E); wire ∈ W, assume W is finite; E is finite. Then

(Equiv.piSplitAt(wire, ((x₁ ↦ E)))_*independentDistribution(wireDistribution)) = (wireDistribution(wire) ⊗ independentDistribution(((w ∈ {w | w ≠ wire} ↦ wireDistribution(w))))).
-/
theorem independentDistribution_splitAt {W E : Type*} [Fintype W] [DecidableEq W] [Fintype E]
    (wireDistribution : W → FiniteDistribution E) (wire : W) :
    (independentDistribution wireDistribution).map (Equiv.piSplitAt wire (fun _ => E)) =
      (wireDistribution wire).prod (independentDistribution (fun w : {w // w ≠ wire} => wireDistribution w)) := by
  ext encoding
  rw [map_equiv_weight]
  change (∏ w, (wireDistribution w).weight ((Equiv.piSplitAt wire (fun _ => E)).symm encoding w)) =
    (wireDistribution wire).weight encoding.1 *
      ∏ w : {w // w ≠ wire}, (wireDistribution w).weight (encoding.2 w)
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ wire]
  simp only [Equiv.piSplitAt, Equiv.coe_fn_symm_mk, dif_pos rfl]
  congr 1
  apply Finset.prod_congr rfl
  intro w _
  simp [w.property]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For W,E a set; wireDistribution ∈ W → 𝒟(E); wire ∈ W, assume W is finite; E is finite. Then

independentDistribution(wireDistribution) = ((Equiv.piSplitAt(wire, ((x₁ ↦ E))))⁻¹_*(wireDistribution(wire) ⊗ independentDistribution(((w ∈ {w | w ≠ wire} ↦ wireDistribution(w)))))).
-/
theorem independentDistribution_splitAt_reverse {W E : Type*} [Fintype W] [DecidableEq W] [Fintype E]
    (wireDistribution : W → FiniteDistribution E) (wire : W) :
    independentDistribution wireDistribution =
      ((wireDistribution wire).prod (independentDistribution (fun w : {w // w ≠ wire} => wireDistribution w))).map
        (Equiv.piSplitAt wire (fun _ => E)).symm := by
  let e := Equiv.piSplitAt wire (fun _ => E)
  ext encoding
  rw [map_equiv_weight]
  have h := congrArg (fun P => P.weight (e encoding)) (independentDistribution_splitAt wireDistribution wire)
  try dsimp only at h
  rw [map_equiv_weight] at h
  simpa only [e, Equiv.symm_apply_apply, Equiv.symm_symm] using h

end CircuitCompiler.Composition
