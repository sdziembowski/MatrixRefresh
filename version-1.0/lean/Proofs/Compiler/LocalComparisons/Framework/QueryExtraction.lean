import Proofs.Compiler.LocalComparisons.Framework.Composition



/-!
# Extracting one gate's signed error from an adaptive execution

The extraction keeps every answer branch and moves the selected gate factor to the leaves. The resulting answer table at that gate is the constant one, hence has answer sum equal to the alphabet size. This is the precise operation used to feed a valid-gate approximation error into the adaptive forcing theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace CircuitCompiler.Composition.ErrorProcess

variable {A X : Type*}

/-- Multiply every terminal error by the same function of the encodings. -/
/- Mathematical definition (normal notation): Multiply every terminal-error function in an adaptive process by the same state function a(x), leaving all answer tables and branch choices unchanged. -/
def scaleLeaves (factor : X → ℝ) : {n : ℕ} → ErrorProcess A X n → ErrorProcess A X n
  | 0, .stop error => .stop (fun x => factor x * error x)
  | _ + 1, .query answerTable next => .query answerTable (fun a => scaleLeaves factor (next a))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; factor ∈ X → ℝ; process ∈ ErrorProcess(A, X, n); h ∈ Answers(A, n); x ∈ X, we have

weight(scaleLeaves(factor, process))(h, x) = factor(x) · weight(process)(h, x).
-/
theorem weight_scaleLeaves {n : ℕ} (factor : X → ℝ)
    (process : ErrorProcess A X n) (h : Answers A n) (x : X) :
    (scaleLeaves factor process).weight h x = factor x * process.weight h x := by
  induction process with
  | stop error => rfl
  | query answerTable next ih =>
      simp only [scaleLeaves, weight, ih]
      ring

/-- Move the selected answer table into the terminal error, keeping its answer as an ordinary branch. If the position is beyond the end, the tree is unchanged. -/
/- Mathematical definition (normal notation): Move the answer-table factor at the chosen query position into every descendant terminal-error function, replacing that query's numerical weights by one while retaining its answer-dependent branches. A position beyond the process length leaves the process unchanged. -/
def extractAt : {n : ℕ} → ℕ → ErrorProcess A X n → ErrorProcess A X n
  | 0, _, .stop error => .stop error
  | _ + 1, 0, .query answerTable next =>
      .query (fun _ _ => 1) (fun a => scaleLeaves (fun x => answerTable x a) (next a))
  | _ + 1, position + 1, .query answerTable next =>
      .query answerTable (fun a => extractAt position (next a))

/-- Bounds on query answer tables alone, without any assumption on terminal errors. -/
/- Mathematical definition (normal notation): For every query and history, bound the pointwise sum of absolute answer weights by the specified budget. Queries marked nonlocal must be independent of the selected state coordinates. Impose no bound on the terminal-error functions. -/
def TableControlled [Fintype A] : {n : ℕ} → ErrorProcess A X n →
    (Fin n → ℝ) → (Fin n → Bool) → Prop
  | 0, .stop _, _, _ => True
  | _ + 1, .query answerTable next, budget, localQuery =>
      (∀ x, (∑ a, |answerTable x a|) ≤ budget 0) ∧
      (localQuery 0 = false → ∃ fixed : A → ℝ, ∀ x a, answerTable x a = fixed a) ∧
      ∀ a, TableControlled (next a) (Fin.tail budget) (Fin.tail localQuery)

/-- A usual execution tree has no extra terminal multiplicative factor. -/
/- Mathematical definition (normal notation): Every terminal function of the adaptive process is identically one, so there is no additional multiplicative factor after the history product. -/
def UnitLeaves : {n : ℕ} → ErrorProcess A X n → Prop
  | 0, .stop leaf => ∀ x, leaf x = 1
  | _ + 1, .query _ next => ∀ a, UnitLeaves (next a)

/-- Moving an integrable local error to unit leaves preserves all answer table bounds and makes its original mean bound the terminal forcing premise. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; P ∈ 𝒟(X); η ∈ ℝ; factor ∈ X → ℝ; process ∈ ErrorProcess(A, X, n); budget ∈ {0,…,n-1} → ℝ; localQuery ∈ {0,…,n-1} → Bool, assume A is finite; X is finite; 𝔼_(x ← P) [|factor(x)|] ≤ η; process.UnitLeaves; process.TableControlled(budget, localQuery). Then

Controlled(scaleLeaves(factor, process))(P, η, budget, localQuery).
-/
theorem scaleLeaves_controlled [Fintype A] [Fintype X] {n : ℕ}
    (P : Refresh.FiniteDistribution X) (η : ℝ) (factor : X → ℝ)
    (hfactor : P.expect (fun x => |factor x|) ≤ η)
    (process : ErrorProcess A X n) (hunit : process.UnitLeaves)
    (budget : Fin n → ℝ) (localQuery : Fin n → Bool)
    (hkernel : process.TableControlled budget localQuery) :
    (scaleLeaves factor process).Controlled P η budget localQuery := by
  induction process with
  | stop leaf =>
      simp only [UnitLeaves] at hunit
      simpa only [scaleLeaves, Controlled, hunit, mul_one] using hfactor
  | query answerTable next ih =>
      simp only [scaleLeaves, Controlled, TableControlled] at *
      exact ⟨hkernel.1, hkernel.2.1, fun a =>
        ih a (hunit a) (Fin.tail budget) (Fin.tail localQuery) (hkernel.2.2 a)⟩

/-- Extraction preserves every signed history weight pointwise. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; position ∈ ℕ; process ∈ ErrorProcess(A, X, n); h ∈ Answers(A, n); x ∈ X, we have

weight(extractAt(position, process))(h, x) = weight(process)(h, x).
-/
theorem weight_extractAt {n : ℕ} (position : ℕ) (process : ErrorProcess A X n)
    (h : Answers A n) (x : X) :
    (extractAt position process).weight h x = process.weight h x := by
  induction process generalizing position with
  | stop error => cases position <;> rfl
  | query answerTable next ih =>
      cases position with
      | zero => simp [extractAt, weight, weight_scaleLeaves]
      | succ position => simp only [extractAt, weight, ih]

/-- Two executions differ only at one query position. Equality of continuation trees at that position retains arbitrary adaptivity to the selected answer. -/
/- Mathematical definition (normal notation): The two adaptive processes have identical answer tables and branch structure except possibly for the answer table at the selected position. At that position the continuations agree for every answer, retaining their full adaptivity. -/
def AgreeExceptAt : {n : ℕ} → ℕ → ErrorProcess A X n → ErrorProcess A X n → Prop
  | 0, _, .stop first, .stop second => first = second
  | _ + 1, 0, .query _ firstNext, .query _ secondNext => firstNext = secondNext
  | _ + 1, position + 1, .query first firstNext, .query second secondNext =>
      first = second ∧ ∀ a, AgreeExceptAt position (firstNext a) (secondNext a)

/-- The difference tree uses the answer table difference at the selected gate and the common answer tables everywhere else. -/
/- Mathematical definition (normal notation): Construct a process using the difference of the two answer tables at the selected position and the first process's tables elsewhere, recursively aligning their branches. At depth zero use the difference of the terminal errors. -/
def differenceAt : {n : ℕ} → ℕ → ErrorProcess A X n → ErrorProcess A X n →
    ErrorProcess A X n
  | 0, _, .stop first, .stop second => .stop (fun x => first x - second x)
  | _ + 1, 0, .query first firstNext, .query second _ =>
      .query (fun x a => first x a - second x a) firstNext
  | _ + 1, position + 1, .query first firstNext, .query _ secondNext =>
      .query first (fun a => differenceAt position (firstNext a) (secondNext a))

/-- The only analytic error premise for extracting a gate: for each incoming history and fixed answer, the answer table difference has mean absolute value at most `η`. Every continuation has unit terminal factor. -/
/- Mathematical definition (normal notation): At the selected query, for every earlier history and each fixed next answer, require 𝔼_(x ∼ P) [|p(x)-q(x)|] ≤ η, and require all continuations of the first process to have terminal factor one. If the selected position is past all queries, impose this expected-error bound on the terminal functions instead. -/
def DifferenceBound [Fintype X] (P : Refresh.FiniteDistribution X) (η : ℝ) :
    {n : ℕ} → ℕ → ErrorProcess A X n → ErrorProcess A X n → Prop
  | 0, _, .stop first, .stop second => P.expect (fun x => |first x - second x|) ≤ η
  | _ + 1, 0, .query first firstNext, .query second _ =>
      (∀ a, P.expect (fun x => |first x a - second x a|) ≤ η) ∧
        ∀ a, UnitLeaves (firstNext a)
  | _ + 1, position + 1, .query _ firstNext, .query _ secondNext =>
      ∀ a, DifferenceBound P η position (firstNext a) (secondNext a)

/-- Answer table bounds and the local gate error mechanically imply the forcing premise for the extracted difference. The selected gate costs one alphabet factor through its constant-one answer sum and is no longer marked local. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; P ∈ 𝒟(X); η ∈ ℝ; position ∈ ℕ; first, second ∈ ErrorProcess(A, X, n); budget ∈ {0,…,n-1} → ℝ; localQuery ∈ {0,…,n-1} → Bool, assume A is finite; X is finite; first.TableControlled(budget, localQuery); DifferenceBound(P, η, position, first, second). Then

Controlled(extractAt(position, differenceAt(position, first, second)))(P, η, ((i ↦ { |A| if i = position,; budget(i) otherwise })), ((i ↦ { false if i = position,; localQuery(i) otherwise }))).
-/
theorem extracted_difference_controlled [Fintype A] [Fintype X] {n : ℕ}
    (P : Refresh.FiniteDistribution X) (η : ℝ) (position : ℕ)
    (first second : ErrorProcess A X n) (budget : Fin n → ℝ) (localQuery : Fin n → Bool)
    (hkernel : first.TableControlled budget localQuery)
    (herror : DifferenceBound P η position first second) :
    (extractAt position (differenceAt position first second)).Controlled P η
      (fun i => if i.val = position then (Fintype.card A : ℝ) else budget i)
      (fun i => if i.val = position then false else localQuery i) := by
  induction first generalizing position with
  | stop first =>
      cases second
      cases position <;> exact herror
  | query first firstNext ih =>
      cases second with
      | query second secondNext =>
          cases position with
          | zero =>
              simp only [DifferenceBound] at herror
              simp only [TableControlled] at hkernel
              simp only [differenceAt, extractAt, Controlled, Fin.val_zero, ↓reduceIte]
              refine ⟨?_, ?_, ?_⟩
              · intro x; simp
              · intro _; exact ⟨fun _ => 1, fun _ _ => rfl⟩
              · intro a
                have h := scaleLeaves_controlled P η (fun x => first x a - second x a)
                  (herror.1 a) (firstNext a) (herror.2 a)
                  (Fin.tail budget) (Fin.tail localQuery) (hkernel.2.2 a)
                simpa [Fin.tail_def] using h
          | succ position =>
              simp only [DifferenceBound] at herror
              simp only [TableControlled] at hkernel
              simp only [differenceAt, extractAt, Controlled, Fin.val_zero,
                Nat.zero_ne_add_one, ↓reduceIte]
              refine ⟨hkernel.1, hkernel.2.1, ?_⟩
              intro a
              have h := ih a position (secondNext a) (Fin.tail budget)
                (Fin.tail localQuery) (hkernel.2.2 a) (herror a)
              simpa [Fin.tail_def] using h

/-- A one-gate answer table replacement is exactly represented by its difference tree; this identity holds for each full history and each encoding tuple. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; position ∈ ℕ; first, second ∈ ErrorProcess(A, X, n); h ∈ Answers(A, n); x ∈ X, assume AgreeExceptAt(position, first, second). Then

weight(differenceAt(position, first, second))(h, x) = weight(first)(h, x) - weight(second)(h, x).
-/
theorem weight_differenceAt {n : ℕ} (position : ℕ)
    (first second : ErrorProcess A X n) (hagree : AgreeExceptAt position first second)
    (h : Answers A n) (x : X) :
    (differenceAt position first second).weight h x = first.weight h x - second.weight h x := by
  induction first generalizing position with
  | stop first => cases second; cases position <;> rfl
  | query first firstNext ih =>
      cases second with
      | query second secondNext =>
          cases position with
          | zero =>
              simp only [AgreeExceptAt] at hagree
              subst secondNext
              simp only [differenceAt, weight]
              ring
          | succ position =>
              simp only [AgreeExceptAt] at hagree
              rcases hagree with ⟨hkernel, hnext⟩
              subst second
              simp only [differenceAt, weight, ih _ _ _ (hnext _)]
              ring

/-- After extraction, the one-gate error is in the leaf function and the selected gate has constant-one answer weights, exactly as required by forcing. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; position ∈ ℕ; first, second ∈ ErrorProcess(A, X, n); h ∈ Answers(A, n); x ∈ X, assume AgreeExceptAt(position, first, second). Then

weight(extractAt(position, differenceAt(position, first, second)))(h, x) = weight(first)(h, x) - weight(second)(h, x).
-/
theorem weight_extracted_difference {n : ℕ} (position : ℕ)
    (first second : ErrorProcess A X n) (hagree : AgreeExceptAt position first second)
    (h : Answers A n) (x : X) :
    (extractAt position (differenceAt position first second)).weight h x =
      first.weight h x - second.weight h x := by
  rw [weight_extractAt, weight_differenceAt position first second hagree]

/-- The finite signed view of any query tree, including a chosen observation of the encoding tuple itself. -/
/-
Mathematical definition (normal notation): For V a set; n ∈ ℕ; P ∈ 𝒟(X); process ∈ ErrorProcess(A, X, n); observe ∈ Answers(A, n) × X → V, assume A is finite; X is finite; V is finite. define

observedWeight(P, process, observe) := (v ↦ ∑_(hx ∈ Answers(A, n) × X) (P((hx)₂) · weight(process)((hx)₁, (hx)₂) · Refresh.FiniteDistribution.pure(observe(hx))(v))) .
-/
noncomputable def observedWeight [Fintype A] [Fintype X]
    {V : Type*} [Fintype V] {n : ℕ}
    (P : Refresh.FiniteDistribution X) (process : ErrorProcess A X n)
    (observe : Answers A n × X → V) : V → ℝ :=
  fun v => ∑ hx : Answers A n × X,
    P.weight hx.2 * process.weight hx.1 hx.2 * (Refresh.FiniteDistribution.pure (observe hx)).weight v

/-- Subtracting the two observed distributions is the observed extracted error tree. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; n ∈ ℕ; P ∈ 𝒟(X); position ∈ ℕ; first, second ∈ ErrorProcess(A, X, n); observe ∈ Answers(A, n) × X → V, assume A is finite; X is finite; V is finite; AgreeExceptAt(position, first, second). Then

((v ↦ observedWeight(P, first, observe, v) - observedWeight(P, second, observe, v))) = observedWeight(P, extractAt(position, differenceAt(position, first, second)), observe).
-/
theorem observedWeight_difference [Fintype A] [Fintype X]
    {V : Type*} [Fintype V] {n : ℕ}
    (P : Refresh.FiniteDistribution X) (position : ℕ)
    (first second : ErrorProcess A X n) (hagree : AgreeExceptAt position first second)
    (observe : Answers A n × X → V) :
    (fun v => observedWeight P first observe v - observedWeight P second observe v) =
      observedWeight P (extractAt position (differenceAt position first second)) observe := by
  funext v
  simp only [observedWeight, weight_extracted_difference position first second hagree,
    mul_sub, sub_mul, Finset.sum_sub_distrib]

/-- Concrete valid-gate switching: algebraic extraction and adaptive forcing together bound the difference of the two complete observed executions. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; n ∈ ℕ; P ∈ 𝒟(X); position ∈ ℕ; first, second ∈ ErrorProcess(A, X, n); η ∈ ℝ; budget ∈ {0,…,n-1} → ℝ; localQuery ∈ {0,…,n-1} → Bool; observe ∈ Answers(A, n) × X → V, assume A is finite; X is finite; X ≠ ∅; V is finite; AgreeExceptAt(position, first, second); 0 ≤ η; ∀ i, 0 ≤ budget(i); Controlled(extractAt(position, differenceAt(position, first, second)))(P, η, budget, localQuery). Then

Refresh.variationNorm(((v ↦ observedWeight(P, first, observe, v) - observedWeight(P, second, observe, v)))) ≤ (|A|)^(localCount(localQuery)) · (∏ᵢ (budget(i))) · η.
-/
theorem gate_switch_bound [Fintype A] [Fintype X] [Nonempty X]
    {V : Type*} [Fintype V] {n : ℕ}
    (P : Refresh.FiniteDistribution X) (position : ℕ)
    (first second : ErrorProcess A X n) (hagree : AgreeExceptAt position first second)
    (η : ℝ) (hη : 0 ≤ η) (budget : Fin n → ℝ) (localQuery : Fin n → Bool)
    (hbudget : ∀ i, 0 ≤ budget i)
    (hcontrolled : (extractAt position (differenceAt position first second)).Controlled
      P η budget localQuery)
    (observe : Answers A n × X → V) :
    Refresh.variationNorm
      (fun v => observedWeight P first observe v - observedWeight P second observe v) ≤
      (Fintype.card A : ℝ) ^ localCount localQuery * (∏ i, budget i) * η := by
  rw [observedWeight_difference P position first second hagree observe]
  exact observed_forced_error_bound P η hη
    (extractAt position (differenceAt position first second)) budget localQuery hbudget
    hcontrolled observe

/-- A complete gate-switch theorem whose assumptions concern only individual answer tables and the selected gate's local error; the extracted-tree premise has been discharged by `extracted_difference_controlled`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; n ∈ ℕ; P ∈ 𝒟(X); position ∈ ℕ; first, second ∈ ErrorProcess(A, X, n); η ∈ ℝ; budget ∈ {0,…,n-1} → ℝ; localQuery ∈ {0,…,n-1} → Bool; observe ∈ Answers(A, n) × X → V, assume A is finite; X is finite; X ≠ ∅; V is finite; AgreeExceptAt(position, first, second); 0 ≤ η; ∀ i, 0 ≤ budget(i); first.TableControlled(budget, localQuery); DifferenceBound(P, η, position, first, second). Then

Refresh.variationNorm(((v ↦ observedWeight(P, first, observe, v) - observedWeight(P, second, observe, v)))) ≤ (|A|)^(localCount(((i ↦ { false if i = position,; localQuery(i) otherwise })))) · (∏ᵢ ({ |A| if i = position,; budget(i) otherwise })) · η.
-/
theorem table_gate_switch_bound [Fintype A] [Fintype X] [Nonempty X]
    {V : Type*} [Fintype V] {n : ℕ}
    (P : Refresh.FiniteDistribution X) (position : ℕ)
    (first second : ErrorProcess A X n) (hagree : AgreeExceptAt position first second)
    (η : ℝ) (hη : 0 ≤ η) (budget : Fin n → ℝ) (localQuery : Fin n → Bool)
    (hbudget : ∀ i, 0 ≤ budget i)
    (hkernel : first.TableControlled budget localQuery)
    (herror : DifferenceBound P η position first second)
    (observe : Answers A n × X → V) :
    Refresh.variationNorm
      (fun v => observedWeight P first observe v - observedWeight P second observe v) ≤
      (Fintype.card A : ℝ) ^ localCount
        (fun i => if i.val = position then false else localQuery i) *
      (∏ i, if i.val = position then (Fintype.card A : ℝ) else budget i) * η := by
  apply gate_switch_bound P position first second hagree η hη
    (fun i => if i.val = position then (Fintype.card A : ℝ) else budget i)
    (fun i => if i.val = position then false else localQuery i)
  · intro i
    split_ifs
    · exact Nat.cast_nonneg _
    · exact hbudget i
  · exact extracted_difference_controlled P η position first second budget localQuery hkernel herror

/-- The exact gate-switch estimate: one alphabet-size factor per neighboring gate, one `B` per other signed gate, and the local approximation error. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; n ∈ ℕ; P ∈ 𝒟(X); position ∈ {0,…,n-1}; first, second ∈ ErrorProcess(A, X, n); η, B ∈ ℝ; signed, localPositions ∈ Finset({0,…,n-1}); observe ∈ Answers(A, n) × X → V, assume A is finite; X is finite; X ≠ ∅; V is finite; AgreeExceptAt(position, first, second); 0 ≤ η; 0 ≤ B; position ∈ localPositions; first.TableControlled(((i ↦ { B if i ∈ signed,; 1 otherwise })), ((i ↦ decide((i ∈ localPositions))))); DifferenceBound(P, η, position, first, second). Then

Refresh.variationNorm(((v ↦ observedWeight(P, first, observe, v) - observedWeight(P, second, observe, v)))) ≤ (|A|)^(|localPositions|) · B^(|signed.erase(position)|) · η.
-/
theorem table_gate_switch_bound_pow [Fintype A] [Fintype X] [Nonempty X]
    {V : Type*} [Fintype V] {n : ℕ}
    (P : Refresh.FiniteDistribution X) (position : Fin n)
    (first second : ErrorProcess A X n) (hagree : AgreeExceptAt position.val first second)
    (η B : ℝ) (hη : 0 ≤ η) (hB : 0 ≤ B)
    (signed localPositions : Finset (Fin n)) (hposition : position ∈ localPositions)
    (hkernel : first.TableControlled
      (fun i => if i ∈ signed then B else 1) (fun i => decide (i ∈ localPositions)))
    (herror : DifferenceBound P η position.val first second)
    (observe : Answers A n × X → V) :
    Refresh.variationNorm
      (fun v => observedWeight P first observe v - observedWeight P second observe v) ≤
      (Fintype.card A : ℝ) ^ localPositions.card * B ^ (signed.erase position).card * η := by
  classical
  have h := table_gate_switch_bound P position.val first second hagree η hη
    (fun i => if i ∈ signed then B else 1) (fun i => decide (i ∈ localPositions))
    (fun i => by (try dsimp); split_ifs <;> positivity) hkernel herror observe
  have hmask : (fun i : Fin n => if i.val = position.val then false else decide (i ∈ localPositions)) =
      (fun i => decide (i ∈ localPositions.erase position)) := by
    funext i
    by_cases hi : i = position
    · simp [hi]
    · have hv : i.val ≠ position.val := fun hv => hi (Fin.ext hv)
      simp [hi, hv]
  have hbudget : (fun i : Fin n => if i.val = position.val then (Fintype.card A : ℝ)
      else if i ∈ signed then B else 1) =
      (fun i => (if i = position then (Fintype.card A : ℝ) else 1) *
        (if i ∈ signed.erase position then B else 1)) := by
    funext i
    by_cases hi : i = position
    · simp [hi]
    · have hv : i.val ≠ position.val := fun hv => hi (Fin.ext hv)
      simp [hi, hv]
  rw [hmask, localCount_mem, hbudget, Finset.prod_mul_distrib] at h
  simp only [Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte,
    Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const] at h
  have hcard : localPositions.card = (localPositions.erase position).card + 1 :=
    (Finset.card_erase_add_one hposition).symm
  rw [hcard, pow_succ]
  convert h using 1
  ring

end CircuitCompiler.Composition.ErrorProcess
