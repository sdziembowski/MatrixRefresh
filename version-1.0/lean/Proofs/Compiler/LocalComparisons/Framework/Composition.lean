import Mathlib.Algebra.BigOperators.Fin
import Proofs.Compiler.Foundations.MatrixRefreshing.Probability.FiniteDistribution
import Proofs.Compiler.Construction.Parameters



/-!
# Finite signed adaptive executions and path composition

The intermediate objects in circuit composition are signed weights.  This file proves their adaptive absolute-mass bound and the final path telescoping bound. Local gate replacement, truncation, and one-wire estimates are separate premises of the final theorem; this file does not claim to establish those analytic bounds.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

universe u

namespace CircuitCompiler.Composition

open Refresh

/-- Every node can choose a different answer table after every previous answer. Weights may be signed and are not assumed to be probability distributions. -/
/- Mathematical definition (normal notation): A finite adaptive process is either a halted empty process or a real answer weight table followed by one continuation per possible answer. The weights may be signed and need not form a probability distribution. -/
inductive AdaptiveProcess (A : Type*) : ℕ → Type _
  | halt : AdaptiveProcess A 0
  | query {n : ℕ} (weight : A → ℝ)
      (next : A → AdaptiveProcess A n) : AdaptiveProcess A (n + 1)

namespace AdaptiveProcess

variable {A : Type*} [Fintype A]

/-- The product of adaptive answer table weights along a complete history. -/
/- Mathematical definition (normal notation): The weight of a complete adaptive history is the product of the answer-table entries encountered along its path. At each node the selected answer determines the next table. The weight of the empty history is one. -/
def weight : {n : ℕ} → AdaptiveProcess A n → Answers A n → ℝ
  | 0, .halt, _ => 1
  | _ + 1, .query answerTable next, h => answerTable h.1 * weight (next h.1) h.2

/-- A common absolute answer-sum budget for every history at each position. -/
/- Mathematical definition (normal notation): At each position and every adaptive prefix, the next real answer table has absolute answer sum at most the corresponding budget: ∑_z |p_(i,h)(z)| ≤ Bᵢ. -/
def BoundedBy : {n : ℕ} → AdaptiveProcess A n → (Fin n → ℝ) → Prop
  | 0, .halt, _ => True
  | _ + 1, .query answerTable next, budget =>
      (∑ a, |answerTable a|) ≤ budget 0 ∧
        ∀ a, BoundedBy (next a) (Fin.tail budget)

/-- Summing the last answer backwards bounds an adaptive signed execution by the product of its answer-sum budgets. No independence between answers is used. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; process ∈ AdaptiveProcess(A, n); budget ∈ {0,…,n-1} → ℝ, assume ∀ i, 0 ≤ budget(i); process.BoundedBy(budget). Then

variationNorm(process.weight) ≤ ∏ᵢ (budget(i)).
-/
theorem variationNorm_le {n : ℕ} (process : AdaptiveProcess A n)
    (budget : Fin n → ℝ) (hbudget : ∀ i, 0 ≤ budget i)
    (hprocess : process.BoundedBy budget) :
    variationNorm process.weight ≤ ∏ i, budget i := by
  induction process with
  | halt => simp [variationNorm, weight, Answers]
  | @query n answerTable next ih =>
      simp only [BoundedBy] at hprocess
      simp only [variationNorm, weight, Answers, Fintype.sum_prod_type, abs_mul]
      rw [Fin.prod_univ_succ]
      calc
        (∑ a, ∑ h, |answerTable a| * |(next a).weight h|)
            ≤ ∑ a, |answerTable a| * ∏ i, Fin.tail budget i := by
          apply Finset.sum_le_sum
          intro a _
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left
            (ih a (Fin.tail budget) (fun i => hbudget i.succ) (hprocess.2 a))
            (abs_nonneg _)
        _ = (∑ a, |answerTable a|) * ∏ i : Fin n, budget i.succ := by
          rw [Finset.sum_mul]
          rfl
        _ ≤ budget 0 * ∏ i : Fin n, budget i.succ :=
          mul_le_mul_of_nonneg_right hprocess.1
            (Finset.prod_nonneg (fun i _ => hbudget i.succ))

/-- The budget product is exactly one factor `B` for each designated signed position. This is the `B^a` bound used after forcing nearby gate answers. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; process ∈ AdaptiveProcess(A, n); signed ∈ Finset({0,…,n-1}); B ∈ ℝ, assume 0 ≤ B; process.BoundedBy(((i ↦ { B if i ∈ signed,; 1 otherwise }))). Then

variationNorm(process.weight) ≤ B^(|signed|).
-/
theorem variationNorm_le_pow {n : ℕ} (process : AdaptiveProcess A n)
    (signed : Finset (Fin n)) (B : ℝ) (hB : 0 ≤ B)
    (hprocess : process.BoundedBy (fun i => if i ∈ signed then B else 1)) :
    variationNorm process.weight ≤ B ^ signed.card := by
  classical
  have h := process.variationNorm_le (fun i => if i ∈ signed then B else 1)
    (fun i => by split_ifs <;> positivity) hprocess
  simpa only [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const] using h

end AdaptiveProcess

/-- An adaptive prefix whose leaves contain the local error being integrated. `X` represents the wire encodings to be hidden from all nonlocal queries. -/
/- Mathematical definition (normal notation): An adaptive process depending on a state x has real answer tables at internal nodes and a real terminal-error function at each leaf. The next answer selects the continuation, so every terminal error may depend on the whole history. -/
inductive ErrorProcess (A X : Type*) : ℕ → Type _
  | stop (error : X → ℝ) : ErrorProcess A X 0
  | query {n : ℕ} (answerTable : X → A → ℝ)
      (next : A → ErrorProcess A X n) : ErrorProcess A X (n + 1)

namespace ErrorProcess

variable {A X : Type*} [Fintype A] [Fintype X]

/-- A prefix product multiplied by its history-dependent terminal error. -/
/- Mathematical definition (normal notation): For fixed state x, multiply the successive adaptive answer-table entries along the history and then multiply by that history's terminal error eₕ(x). With no queries the weight is just the terminal error. -/
def weight : {n : ℕ} → ErrorProcess A X n → Answers A n → X → ℝ
  | 0, .stop error, _, x => error x
  | _ + 1, .query answerTable next, h, x => answerTable x h.1 * weight (next h.1) h.2 x

/-- Local queries may depend on the selected encodings. All other answer tables must be independent of those encodings, even after conditioning on earlier answers. Leaf error estimates are uniform over all adaptive histories. -/
/- Mathematical definition (normal notation): Every terminal error has 𝔼_(x ∼ P) [|eₕ(x)|] ≤ η, and each answer table has pointwise absolute answer sum at most its budget. At positions marked nonlocal the answer table is independent of x, even though it may depend on the earlier history. These conditions hold recursively for every answer branch. -/
def Controlled (P : FiniteDistribution X) (η : ℝ) : {n : ℕ} → ErrorProcess A X n →
    (Fin n → ℝ) → (Fin n → Bool) → Prop
  | 0, .stop error, _, _ => P.expect (fun x => |error x|) ≤ η
  | _ + 1, .query answerTable next, budget, localQuery =>
      (∀ x, (∑ a, |answerTable x a|) ≤ budget 0) ∧
      (localQuery 0 = false → ∃ fixed : A → ℝ, ∀ x a, answerTable x a = fixed a) ∧
      ∀ a, Controlled P η (next a) (Fin.tail budget) (Fin.tail localQuery)

/-- Number of positions whose answer tables can inspect the selected encodings. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; localQuery ∈ {0,…,n-1} → Bool, define

localCount(localQuery) := ∑ᵢ ({ 1 if localQuery(i),; 0 otherwise }).
-/
def localCount {n : ℕ} (localQuery : Fin n → Bool) : ℕ :=
  ∑ i, if localQuery i then 1 else 0

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; localQuery ∈ {0,…,(n + 1)-1} → Bool, we have

localCount(localQuery) = ({ 1 if localQuery(0),; 0 otherwise }) + localCount(Fin.tail(localQuery)) .
-/
theorem localCount_succ {n : ℕ} (localQuery : Fin (n + 1) → Bool) :
    localCount localQuery = (if localQuery 0 then 1 else 0) +
      localCount (Fin.tail localQuery) := by
  exact Fin.sum_univ_succ (fun i => if localQuery i then 1 else 0)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; positions ∈ Finset({0,…,n-1}), we have

localCount(((i ↦ decide((i ∈ positions))))) = |positions| .
-/
theorem localCount_mem {n : ℕ} (positions : Finset (Fin n)) :
    localCount (fun i => decide (i ∈ positions)) = positions.card := by
  classical
  simp [localCount]

/-- Adaptive forcing, including its averaging step. Every query touching the selected encodings costs at most the alphabet size; other queries cost only their answer-sum budget. This is an actual query-tree theorem, not a premise about already-composed transcript distributions. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; P ∈ 𝒟(X); η ∈ ℝ; process ∈ ErrorProcess(A, X, n); budget ∈ {0,…,n-1} → ℝ; localQuery ∈ {0,…,n-1} → Bool, assume X ≠ ∅; 0 ≤ η; ∀ i, 0 ≤ budget(i); process.Controlled(P, η, budget, localQuery). Then

(∑ₕ (𝔼_(x ← P) [|weight(process)(h, x)|])) ≤ (|A|)^(localCount(localQuery)) · (∏ᵢ (budget(i))) · η.
-/
theorem forced_error_bound [Nonempty X] {n : ℕ} (P : FiniteDistribution X) (η : ℝ)
    (hη : 0 ≤ η) (process : ErrorProcess A X n) (budget : Fin n → ℝ)
    (localQuery : Fin n → Bool) (hbudget : ∀ i, 0 ≤ budget i)
    (hprocess : process.Controlled P η budget localQuery) :
    (∑ h, P.expect (fun x => |process.weight h x|)) ≤
      (Fintype.card A : ℝ) ^ localCount localQuery * (∏ i, budget i) * η := by
  classical
  induction process with
  | stop error => simpa [weight, Answers, localCount, Controlled] using hprocess
  | @query n answerTable next ih =>
      simp only [Controlled] at hprocess
      let tailBound := (Fintype.card A : ℝ) ^ localCount (Fin.tail localQuery) *
        (∏ i, Fin.tail budget i) * η
      have htail : ∀ a, (∑ h, P.expect (fun x => |(next a).weight h x|)) ≤
          tailBound := fun a => ih a (Fin.tail budget) (Fin.tail localQuery)
            (fun i => hbudget i.succ) (hprocess.2.2 a)
      have htailNonneg : 0 ≤ tailBound := by
        dsimp [tailBound]
        exact mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
          (Finset.prod_nonneg (fun i _ => hbudget i.succ))) hη
      have hsingle : ∀ x a, |answerTable x a| ≤ budget 0 := by
        intro x a
        exact (Finset.single_le_sum (fun b _ => abs_nonneg (answerTable x b))
          (Finset.mem_univ a)).trans (hprocess.1 x)
      simp only [weight, Answers, Fintype.sum_prod_type, abs_mul]
      cases hlocal : localQuery 0 with
      | false =>
          obtain ⟨fixed, hfixed⟩ := hprocess.2.1 hlocal
          have hfixedBudget : (∑ a, |fixed a|) ≤ budget 0 := by
            let x := Classical.choice (inferInstance : Nonempty X)
            simpa only [hfixed] using hprocess.1 x
          have hbound : (∑ a, ∑ h, P.expect
              (fun x => |answerTable x a| * |(next a).weight h x|)) ≤ budget 0 * tailBound := by
            calc
              _ = ∑ a, |fixed a| * ∑ h, P.expect
                    (fun x => |(next a).weight h x|) := by
                simp only [hfixed, FiniteDistribution.expect, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro a _
                apply Finset.sum_congr rfl
                intro h _
                apply Finset.sum_congr rfl
                intro x _
                ring
              _ ≤ ∑ a, |fixed a| * tailBound := Finset.sum_le_sum
                (fun a _ => mul_le_mul_of_nonneg_left (htail a) (abs_nonneg _))
              _ = (∑ a, |fixed a|) * tailBound := (Finset.sum_mul _ _ _).symm
              _ ≤ budget 0 * tailBound :=
                mul_le_mul_of_nonneg_right hfixedBudget htailNonneg
          convert hbound using 1
          rw [localCount_succ, hlocal]
          simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
          dsimp [tailBound]
          rw [Fin.prod_univ_succ]
          simp only [Fin.tail_def]
          ring
      | true =>
          have hbound : (∑ a, ∑ h, P.expect
              (fun x => |answerTable x a| * |(next a).weight h x|)) ≤
                (Fintype.card A : ℝ) * budget 0 * tailBound := by
            calc
              _ ≤ ∑ a, ∑ h, P.expect
                    (fun x => budget 0 * |(next a).weight h x|) := by
                apply Finset.sum_le_sum
                intro a _
                apply Finset.sum_le_sum
                intro h _
                exact P.expect_mono (fun x => mul_le_mul_of_nonneg_right
                  (hsingle x a) (abs_nonneg _))
              _ = ∑ a, budget 0 * ∑ h, P.expect
                    (fun x => |(next a).weight h x|) := by
                simp only [FiniteDistribution.expect, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro a _
                apply Finset.sum_congr rfl
                intro h _
                apply Finset.sum_congr rfl
                intro x _
                ring
              _ ≤ ∑ _a : A, budget 0 * tailBound := Finset.sum_le_sum
                (fun a _ => mul_le_mul_of_nonneg_left (htail a) (hbudget 0))
              _ = _ := by simp; ring
          convert hbound using 1
          rw [localCount_succ, hlocal]
          simp only [↓reduceIte, pow_add, pow_one]
          dsimp [tailBound]
          rw [Fin.prod_univ_succ]
          simp only [Fin.tail_def]
          ring

/-- The forcing bound with one budget `B` per signed gate and unit budget at all real gates. Its powers are exactly those in the manuscript. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; P ∈ 𝒟(X); η, B ∈ ℝ; process ∈ ErrorProcess(A, X, n); signed, localPositions ∈ Finset({0,…,n-1}), assume X ≠ ∅; 0 ≤ η; 0 ≤ B; process.Controlled(P, η, ((i ↦ { B if i ∈ signed,; 1 otherwise })), ((i ↦ decide((i ∈ localPositions))))). Then

(∑ₕ (𝔼_(x ← P) [|weight(process)(h, x)|])) ≤ (|A|)^(|localPositions|) · B^(|signed|) · η.
-/
theorem forced_error_bound_pow [Nonempty X] {n : ℕ} (P : FiniteDistribution X) (η B : ℝ)
    (hη : 0 ≤ η) (hB : 0 ≤ B) (process : ErrorProcess A X n)
    (signed localPositions : Finset (Fin n))
    (hprocess : process.Controlled P η
      (fun i => if i ∈ signed then B else 1)
      (fun i => decide (i ∈ localPositions))) :
    (∑ h, P.expect (fun x => |process.weight h x|)) ≤
      (Fintype.card A : ℝ) ^ localPositions.card * B ^ signed.card * η := by
  classical
  have h := forced_error_bound P η hη process
    (fun i => if i ∈ signed then B else 1) (fun i => decide (i ∈ localPositions))
    (fun i => by split_ifs <;> positivity) hprocess
  simpa only [localCount_mem, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const] using h

/-- The forcing bound continues to hold when the observer receives any function of the full history and the selected encodings. In particular, it allows complete disclosure of designated boundary encodings. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; V a set; P ∈ 𝒟(X); η ∈ ℝ; process ∈ ErrorProcess(A, X, n); budget ∈ {0,…,n-1} → ℝ; localQuery ∈ {0,…,n-1} → Bool; observe ∈ Answers(A, n) × X → V, assume X ≠ ∅; V is finite; 0 ≤ η; ∀ i, 0 ≤ budget(i); process.Controlled(P, η, budget, localQuery). Then

variationNorm(((v ↦ ∑_(hx ∈ Answers(A, n) × X) (P((hx)₂) · weight(process)((hx)₁, (hx)₂) · FiniteDistribution.pure(observe(hx))(v))))) ≤ (|A|)^(localCount(localQuery)) · (∏ᵢ (budget(i))) · η.
-/
theorem observed_forced_error_bound [Nonempty X] {n : ℕ} {V : Type*} [Fintype V]
    (P : FiniteDistribution X) (η : ℝ) (hη : 0 ≤ η) (process : ErrorProcess A X n)
    (budget : Fin n → ℝ) (localQuery : Fin n → Bool)
    (hbudget : ∀ i, 0 ≤ budget i)
    (hprocess : process.Controlled P η budget localQuery)
    (observe : Answers A n × X → V) :
    variationNorm (fun v => ∑ hx : Answers A n × X,
      P.weight hx.2 * process.weight hx.1 hx.2 * (FiniteDistribution.pure (observe hx)).weight v) ≤
      (Fintype.card A : ℝ) ^ localCount localQuery * (∏ i, budget i) * η := by
  have hcontract := variationNorm_stochastic_le
    (fun hx : Answers A n × X => P.weight hx.2 * process.weight hx.1 hx.2)
    (fun hx => FiniteDistribution.pure (observe hx))
  have hmass : variationNorm
      (fun hx : Answers A n × X => P.weight hx.2 * process.weight hx.1 hx.2) =
        ∑ h, P.expect (fun x => |process.weight h x|) := by
    simp [variationNorm, Fintype.sum_prod_type, abs_mul,
      abs_of_nonneg (P.nonneg _), FiniteDistribution.expect]
  rw [hmass] at hcontract
  exact hcontract.trans (forced_error_bound P η hη process budget localQuery hbudget hprocess)

end ErrorProcess

variable {V : Type*} [Fintype V]

/-- Averaging a uniform signed-measure estimate over the other independent wire encodings cannot enlarge its bound. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Y a set; P ∈ 𝒟(Y); weight ∈ Y → V → ℝ; bound ∈ ℝ, assume Y is finite; ∀ y, variationNorm(weight(y)) ≤ bound. Then

variationNorm(((v ↦ 𝔼_(y ← P) [weight(y, v)]))) ≤ bound.
-/
theorem variationNorm_average_le {Y : Type*} [Fintype Y]
    (P : FiniteDistribution Y) (weight : Y → V → ℝ) (bound : ℝ)
    (hbound : ∀ y, variationNorm (weight y) ≤ bound) :
    variationNorm (fun v => P.expect (fun y => weight y v)) ≤ bound := by
  calc
    _ ≤ ∑ v, P.expect (fun y => |weight y v|) :=
      Finset.sum_le_sum (fun v _ => MatrixRefresh.abs_expect_le_expect_abs P _)
    _ = P.expect (fun y => variationNorm (weight y)) := by
      simp only [FiniteDistribution.expect, variationNorm, Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ bound := P.expect_le_const hbound

/-- The absolute difference of finite signed measures is symmetric. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p, q ∈ V → ℝ, we have

variationNorm(((v ↦ p(v) - q(v)))) = variationNorm(((v ↦ q(v) - p(v)))).
-/
theorem variationNorm_sub_comm (p q : V → ℝ) :
    variationNorm (fun v => p v - q v) = variationNorm (fun v => q v - p v) := by
  simp only [variationNorm, abs_sub_comm]

/-- A uniform one-step bound telescopes along any finite sequence of signed measures, without requiring intermediate nonnegativity or normalization. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Q ∈ ℕ → V → ℝ; L ∈ ℕ; step ∈ ℝ, assume ∀ j, <, L, variationNorm(((v ↦ Q(j, v) - Q((j + 1), v)))) ≤ step. Then

variationNorm(((v ↦ Q(0, v) - Q(L, v)))) ≤ L · step.
-/
theorem signed_path_bound (Q : ℕ → V → ℝ) (L : ℕ) (step : ℝ)
    (hstep : ∀ j < L, variationNorm (fun v => Q j v - Q (j + 1) v) ≤ step) :
    variationNorm (fun v => Q 0 v - Q L v) ≤ (L : ℝ) * step := by
  induction L with
  | zero => simp [variationNorm]
  | succ L ih =>
      have hprefix := ih (fun j hj => hstep j (Nat.lt_trans hj (Nat.lt_succ_self L)))
      have hlast := hstep L (Nat.lt_succ_self L)
      have htriangle := variationNorm_sub_le (Q 0) (Q L) (Q (L + 1))
      push_cast
      nlinarith

/-- A path step may first enlarge its signed set, then change a wire, then shrink the signed set. This packages exactly those three comparisons. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p, before, after, q ∈ V → ℝ; switch, wire ∈ ℝ, assume variationNorm(((v ↦ p(v) - before(v)))) ≤ switch; variationNorm(((v ↦ before(v) - after(v)))) ≤ wire; variationNorm(((v ↦ after(v) - q(v)))) ≤ switch. Then

variationNorm(((v ↦ p(v) - q(v)))) ≤ 2 · switch + wire.
-/
theorem signed_step_bound (p before after q : V → ℝ) (switch wire : ℝ)
    (hbefore : variationNorm (fun v => p v - before v) ≤ switch)
    (hwire : variationNorm (fun v => before v - after v) ≤ wire)
    (hafter : variationNorm (fun v => after v - q v) ≤ switch) :
    variationNorm (fun v => p v - q v) ≤ 2 * switch + wire := by
  have h₁ := variationNorm_sub_le p before q
  have h₂ := variationNorm_sub_le before after q
  linarith

/-- Several valid-gate replacements cost one elementary error per newly signed gate. The order of the replacements is immaterial for this bound. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For G a set; Q ∈ Finset(G) → V → ℝ; base, extra ∈ Finset(G); error ∈ ℝ, assume Disjoint(base, extra); ∀ S, (base ⊆ S) ⇒ (S ⊆ base ∪ extra) ⇒ ∀ i ∈ S, (i ∉ base) ⇒ variationNorm(((v ↦ Q(S, v) - Q(S.erase(i), v)))) ≤ error. Then

variationNorm(((v ↦ Q(base, v) - Q((base ∪ extra), v)))) ≤ |extra| · error.
-/
theorem signed_set_enlarge_bound {G : Type*} [DecidableEq G]
    (Q : Finset G → V → ℝ) (base extra : Finset G) (error : ℝ)
    (hdisjoint : Disjoint base extra)
    (hswitch : ∀ S, base ⊆ S → S ⊆ base ∪ extra →
      ∀ i ∈ S, i ∉ base →
        variationNorm (fun v => Q S v - Q (S.erase i) v) ≤ error) :
    variationNorm (fun v => Q base v - Q (base ∪ extra) v) ≤
      (extra.card : ℝ) * error := by
  induction extra using Finset.induction_on with
  | empty => simp [variationNorm]
  | @insert i extra hi ih =>
      have hib : i ∉ base := by
        intro hib
        exact Finset.disjoint_left.mp hdisjoint hib (by simp)
      have hdisjoint' : Disjoint base extra :=
        Finset.disjoint_of_subset_right (Finset.subset_insert i extra) hdisjoint
      have hsubset : base ∪ extra ⊆ base ∪ insert i extra := by
        intro j hj
        simp only [Finset.mem_union, Finset.mem_insert] at *
        tauto
      have hp := ih hdisjoint' (fun S hbase hS j hj hjb =>
        hswitch S hbase (hS.trans hsubset) j hj hjb)
      have hs := hswitch (base ∪ insert i extra) Finset.subset_union_left
        (Finset.Subset.refl _) i (by simp) hib
      have herase : (base ∪ insert i extra).erase i = base ∪ extra := by
        ext j
        by_cases hji : j = i <;> simp [hji, hi, hib]
      rw [herase, variationNorm_sub_comm] at hs
      have ht := variationNorm_sub_le (Q base) (Q (base ∪ extra))
        (Q (base ∪ insert i extra))
      rw [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
      nlinarith

/-- Equivalent formulation for nested signed sets, with the precise number of gate replacements given by the set difference. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For G a set; Q ∈ Finset(G) → V → ℝ; base, target ∈ Finset(G); error ∈ ℝ, assume base ⊆ target; ∀ S, (base ⊆ S) ⇒ (S ⊆ target) ⇒ ∀ i ∈ S, (i ∉ base) ⇒ variationNorm(((v ↦ Q(S, v) - Q(S.erase(i), v)))) ≤ error. Then

variationNorm(((v ↦ Q(base, v) - Q(target, v)))) ≤ |(target ∖ base)| · error.
-/
theorem signed_set_inclusion_bound {G : Type*} [DecidableEq G]
    (Q : Finset G → V → ℝ) (base target : Finset G) (error : ℝ)
    (hsubset : base ⊆ target)
    (hswitch : ∀ S, base ⊆ S → S ⊆ target →
      ∀ i ∈ S, i ∉ base →
        variationNorm (fun v => Q S v - Q (S.erase i) v) ≤ error) :
    variationNorm (fun v => Q base v - Q target v) ≤
      ((target \ base).card : ℝ) * error := by
  have hcover : base ∪ (target \ base) = target := Finset.union_sdiff_of_subset hsubset
  have h := signed_set_enlarge_bound Q base (target \ base) error
    Finset.disjoint_sdiff (by simpa only [hcover] using hswitch)
  simpa only [hcover] using h

/-- At an adjacent pair of labelings, enlarge both defect sets to the common signed set, compare one wire there, and undo the second enlargement. The elementary switch hypothesis is needed only outside the respective defect set. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For G a set; Qstart, Qend ∈ Finset(G) → V → ℝ; startDefects, endDefects, common ∈ Finset(G); d ∈ ℕ; error, wire ∈ ℝ, assume 0 ≤ error; startDefects ⊆ common; endDefects ⊆ common; |(common ∖ startDefects)| ≤ d; |(common ∖ endDefects)| ≤ d; ∀ S, (startDefects ⊆ S) ⇒ (S ⊆ common) ⇒ ∀ i ∈ S, (i ∉ startDefects) ⇒ variationNorm(((v ↦ Qstart(S, v) - Qstart(S.erase(i), v)))) ≤ error; ∀ S, (endDefects ⊆ S) ⇒ (S ⊆ common) ⇒ ∀ i ∈ S, (i ∉ endDefects) ⇒ variationNorm(((v ↦ Qend(S, v) - Qend(S.erase(i), v)))) ≤ error; variationNorm(((v ↦ Qstart(common, v) - Qend(common, v)))) ≤ wire. Then

variationNorm(((v ↦ Qstart(startDefects, v) - Qend(endDefects, v)))) ≤ 2 · (d · error) + wire.
-/
theorem local_signed_step_bound {G : Type*} [DecidableEq G]
    (Qstart Qend : Finset G → V → ℝ) (startDefects endDefects common : Finset G)
    (d : ℕ) (error wire : ℝ) (herror : 0 ≤ error)
    (hstartSubset : startDefects ⊆ common) (hendSubset : endDefects ⊆ common)
    (hstartCount : (common \ startDefects).card ≤ d)
    (hendCount : (common \ endDefects).card ≤ d)
    (hstartSwitch : ∀ S, startDefects ⊆ S → S ⊆ common →
      ∀ i ∈ S, i ∉ startDefects →
        variationNorm (fun v => Qstart S v - Qstart (S.erase i) v) ≤ error)
    (hendSwitch : ∀ S, endDefects ⊆ S → S ⊆ common →
      ∀ i ∈ S, i ∉ endDefects →
        variationNorm (fun v => Qend S v - Qend (S.erase i) v) ≤ error)
    (hwire : variationNorm (fun v => Qstart common v - Qend common v) ≤ wire) :
    variationNorm (fun v => Qstart startDefects v - Qend endDefects v) ≤
      2 * ((d : ℝ) * error) + wire := by
  have hs := signed_set_inclusion_bound Qstart startDefects common error
    hstartSubset hstartSwitch
  have he := signed_set_inclusion_bound Qend endDefects common error
    hendSubset hendSwitch
  have hs' : variationNorm (fun v => Qstart startDefects v - Qstart common v) ≤
      (d : ℝ) * error := hs.trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hstartCount) herror)
  have he' : variationNorm (fun v => Qend common v - Qend endDefects v) ≤
      (d : ℝ) * error := by
    rw [variationNorm_sub_comm]
    exact he.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hendCount) herror)
  exact signed_step_bound _ _ _ _ _ _ hs' hwire he'

/-- Replacing conditional transition distributions changes a mixture by at most their average statistical distance. The current state can contain the entire adaptive history and all still-live wire encodings. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For S a set; P ∈ 𝒟(S); real, canonical ∈ S → 𝒟(V); error ∈ ℝ, assume S is finite; ∀ s, δ(real(s), canonical(s)) ≤ error. Then

δ(bind(P, real), bind(P, canonical)) ≤ error.
-/
theorem statisticalDistance_bind_transition_le {S : Type*} [Fintype S]
    (P : FiniteDistribution S) (real canonical : S → FiniteDistribution V) (error : ℝ)
    (hstep : ∀ s, statisticalDistance (real s) (canonical s) ≤ error) :
    statisticalDistance (P.bind real) (P.bind canonical) ≤ error := by
  have hjoint : statisticalDistance (P.joint real) (P.joint canonical) =
      P.expect (fun s => statisticalDistance (real s) (canonical s)) :=
    statisticalDistance_joint_mixture P real canonical
  have hmap := statisticalDistance_map_le (P.joint real) (P.joint canonical) Prod.snd
  have hreal : (P.joint real).map Prod.snd = P.bind real := by
    classical
    ext v
    simp [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.joint, FiniteDistribution.pure,
      Fintype.sum_prod_type]
  have hcanonical : (P.joint canonical).map Prod.snd = P.bind canonical := by
    classical
    ext v
    simp [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.joint, FiniteDistribution.pure,
      Fintype.sum_prod_type]
  rw [hreal, hcanonical, hjoint] at hmap
  exact hmap.trans (P.expect_le_const hstep)

/-- One adaptive transition costs at most the old state distance plus its uniform conditional error. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For S a set; P, Q ∈ 𝒟(S); real, canonical ∈ S → 𝒟(V); error ∈ ℝ, assume S is finite; ∀ s, δ(real(s), canonical(s)) ≤ error. Then

δ(bind(P, real), bind(Q, canonical)) ≤ δ(P, Q) + error.
-/
theorem statisticalDistance_transition_le {S : Type*} [Fintype S]
    (P Q : FiniteDistribution S) (real canonical : S → FiniteDistribution V) (error : ℝ)
    (hstep : ∀ s, statisticalDistance (real s) (canonical s) ≤ error) :
    statisticalDistance (P.bind real) (Q.bind canonical) ≤
      statisticalDistance P Q + error := by
  have ht := statisticalDistance_triangle (P.bind real) (Q.bind real) (Q.bind canonical)
  have hs := statisticalDistance_bind_le P Q real
  have hk := statisticalDistance_bind_transition_le Q real canonical error hstep
  linarith

/-- Iterate a time-dependent transition. A state may retain the full transcript, so this definition also represents an adaptive protocol with fixed length. -/
/- Mathematical definition (normal notation): Starting from distribution P₀, apply the time-dependent transitions successively: Pᵢ₊₁ = PᵢKᵢ, where Kᵢ(x, ·) is the next-state distribution from state x. The state may include the full previous transcript. -/
noncomputable def execute {S : Type*} [Fintype S]
    (initial : FiniteDistribution S) (transition : ℕ → S → FiniteDistribution S) : ℕ → FiniteDistribution S
  | 0 => initial
  | n + 1 => (execute initial transition n).bind (transition n)

/-- A uniform one-gate error gives `T` times that error for the full execution. This formally justifies the sequential canonical-coupling accumulation; proving the concrete gate error remains a separate gate-level task. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For S a set; initial ∈ 𝒟(S); real, canonical ∈ ℕ → S → 𝒟(S); T ∈ ℕ; error ∈ ℝ, assume S is finite; ∀ i, <, T, ∀ s, δ(real(i, s), canonical(i, s)) ≤ error. Then

δ(execute(initial, real, T), execute(initial, canonical, T)) ≤ T · error.
-/
theorem execute_statisticalDistance_le {S : Type*} [Fintype S]
    (initial : FiniteDistribution S) (real canonical : ℕ → S → FiniteDistribution S)
    (T : ℕ) (error : ℝ)
    (hstep : ∀ i < T, ∀ s, statisticalDistance (real i s) (canonical i s) ≤ error) :
    statisticalDistance (execute initial real T) (execute initial canonical T) ≤
      (T : ℝ) * error := by
  induction T with
  | zero => simp [execute]
  | succ T ih =>
      have hp := ih (fun i hi => hstep i (Nat.lt_trans hi (Nat.lt_succ_self T)))
      have ht := statisticalDistance_transition_le
        (execute initial real T) (execute initial canonical T)
        (real T) (canonical T) error (hstep T (Nat.lt_succ_self T))
      simp only [execute]
      push_cast
      linarith

/-- Endpoint truncation, signed path comparison, and two real/canonical couplings imply a statistical-distance bound. The distributions at the endpoints are probabilities; the intermediate `Q` need not be. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For actualStart, actualEnd, canonicalStart, canonicalEnd ∈ 𝒟(V); Q ∈ ℕ → V → ℝ; L ∈ ℕ; truncation, switch, wire, coupling ∈ ℝ, assume variationNorm(((v ↦ canonicalStart(v) - Q(0, v)))) ≤ truncation; variationNorm(((v ↦ canonicalEnd(v) - Q(L, v)))) ≤ truncation; ∀ j, <, L, variationNorm(((v ↦ Q(j, v) - Q((j + 1), v)))) ≤ 2 · switch + wire; δ(actualStart, canonicalStart) ≤ coupling; δ(actualEnd, canonicalEnd) ≤ coupling. Then

δ(actualStart, actualEnd) ≤ truncation + L · switch + L / 2 · wire + 2 · coupling.
-/
theorem composition_bound
    (actualStart actualEnd canonicalStart canonicalEnd : FiniteDistribution V)
    (Q : ℕ → V → ℝ) (L : ℕ) (truncation switch wire coupling : ℝ)
    (hstart : variationNorm (fun v => canonicalStart.weight v - Q 0 v) ≤ truncation)
    (hend : variationNorm (fun v => canonicalEnd.weight v - Q L v) ≤ truncation)
    (hstep : ∀ j < L, variationNorm (fun v => Q j v - Q (j + 1) v) ≤
      2 * switch + wire)
    (hcoupleStart : statisticalDistance actualStart canonicalStart ≤ coupling)
    (hcoupleEnd : statisticalDistance actualEnd canonicalEnd ≤ coupling) :
    statisticalDistance actualStart actualEnd ≤
      truncation + (L : ℝ) * switch + (L : ℝ) / 2 * wire + 2 * coupling := by
  have hpath := signed_path_bound Q L (2 * switch + wire) hstep
  have he := variationNorm_sub_comm (Q L) canonicalEnd.weight
  have ht₁ := variationNorm_sub_le canonicalStart.weight (Q 0) canonicalEnd.weight
  have ht₂ := variationNorm_sub_le (Q 0) (Q L) canonicalEnd.weight
  have hcanonical : statisticalDistance canonicalStart canonicalEnd ≤
      truncation + (L : ℝ) * switch + (L : ℝ) / 2 * wire := by
    unfold statisticalDistance
    rw [he] at ht₂
    nlinarith
  have houter₁ := statisticalDistance_triangle actualStart canonicalStart actualEnd
  have houter₂ := statisticalDistance_triangle canonicalStart canonicalEnd actualEnd
  rw [Refresh.statisticalDistance_symm canonicalEnd actualEnd] at houter₂
  linarith

/-- Substitution of the paper's local comparison bounds gives exactly the displayed abstract compiler bound. The three analytic bounds remain explicit premises; they must be established from the actual gate answer tables. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For actualStart, actualEnd, canonicalStart, canonicalEnd ∈ 𝒟(V); Q ∈ ℕ → V → ℝ; T, L, d, r, a ∈ ℕ; K, B, H, η, δ, τ ∈ ℝ, assume variationNorm(((v ↦ canonicalStart(v) - Q(0, v)))) ≤ 2 · T · Kʳ / H²; variationNorm(((v ↦ canonicalEnd(v) - Q(L, v)))) ≤ 2 · T · Kʳ / H²; ∀ j, <, L, variationNorm(((v ↦ Q(j, v) - Q((j + 1), v)))) ≤ 2 · (d · Kʳ · B^(a − 1) · η) + Kᵈ · Bᵃ · δ; δ(actualStart, canonicalStart) ≤ T · τ; δ(actualEnd, canonicalEnd) ≤ T · τ. Then

δ(actualStart, actualEnd) ≤ 2 · T · Kʳ / H² + L · d · Kʳ · B^(a − 1) · η + L / 2 · Kᵈ · Bᵃ · δ + 2 · T · τ.
-/
theorem compiler_composition_bound
    (actualStart actualEnd canonicalStart canonicalEnd : FiniteDistribution V)
    (Q : ℕ → V → ℝ) (T L d r a : ℕ) (K B H η δ τ : ℝ)
    (hstart : variationNorm (fun v => canonicalStart.weight v - Q 0 v) ≤
      2 * T * K ^ r / H ^ 2)
    (hend : variationNorm (fun v => canonicalEnd.weight v - Q L v) ≤
      2 * T * K ^ r / H ^ 2)
    (hstep : ∀ j < L, variationNorm (fun v => Q j v - Q (j + 1) v) ≤
      2 * (d * K ^ r * B ^ (a - 1) * η) + K ^ d * B ^ a * δ)
    (hcoupleStart : statisticalDistance actualStart canonicalStart ≤ T * τ)
    (hcoupleEnd : statisticalDistance actualEnd canonicalEnd ≤ T * τ) :
    statisticalDistance actualStart actualEnd ≤
      2 * T * K ^ r / H ^ 2 + L * d * K ^ r * B ^ (a - 1) * η +
        (L : ℝ) / 2 * K ^ d * B ^ a * δ + 2 * T * τ := by
  convert composition_bound actualStart actualEnd canonicalStart canonicalEnd Q L
    (2 * T * K ^ r / H ^ 2) (d * K ^ r * B ^ (a - 1) * η)
    (K ^ d * B ^ a * δ) (T * τ) hstart hend hstep hcoupleStart hcoupleEnd using 1
  ring

end CircuitCompiler.Composition
