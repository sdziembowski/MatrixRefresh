import Proofs.Compiler.LocalComparisons.Isolation
import Proofs.Compiler.LocalComparisons.Framework.ScopedWireComparison



/-!
# Connecting adaptive scoped executions to guard isolation

The split is constructed from the actual per-history tables. Signed tables remain in the local product; only genuine answer probabilities are summed outside it. For a wire-label change, the changed wire is integrated before taking an absolute value, and arbitrary observations of the other wires are retained.
-/
set_option autoImplicit false

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace CircuitCompiler.AveragedEnergyComparison

open Refresh MatrixRefresh Composition

namespace SplitProcess

variable {A X Y : Type*}

/- Mathematical definition (normal notation): Given history-dependent outer factors oₕ(x,z), local factors lₕ(x,z), and terminal functions tₕ(x), form the depth-n adaptive split process starting at history h. At the next answer z, use oₕ,lₕ, append z to h, and continue. At depth zero, return terminal weight tₕ. -/
def fromTables (outer innerFactor : List A → X → A → ℝ)
    (terminal : List A → X → ℝ) : (n : ℕ) → List A → SplitProcess A X n
  | 0, history => .stop (terminal history)
  | n + 1, history => .query (outer history) (innerFactor history)
      (fun a => fromTables outer innerFactor terminal n (history ++ [a]))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For outer, innerFactor ∈ A* → X → A → ℝ; terminal ∈ A* → X → ℝ; n ∈ ℕ; history ∈ A*, we have

full(fromTables(outer, innerFactor, terminal, n, history)) = ErrorProcess.fromTables(((h, x, a ↦ outer(h, x, a) · innerFactor(h, x, a))), terminal, n, history).
-/
theorem full_fromTables (outer innerFactor : List A → X → A → ℝ)
    (terminal : List A → X → ℝ) (n : ℕ) (history : List A) :
    (fromTables outer innerFactor terminal n history).full =
      ErrorProcess.fromTables (fun h x a => outer h x a * innerFactor h x a)
        terminal n history := by
  induction n generalizing history with
  | zero => rfl
  | succ n ih => simp only [fromTables, full, ErrorProcess.fromTables, ih]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For outer, innerFactor ∈ A* → X → A → ℝ; terminal ∈ A* → X → ℝ; n ∈ ℕ; history ∈ A*, we have

localPart(fromTables(outer, innerFactor, terminal, n, history)) = ErrorProcess.fromTables(innerFactor, terminal, n, history).
-/
theorem localPart_fromTables (outer innerFactor : List A → X → A → ℝ)
    (terminal : List A → X → ℝ) (n : ℕ) (history : List A) :
    (fromTables outer innerFactor terminal n history).localPart =
      ErrorProcess.fromTables innerFactor terminal n history := by
  induction n generalizing history with
  | zero => rfl
  | succ n ih => simp only [fromTables, localPart, ErrorProcess.fromTables, ih]

variable [Fintype A] [Fintype X]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): Suppose every outer factor's absolute answer sum at history h is at most b_(|h|), and the outer factor is independent of the local state whenever round |h| is not a guard. The depth-n split process constructed from these tables, starting at history h₀, satisfies outer control with budgets b_(|h₀|+i) and the corresponding shifted guard flags. -/
theorem fromTables_controlled
    (outer innerFactor : List A → X → A → ℝ) (terminal : List A → X → ℝ)
    (budget : ℕ → ℝ) (guard : ℕ → Bool)
    (hbudget : ∀ h x, (∑ a, |outer h x a|) ≤ budget h.length)
    (hguard : ∀ h, guard h.length = false →
      ∃ fixed : A → ℝ, ∀ x a, outer h x a = fixed a)
    (n : ℕ) (history : List A) :
    (fromTables outer innerFactor terminal n history).OuterControlled
      (fun i => budget (history.length + i.val))
      (fun i => guard (history.length + i.val)) := by
  induction n generalizing history with
  | zero => trivial
  | succ n ih =>
      refine ⟨?_, ?_, ?_⟩
      · simpa using hbudget history
      · simpa using hguard history
      · intro a
        simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
          Fin.tail_def] using ih (history ++ [a])

/-- Actual adaptive answer tables satisfy the split-isolation bound as soon as unsigned gates have probability budgets and are scoped outside the guards. The local hypothesis is an averaged product, not a pointwise error bound. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For outer, innerFactor ∈ A* → X → A → ℝ; terminal ∈ A* → X → ℝ; P ∈ 𝒟(X); error ∈ ℝ; budget ∈ ℕ → ℝ; guard ∈ ℕ → Bool; n ∈ ℕ, assume X ≠ ∅; 0 ≤ error; ∀ i, 0 ≤ budget(i); ∀ h, x, (∑ₐ (|outer(h, x, a)|)) ≤ budget(|h|); ∀ h, (guard(|h|) = false) ⇒ ∃ fixed ∈ A → ℝ, ∀ x, a, outer(h, x, a) = fixed(a); ∀ history ∈ Answers(A, n), 𝔼_(x ← P) [|weight(ErrorProcess.fromTables(innerFactor, terminal, n, []))(history, x)|] ≤ error. Then

(∑_(history ∈ Answers(A, n)) (𝔼_(x ← P) [|weight(ErrorProcess.fromTables(((h, x, a ↦ outer(h, x, a) · innerFactor(h, x, a))), terminal, n, []))(history, x)|])) ≤ (|A|)^(ErrorProcess.localCount(((i ∈ {0,…,n−1} ↦ guard(i))))) · (∏_(i ∈ {0,…,n−1}) (budget(i))) · error.
-/
theorem tables_isolate [Nonempty X]
    (outer innerFactor : List A → X → A → ℝ) (terminal : List A → X → ℝ)
    (P : FiniteDistribution X) (error : ℝ) (herror : 0 ≤ error)
    (budget : ℕ → ℝ) (guard : ℕ → Bool) (n : ℕ)
    (hbudget0 : ∀ i, 0 ≤ budget i)
    (hbudget : ∀ h x, (∑ a, |outer h x a|) ≤ budget h.length)
    (hguard : ∀ h, guard h.length = false →
      ∃ fixed : A → ℝ, ∀ x a, outer h x a = fixed a)
    (hlocal : ∀ history : Answers A n,
      P.expect (fun x => |(ErrorProcess.fromTables innerFactor terminal n []).weight history x|)
        ≤ error) :
    (∑ history : Answers A n, P.expect (fun x =>
      |(ErrorProcess.fromTables
        (fun h x a => outer h x a * innerFactor h x a) terminal n []).weight history x|)) ≤
      (Fintype.card A : ℝ)^ErrorProcess.localCount (fun i : Fin n => guard i.val) *
        (∏ i : Fin n, budget i.val) * error := by
  have hc := fromTables_controlled outer innerFactor terminal budget guard hbudget hguard n []
  have hi := (fromTables outer innerFactor terminal n []).isolate P error herror
    (fun i => budget i.val) (fun i => guard i.val) (fun i => hbudget0 i.val)
    (by simpa using hc) (by simpa only [localPart_fromTables] using hlocal)
  simpa only [full_fromTables] using hi

variable [Fintype Y]

/-- Integrate the changed wire at the leaf, after multiplying all incident signed factors. Unsigned factors have no dependence on this wire. -/
/-
Mathematical definition (normal notation): Construct the signed process comparing distributions P,Q of one wire x. Preserve all outer factors, which depend only on the remaining state y, and accumulate the local factors until the leaf. The final weight is

𝔼_(x ← P) [a(x,y) · tₕ(x,y)]- 𝔼_(x ← Q) [a(x,y) · tₕ(x,y)],

where a is the accumulated local product and h the completed history.
-/
noncomputable def wireDifference
    (outer : List A → Y → A → ℝ)
    (innerFactor : List A → (X × Y) → A → ℝ)
    (terminal : List A → (X × Y) → ℝ) (P Q : FiniteDistribution X) :
    (n : ℕ) → List A → (X × Y → ℝ) → SplitProcess A Y n
  | 0, history, accumulated => .stop (fun y =>
      P.expect (fun x => accumulated (x,y) * terminal history (x,y)) -
      Q.expect (fun x => accumulated (x,y) * terminal history (x,y)))
  | n+1, history, accumulated => .query (outer history) (fun _ _ => 1)
      (fun a => wireDifference outer innerFactor terminal P Q n (history ++ [a])
        (fun xy => accumulated xy * innerFactor history xy a))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For outer ∈ A* → Y → A → ℝ; innerFactor ∈ A* → (X × Y) → A → ℝ; terminal ∈ A* → (X × Y) → ℝ; P, Q ∈ 𝒟(X); n ∈ ℕ; history ∈ A*; accumulated ∈ X × Y → ℝ; answers ∈ Answers(A, n); y ∈ Y, we have

localPart.weight(wireDifference(outer, innerFactor, terminal, P, Q, n, history, accumulated))(answers, y) = 𝔼_(x ← P) [accumulated((x, y)) · weight(ErrorProcess.fromTables(innerFactor, terminal, n, history))(answers, (x, y))] - 𝔼_(x ← Q) [accumulated((x, y)) · weight(ErrorProcess.fromTables(innerFactor, terminal, n, history))(answers, (x, y))].
-/
theorem wireDifference_local_weight
    (outer : List A → Y → A → ℝ)
    (innerFactor : List A → (X × Y) → A → ℝ)
    (terminal : List A → (X × Y) → ℝ) (P Q : FiniteDistribution X)
    (n : ℕ) (history : List A) (accumulated : X × Y → ℝ)
    (answers : Answers A n) (y : Y) :
    (wireDifference outer innerFactor terminal P Q n history accumulated).localPart.weight answers y =
      P.expect (fun x => accumulated (x,y) *
        (ErrorProcess.fromTables innerFactor terminal n history).weight answers (x,y)) -
      Q.expect (fun x => accumulated (x,y) *
        (ErrorProcess.fromTables innerFactor terminal n history).weight answers (x,y)) := by
  induction n generalizing history accumulated with
  | zero => rfl
  | succ n ih =>
      simp only [wireDifference, localPart, ErrorProcess.weight, ErrorProcess.fromTables,
        one_mul, ih, mul_assoc]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For outer ∈ A* → Y → A → ℝ; innerFactor ∈ A* → (X × Y) → A → ℝ; terminal ∈ A* → (X × Y) → ℝ; P, Q ∈ 𝒟(X); n ∈ ℕ; history ∈ A*; accumulated ∈ X × Y → ℝ; answers ∈ Answers(A, n); y ∈ Y, we have

full.weight(wireDifference(outer, innerFactor, terminal, P, Q, n, history, accumulated))(answers, y) = 𝔼_(x ← P) [accumulated((x, y)) · weight(ErrorProcess.fromTables(((h, xy, a ↦ outer(h, (xy)₂, a) · innerFactor(h, xy, a))), terminal, n, history))(answers, (x, y))] - 𝔼_(x ← Q) [accumulated((x, y)) · weight(ErrorProcess.fromTables(((h, xy, a ↦ outer(h, (xy)₂, a) · innerFactor(h, xy, a))), terminal, n, history))(answers, (x, y))].
-/
theorem wireDifference_full_weight
    (outer : List A → Y → A → ℝ)
    (innerFactor : List A → (X × Y) → A → ℝ)
    (terminal : List A → (X × Y) → ℝ) (P Q : FiniteDistribution X)
    (n : ℕ) (history : List A) (accumulated : X × Y → ℝ)
    (answers : Answers A n) (y : Y) :
    (wireDifference outer innerFactor terminal P Q n history accumulated).full.weight answers y =
      P.expect (fun x => accumulated (x,y) *
        (ErrorProcess.fromTables (fun h xy a => outer h xy.2 a * innerFactor h xy a)
          terminal n history).weight answers (x,y)) -
      Q.expect (fun x => accumulated (x,y) *
        (ErrorProcess.fromTables (fun h xy a => outer h xy.2 a * innerFactor h xy a)
          terminal n history).weight answers (x,y)) := by
  induction n generalizing history accumulated with
  | zero => rfl
  | succ n ih =>
      simp only [wireDifference, full, ErrorProcess.weight, ErrorProcess.fromTables,
        mul_one, ih]
      simp only [FiniteDistribution.expect, Finset.mul_sum, mul_sub]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro x _ <;> ring

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For outer ∈ A* → Y → A → ℝ; innerFactor ∈ A* → (X × Y) → A → ℝ; terminal ∈ A* → (X × Y) → ℝ; P, Q ∈ 𝒟(X); budget ∈ ℕ → ℝ; guard ∈ ℕ → Bool; n ∈ ℕ; history ∈ A*; accumulated ∈ X × Y → ℝ, assume ∀ h, y, (∑ₐ (|outer(h, y, a)|)) ≤ budget(|h|); ∀ h, (guard(|h|) = false) ⇒ ∃ fixed ∈ A → ℝ, ∀ y, a, outer(h, y, a) = fixed(a). Then

OuterControlled(wireDifference(outer, innerFactor, terminal, P, Q, n, history, accumulated))(((i ↦ budget((|history| + i)))), ((i ↦ guard((|history| + i))))).
-/
theorem wireDifference_controlled
    (outer : List A → Y → A → ℝ)
    (innerFactor : List A → (X × Y) → A → ℝ)
    (terminal : List A → (X × Y) → ℝ) (P Q : FiniteDistribution X)
    (budget : ℕ → ℝ) (guard : ℕ → Bool)
    (hbudget : ∀ h y, (∑ a, |outer h y a|) ≤ budget h.length)
    (hguard : ∀ h, guard h.length = false →
      ∃ fixed : A → ℝ, ∀ y a, outer h y a = fixed a)
    (n : ℕ) (history : List A) (accumulated : X × Y → ℝ) :
    (wireDifference outer innerFactor terminal P Q n history accumulated).OuterControlled
      (fun i => budget (history.length + i.val))
      (fun i => guard (history.length + i.val)) := by
  induction n generalizing history accumulated with
  | zero => trivial
  | succ n ih =>
      refine ⟨?_, ?_, ?_⟩
      · simpa using hbudget history
      · simpa using hguard history
      · intro a
        simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
          Fin.tail_def] using ih (history ++ [a])
            (fun xy => accumulated xy * innerFactor history xy a)

/-- The exact adaptive wire-label comparison. The absolute value is outside the changed-wire expectation and inside the average of all other patch encodings; no pointwise fine-factor bound is required. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For outer ∈ A* → Y → A → ℝ; innerFactor ∈ A* → (X × Y) → A → ℝ; terminal ∈ A* → (X × Y) → ℝ; P, Q ∈ 𝒟(X); R ∈ 𝒟(Y); error ∈ ℝ; budget ∈ ℕ → ℝ; guard ∈ ℕ → Bool; n ∈ ℕ, assume Y ≠ ∅; 0 ≤ error; ∀ i, 0 ≤ budget(i); ∀ h, y, (∑ₐ (|outer(h, y, a)|)) ≤ budget(|h|); ∀ h, (guard(|h|) = false) ⇒ ∃ fixed ∈ A → ℝ, ∀ y, a, outer(h, y, a) = fixed(a); ∀ history ∈ Answers(A, n), 𝔼_(y ← R) [|𝔼_(x ← P) [weight(ErrorProcess.fromTables(innerFactor, terminal, n, []))(history, (x, y))] - 𝔼_(x ← Q) [weight(ErrorProcess.fromTables(innerFactor, terminal, n, []))(history, (x, y))]|] ≤ error. Then

(∑_(history ∈ Answers(A, n)) (𝔼_(y ← R) [|𝔼_(x ← P) [weight(ErrorProcess.fromTables(((h, xy, a ↦ outer(h, (xy)₂, a) · innerFactor(h, xy, a))), terminal, n, []))(history, (x, y))] - 𝔼_(x ← Q) [weight(ErrorProcess.fromTables(((h, xy, a ↦ outer(h, (xy)₂, a) · innerFactor(h, xy, a))), terminal, n, []))(history, (x, y))]|])) ≤ (|A|)^(ErrorProcess.localCount(((i ∈ {0,…,n−1} ↦ guard(i))))) · (∏_(i ∈ {0,…,n−1}) (budget(i))) · error.
-/
theorem tables_wire_isolate [Nonempty Y]
    (outer : List A → Y → A → ℝ)
    (innerFactor : List A → (X × Y) → A → ℝ)
    (terminal : List A → (X × Y) → ℝ) (P Q : FiniteDistribution X) (R : FiniteDistribution Y)
    (error : ℝ) (herror : 0 ≤ error)
    (budget : ℕ → ℝ) (guard : ℕ → Bool) (n : ℕ)
    (hbudget0 : ∀ i, 0 ≤ budget i)
    (hbudget : ∀ h y, (∑ a, |outer h y a|) ≤ budget h.length)
    (hguard : ∀ h, guard h.length = false →
      ∃ fixed : A → ℝ, ∀ y a, outer h y a = fixed a)
    (hlocal : ∀ history : Answers A n, R.expect (fun y =>
      |P.expect (fun x => (ErrorProcess.fromTables innerFactor terminal n []).weight history (x,y)) -
       Q.expect (fun x => (ErrorProcess.fromTables innerFactor terminal n []).weight history (x,y))|)
        ≤ error) :
    (∑ history : Answers A n, R.expect (fun y =>
      |P.expect (fun x => (ErrorProcess.fromTables
        (fun h xy a => outer h xy.2 a * innerFactor h xy a) terminal n []).weight history (x,y)) -
       Q.expect (fun x => (ErrorProcess.fromTables
        (fun h xy a => outer h xy.2 a * innerFactor h xy a) terminal n []).weight history (x,y))|)) ≤
      (Fintype.card A : ℝ)^ErrorProcess.localCount (fun i : Fin n => guard i.val) *
        (∏ i : Fin n, budget i.val) * error := by
  let process := wireDifference outer innerFactor terminal P Q n [] (fun _ => 1)
  have hc := wireDifference_controlled outer innerFactor terminal P Q budget guard
    hbudget hguard n [] (fun _ => 1)
  have hi := process.isolate R error herror (fun i => budget i.val) (fun i => guard i.val)
    (fun i => hbudget0 i.val) (by simpa using hc)
    (by simpa only [process, wireDifference_local_weight, one_mul] using hlocal)
  simpa only [process, wireDifference_full_weight, one_mul] using hi

end SplitProcess

end CircuitCompiler.AveragedEnergyComparison
