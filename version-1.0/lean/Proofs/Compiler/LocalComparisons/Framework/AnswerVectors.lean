import Mathlib.Data.List.OfFn
import Proofs.Compiler.LocalComparisons.Framework.NetworkExecution
import Proofs.Compiler.Construction.Parameters



/-!
# Converting adaptive answer trees to finite chronological vectors
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace CircuitCompiler.Composition

open Refresh

universe u

namespace ErrorProcess

variable {A X : Type*}

/-- Chronological evaluation of the same complete adaptive transcript. -/
/- Mathematical definition (normal notation): For prefix h, answer vector z = (z₀,…,zₙ₋₁), and fixed state x, define the chronological weight ∏ᵢ₌₀ ⁿ⁻¹p(h‖z_(<i),x,zᵢ). The empty product is one. -/
def vectorWeight (answerTable : List A → X → A → ℝ) :
    (n : ℕ) → List A → (Fin n → A) → X → ℝ
  | 0, _, _, _ => 1
  | n + 1, history, answer, x =>
      answerTable history x (answer 0) * vectorWeight answerTable n (history ++ [answer 0]) (Fin.tail answer) x

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For answerTable ∈ A* → X → A → ℝ; n ∈ ℕ; history ∈ A*; answer ∈ {0,…,n-1} → A; x ∈ X, we have

weight(fromTables(answerTable, ((x₁, x₂ ↦ 1)), n, history))((answersEquiv(A, n))⁻¹(answer), x) = vectorWeight(answerTable, n, history, answer, x).
-/
theorem fromTables_vectorWeight (answerTable : List A → X → A → ℝ)
    (n : ℕ) (history : List A) (answer : Fin n → A) (x : X) :
    (fromTables answerTable (fun _ _ => 1) n history).weight ((answersEquiv A n).symm answer) x =
      vectorWeight answerTable n history answer x := by
  induction n generalizing history with
  | zero => rfl
  | succ n ih =>
      simpa only [fromTables, weight, vectorWeight, answersEquiv, vectorToAnswers,
        Equiv.coe_fn_symm_mk] using
        congrArg (fun z => answerTable history x (answer 0) * z)
          (ih (history ++ [answer 0]) (Fin.tail answer))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Y a set; f ∈ Y → X; answerTable ∈ A* → X → A → ℝ; n ∈ ℕ; history ∈ A*; answer ∈ {0,…,n-1} → A; y ∈ Y, we have

vectorWeight(((h, x ↦ answerTable(h, f(x)))), n, history, answer, y) = vectorWeight(answerTable, n, history, answer, f(y)).
-/
theorem vectorWeight_map_state {Y : Type*} (f : Y → X)
    (answerTable : List A → X → A → ℝ) (n : ℕ) (history : List A) (answer : Fin n → A) (y : Y) :
    vectorWeight (fun h x => answerTable h (f x)) n history answer y =
      vectorWeight answerTable n history answer (f y) := by
  induction n generalizing history with
  | zero => rfl
  | succ n ih => simp only [vectorWeight, ih]

/-- Earlier answer tables need only agree on histories that can still be reached. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For first, second ∈ A* → X → A → ℝ; n ∈ ℕ; history ∈ A*; answer ∈ {0,…,n-1} → A; x ∈ X, assume ∀ h, (|history| ≤ |h|) ⇒ (|h| < |history| + n) ⇒ ∀ a, first(h, x, a) = second(h, x, a). Then

vectorWeight(first, n, history, answer, x) = vectorWeight(second, n, history, answer, x).
-/
theorem vectorWeight_congr (first second : List A → X → A → ℝ)
    (n : ℕ) (history : List A) (answer : Fin n → A) (x : X)
    (heq : ∀ h, history.length ≤ h.length → h.length < history.length + n →
      ∀ a, first h x a = second h x a) :
    vectorWeight first n history answer x = vectorWeight second n history answer x := by
  induction n generalizing history with
  | zero => rfl
  | succ n ih =>
      simp only [vectorWeight]
      rw [heq history (le_refl _) (by omega)]
      congr 1
      apply ih
      intro h hlo hhi a
      apply heq h
      · simp only [List.length_append, List.length_singleton] at hlo
        omega
      · simp only [List.length_append, List.length_singleton] at hhi
        omega

/-- Splitting the last answer from a chronological transcript splits off its last adaptive answer table, with the entire earlier history as its argument. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For answerTable ∈ A* → X → A → ℝ; n ∈ ℕ; history ∈ A*; answer ∈ {0,…,n-1} → A; last ∈ A; x ∈ X, we have

vectorWeight(answerTable, (n + 1), history, Fin.snoc(answer, last), x) = vectorWeight(answerTable, n, history, answer, x) · answerTable((history + +(List.ofFn, answer)), x, last).
-/
theorem vectorWeight_snoc (answerTable : List A → X → A → ℝ)
    (n : ℕ) (history : List A) (answer : Fin n → A) (last : A) (x : X) :
    vectorWeight answerTable (n + 1) history (Fin.snoc answer last) x =
      vectorWeight answerTable n history answer x * answerTable (history ++ List.ofFn answer) x last := by
  induction n generalizing history with
  | zero => simp [vectorWeight, List.ofFn, Fin.snoc_zero]
  | succ n ih =>
      have htail : Fin.tail (Fin.snoc (α := fun _ => A) answer last) = Fin.snoc (α := fun _ => A) (Fin.tail answer) last := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [Fin.tail_def]
        · simp only [Fin.tail_def, Fin.snoc_castSucc]
          exact Fin.snoc_castSucc (α := fun _ => A) last answer j.succ
      have hzero : Fin.snoc (α := fun _ => A) answer last 0 = answer 0 := by
        exact Fin.snoc_castSucc (α := fun _ => A) last answer 0
      rw [vectorWeight, hzero, htail, ih]
      rw [vectorWeight]
      simp only [List.ofFn_succ, List.append_assoc, List.singleton_append, mul_assoc, Fin.tail_def]

end ErrorProcess

end CircuitCompiler.Composition
