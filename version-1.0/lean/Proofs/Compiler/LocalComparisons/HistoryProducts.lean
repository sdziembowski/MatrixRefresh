import Proofs.Compiler.LocalComparisons.Framework.AnswerVectors
import Proofs.Compiler.LocalComparisons.ScopedSplit



/-!
# Explicit products along a fixed formal history
-/
set_option autoImplicit false

set_option maxHeartbeats 1200000

open scoped BigOperators

namespace CircuitCompiler.Composition.ErrorProcess

variable {A X : Type*}

/-- Every factor is evaluated at its own actual formal prefix. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For answerTable ∈ A* → X → A → ℝ; n ∈ ℕ; history ∈ A*; answer ∈ {0,…,n-1} → A; x ∈ X, we have

vectorWeight(answerTable, n, history, answer, x) = ∏_(i ∈ {0,…,n−1}) (answerTable((history + +(take(List.ofFn(answer)), i)), x, answer(i))).
-/
theorem vectorWeight_product (answerTable : List A → X → A → ℝ)
    (n : ℕ) (history : List A) (answer : Fin n → A) (x : X) :
    vectorWeight answerTable n history answer x =
      ∏ i : Fin n, answerTable (history ++ (List.ofFn answer).take i.val) x (answer i) := by
  induction n generalizing history with
  | zero => simp [vectorWeight]
  | succ n ih =>
      rw [vectorWeight, Fin.prod_univ_succ]
      simp only [Fin.val_zero, List.take_zero, List.append_nil]
      rw [ih]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      simp only [List.ofFn_succ, Fin.val_succ, List.take_succ_cons,
        List.append_assoc, List.singleton_append, Fin.tail_def]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For answerTable ∈ A* → X → A → ℝ; n ∈ ℕ; history ∈ A*; answer ∈ {0,…,n-1} → A; x ∈ X, we have

weight(fromTables(answerTable, ((x₁, x₂ ↦ 1)), n, history))((answersEquiv(A, n))⁻¹(answer), x) = ∏_(i ∈ {0,…,n−1}) (answerTable((history + +(take(List.ofFn(answer)), i)), x, answer(i))).
-/
theorem fromTables_product (answerTable : List A → X → A → ℝ)
    (n : ℕ) (history : List A) (answer : Fin n → A) (x : X) :
    (fromTables answerTable (fun _ _ => 1) n history).weight ((answersEquiv A n).symm answer) x =
      ∏ i : Fin n, answerTable (history ++ (List.ofFn answer).take i.val) x (answer i) := by
  rw [fromTables_vectorWeight, vectorWeight_product]

end CircuitCompiler.Composition.ErrorProcess

namespace CircuitCompiler.AveragedEnergyComparison.ScopedProbabilities

open Refresh MatrixRefresh Composition

variable {W E A : Type*} [Fintype W] [DecidableEq W] [Fintype E] [Fintype A]
  {T : ℕ}

/-- The local split consists exactly of the signed gate factors, with all unsigned factors replaced by one and all prefixes retained. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For table ∈ {0,…,T-1} → A* → (W → E) → A → ℝ; signed ∈ Finset({0,…,T-1}); answer ∈ {0,…,T-1} → A; e ∈ W → E, we have

weight(ErrorProcess.fromTables(inner(table, signed), ((x₁, x₂ ↦ 1)), T, []))((answersEquiv(A, T))⁻¹(answer), e) = ∏_(i ∈ signed) (table(i, take(List.ofFn(answer))(i), e, answer(i))).
-/
theorem inner_product
    (table : Fin T → List A → (W → E) → A → ℝ) (signed : Finset (Fin T))
    (answer : Fin T → A) (e : W → E) :
    (ErrorProcess.fromTables (inner table signed) (fun _ _ => 1) T []).weight
      ((answersEquiv A T).symm answer) e =
      ∏ i ∈ signed, table i ((List.ofFn answer).take i.val) e (answer i) := by
  classical
  rw [ErrorProcess.fromTables_product]
  have hp (i : Fin T) : ((List.ofFn answer).take i.val).length = i.val := by
    simp only [List.length_take, List.length_ofFn, min_eq_left (Nat.le_of_lt i.isLt)]
  have he (i : Fin T) : inner table signed ((List.ofFn answer).take i.val) e (answer i) =
      if i ∈ signed then table i ((List.ofFn answer).take i.val) e (answer i) else 1 := by
    unfold inner
    rw [hp]
    simp only [dif_pos i.isLt]
  simp only [List.nil_append, he]
  simp

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For scope ∈ {0,…,T-1} → Finset(W); network ∈ ScopedProbabilities(E = E, A = A, scope); table ∈ {0,…,T-1} → A* → (W → E) → A → ℝ; signed ∈ Finset({0,…,T-1}); selected ∈ Finset(W); outside ∈ {w | w ∉ selected} → E; answer ∈ {0,…,T-1} → A; inside ∈ {w | w ∈ selected} → E, we have

localPart.weight(network.split(table, signed, selected, outside))((answersEquiv(A, T))⁻¹(answer), inside) = ∏_(i ∈ signed) (table(i, take(List.ofFn(answer))(i), joinScope(selected, inside, outside), answer(i))).
-/
theorem split_localPart_product
    {scope : Fin T → Finset W} (network : ScopedProbabilities (E := E) (A := A) scope)
    (table : Fin T → List A → (W → E) → A → ℝ) (signed : Finset (Fin T))
    (selected : Finset W) (outside : {w // w ∉ selected} → E)
    (answer : Fin T → A) (inside : {w // w ∈ selected} → E) :
    (network.split table signed selected outside).localPart.weight
      ((answersEquiv A T).symm answer) inside =
      ∏ i ∈ signed, table i ((List.ofFn answer).take i.val)
        (joinScope selected inside outside) (answer i) := by
  rw [split, SplitProcess.localPart_fromTables]
  have h := inner_product table signed answer (joinScope selected inside outside)
  rw [ErrorProcess.fromTables_vectorWeight] at h ⊢
  rw [ErrorProcess.vectorWeight_map_state]
  exact h

end CircuitCompiler.AveragedEnergyComparison.ScopedProbabilities
