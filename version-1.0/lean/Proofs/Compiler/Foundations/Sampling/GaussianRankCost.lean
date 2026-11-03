import Mathlib.Data.Vector.Basic
import Proofs.Compiler.GateApproximation.Shortening.RectangularCompletionCount
import Proofs.Compiler.Construction.Parameters



/-!
# Executable Gaussian row-independence test

Rows are stored in eager vectors. Each step scans the first row for a pivot, subtracts its multiples from the remaining rows, and recurses on one fewer row. The proof identifies the Boolean result with full row rank. An explicit operation counter charges comparisons and arithmetic in these loops; it does not count a decidable rank proposition as a primitive operation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace CircuitCompiler.Rectangular.Gaussian

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- A pivot elimination is reversible on linear relations between the rows. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; H ∈ {0,…,(n + 1)-1} → {0,…,m-1} → F; j ∈ {0,…,m-1}, assume H(0, j) ≠ 0. Then

LinearIndependent(F, H) ⇔ LinearIndependent(F, reduce(H, j)).
-/
theorem independent_reduce_iff {n m : ℕ} (H : Fin (n+1) → Fin m → F)
    (j : Fin m) (hj : H 0 j ≠ 0) :
    LinearIndependent F H ↔ LinearIndependent F (reduce H j) := by
  simp only [Fintype.linearIndependent_iff]
  constructor
  · intro h c hc i
    let d : Fin (n+1) → F := Fin.cons
      (-∑ k, c k * (H k.succ j / H 0 j)) c
    have hd : ∑ k, d k • H k = 0 := by
      ext l
      have he := congrFun hc l
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,reduce,
        mul_sub,Finset.sum_sub_distrib] at he
      simp only [Fin.sum_univ_succ,d,Fin.cons_zero,Fin.cons_succ,
        Pi.smul_apply,smul_eq_mul,Finset.sum_apply,Pi.zero_apply]
      rw [neg_mul,Finset.sum_mul]
      simp_rw [mul_assoc]
      linear_combination he
    exact h d hd i.succ
  · intro h c hc i
    have hp := congrFun hc j
    simp only [Fin.sum_univ_succ,Pi.smul_apply,smul_eq_mul,
      Finset.sum_apply,Pi.zero_apply] at hp
    have hc0 : c 0 = -∑ k : Fin n, c k.succ * (H k.succ j / H 0 j) := by
      simp_rw [← mul_div_assoc]
      rw [← Finset.sum_div]
      apply (eq_neg_iff_add_eq_zero).mpr
      apply (mul_left_injective₀ hj)
      change (c 0 + _) * H 0 j = 0 * H 0 j
      rw [add_mul,div_mul_cancel₀ _ hj,zero_mul]
      exact hp
    have he : ∑ k : Fin n, c k.succ • reduce H j k = 0 := by
      ext l
      have hl := congrFun hc l
      simp only [Fin.sum_univ_succ,Pi.smul_apply,smul_eq_mul,
        Finset.sum_apply,Pi.zero_apply,hc0,neg_mul,Finset.sum_mul] at hl
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,reduce,
        mul_sub,Finset.sum_sub_distrib]
      simp_rw [mul_assoc] at hl
      linear_combination hl
    have hz : ∀ k : Fin n, c k.succ = 0 := h _ he
    refine Fin.cases ?_ (fun k => hz k) i
    simpa only [hz,zero_mul,Finset.sum_const_zero,neg_zero] using hc0

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α a set; n ∈ ℕ; f ∈ {0,…,n-1} → Counted(α); i ∈ {0,…,n-1}, we have

value.get(tabulate(f))(i) = value(f(i)).
-/
@[simp] theorem tabulate_value_get {α : Type*} {n : ℕ}
    (f : Fin n → Counted α) (i : Fin n) :
    (tabulate f).value.get i = (f i).value := by
  simp [tabulate,Vector.get]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α a set; n ∈ ℕ; f ∈ {0,…,n-1} → Counted(α), we have

operations(tabulate(f)) = ∑_(i ∈ {0,…,n−1}) (operations(f(i))).
-/
@[simp] theorem tabulate_operations {α : Type*} {n : ℕ}
    (f : Fin n → Counted α) :
    (tabulate f).operations = ∑ i : Fin n, (f i).operations := by
  simp [tabulate,Vector.get]

/-
Mathematical definition (normal notation): For n, m ∈ ℕ; H ∈ Data(F, n, m), define

entries(H) := (i, j ↦ get(H.get(i))(j)).
-/
def entries {n m : ℕ} (H : Data F n m) : Fin n → Fin m → F :=
  fun i j => (H.get i).get j

omit [DecidableEq F] in
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; first, row ∈ Vector(F, m); j, k ∈ {0,…,m-1}, we have

value.get(reduceRow(first, row, j))(k) = row.get(k) - (row.get(j) / first.get(j)) · first.get(k).
-/
@[simp] theorem reduceRow_value_get {m : ℕ} (first row : Vector F m)
    (j k : Fin m) :
    (reduceRow first row j).value.get k =
      row.get k - (row.get j / first.get j) * first.get k := by
  simp [reduceRow,Counted.bind,divOp,mulOp,subOp]

omit [DecidableEq F] in
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; first, row ∈ Vector(F, m); j ∈ {0,…,m-1}, we have

operations(reduceRow(first, row, j)) = 1 + 2 · m.
-/
@[simp] theorem reduceRow_operations {m : ℕ} (first row : Vector F m) (j : Fin m) :
    (reduceRow first row j).operations = 1+2*m := by
  simp [reduceRow,Counted.bind,divOp,mulOp,subOp,Nat.mul_comm]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; H ∈ Data(F, (n + 1), m); j ∈ {0,…,m-1}, we have

entries(value(reduceData(H, j))) = reduce(entries(H), j).
-/
@[simp] theorem reduceData_entries {n m : ℕ} (H : Data F (n+1) m) (j : Fin m) :
    entries (reduceData H j).value = reduce (entries H) j := by
  funext i k
  simp [entries,reduceData,reduce]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; H ∈ Data(F, (n + 1), m); j ∈ {0,…,m-1}, we have

operations(reduceData(H, j)) = n · (1 + 2 · m).
-/
@[simp] theorem reduceData_operations {n m : ℕ} (H : Data F (n+1) m) (j : Fin m) :
    (reduceData H j).operations = n*(1+2*m) := by
  simp [reduceData]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; row ∈ Vector(F, m); js ∈ {0,…,m-1}*, we have

operations(pivotScan(row, js)) ≤ |js|.
-/
theorem pivotScan_operations_le {m : ℕ} (row : Vector F m) (js : List (Fin m)) :
    (pivotScan row js).operations ≤ js.length := by
  induction js with
  | nil => simp [pivotScan]
  | cons j js ih =>
    by_cases hj : row.get j = 0
    · simp only [pivotScan,if_pos hj,List.length_cons]; omega
    · simp [pivotScan,hj]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; row ∈ Vector(F, m), we have

operations(findPivot(row)) ≤ m .
-/
@[simp] theorem findPivot_operations_le {m : ℕ} (row : Vector F m) :
    (findPivot row).operations ≤ m := by
  simpa [findPivot] using pivotScan_operations_le row (List.finRange m)

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; row ∈ Vector(F, m), we have

value(scanNonzero(row)) = true ⇔ ((i ↦ row.get(i))) ≠ 0.
-/
@[simp] theorem scanNonzero_correct {m : ℕ} (row : Vector F m) :
    (scanNonzero row).value = true ↔ (fun i => row.get i) ≠ (0 : Fin m → F) := by
  cases hp : (findPivot row).value with
  | none =>
    simp only [scanNonzero,hp,Option.isSome_none,Bool.false_eq_true,false_iff,not_not]
    ext i
    exact pivotScan_none row (List.finRange m) hp i (List.mem_finRange i)
  | some j =>
    simp only [scanNonzero,hp,Option.isSome_some,true_iff]
    intro hz
    have hj := pivotScan_some row (List.finRange m) j hp
    exact hj (congrFun hz j)

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; row ∈ Vector(F, m), we have

operations(scanNonzero(row)) ≤ m.
-/
@[simp] theorem scanNonzero_operations_le {m : ℕ} (row : Vector F m) :
    (scanNonzero row).operations ≤ m :=
  findPivot_operations_le row

/-- Correctness of the executable test; the proof uses reversible elimination, not an unproved correctness assumption for a rank oracle. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; n ∈ ℕ; H ∈ Data(F, n, m), we have

value(check(n, H)) = true ⇔ LinearIndependent(F, entries(H)).
-/
theorem check_correct {m : ℕ} (n : ℕ) (H : Data F n m) :
    (check n H).value = true ↔ LinearIndependent F (entries H) := by
  induction n with
  | zero => simp [check,Counted.pure]
  | succ n ih =>
    cases hp : (findPivot (H.get 0)).value with
    | none =>
      simp only [check,Counted.bind,hp,Counted.pure,Bool.false_eq_true,false_iff]
      intro hLI
      have hz : entries H 0 = 0 := by
        ext j
        exact pivotScan_none (H.get 0) (List.finRange m) hp j (List.mem_finRange j)
      exact hLI.ne_zero 0 hz
    | some j =>
      simp only [check,Counted.bind,hp,ih,reduceData_entries]
      exact (independent_reduce_iff (entries H) j
        (pivotScan_some (H.get 0) (List.finRange m) j hp)).symm

/-- A polynomial bound on the operations actually counted by the algorithm. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; n ∈ ℕ; H ∈ Data(F, n, m), we have

operations(check(n, H)) ≤ n · m + n² · (1 + 2 · m).
-/
theorem check_operations_le {m : ℕ} (n : ℕ) (H : Data F n m) :
    (check n H).operations ≤ n*m+n^2*(1+2*m) := by
  induction n with
  | zero => simp [check,Counted.pure]
  | succ n ih =>
    have hs := findPivot_operations_le (H.get 0)
    cases hp : (findPivot (H.get 0)).value with
    | none =>
      simp only [check,Counted.bind,hp,Counted.pure,Nat.add_zero]
      nlinarith
    | some j =>
      have hi := ih (reduceData H j).value
      simp only [check,Counted.bind,hp,reduceData_operations]
      nlinarith

omit [Field F] [DecidableEq F] in
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; H ∈ {0,…,n-1} → {0,…,m-1} → F, we have

entries(materialize(H)) = H.
-/
@[simp] theorem entries_materialize {n m : ℕ} (H : Fin n → Fin m → F) :
    entries (materialize H) = H := by
  funext i j
  simp [entries,materialize,Vector.get]

/-- This replaces the abstract decidability test by executable Gaussian elimination. -/
/-
Mathematical definition (normal notation): For n, m ∈ ℕ; H ∈ F^({0,…,n−1} × {0,…,m−1}), define

rankTest(H) := value(check(n, materialize(H))).
-/
def rankTest {n m : ℕ} (H : Matrix (Fin n) (Fin m) F) : Bool :=
  (check n (materialize H)).value

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; H ∈ F^({0,…,n−1} × {0,…,m−1}), we have

rankTest(H) = true ⇔ FullRowRank(H).
-/
@[simp] theorem rankTest_correct {n m : ℕ} (H : Matrix (Fin n) (Fin m) F) :
    rankTest H = true ↔ FullRowRank H := by
  rw [rankTest,check_correct,entries_materialize,fullRowRank_iff_linearIndependent]

/-- A uniform cubic envelope, also valid for empty matrices. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; H ∈ F^({0,…,n−1} × {0,…,m−1}), we have

operations(check(n, materialize(H))) ≤ 3 · (n + 1)² · (m + 1).
-/
theorem rankTest_operations_le {n m : ℕ} (H : Matrix (Fin n) (Fin m) F) :
    (check n (materialize H)).operations ≤ 3*(n+1)^2*(m+1) := by
  have h := check_operations_le n (materialize H)
  nlinarith

end CircuitCompiler.Rectangular.Gaussian
