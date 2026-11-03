import Proofs.Compiler.Foundations.Sampling.GaussianAlgebraCost
import Proofs.Compiler.Construction.Parameters



/-!
# A counted Gaussian linear-system solver

This supplies the inverse-matrix application needed by the refresh algorithm without treating inversion as an unverified unit-cost primitive.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 3000000

open scoped BigOperators

namespace CircuitCompiler.Rectangular.Gaussian

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; H ∈ Data(F, (n + 1), m); b ∈ Vector(F, (n + 1)); j ∈ {0,…,m-1}; i ∈ {0,…,n-1}, we have

value.get(reduceRhs(H, b, j))(i) = b.get(i.succ) - (entries(H, i.succ, j) / entries(H, 0, j)) · b.get(0).
-/
@[simp] theorem reduceRhs_value {n m : ℕ} (H : Data F (n+1) m)
    (b : Vector F (n+1)) (j : Fin m) (i : Fin n) :
    (reduceRhs H b j).value.get i = b.get i.succ -
      (entries H i.succ j / entries H 0 j)*b.get 0 := by
  simp [reduceRhs,Counted.bind,divOp,mulOp,subOp,entries]

omit [DecidableEq F] in
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; H ∈ Data(F, (n + 1), m); b ∈ Vector(F, (n + 1)); j ∈ {0,…,m-1}, we have

operations(reduceRhs(H, b, j)) = 3 · n.
-/
@[simp] theorem reduceRhs_operations {n m : ℕ} (H : Data F (n+1) m)
    (b : Vector F (n+1)) (j : Fin m) : (reduceRhs H b j).operations = 3*n := by
  simp [reduceRhs,Counted.bind,divOp,mulOp,subOp,Nat.mul_comm]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; first ∈ Vector(F, m); target ∈ F; j ∈ {0,…,m-1}; y ∈ Vector(F, m); k ∈ {0,…,m-1}, we have

value.get(backSubstitute(first, target, j, y))(k) = { y.get(k) + (target - ∑_(l ∈ {0,…,m−1}) (first.get(l) · y.get(l))) / first.get(j) if k = j,; y.get(k) otherwise }.
-/
@[simp] theorem backSubstitute_value {m : ℕ} (first : Vector F m) (target : F)
    (j : Fin m) (y : Vector F m) (k : Fin m) :
    (backSubstitute first target j y).value.get k =
      if k=j then y.get k+(target-∑ l : Fin m, first.get l*y.get l)/first.get j else y.get k := by
  simp only [backSubstitute,Counted.bind,dotData_value,subOp,divOp,tabulate_value_get]
  split_ifs <;> rfl

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; first ∈ Vector(F, m); target ∈ F; j ∈ {0,…,m-1}; y ∈ Vector(F, m), we have

operations(backSubstitute(first, target, j, y)) ≤ 3 · m + 2.
-/
theorem backSubstitute_operations_le {m : ℕ} (first : Vector F m) (target : F)
    (j : Fin m) (y : Vector F m) :
    (backSubstitute first target j y).operations ≤ 3*m+2 := by
  simp only [backSubstitute,Counted.bind,dotData_operations,dotData_value,subOp,divOp,tabulate_operations]
  have h : (∑ k : Fin m, (if k=j then addOp (y.get k)
      ((target-∑ l : Fin m, first.get l*y.get l)/first.get j)
      else Counted.pure (y.get k)).operations) ≤ m := by
    calc
      _ ≤ ∑ _k : Fin m, 1 := by
        apply Finset.sum_le_sum
        intro k _
        split_ifs <;> simp [addOp,Counted.pure]
      _ = m := by simp
  omega

omit [DecidableEq F] in
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; row, y ∈ {0,…,m-1} → F; j ∈ {0,…,m-1}; c ∈ F, we have

(∑ₖ (row(k) · ({ y(k) + c if k = j,; y(k) otherwise }))) = (∑ₖ (row(k) · y(k))) + row(j) · c.
-/
private theorem sum_update {m : ℕ} (row y : Fin m → F) (j : Fin m) (c : F) :
    (∑ k, row k*(if k=j then y k+c else y k)) =
      (∑ k, row k*y k)+row j*c := by
  have hp (k : Fin m) : row k*(if k=j then y k+c else y k) =
      row k*y k+(if k=j then row j*c else 0) := by
    by_cases hk : k=j <;> simp [hk,mul_add]
  simp_rw [hp]
  simp [Finset.sum_add_distrib]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; first ∈ Vector(F, m); target ∈ F; j ∈ {0,…,m-1}; y ∈ Vector(F, m), assume first.get(j) ≠ 0. Then

(∑_(k ∈ {0,…,m−1}) (first.get(k) · value.get(backSubstitute(first, target, j, y))(k))) = target.
-/
theorem backSubstitute_head {m : ℕ} (first : Vector F m) (target : F)
    (j : Fin m) (hj : first.get j ≠ 0) (y : Vector F m) :
    (∑ k : Fin m, first.get k*(backSubstitute first target j y).value.get k) = target := by
  simp only [backSubstitute_value]
  rw [sum_update]
  field_simp
  ring

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; first ∈ Vector(F, m); target ∈ F; j ∈ {0,…,m-1}; y ∈ Vector(F, m); row ∈ {0,…,m-1} → F, assume row(j) = 0. Then

(∑_(k ∈ {0,…,m−1}) (row(k) · value.get(backSubstitute(first, target, j, y))(k))) = ∑_(k ∈ {0,…,m−1}) (row(k) · y.get(k)).
-/
theorem backSubstitute_zero {m : ℕ} (first : Vector F m) (target : F)
    (j : Fin m) (y : Vector F m) (row : Fin m → F) (hj : row j = 0) :
    (∑ k : Fin m, row k*(backSubstitute first target j y).value.get k) =
      ∑ k : Fin m, row k*y.get k := by
  simp only [backSubstitute_value]
  rw [sum_update,hj,zero_mul,add_zero]

/-- On full-row-rank inputs the solver returns a genuine solution. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; n ∈ ℕ; H ∈ Data(F, n, m); b ∈ Vector(F, n), assume LinearIndependent(F, entries(H)). Then

∃ x ∈ Vector(F, m), value(solve(n, H, b)) = some(x) ∧ ∀ i ∈ {0,…,n-1}, (∑_(k ∈ {0,…,m−1}) (entries(H, i, k) · x.get(k))) = b.get(i).
-/
theorem solve_correct {m : ℕ} (n : ℕ) (H : Data F n m) (b : Vector F n)
    (hH : LinearIndependent F (entries H)) :
    ∃ x : Vector F m, (solve n H b).value = some x ∧
      ∀ i : Fin n, (∑ k : Fin m, entries H i k*x.get k) = b.get i := by
  induction n with
  | zero =>
    refine ⟨Vector.replicate m 0,rfl,?_⟩
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    cases hp : (findPivot (H.get 0)).value with
    | none =>
      have hz : entries H 0 = 0 := by
        ext j
        exact pivotScan_none (H.get 0) (List.finRange m) hp j (List.mem_finRange j)
      exact False.elim (hH.ne_zero 0 hz)
    | some j =>
      have hj : entries H 0 j ≠ 0 :=
        pivotScan_some (H.get 0) (List.finRange m) j hp
      have hred : LinearIndependent F (entries (reduceData H j).value) := by
        rw [reduceData_entries]
        exact (independent_reduce_iff (entries H) j hj).mp hH
      obtain ⟨y,hy,hys⟩ := ih (reduceData H j).value (reduceRhs H b j).value hred
      let x := (backSubstitute (H.get 0) (b.get 0) j y).value
      have hhead : (∑ k : Fin m, entries H 0 k*x.get k) = b.get 0 :=
        backSubstitute_head (H.get 0) (b.get 0) j hj y
      refine ⟨x,?_,?_⟩
      · simp only [solve,Counted.bind,hp,hy,Counted.pure,x]
      · intro i
        refine Fin.cases hhead ?_ i
        intro i
        have hrowzero : reduce (entries H) j i j = 0 := by
          simp only [reduce]
          rw [div_mul_cancel₀ _ hj,sub_self]
        have hredx := backSubstitute_zero (H.get 0) (b.get 0) j y
          (reduce (entries H) j i) hrowzero
        have htail := hys i
        rw [reduceData_entries,reduceRhs_value] at htail
        have hrelation : (∑ k : Fin m, reduce (entries H) j i k*x.get k) =
            (∑ k : Fin m, entries H i.succ k*x.get k) -
              (entries H i.succ j / entries H 0 j)*(∑ k : Fin m, entries H 0 k*x.get k) := by
          simp only [reduce,sub_mul,Finset.sum_sub_distrib,Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          ring
        rw [hhead] at hrelation
        change (∑ k : Fin m, reduce (entries H) j i k*x.get k) = _ at hredx
        linear_combination -hrelation+hredx+htail

/-- The complete solve, including right-hand-side updates and back substitution, has polynomial scalar operation count even on inputs that fail the test. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; n ∈ ℕ; H ∈ Data(F, n, m); b ∈ Vector(F, n), we have

operations(solve(n, H, b)) ≤ 8 · (n + 1)² · (m + 1).
-/
theorem solve_operations_le {m : ℕ} (n : ℕ) (H : Data F n m) (b : Vector F n) :
    (solve n H b).operations ≤ 8*(n+1)^2*(m+1) := by
  have hbound : ∀ (n : ℕ) (H : Data F n m) (b : Vector F n),
      (solve n H b).operations ≤ n*(4*m+2)+n^2*(4+2*m) := by
    intro n
    induction n with
    | zero => intro H b; simp [solve,Counted.pure]
    | succ n ih =>
      intro H b
      have hs := findPivot_operations_le (H.get 0)
      cases hp : (findPivot (H.get 0)).value with
      | none =>
        simp only [solve,Counted.bind,hp,Counted.pure,Nat.add_zero]
        nlinarith
      | some j =>
        have hi := ih (reduceData H j).value (reduceRhs H b j).value
        cases hy : (solve n (reduceData H j).value (reduceRhs H b j).value).value with
        | none =>
          simp only [solve,Counted.bind,hp,hy,Counted.pure,reduceData_operations,
            reduceRhs_operations,Nat.add_zero]
          nlinarith
        | some y =>
          have hb := backSubstitute_operations_le (H.get 0) (b.get 0) j y
          simp only [solve,Counted.bind,hp,hy,Counted.pure,reduceData_operations,
            reduceRhs_operations,Nat.add_zero]
          nlinarith
  have h := hbound n H b
  nlinarith

/-- In the square invertible case, the returned vector is exactly the mathematical inverse action used in the protocol. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; M ∈ GLₘ(F); b ∈ Vector(F, m), we have

value(solve(m, materialize(M), b)) = some(Vector.ofFn(Matrix.mulVec((M)⁻¹, ((i ↦ b.get(i)))))).
-/
theorem solve_eq_inverse {m : ℕ} (M : Refresh.«GL» F m) (b : Vector F m) :
    (solve m (materialize M.val) b).value =
      some (Vector.ofFn (Matrix.mulVec (M⁻¹).val (fun i => b.get i))) := by
  have hLI : LinearIndependent F (entries (materialize M.val)) := by
    rw [entries_materialize]
    exact Matrix.linearIndependent_rows_of_isUnit M.isUnit
  obtain ⟨x,hx,hs⟩ := solve_correct m (materialize M.val) b hLI
  rw [hx]
  congr 1
  apply Vector.ext
  intro i hi
  have hsystem : Matrix.mulVec M.val (fun j => x.get j) = fun j => b.get j := by
    ext j
    simpa only [entries_materialize,Matrix.mulVec,dotProduct] using hs j
  have hinv := congrArg (Matrix.mulVec (M⁻¹).val) hsystem
  simp only [Matrix.mulVec_mulVec,Units.inv_mul,Matrix.one_mulVec] at hinv
  have hc := congrFun hinv ⟨i,hi⟩
  simpa [Vector.get] using hc

end CircuitCompiler.Rectangular.Gaussian
