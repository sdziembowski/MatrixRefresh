import Proofs.Compiler.Foundations.Sampling.GaussianRankCost
import Proofs.Compiler.Construction.Parameters



/-!
# Counted finite-field vector operations

The counters below are produced compositionally by the explicit loops. They count scalar arithmetic; indexing, copying, and the allocation of the eager vectors add polynomial structural overhead.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace CircuitCompiler.Rectangular.Gaussian

variable {F : Type*} [Field F] [DecidableEq F]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α a set; n ∈ ℕ; f ∈ {0,…,n-1} → α; i ∈ {0,…,n-1}, we have

get(Vector.ofFn(f))(i) = f(i).
-/
@[simp] theorem get_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  simp [Vector.get]

omit [DecidableEq F] in
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For xs ∈ F*, we have

value(sumLoop(xs)) = xs.sum.
-/
@[simp] theorem sumLoop_value (xs : List F) : (sumLoop xs).value = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumLoop,Counted.bind,addOp,ih]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For xs ∈ F*, we have

operations(sumLoop(xs)) = |xs|.
-/
@[simp] theorem sumLoop_operations (xs : List F) : (sumLoop xs).operations = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumLoop,Counted.bind,addOp,ih]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; x, y ∈ Vector(F, m), we have

value(dotData(x, y)) = ∑_(i ∈ {0,…,m−1}) (x.get(i) · y.get(i)).
-/
@[simp] theorem dotData_value {m : ℕ} (x y : Vector F m) :
    (dotData x y).value = ∑ i : Fin m, x.get i * y.get i := by
  simp [dotData,Counted.bind,tabulate,mulOp,Vector.toList_map,List.map_ofFn,Vector.toList_ofFn,List.sum_ofFn,
    Vector.get]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; x, y ∈ Vector(F, m), we have

operations(dotData(x, y)) = 2 · m.
-/
@[simp] theorem dotData_operations {m : ℕ} (x y : Vector F m) :
    (dotData x y).operations = 2*m := by
  simp [dotData,Counted.bind,mulOp]
  omega

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; H ∈ Data(F, n, m); v ∈ Vector(F, m); i ∈ {0,…,n-1}, we have

value.get(mulVecData(H, v))(i) = Matrix.mulVec(entries(H), ((j ↦ v.get(j))), i).
-/
@[simp] theorem mulVecData_value {n m : ℕ} (H : Data F n m) (v : Vector F m) (i : Fin n) :
    (mulVecData H v).value.get i = Matrix.mulVec (entries H) (fun j => v.get j) i := by
  simp [mulVecData,Matrix.mulVec,dotProduct,entries]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; H ∈ Data(F, n, m); v ∈ Vector(F, m), we have

operations(mulVecData(H, v)) = 2 · n · m .
-/
@[simp] theorem mulVecData_operations {n m : ℕ} (H : Data F n m) (v : Vector F m) :
    (mulVecData H v).operations = 2*n*m := by
  simp [mulVecData]; ring

omit [DecidableEq F] in
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; j ∈ {0,…,n-1}; f ∈ {i ∈ {0,…,n-1} | i ≠ j} → F, we have

(∑_(i ∈ {0,…,n−1}) ({ 0 if i = j,; f((i, hi)) otherwise })) = ∑ᵢ (f(i)).
-/
private theorem sum_skip {n : ℕ} (j : Fin n) (f : {i : Fin n // i ≠ j} → F) :
    (∑ i : Fin n, if hi : i = j then 0 else f ⟨i,hi⟩) = ∑ i, f i := by
  letI : Fintype {i : Fin n // i=j} := Subtype.fintype (fun i : Fin n => i=j)
  have h := Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => i = j)
    (fun i => if hi : i = j then 0 else f ⟨i,hi⟩)
  have hz : (∑ i : {i : Fin n // i=j}, if hi : i.val=j then 0 else f ⟨i.val,hi⟩) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only [dif_pos i.property]
  have ht : (∑ i : {i : Fin n // i≠j}, if hi : i.val=j then 0 else f ⟨i.val,hi⟩) = ∑ i, f i := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [dif_neg i.property]
  calc
    _ = (∑ i : {i : Fin n // i=j}, if hi : i.val=j then (0:F) else f ⟨i.val,hi⟩) +
        (∑ i : {i : Fin n // i≠j}, if hi : i.val=j then (0:F) else f ⟨i.val,hi⟩) := h.symm
    _ = _ := by rw [hz,zero_add,ht]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; u ∈ Vector(F, m); a ∈ Vector(F, n); j ∈ {0,…,n-1}; w ∈ {i ∈ {0,…,n-1} | i ≠ j} → {0,…,m-1} → F; k ∈ {0,…,m-1}, we have

value.get(fillPivotRow(u, a, j, w))(k) = (u.get(k) - ∑ᵢ (a.get(i) · w(i, k))) / a.get(j).
-/
@[simp] theorem fillPivotRow_value {n m : ℕ} (u : Vector F m) (a : Vector F n)
    (j : Fin n) (w : {i : Fin n // i ≠ j} → Fin m → F) (k : Fin m) :
    (fillPivotRow u a j w).value.get k =
      (u.get k - ∑ i, a.get i.val * w i k) / a.get j := by
  simp only [fillPivotRow,tabulate_value_get,Counted.bind,subOp,divOp,sumLoop_value]
  have h : ((tabulate fun i : Fin n => if hi : i=j then Counted.pure (0:F)
      else mulOp (a.get i) (w ⟨i,hi⟩ k)).value.toList).sum =
      ∑ i, a.get i.val * w i k := by
    change ((Vector.ofFn _).map Counted.value).toList.sum = _
    rw [Vector.toList_map,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn]
    convert sum_skip j (fun i => a.get i.val * w i k) using 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i=j <;> simp [hi,Counted.pure,mulOp]
  rw [h]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; u ∈ Vector(F, m); a ∈ Vector(F, n); j ∈ {0,…,n-1}; w ∈ {i ∈ {0,…,n-1} | i ≠ j} → {0,…,m-1} → F, we have

operations(fillPivotRow(u, a, j, w)) ≤ m · (2 · n + 2).
-/
theorem fillPivotRow_operations_le {n m : ℕ} (u : Vector F m) (a : Vector F n)
    (j : Fin n) (w : {i : Fin n // i ≠ j} → Fin m → F) :
    (fillPivotRow u a j w).operations ≤ m*(2*n+2) := by
  rw [fillPivotRow,tabulate_operations]
  calc
    _ ≤ ∑ _k : Fin m, (2*n+2) := by
      apply Finset.sum_le_sum
      intro k _
      simp only [Counted.bind,subOp,divOp,sumLoop_operations,Vector.length_toList,
        tabulate_operations]
      have h : (∑ i : Fin n, (if hi : i=j then Counted.pure (0:F)
          else mulOp (a.get i) (w ⟨i,hi⟩ k)).operations) ≤ n := by
        calc
          _ ≤ ∑ _i : Fin n, 1 := by
            apply Finset.sum_le_sum
            intro i _
            split_ifs <;> simp [Counted.pure,mulOp]
          _ = n := by simp
      omega
    _ = _ := by simp

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; u ∈ Vector(F, m); a ∈ Vector(F, n); j ∈ {0,…,n-1}; w ∈ {i ∈ {0,…,n-1} | i ≠ j} → {0,…,m-1} → F; i ∈ {0,…,n-1}; k ∈ {0,…,m-1}, we have

entries(value(fillData(u, a, j, w)), i, k) = { (u.get(k) - ∑ᵣ (a.get(r) · w(r, k))) / a.get(j) if i = j,; w((i, hi), k) otherwise }.
-/
@[simp] theorem fillData_entries {n m : ℕ} (u : Vector F m) (a : Vector F n)
    (j : Fin n) (w : {i : Fin n // i ≠ j} → Fin m → F) (i : Fin n) (k : Fin m) :
    entries (fillData u a j w).value i k =
      if hi : i=j then (u.get k - ∑ r, a.get r.val * w r k) / a.get j else w ⟨i,hi⟩ k := by
  simp only [fillData,Counted.bind,Counted.pure,entries]
  by_cases hi : i=j
  · simp only [get_ofFn,dif_pos hi]
    exact fillPivotRow_value u a j w k
  · simp [hi,Vector.get]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; u ∈ Vector(F, m); a ∈ Vector(F, n); j ∈ {0,…,n-1}; w ∈ {i ∈ {0,…,n-1} | i ≠ j} → {0,…,m-1} → F, we have

operations(fillData(u, a, j, w)) ≤ m · (2 · n + 2).
-/
theorem fillData_operations_le {n m : ℕ} (u : Vector F m) (a : Vector F n)
    (j : Fin n) (w : {i : Fin n // i ≠ j} → Fin m → F) :
    (fillData u a j w).operations ≤ m*(2*n+2) := by
  simpa only [fillData,Counted.bind,Counted.pure,Nat.add_zero] using
    fillPivotRow_operations_le u a j w

end CircuitCompiler.Rectangular.Gaussian
