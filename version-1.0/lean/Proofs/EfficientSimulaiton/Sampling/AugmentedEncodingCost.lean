import Proofs.Compiler.GateApproximation.MatrixPhase.AugmentedTensor
import Proofs.Compiler.Foundations.Sampling.GaussianAlgebraCost
import Proofs.Compiler.Construction.Parameters



/-! # Counted construction of the augmented tensor shares -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace CircuitCompiler.Rectangular.Gaussian

open Refresh

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; x, y ∈ Vector(F, n); k ∈ {0,…,(n · n)-1}, we have

value.get(tensorData(x, y))(k) = tensorVector(((i ↦ x.get(i))), ((i ↦ y.get(i))), k).
-/
@[simp] theorem tensorData_value {n : ℕ} (x y : Vector F n) (k : Fin (n*n)) :
    (tensorData x y).value.get k = tensorVector (fun i => x.get i) (fun i => y.get i) k := by
  simp [tensorData,tensorVector,mulOp]

omit [DecidableEq F] in
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; x, y ∈ Vector(F, n), we have

operations(tensorData(x, y)) = n · n.
-/
@[simp] theorem tensorData_operations {n : ℕ} (x y : Vector F n) :
    (tensorData x y).operations = n*n := by
  simp [tensorData,mulOp]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; c ∈ F; x, y ∈ Vector(F, n), we have

operations(augmentedShareData(c, x, y)) = n · n.
-/
@[simp] theorem augmentedShareData_operations {n : ℕ} (c : F) (x y : Vector F n) :
    (augmentedShareData c x y).operations = n*n := by
  simp [augmentedShareData,Counted.bind,Counted.pure]

variable [Fintype F]

/-- The counted routine returns exactly the augmented share used by the compiler proof. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; c ∈ F; x, y ∈ U(F, n), we have

((k ↦ value.get(augmentedShareData(c, Vector.ofFn(x), Vector.ofFn(y)))(k))) = augmentedShare(c, (x, y)).
-/
@[simp] theorem augmentedShareData_value {n : ℕ} (c : F) (x y : U F n) :
    (fun k => (augmentedShareData c (Vector.ofFn x.val) (Vector.ofFn y.val)).value.get k) =
      (augmentedShare c (x,y)).val := by
  funext k
  simp only [augmentedShareData,Counted.bind,Counted.pure,get_ofFn,augmentedShare]
  have h : (fun i => (tensorData (Vector.ofFn x.val) (Vector.ofFn y.val)).value.get i) =
      tensorVector x.val y.val := by
    funext i
    simp [tensorData_value,get_ofFn]
  rw [h]

end CircuitCompiler.Rectangular.Gaussian
