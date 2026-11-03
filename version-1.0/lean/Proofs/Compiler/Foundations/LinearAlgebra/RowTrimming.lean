import Proofs.Compiler.Foundations.MatrixRefreshing.Analysis.FourthRootProduct
import Proofs.Compiler.Foundations.LinearAlgebra.TableGeometry



/-!
# Deleting rows and columns using their original uniform L2 norms

The masks act on the original table simultaneously. All norms have the uniform-measure normalization of `TableGeometry`. A positive cutoff `t` costs at most `2 * tableL2Norm A ^ 2 / t` in L1.
-/

set_option autoImplicit false

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace TableAnalysis

open MatrixRefresh

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- Mathematical definition (normal notation): For row and column predicates R,C, define the masked table by Ãᵢⱼ := Aᵢⱼ if both R(i) and C(j) hold, and by Ãᵢⱼ := 0 otherwise. -/
def maskRowsColumns (A : Matrix ι ι ℝ) (r c : ι → Prop) : Matrix ι ι ℝ := by
  classical
  exact fun i j => if r i ∧ c j then A i j else 0

/- Mathematical definition (normal notation): The one-dimensional mask vector at i has coordinate 1 when the row predicate holds at i, and coordinate 0 otherwise. -/
def maskFeature (r : ι → Prop) (i : ι) : EuclideanSpace ℝ Unit := by
  classical
  exact EuclideanSpace.single () (if r i then 1 else 0)

omit [Fintype ι] [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ι → Prop; i ∈ ι, we have

‖ maskFeature(r, i)‖ ≤ 1.
-/
theorem maskFeature_norm_le (r : ι → Prop) (i : ι) : ‖maskFeature r i‖ ≤ 1 := by
  classical
  simp only [maskFeature, PiLp.norm_single, Real.norm_eq_abs]
  split_ifs <;> norm_num

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ι → Prop, we have

‖ maskFeature(r)‖ ≤ 1.
-/
theorem maskFeature_family_norm_le (r : ι → Prop) : ‖maskFeature r‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    (maskFeature_norm_le r)

omit [Fintype ι] [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); r, c ∈ ι → Prop, we have

maskRowsColumns(A, r, c) = innerProductTable(maskFeature(r), maskFeature(c)) ⊙ A.
-/
theorem maskRowsColumns_eq_innerProductTable (A : Matrix ι ι ℝ) (r c : ι → Prop) :
    maskRowsColumns A r c = innerProductTable (maskFeature r) (maskFeature c) ⊙ A := by
  classical
  ext i j
  simp only [maskRowsColumns, innerProductTable, maskFeature, Matrix.hadamard_apply,
    EuclideanSpace.inner_single_left, PiLp.single_apply]
  by_cases hr : r i <;> by_cases hc : c j <;> simp [hr, hc]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); r, c ∈ ι → Prop, we have

‖ maskRowsColumns(A, r, c)‖ ≤ ‖ A‖.
-/
theorem maskRowsColumns_operator_norm_le (A : Matrix ι ι ℝ) (r c : ι → Prop) :
    ‖maskRowsColumns A r c‖ ≤ ‖A‖ := by
  rw [maskRowsColumns_eq_innerProductTable]
  simpa only [one_mul] using schur_multiplier_norm_le_of_bounds
    (maskFeature r) (maskFeature c) A 1 1 (by norm_num) (by norm_num)
    (maskFeature_norm_le r) (maskFeature_norm_le c)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); r, c ∈ ι → Prop, we have

‖ maskRowsColumns(A, r, c)‖_(*,count) ≤ ‖ A‖_(*,count).
-/
theorem maskRowsColumns_nuclearNorm_le (A : Matrix ι ι ℝ) (r c : ι → Prop) :
    nuclearNorm (maskRowsColumns A r c) ≤ nuclearNorm A := by
  rw [maskRowsColumns_eq_innerProductTable]
  calc
    nuclearNorm (innerProductTable (maskFeature r) (maskFeature c) ⊙ A) ≤
        ‖maskFeature r‖ * ‖maskFeature c‖ * nuclearNorm A :=
      schur_multiplier_nuclearNorm_le _ _ _
    _ ≤ 1 * 1 * nuclearNorm A := by
      apply mul_le_mul_of_nonneg_right _ (nuclearNorm_nonneg A)
      exact mul_le_mul (maskFeature_family_norm_le r) (maskFeature_family_norm_le c)
        (norm_nonneg _) (by norm_num)
    _ = nuclearNorm A := by ring

omit [Fintype ι] [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); r, c ∈ ι → Prop; i, j ∈ ι, we have

(maskRowsColumns(A, r, c, i, j))² ≤ (A(i, j))².
-/
theorem maskRowsColumns_sq_le (A : Matrix ι ι ℝ) (r c : ι → Prop) (i j : ι) :
    maskRowsColumns A r c i j ^ 2 ≤ A i j ^ 2 := by
  classical
  unfold maskRowsColumns
  split_ifs <;> simp [sq_nonneg]

omit [Fintype ι] [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); r, c ∈ ι → Prop; i, j ∈ ι, we have

|maskRowsColumns(A, r, c, i, j)| ≤ |A(i, j)|.
-/
theorem maskRowsColumns_abs_le (A : Matrix ι ι ℝ) (r c : ι → Prop) (i j : ι) :
    |maskRowsColumns A r c i j| ≤ |A i j| := by
  classical
  unfold maskRowsColumns
  split_ifs <;> simp [abs_nonneg]

omit [Fintype ι] [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); r, c ∈ ι → Prop; i, j ∈ ι, we have

|A - maskRowsColumns(A, r, c)(i, j)| ≤ |A(i, j)|.
-/
theorem maskRowsColumns_difference_abs_le
    (A : Matrix ι ι ℝ) (r c : ι → Prop) (i j : ι) :
    |(A - maskRowsColumns A r c) i j| ≤ |A i j| := by
  classical
  simp only [Matrix.sub_apply, maskRowsColumns]
  split_ifs <;> simp [abs_nonneg]

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); i ∈ ι, we have

0 ≤ rowL2(A, i).
-/
theorem rowL2_nonneg (A : Matrix ι ι ℝ) (i : ι) : 0 ≤ rowL2 A i :=
  Real.sqrt_nonneg _

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); j ∈ ι, we have

0 ≤ columnL2(A, j).
-/
theorem columnL2_nonneg (A : Matrix ι ι ℝ) (j : ι) : 0 ≤ columnL2 A j :=
  Real.sqrt_nonneg _

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); i ∈ ι, we have

(rowL2(A, i))² = 𝔼ⱼ [(A(i, j))²].
-/
theorem rowL2_sq (A : Matrix ι ι ℝ) (i : ι) :
    rowL2 A i ^ 2 = uavg (fun j => A i j ^ 2) :=
  Real.sq_sqrt (uavg_nonneg (fun _ => sq_nonneg _))

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); j ∈ ι, we have

(columnL2(A, j))² = 𝔼ᵢ [(A(i, j))²].
-/
theorem columnL2_sq (A : Matrix ι ι ℝ) (j : ι) :
    columnL2 A j ^ 2 = uavg (fun i => A i j ^ 2) :=
  Real.sq_sqrt (uavg_nonneg (fun _ => sq_nonneg _))

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι), we have

(‖ A‖₂)² = 𝔼ᵢ [(rowL2(A, i))²].
-/
theorem tableL2Norm_sq_eq_rows (A : Matrix ι ι ℝ) :
    tableL2Norm A ^ 2 = uavg (fun i => rowL2 A i ^ 2) := by
  rw [tableL2Norm_sq]
  simp only [signedL2Sq, uavg_prod, rowL2_sq]

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι), we have

(‖ A‖₂)² = 𝔼ⱼ [(columnL2(A, j))²].
-/
theorem tableL2Norm_sq_eq_columns (A : Matrix ι ι ℝ) :
    tableL2Norm A ^ 2 = uavg (fun j => columnL2 A j ^ 2) := by
  rw [tableL2Norm_sq_eq_rows]
  simp only [rowL2_sq, columnL2_sq]
  exact uavg_comm _

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); r, c ∈ ι → Prop; i ∈ ι, we have

rowL2(maskRowsColumns(A, r, c), i) ≤ rowL2(A, i).
-/
theorem maskRowsColumns_rowL2_le (A : Matrix ι ι ℝ) (r c : ι → Prop) (i : ι) :
    rowL2 (maskRowsColumns A r c) i ≤ rowL2 A i :=
  Real.sqrt_le_sqrt (uavg_mono (maskRowsColumns_sq_le A r c i))

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); r, c ∈ ι → Prop; j ∈ ι, we have

columnL2(maskRowsColumns(A, r, c), j) ≤ columnL2(A, j).
-/
theorem maskRowsColumns_columnL2_le (A : Matrix ι ι ℝ) (r c : ι → Prop) (j : ι) :
    columnL2 (maskRowsColumns A r c) j ≤ columnL2 A j :=
  Real.sqrt_le_sqrt (uavg_mono (fun i => maskRowsColumns_sq_le A r c i j))

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); r, c ∈ ι → Prop, we have

‖ maskRowsColumns(A, r, c)‖₂ ≤ ‖ A‖₂.
-/
theorem maskRowsColumns_tableL2Norm_le (A : Matrix ι ι ℝ) (r c : ι → Prop) :
    tableL2Norm (maskRowsColumns A r c) ≤ tableL2Norm A := by
  have hsq : tableL2Norm (maskRowsColumns A r c) ^ 2 ≤ tableL2Norm A ^ 2 := by
    simp only [tableL2Norm_sq, signedL2Sq]
    exact uavg_mono (fun p => maskRowsColumns_sq_le A r c p.1 p.2)
  nlinarith [tableL2Norm_nonneg A, tableL2Norm_nonneg (maskRowsColumns A r c)]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); r, c ∈ ι → Prop, we have

‖ maskRowsColumns(A, r, c)‖ₒₚ ≤ ‖ A‖ₒₚ.
-/
theorem maskRowsColumns_largestSingularCoefficient_le (A : Matrix ι ι ℝ) (r c : ι → Prop) :
    largestSingularCoefficient (maskRowsColumns A r c) ≤ largestSingularCoefficient A :=
  div_le_div_of_nonneg_right (maskRowsColumns_operator_norm_le A r c) (Nat.cast_nonneg _)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); r, c ∈ ι → Prop, we have

‖ maskRowsColumns(A, r, c)‖_* ≤ ‖ A‖_*.
-/
theorem maskRowsColumns_tableNuclearNorm_le (A : Matrix ι ι ℝ) (r c : ι → Prop) :
    tableNuclearNorm (maskRowsColumns A r c) ≤ tableNuclearNorm A :=
  div_le_div_of_nonneg_right (maskRowsColumns_nuclearNorm_le A r c) (Nat.cast_nonneg _)

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); r, c ∈ ι → Prop, we have

tableL1(maskRowsColumns(A, r, c)) ≤ tableL1(A).
-/
theorem maskRowsColumns_tableL1_le (A : Matrix ι ι ℝ) (r c : ι → Prop) :
    tableL1 (maskRowsColumns A r c) ≤ tableL1 A :=
  uavg_mono (fun p => maskRowsColumns_abs_le A r c p.1 p.2)

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); r, c ∈ ι → Prop, we have

tableL1((A - maskRowsColumns(A, r, c))) ≤ tableL1(A).
-/
theorem maskRowsColumns_difference_tableL1_le (A : Matrix ι ι ℝ) (r c : ι → Prop) :
    tableL1 (A - maskRowsColumns A r c) ≤ tableL1 A :=
  uavg_mono (fun p => maskRowsColumns_difference_abs_le A r c p.1 p.2)

/-
Mathematical definition (normal notation): For A ∈ ℝ^(ι × ι); t ∈ ℝ, define

rowColumnTrim(A, t) := maskRowsColumns(A, ((i ↦ rowL2(A, i) ≤ t)), ((j ↦ columnL2(A, j) ≤ t))).
-/
def rowColumnTrim (A : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  maskRowsColumns A (fun i => rowL2 A i ≤ t) (fun j => columnL2 A j ≤ t)

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); t ∈ ℝ; i ∈ ι, assume 0 ≤ t. Then

rowL2(rowColumnTrim(A, t), i) ≤ t.
-/
theorem rowColumnTrim_rowL2_le (A : Matrix ι ι ℝ) (t : ℝ) (ht : 0 ≤ t) (i : ι) :
    rowL2 (rowColumnTrim A t) i ≤ t := by
  classical
  by_cases hi : rowL2 A i ≤ t
  · exact (maskRowsColumns_rowL2_le _ _ _ _).trans hi
  · have hzero : rowL2 (rowColumnTrim A t) i = 0 := by
      change Real.sqrt (uavg (fun j => rowColumnTrim A t i j ^ 2)) = 0
      simp [rowColumnTrim, maskRowsColumns, hi]
    rw [hzero]
    exact ht

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); t ∈ ℝ; j ∈ ι, assume 0 ≤ t. Then

columnL2(rowColumnTrim(A, t), j) ≤ t.
-/
theorem rowColumnTrim_columnL2_le (A : Matrix ι ι ℝ) (t : ℝ) (ht : 0 ≤ t) (j : ι) :
    columnL2 (rowColumnTrim A t) j ≤ t := by
  classical
  by_cases hj : columnL2 A j ≤ t
  · exact (maskRowsColumns_columnL2_le _ _ _ _).trans hj
  · have hzero : columnL2 (rowColumnTrim A t) j = 0 := by
      change Real.sqrt (uavg (fun i => rowColumnTrim A t i j ^ 2)) = 0
      simp [rowColumnTrim, maskRowsColumns, hj]
    rw [hzero]
    exact ht

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); t ∈ ℝ, we have

‖ rowColumnTrim(A, t)‖₂ ≤ ‖ A‖₂.
-/
theorem rowColumnTrim_tableL2Norm_le (A : Matrix ι ι ℝ) (t : ℝ) :
    tableL2Norm (rowColumnTrim A t) ≤ tableL2Norm A :=
  maskRowsColumns_tableL2Norm_le _ _ _

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); t ∈ ℝ, we have

‖ rowColumnTrim(A, t)‖ₒₚ ≤ ‖ A‖ₒₚ.
-/
theorem rowColumnTrim_largestSingularCoefficient_le (A : Matrix ι ι ℝ) (t : ℝ) :
    largestSingularCoefficient (rowColumnTrim A t) ≤ largestSingularCoefficient A :=
  maskRowsColumns_largestSingularCoefficient_le _ _ _

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); t ∈ ℝ, we have

‖ rowColumnTrim(A, t)‖_* ≤ ‖ A‖_*.
-/
theorem rowColumnTrim_tableNuclearNorm_le (A : Matrix ι ι ℝ) (t : ℝ) :
    tableNuclearNorm (rowColumnTrim A t) ≤ tableNuclearNorm A :=
  maskRowsColumns_tableNuclearNorm_le _ _ _

section Nonempty

variable [Nonempty ι]

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); i ∈ ι, we have

𝔼ⱼ [|A(i, j)|] ≤ rowL2(A, i).
-/
theorem row_abs_mean_le_rowL2 (A : Matrix ι ι ℝ) (i : ι) :
    uavg (fun j => |A i j|) ≤ rowL2 A i := by
  have h := uavg_mul_sq_le (fun j => |A i j|) (fun _ => 1)
  simp only [mul_one, sq_abs, one_pow, uavg_const, mul_one] at h
  have hsq := rowL2_sq A i
  nlinarith [uavg_nonneg (fun j => abs_nonneg (A i j)), rowL2_nonneg A i]

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); j ∈ ι, we have

𝔼ᵢ [|A(i, j)|] ≤ columnL2(A, j).
-/
theorem column_abs_mean_le_columnL2 (A : Matrix ι ι ℝ) (j : ι) :
    uavg (fun i => |A i j|) ≤ columnL2 A j := by
  have h := uavg_mul_sq_le (fun i => |A i j|) (fun _ => 1)
  simp only [mul_one, sq_abs, one_pow, uavg_const, mul_one] at h
  have hsq := columnL2_sq A j
  nlinarith [uavg_nonneg (fun i => abs_nonneg (A i j)), columnL2_nonneg A j]

omit [DecidableEq ι] [Nonempty ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); t ∈ ℝ; i, j ∈ ι, we have

|A - rowColumnTrim(A, t)(i, j)| ≤ ({ 0 if rowL2(A, i) ≤ t,; |A(i, j)| otherwise }) + ({ 0 if columnL2(A, j) ≤ t,; |A(i, j)| otherwise }).
-/
theorem rowColumnTrim_difference_abs_bound (A : Matrix ι ι ℝ) (t : ℝ) (i j : ι) :
    |(A - rowColumnTrim A t) i j| ≤
      (if rowL2 A i ≤ t then 0 else |A i j|) +
      (if columnL2 A j ≤ t then 0 else |A i j|) := by
  classical
  simp only [Matrix.sub_apply, rowColumnTrim, maskRowsColumns]
  by_cases hr : rowL2 A i ≤ t <;> by_cases hc : columnL2 A j ≤ t <;>
    simp [hr, hc, abs_nonneg]

omit [DecidableEq ι] [Nonempty ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); t ∈ ℝ, we have

tableL1((A - rowColumnTrim(A, t))) ≤ 𝔼ᵢ [{ 0 if rowL2(A, i) ≤ t,; 𝔼ⱼ [|A(i, j)|] otherwise }] + 𝔼ⱼ [{ 0 if columnL2(A, j) ≤ t,; 𝔼ᵢ [|A(i, j)|] otherwise }].
-/
theorem rowColumnTrim_loss_le_deleted_means (A : Matrix ι ι ℝ) (t : ℝ) :
    tableL1 (A - rowColumnTrim A t) ≤
      uavg (fun i => if rowL2 A i ≤ t then 0 else uavg (fun j => |A i j|)) +
      uavg (fun j => if columnL2 A j ≤ t then 0 else uavg (fun i => |A i j|)) := by
  classical
  have h := uavg_mono (fun p : ι × ι => rowColumnTrim_difference_abs_bound A t p.1 p.2)
  change tableL1 (A - rowColumnTrim A t) ≤ _ at h
  rw [uavg_add] at h
  convert h using 1
  congr 1
  · rw [uavg_prod]
    apply uavg_congr
    intro i
    by_cases hi : rowL2 A i ≤ t <;> simp [hi]
  · rw [uavg_prod, uavg_comm]
    apply uavg_congr
    intro j
    by_cases hj : columnL2 A j ≤ t <;> simp [hj]

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); t ∈ ℝ, assume 0 < t. Then

tableL1((A - rowColumnTrim(A, t))) ≤ 2 · (‖ A‖₂)² / t.
-/
theorem rowColumnTrim_tableL1_loss_le (A : Matrix ι ι ℝ) (t : ℝ) (ht : 0 < t) :
    tableL1 (A - rowColumnTrim A t) ≤ 2 * tableL2Norm A ^ 2 / t := by
  classical
  have hr : ∀ i, (if rowL2 A i ≤ t then 0 else uavg (fun j => |A i j|)) ≤
      rowL2 A i ^ 2 / t := by
    intro i
    by_cases hi : rowL2 A i ≤ t
    · simp only [hi, ite_true]
      positivity
    · simp only [hi, ite_false]
      apply (row_abs_mean_le_rowL2 A i).trans
      apply (le_div_iff₀ ht).mpr
      have htrow : t < rowL2 A i := lt_of_not_ge hi
      nlinarith [rowL2_nonneg A i]
  have hc : ∀ j, (if columnL2 A j ≤ t then 0 else uavg (fun i => |A i j|)) ≤
      columnL2 A j ^ 2 / t := by
    intro j
    by_cases hj : columnL2 A j ≤ t
    · simp only [hj, ite_true]
      positivity
    · simp only [hj, ite_false]
      apply (column_abs_mean_le_columnL2 A j).trans
      apply (le_div_iff₀ ht).mpr
      have htcol : t < columnL2 A j := lt_of_not_ge hj
      nlinarith [columnL2_nonneg A j]
  calc
    tableL1 (A - rowColumnTrim A t) ≤ _ := rowColumnTrim_loss_le_deleted_means A t
    _ ≤ uavg (fun i => rowL2 A i ^ 2 / t) +
        uavg (fun j => columnL2 A j ^ 2 / t) := add_le_add (uavg_mono hr) (uavg_mono hc)
    _ = 2 * tableL2Norm A ^ 2 / t := by
      simp only [div_eq_mul_inv, uavg_mul_const, ← tableL2Norm_sq_eq_rows,
        ← tableL2Norm_sq_eq_columns]
      ring

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); H, c ∈ ℝ, assume 0 < H; 0 ≤ c; ‖ A‖₂ ≤ c. Then

tableL1((A - rowColumnTrim(A, (H · c)))) ≤ 2 · c / H.
-/
theorem rowColumnTrim_input_loss_le (A : Matrix ι ι ℝ) (H c : ℝ)
    (hH : 0 < H) (hc : 0 ≤ c) (hA : tableL2Norm A ≤ c) :
    tableL1 (A - rowColumnTrim A (H * c)) ≤ 2 * c / H := by
  by_cases hc0 : c = 0
  · subst c
    have h := (maskRowsColumns_difference_tableL1_le A
      (fun i => rowL2 A i ≤ H * 0) (fun j => columnL2 A j ≤ H * 0)).trans
      (tableL1_le_tableL2Norm A)
    change tableL1 (A - rowColumnTrim A (H * 0)) ≤ _ at h
    simpa using h.trans hA
  · have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    calc
      tableL1 (A - rowColumnTrim A (H * c)) ≤ 2 * tableL2Norm A ^ 2 / (H * c) :=
        rowColumnTrim_tableL1_loss_le A (H * c) (mul_pos hH hcp)
      _ ≤ 2 * c ^ 2 / (H * c) := by
        gcongr
        exact tableL2Norm_nonneg A
      _ = 2 * c / H := by field_simp

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Z a set; W ∈ Z → ℝ^(ι × ι); J ∈ ℝ, assume Z is finite; 0 < J. Then

(∑_z (tableL1((W(z) - rowColumnTrim(W(z), J))))) ≤ (2 / J) · ∑_z ((‖ W(z)‖₂)²).
-/
theorem rowColumnTrim_tuple_loss_le {Z : Type*} [Fintype Z]
    (W : Z → Matrix ι ι ℝ) (J : ℝ) (hJ : 0 < J) :
    (∑ z, tableL1 (W z - rowColumnTrim (W z) J)) ≤
      (2 / J) * ∑ z, tableL2Norm (W z) ^ 2 := by
  calc
    _ ≤ ∑ z, 2 * tableL2Norm (W z) ^ 2 / J :=
      Finset.sum_le_sum (fun z _ => rowColumnTrim_tableL1_loss_le (W z) J hJ)
    _ = _ := by simp only [Finset.mul_sum]; congr 1; funext z; ring

end Nonempty

end

end TableAnalysis
