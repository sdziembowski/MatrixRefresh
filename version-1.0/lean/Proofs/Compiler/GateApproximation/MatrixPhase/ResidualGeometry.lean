import Proofs.Compiler.GateApproximation.MatrixPhase.GateTruncation
import Proofs.Compiler.GateApproximation.MatrixPhase.JointGraphCycle
import Proofs.Compiler.GateApproximation.MatrixPhase.Collisions
import Proofs.Compiler.GateApproximation.MatrixPhase.Counting



/-!
# The inverse-free enlarged table in the residual moment proof

The extra column coordinate is retained for arbitrary matrices. On invertible matrices its sparse embedding preserves every row Gram entry, and hence the whole signed four-cycle. Conditioning is applied only to this nonnegative complete statistic, never to its possibly negative individual corners.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

open scoped BigOperators Classical Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Nonempty Z]

/-- Embed each column at its selected extra coordinate. The square-root normalization compensates exactly for the extra uniform coordinate. -/
/-
Mathematical definition (normal notation): For K ∈ X → Y → ℝ; select ∈ Y → Z, define

sparseColumnLift(K, select) := (x, y ↦ { √(|Z|) · K(x, (y)₁) if (y)₂ = select((y)₁),; 0 otherwise }).
-/
def sparseColumnLift (K : X → Y → ℝ) (select : Y → Z) : X → Y × Z → ℝ :=
  fun x y => if y.2 = select y.1 then Real.sqrt (Fintype.card Z) * K x y.1 else 0

omit [Fintype X] in
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K ∈ X → Y → ℝ; select ∈ Y → Z; x, x' ∈ X, we have

rowProduct(sparseColumnLift(K, select), x, x') = rowProduct(K, x, x').
-/
theorem rowProduct_sparseColumnLift (K : X → Y → ℝ) (select : Y → Z) (x x' : X) :
    rowProduct (sparseColumnLift K select) x x' = rowProduct K x x' := by
  unfold rowProduct
  rw [uavg_prod]
  apply uavg_congr
  intro y
  have hp (z : Z) : sparseColumnLift K select x (y,z) *
      sparseColumnLift K select x' (y,z) =
        if z = select y then (Fintype.card Z : ℝ) * (K x y * K x' y) else 0 := by
    by_cases hz : z = select y
    · simp only [sparseColumnLift, hz, if_true]
      calc
        _ = Real.sqrt (Fintype.card Z : ℝ) ^ 2 * (K x y * K x' y) := by ring
        _ = _ := by rw [Real.sq_sqrt (by positivity)]
    · simp [sparseColumnLift, hz]
  simp_rw [hp]
  have hZ : (Fintype.card Z : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [uavg, hZ]

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K ∈ X → Y → ℝ; select ∈ Y → Z, we have

fourCycle(sparseColumnLift(K, select)) = fourCycle(K).
-/
theorem fourCycle_sparseColumnLift (K : X → Y → ℝ) (select : Y → Z) :
    fourCycle (sparseColumnLift K select) = fourCycle K := by
  simp only [fourCycle, rowProduct_sparseColumnLift]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

/-- Extend only the two refreshed share coordinates by zero. The old coordinates range over arbitrary finite feature carriers. -/
/-
Mathematical definition (normal notation): For E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ; x ∈ X; u ∈ V(F, m); y ∈ Y; v ∈ V(F, m), define

featureZeroExtend(E, x, u, y, v) := { E((x, (u, (h)₁)), (y, (v, (h)₂))) if u ≠ 0 ∧ v ≠ 0,; 0 otherwise }.
-/
def featureZeroExtend (E : (X × U F m) → (Y × U F m) → ℝ)
    (x : X) (u : V F m) (y : Y) (v : V F m) : ℝ :=
  if h : u ≠ 0 ∧ v ≠ 0 then E (x, ⟨u,h.1⟩) (y,⟨v,h.2⟩) else 0

omit [Fintype X] [Fintype Y] [Fintype F] in
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ; x ∈ X; u ∈ U(F, m); y ∈ Y; v ∈ U(F, m), we have

featureZeroExtend(E, x, u, y, v) = E((x, u), (y, v)).
-/
@[simp] theorem featureZeroExtend_nonzero
    (E : (X × U F m) → (Y × U F m) → ℝ)
    (x : X) (u : U F m) (y : Y) (v : U F m) :
    featureZeroExtend E x u.val y v.val = E (x,u) (y,v) := by
  simp [featureZeroExtend, u.property, v.property]

/-- The actual restriction, written over independent old feature carriers. -/
/-
Mathematical definition (normal notation): Substitute the refresh equations into a table of old and new shares:

E^M(x,y) := E((x,a(x) · M),(y,M⁻¹ · b(y))).

The matrix M is invertible, and the resulting table has only the old-data row and column arguments.
-/
def refreshTable (a : X → U F m) (b : Y → U F m)
    (E : (X × U F m) → (Y × U F m) → ℝ) (M : Refresh.«GL» F m) : X → Y → ℝ :=
  fun x y => E (x,rowRefresh (a x) M) (y,columnRefresh (b y) M)

/-- An inverse-free rectangular table, defined also for singular matrices. -/
/-
Mathematical definition (normal notation): Let N = |𝔽|ᵐ and extend E by zero whenever a share is zero. For any matrix A, including singular matrices, define a table with rows x and columns (y,v) by

Ẽ^A(x,(y,v)) := { √N · E((x,a(x) · A),(y,v)), A · v = b(y),; 0, otherwise }

This construction avoids taking A⁻¹.
-/
def enlargedRestriction (a : X → U F m) (b : Y → U F m)
    (E : (X × U F m) → (Y × U F m) → ℝ)
    (A : Matrix (Fin m) (Fin m) F) : X → Y × V F m → ℝ :=
  fun x yv => if Matrix.mulVec A yv.2 = (b yv.1).val then
    Real.sqrt (Fintype.card (V F m)) *
      featureZeroExtend E x (Matrix.vecMul (a x).val A) yv.1 yv.2 else 0

omit [Fintype F] [DecidableEq F] in
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For M ∈ GLₘ(F); v ∈ V(F, m); r ∈ U(F, m), we have

Matrix.mulVec(M, v) = r ⇔ v = columnRefresh(r, M).
-/
theorem mulVec_eq_iff_columnRefresh (M : Refresh.«GL» F m) (v : V F m) (r : U F m) :
    Matrix.mulVec M.val v = r.val ↔ v = (columnRefresh r M).val := by
  constructor
  · intro h
    have h' := congrArg (fun u => Matrix.mulVec (M⁻¹).val u) h
    simpa [columnRefresh] using h'
  · intro h
    simp [h, columnRefresh]

omit [Fintype X] [Fintype Y] in
/-- On an invertible matrix the enlarged table is exactly a sparse lift of the actual refresh graph, with one selected new column per old input. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m); b ∈ Y → U(F, m); E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ; M ∈ GLₘ(F), we have

enlargedRestriction(a, b, E, M) = sparseColumnLift(refreshTable(a, b, E, M), ((y ↦ columnRefresh(b(y), M)))).
-/
theorem enlargedRestriction_GL (a : X → U F m) (b : Y → U F m)
    (E : (X × U F m) → (Y × U F m) → ℝ) (M : Refresh.«GL» F m) :
    enlargedRestriction a b E M.val =
      sparseColumnLift (refreshTable a b E M) (fun y => (columnRefresh (b y) M).val) := by
  funext x yv
  simp only [enlargedRestriction, sparseColumnLift, mulVec_eq_iff_columnRefresh]
  by_cases h : yv.2 = (columnRefresh (b yv.1) M).val
  · simp only [h, if_true]
    congr 1
    change featureZeroExtend E x (rowRefresh (a x) M).val yv.1
      (columnRefresh (b yv.1) M).val = _
    exact featureZeroExtend_nonzero _ _ _ _ _
  · simp only [if_neg h]

/-- The enlarged and actual graph tables have identical four-cycle moments on every invertible matrix. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m); b ∈ Y → U(F, m); E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ; M ∈ GLₘ(F), we have

fourCycle(enlargedRestriction(a, b, E, M)) = fourCycle(refreshTable(a, b, E, M)).
-/
theorem fourCycle_enlargedRestriction_GL (a : X → U F m) (b : Y → U F m)
    (E : (X × U F m) → (Y × U F m) → ℝ) (M : Refresh.«GL» F m) :
    fourCycle (enlargedRestriction a b E M.val) = fourCycle (refreshTable a b E M) := by
  rw [enlargedRestriction_GL, fourCycle_sparseColumnLift]

/-- The actual GL four-cycle average costs at most four times the unrestricted matrix average. Nonnegativity is justified for the complete signed cycle. -/

/-
Mathematical statement (normal notation): Let E be any real old/new-share table, and let a,b be maps to nonzero long shares. Write E^M(x,y) = E((x,a(x) · M),(y,M⁻¹ · b(y))). Let Ẽ^A be the inverse-free enlarged table, with its √(|𝔽ᵐ|) normalization. Then

𝔼_(M ← GLₘ(𝔽)) [C₄(E^M)] ≤ 4 · 𝔼_(A ← 𝔽^(m × m)) [C₄(Ẽ^A)],

where C₄(K) = 𝔼_(x,x',y,y') [K(x,y) · K(x',y) · K(x,y') · K(x',y')].
-/
theorem refreshTable_fourCycle_le_unrestricted (a : X → U F m) (b : Y → U F m)
    (E : (X × U F m) → (Y × U F m) → ℝ) :
    uavg (fun M : Refresh.«GL» F m => fourCycle (refreshTable a b E M)) ≤
      4 * uavg (fun A : Matrix (Fin m) (Fin m) F => fourCycle (enlargedRestriction a b E A)) := by
  simpa only [fourCycle_enlargedRestriction_GL] using
    uavg_GL_le_four_mul_uavg_matrices
      (fun A => fourCycle (enlargedRestriction a b E A))
      (fun A => fourCycle_nonneg (enlargedRestriction a b E A))

/-- Casting a real table to the existing complex matrix interface preserves the signed normalized four-cycle exactly. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K ∈ X → X → ℝ, we have

𝔼ᵤ [cycleEntry(((x, y ↦ K(x, y))), u)] = fourCycle(K).
-/
theorem real_fourCycle_eq_complex (K : X → X → ℝ) :
    uavg (cycleEntry (fun x y => (K x y : ℂ))) = fourCycle K := by
  rw [fourCycle_expansion]
  simp [uavg_prod, cycleEntry]

/-- The fourth power of the actual normalized operator norm is bounded by the complete real four-cycle. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K ∈ X → X → ℝ, we have

(GateTruncation.opNorm(((x, y ↦ K(x, y)))))⁴ ≤ fourCycle(K).
-/
theorem real_opNorm_four_le_fourCycle [DecidableEq X]
    (K : X → X → ℝ) :
    GateTruncation.opNorm (fun x y => (K x y : ℂ)) ^ 4 ≤ fourCycle K := by
  rw [← real_fourCycle_eq_complex, uavg_cycleEntry, GateTruncation.opNorm, div_pow]
  exact div_le_div_of_nonneg_right
    (complexMatrix_norm_four_le_fourCycle (fun x y => (K x y : ℂ))) (by positivity)

/-- The operational residual fourth moment reduces to the actual unrestricted enlarged-table average with the correct absolute conditioning constant. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); E ∈ (X × U(F, m)) → (X × U(F, m)) → ℝ, we have

𝔼_(M ∈ GLₘ(F)) [(GateTruncation.opNorm(((x, y ↦ refreshTable(a, b, E, M, x, y)))))⁴] ≤ 4 · 𝔼_(A ∈ F^({0,…,m−1} × {0,…,m−1})) [fourCycle(enlargedRestriction(a, b, E, A))].
-/
theorem refreshTable_op_four_le_unrestricted [DecidableEq X]
    (a b : X → U F m) (E : (X × U F m) → (X × U F m) → ℝ) :
    uavg (fun M : Refresh.«GL» F m =>
      GateTruncation.opNorm (fun x y => (refreshTable a b E M x y : ℂ)) ^ 4) ≤
      4 * uavg (fun A : Matrix (Fin m) (Fin m) F => fourCycle (enlargedRestriction a b E A)) := by
  exact (uavg_mono (fun M => real_opNorm_four_le_fourCycle (refreshTable a b E M))).trans
    (refreshTable_fourCycle_le_unrestricted a b E)

end

end CircuitCompiler.RefreshAnalysis
