import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Data.Matrix.Basis
import Proofs.Compiler.Foundations.LinearAlgebra.NuclearNorm
import Proofs.Compiler.Foundations.LinearAlgebra.Projection
import Proofs.Compiler.Foundations.LinearAlgebra.TableGeometry



/-!
# Joint nuclear balls in counting-measure L2 geometry

Matrix entries are represented by Euclidean vectors, so `PiLp 2` on blocks has the joint counting-measure L2 norm. The feasible set uses the genuine matrix nuclear norm (defined as the dual of the matrix operator norm). We prove its nonemptiness, closedness, convexity, and stability under zeroing a block, then apply the generic closest-point projection theorem.
-/

set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace TableAnalysis

noncomputable section

variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype Z]

/-- If d ≥ 0, e ≥ 0, b ≤ c, a ≤ b + e · d, and d² = a − c, then d ≤ e. -/
private theorem projection_dual_scalar (a b c d e : ℝ) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hvar : b - c ≤ 0) (htest : a ≤ b + e * d) (hself : d ^ 2 = a - c) :
    d ≤ e := by
  nlinarith only [hd, he, hvar, htest, hself]

/-- If b ≤ c, a ≤ b + e, and a − c = d, then d ≤ e. -/
private theorem projection_unit_scalar (a b c d e : ℝ) (hsupport : b ≤ c)
    (htest : a ≤ b + e) (hresidual : a - c = d) : d ≤ e := by
  linarith only [hsupport, htest, hresidual]

/-- A square matrix's entries, with the counting-measure L2 norm. -/
/-
Mathematical definition (normal notation): For ι a set, define

MatrixEntries := EuclideanSpace(ℝ, (ι × ι)).
-/
abbrev MatrixEntries (ι : Type*) := EuclideanSpace ℝ (ι × ι)

/-- A tuple of square matrix blocks with the joint counting-measure L2 norm. -/
/-
Mathematical definition (normal notation): For Z,ι a set, define

MatrixTuple := PiLp(2, ((x ∈ Z ↦ MatrixEntries(ι)))).
-/
abbrev MatrixTuple (Z ι : Type*) := PiLp 2 (fun _ : Z => MatrixEntries ι)

/-
Mathematical definition (normal notation): For x ∈ MatrixEntries(ι), define

entryMatrix(x) := (i, j ↦ x((i, j))) .
-/
def entryMatrix (x : MatrixEntries ι) : Matrix ι ι ℝ := fun i j => x (i, j)

omit [Fintype ι] [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

entryMatrix(0) = 0.
-/
@[simp] lemma entryMatrix_zero : entryMatrix (0 : MatrixEntries ι) = 0 :=
  rfl

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For x, y ∈ MatrixEntries(ι), we have

entryMatrix((x + y)) = entryMatrix(x) + entryMatrix(y).
-/
@[simp] lemma entryMatrix_add (x y : MatrixEntries ι) :
    entryMatrix (x + y) = entryMatrix x + entryMatrix y :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ℝ; x ∈ MatrixEntries(ι), we have

entryMatrix((r · x)) = r · entryMatrix(x).
-/
@[simp] lemma entryMatrix_smul (r : ℝ) (x : MatrixEntries ι) :
    entryMatrix (r • x) = r • entryMatrix x :=
  rfl

/- Mathematical definition (normal notation): From a vector of matrix entries x, construct the linear functional B ↦ ∑_(i,j) xᵢⱼ · Bᵢⱼ. This assignment is itself linear in x. -/
def entryDualLinear : MatrixEntries ι →ₗ[ℝ] (Matrix ι ι ℝ →L[ℝ] ℝ) where
  toFun x := countingPairingDual (entryMatrix x)
  map_add' x y := by rw [entryMatrix_add, countingPairingDual_add]
  map_smul' r x := by
    ext B
    simp [countingPairingDual_apply, countingPairing, entryMatrix, Finset.mul_sum,
      smul_eq_mul, mul_assoc]

/-
Mathematical definition (normal notation): For x ∈ MatrixEntries(ι), define

blockNuclearNorm(x) := ‖ entryMatrix(x)‖_(*,count).
-/
def blockNuclearNorm (x : MatrixEntries ι) : ℝ := nuclearNorm (entryMatrix x)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

ConvexOn(ℝ, universe, blockNuclearNorm(ι = ι)).
-/
lemma blockNuclearNorm_convexOn : ConvexOn ℝ Set.univ (blockNuclearNorm (ι := ι)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  change nuclearNorm (entryMatrix (a • x + b • y)) ≤ _
  rw [entryMatrix_add, entryMatrix_smul, entryMatrix_smul]
  calc
    _ ≤ nuclearNorm (a • entryMatrix x) + nuclearNorm (b • entryMatrix y) :=
      nuclearNorm_add_le _ _
    _ = _ := by
      rw [nuclearNorm_smul, nuclearNorm_smul, abs_of_nonneg ha, abs_of_nonneg hb]
      rfl

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

Continuous(blockNuclearNorm(ι = ι)).
-/
lemma continuous_blockNuclearNorm : Continuous (blockNuclearNorm (ι := ι)) := by
  exact continuousOn_univ.mp (blockNuclearNorm_convexOn.continuousOn isOpen_univ)

/-
Mathematical definition (normal notation): For G ∈ MatrixTuple(Z, ι), define

jointNuclearNorm(G) := ∑_z (blockNuclearNorm(G(z))).
-/
def jointNuclearNorm (G : MatrixTuple Z ι) : ℝ := ∑ z, blockNuclearNorm (G z)

/-
Mathematical definition (normal notation): For R ∈ ℝ, define

jointNuclearBall(R) := {G | jointNuclearNorm(G) ≤ R}.
-/
def jointNuclearBall (R : ℝ) : Set (MatrixTuple Z ι) := {G | jointNuclearNorm G ≤ R}

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

Continuous(jointNuclearNorm(Z = Z, ι = ι)).
-/
lemma continuous_jointNuclearNorm : Continuous (jointNuclearNorm (Z := Z) (ι := ι)) := by
  unfold jointNuclearNorm
  exact continuous_finset_sum _ (fun z _ =>
    continuous_blockNuclearNorm.comp (PiLp.continuous_apply 2 _ z))

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For R ∈ ℝ, assume 0 ≤ R. Then

Nonempty(jointNuclearBall(Z = Z, ι = ι, R)) .
-/
lemma jointNuclearBall_nonempty (R : ℝ) (hR : 0 ≤ R) :
    (jointNuclearBall (Z := Z) (ι := ι) R).Nonempty := by
  refine ⟨0, ?_⟩
  simpa [jointNuclearBall, jointNuclearNorm, blockNuclearNorm] using hR

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For R ∈ ℝ, we have

IsClosed(jointNuclearBall(Z = Z, ι = ι, R)) .
-/
lemma jointNuclearBall_closed (R : ℝ) :
    IsClosed (jointNuclearBall (Z := Z) (ι := ι) R) :=
  isClosed_le continuous_jointNuclearNorm continuous_const

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For R ∈ ℝ, we have

Convex(ℝ, jointNuclearBall(Z = Z, ι = ι, R)).
-/
lemma jointNuclearBall_convex (R : ℝ) :
    Convex ℝ (jointNuclearBall (Z := Z) (ι := ι) R) := by
  intro G hG H hH a b ha hb hab
  change jointNuclearNorm (a • G + b • H) ≤ R
  change jointNuclearNorm G ≤ R at hG
  change jointNuclearNorm H ≤ R at hH
  calc
    jointNuclearNorm (a • G + b • H) ≤
        ∑ z, (a * blockNuclearNorm (G z) + b * blockNuclearNorm (H z)) := by
      apply Finset.sum_le_sum
      intro z _
      change nuclearNorm (entryMatrix (a • G z + b • H z)) ≤ _
      rw [entryMatrix_add, entryMatrix_smul, entryMatrix_smul]
      calc
        _ ≤ nuclearNorm (a • entryMatrix (G z)) + nuclearNorm (b • entryMatrix (H z)) :=
          nuclearNorm_add_le _ _
        _ = _ := by
          rw [nuclearNorm_smul, nuclearNorm_smul, abs_of_nonneg ha, abs_of_nonneg hb]
          rfl
    _ = a * jointNuclearNorm G + b * jointNuclearNorm H := by
      simp [jointNuclearNorm, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ a * R + b * R := add_le_add
      (mul_le_mul_of_nonneg_left hG ha) (mul_le_mul_of_nonneg_left hH hb)
    _ = R := by rw [← add_mul, hab, one_mul]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For R ∈ ℝ, we have

ZeroBlockStable(jointNuclearBall(Z = Z, ι = ι, R)).
-/
lemma jointNuclearBall_zeroBlockStable (R : ℝ) :
    ZeroBlockStable (jointNuclearBall (Z := Z) (ι := ι) R) := by
  classical
  intro G hG z
  change jointNuclearNorm (zeroBlock z G) ≤ R
  apply le_trans _ hG
  apply Finset.sum_le_sum
  intro w _
  by_cases hw : w = z
  · subst w
    simp only [zeroBlock_apply_same, blockNuclearNorm, entryMatrix_zero, nuclearNorm_zero]
    exact nuclearNorm_nonneg _
  · rw [zeroBlock_apply_ne z w G hw]

omit [DecidableEq ι] in
/-- The Euclidean entry norm is exactly the counting-measure matrix L2 norm. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For x ∈ MatrixEntries(ι), we have

(‖ x‖)² = ∑ᵢ (∑ⱼ ((entryMatrix(x, i, j))²)).
-/
lemma matrixEntries_norm_sq (x : MatrixEntries ι) :
    ‖x‖ ^ 2 = ∑ i, ∑ j, (entryMatrix x i j) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  simp [entryMatrix, Real.norm_eq_abs, sq_abs]

/-- The actual joint nuclear ball admits a counting-measure L2 closest point, and every output matrix block has no larger counting-measure L2 norm. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For R ∈ ℝ; A ∈ MatrixTuple(Z, ι), assume 0 ≤ R. Then

∃ G ∈ jointNuclearBall(Z = Z, ι = ι, R), (‖ A - G‖ = inf_(W ∈ jointNuclearBall(Z = Z, ι = ι, R)) (‖ A - W‖)) ∧ (∀ z, (‖ G(z)‖)² ≤ inner(ℝ, A(z), G(z))) ∧ (∀ z, ‖ G(z)‖ ≤ ‖ A(z)‖).
-/
theorem exists_jointNuclearProjection (R : ℝ) (hR : 0 ≤ R) (A : MatrixTuple Z ι) :
    ∃ G ∈ jointNuclearBall (Z := Z) (ι := ι) R,
      (‖A - G‖ = ⨅ W : jointNuclearBall (Z := Z) (ι := ι) R, ‖A - W‖) ∧
      (∀ z, ‖G z‖ ^ 2 ≤ inner ℝ (A z) (G z)) ∧
      (∀ z, ‖G z‖ ≤ ‖A z‖) :=
  exists_nearestPoint_block_contraction (β := fun _ : Z => MatrixEntries ι)
    (jointNuclearBall (Z := Z) (ι := ι) R)
    (jointNuclearBall_nonempty R hR) (jointNuclearBall_closed R)
    (jointNuclearBall_convex R) (jointNuclearBall_zeroBlockStable R) A

/-
Mathematical definition (normal notation): For A ∈ ℝ^(ι × ι), define

euclideanEntries(A) := WithLp.toLp(2, ((ij ↦ A((ij)₁, (ij)₂)))).
-/
def euclideanEntries (A : Matrix ι ι ℝ) : MatrixEntries ι :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

omit [Fintype ι] [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι), we have

entryMatrix(euclideanEntries(A)) = A.
-/
@[simp] lemma entryMatrix_euclideanEntries (A : Matrix ι ι ℝ) :
    entryMatrix (euclideanEntries A) = A :=
  rfl

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(ι × ι); W ∈ MatrixEntries(ι), we have

inner(ℝ, euclideanEntries(A), W) = countingPairing(A, entryMatrix(W)).
-/
lemma euclideanEntries_inner (A : Matrix ι ι ℝ) (W : MatrixEntries ι) :
    inner ℝ (euclideanEntries A) W = countingPairing A (entryMatrix W) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp [euclideanEntries, countingPairing, entryMatrix, mul_comm]

/-- Coefficients of a matrix functional in the standard coordinate basis. -/
/-
Mathematical definition (normal notation): For f ∈ ℝ^(ι × ι) —linear over ℝ→ ℝ, define

functionalMatrix(f) := (i, j ↦ f(Matrix.single(i, j, 1))).
-/
def functionalMatrix (f : Matrix ι ι ℝ →L[ℝ] ℝ) : Matrix ι ι ℝ :=
  fun i j => f (Matrix.single i j 1)

/-- Every matrix functional is a counting pairing with a genuine matrix, independently of the norm chosen on the matrix domain. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ ℝ^(ι × ι) —linear over ℝ→ ℝ, we have

countingPairingDual(functionalMatrix(f)) = f.
-/
lemma countingPairingDual_functionalMatrix (f : Matrix ι ι ℝ →L[ℝ] ℝ) :
    countingPairingDual (functionalMatrix f) = f := by
  ext B
  rw [countingPairingDual_apply]
  have hsingle (i j : ι) (c : ℝ) :
      Matrix.single i j c = c • (Matrix.single i j 1 : Matrix ι ι ℝ) := by
    rw [Matrix.smul_single]
    simp
  calc
    countingPairing (functionalMatrix f) B =
        ∑ i, ∑ j, f (Matrix.single i j (B i j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hsingle i j (B i j), map_smul]
      simp [functionalMatrix, smul_eq_mul, mul_comm]
    _ = f (∑ i, ∑ j, Matrix.single i j (B i j)) := by simp [map_sum]
    _ = f B := by rw [← Matrix.matrix_eq_sum_single]

/-- The dual nuclear unit ball attains the operator norm of every test matrix. Hahn--Banach supplies a norming functional; its coefficient matrix supplies the nuclear-unit witness. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For W ∈ MatrixEntries(ι), we have

∃ B ∈ MatrixEntries(ι), blockNuclearNorm(B) ≤ 1 ∧ inner(ℝ, B, W) = ‖ entryMatrix(W)‖.
-/
theorem exists_blockNuclear_dualWitness (W : MatrixEntries ι) :
    ∃ B : MatrixEntries ι, blockNuclearNorm B ≤ 1 ∧
      inner ℝ B W = ‖entryMatrix W‖ := by
  obtain ⟨f, hf, hval⟩ := exists_dual_vector'' ℝ (entryMatrix W)
  refine ⟨euclideanEntries (functionalMatrix f), ?_, ?_⟩
  · simpa [blockNuclearNorm, nuclearNorm, countingPairingDual_functionalMatrix] using hf
  · rw [euclideanEntries_inner, ← countingPairingDual_apply,
      countingPairingDual_functionalMatrix]
    exact hval

/-- The maximum of the operator norms of the test blocks, encoded by the ordinary supremum norm of a real-valued finite function. -/
/-
Mathematical definition (normal notation): For W ∈ MatrixTuple(Z, ι), define

tupleOperatorNorm(W) := ‖ (z ↦ ‖ entryMatrix(W(z))‖)‖.
-/
def tupleOperatorNorm (W : MatrixTuple Z ι) : ℝ := ‖fun z => ‖entryMatrix (W z)‖‖

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, W ∈ MatrixEntries(ι), we have

inner(ℝ, A, W) = countingPairing(entryMatrix(A), entryMatrix(W)).
-/
lemma matrixEntries_inner (A W : MatrixEntries ι) :
    inner ℝ A W = countingPairing (entryMatrix A) (entryMatrix W) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp [countingPairing, entryMatrix, mul_comm]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For W ∈ MatrixTuple(Z, ι); z ∈ Z, we have

‖ entryMatrix(W(z))‖ ≤ tupleOperatorNorm(W).
-/
lemma blockOperatorNorm_le_tuple (W : MatrixTuple Z ι) (z : Z) :
    ‖entryMatrix (W z)‖ ≤ tupleOperatorNorm W := by
  simpa [tupleOperatorNorm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    norm_le_pi_norm (fun w => ‖entryMatrix (W w)‖) z

omit [DecidableEq ι] in
/-- Passing from joint counting-measure L2 error to the sum of block errors costs exactly the square root of the number of blocks. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For G ∈ MatrixTuple(Z, ι), we have

(∑_z (‖ G(z)‖)) ≤ √(|Z|) · ‖ G‖.
-/
theorem sum_blockNorm_le (G : MatrixTuple Z ι) :
    (∑ z, ‖G z‖) ≤ Real.sqrt (Fintype.card Z : ℝ) * ‖G‖ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Z => (1 : ℝ)) (fun z => ‖G z‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hcs
  rw [← PiLp.norm_sq_eq_of_L2] at hcs
  have hsq : (Real.sqrt (Fintype.card Z : ℝ) * ‖G‖) ^ 2 =
      (Fintype.card Z : ℝ) * ‖G‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun z _ => norm_nonneg (G z)))
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1
  rwa [hsq]

/-- Vectorization of a family of uniform tables: entries are divided by the cardinality of the share space, giving exactly the table HS geometry. -/
/-
Mathematical definition (normal notation): For A ∈ Z → ℝ^(ι × ι), define

uniformTuple(A) := WithLp.toLp(2, ((z ↦ (|ι|)⁻¹ · euclideanEntries(A(z))))).
-/
def uniformTuple (A : Z → Matrix ι ι ℝ) : MatrixTuple Z ι :=
  WithLp.toLp 2 (fun z => (Fintype.card ι : ℝ)⁻¹ • euclideanEntries (A z))

omit [DecidableEq ι] [Fintype Z] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ Z → ℝ^(ι × ι); z ∈ Z, we have

‖ uniformTuple(A, z)‖ = ‖ A(z)‖₂.
-/
lemma uniformTuple_blockNorm (A : Z → Matrix ι ι ℝ) (z : Z) :
    ‖uniformTuple A z‖ = tableL2Norm (A z) := by
  simp [uniformTuple, tableL2Norm, entryVector, euclideanEntries, norm_smul,
    div_eq_mul_inv, mul_comm]

omit [Fintype Z] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ Z → ℝ^(ι × ι); z ∈ Z, we have

blockNuclearNorm(uniformTuple(A, z)) = ‖ A(z)‖_*.
-/
lemma uniformTuple_blockNuclearNorm (A : Z → Matrix ι ι ℝ) (z : Z) :
    blockNuclearNorm (uniformTuple A z) = tableNuclearNorm (A z) := by
  simp [uniformTuple, blockNuclearNorm, entryMatrix_smul, nuclearNorm_smul,
    tableNuclearNorm, abs_of_nonneg (show 0 ≤ (Fintype.card ι : ℝ)⁻¹ by positivity),
    div_eq_mul_inv, mul_comm]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ Z → ℝ^(ι × ι), we have

jointNuclearNorm(uniformTuple(A)) = ∑_z (‖ A(z)‖_*).
-/
lemma uniformTuple_jointNuclearNorm (A : Z → Matrix ι ι ℝ) :
    jointNuclearNorm (uniformTuple A) = ∑ z, tableNuclearNorm (A z) := by
  simp [jointNuclearNorm, uniformTuple_blockNuclearNorm]

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ Z → ℝ^(ι × ι), we have

(‖ uniformTuple(A)‖)² = ∑_z ((‖ A(z)‖₂)²).
-/
lemma uniformTuple_norm_sq (A : Z → Matrix ι ι ℝ) :
    ‖uniformTuple A‖ ^ 2 = ∑ z, tableL2Norm (A z) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp_rw [uniformTuple_blockNorm]

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ Z → ℝ^(ι × ι), we have

‖ uniformTuple(A)‖ = √(∑_z ((‖ A(z)‖₂)²)).
-/
lemma uniformTuple_norm_eq_sqrt_sum (A : Z → Matrix ι ι ℝ) :
    ‖uniformTuple A‖ = Real.sqrt (∑ z, tableL2Norm (A z) ^ 2) := by
  rw [← uniformTuple_norm_sq, Real.sqrt_sq (norm_nonneg _)]

omit [Fintype Z] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ Z → ℝ^(ι × ι); z ∈ Z, we have

‖ entryMatrix(uniformTuple(A, z))‖ = ‖ A(z)‖ₒₚ.
-/
lemma uniformTuple_blockOperatorNorm (A : Z → Matrix ι ι ℝ) (z : Z) :
    ‖entryMatrix (uniformTuple A z)‖ = largestSingularCoefficient (A z) := by
  change ‖(Fintype.card ι : ℝ)⁻¹ • A z‖ = _
  rw [norm_smul_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  simp [largestSingularCoefficient, div_eq_mul_inv, mul_comm]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ Z → ℝ^(ι × ι), we have

tupleOperatorNorm(uniformTuple(A)) = ‖ (z ↦ ‖ A(z)‖ₒₚ)‖.
-/
lemma uniformTuple_operatorNorm (A : Z → Matrix ι ι ℝ) :
    tupleOperatorNorm (uniformTuple A) = ‖fun z => largestSingularCoefficient (A z)‖ := by
  simp [tupleOperatorNorm, uniformTuple_blockOperatorNorm]

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B ∈ Z → ℝ^(ι × ι), we have

inner(ℝ, uniformTuple(A), uniformTuple(B)) = ∑_z (countingPairing(A(z), B(z)) / (|ι|)²).
-/
lemma uniformTuple_inner (A B : Z → Matrix ι ι ℝ) :
    inner ℝ (uniformTuple A) (uniformTuple B) =
      ∑ z, countingPairing (A z) (B z) / (Fintype.card ι : ℝ) ^ 2 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro z _
  change inner ℝ ((Fintype.card ι : ℝ)⁻¹ • euclideanEntries (A z))
    ((Fintype.card ι : ℝ)⁻¹ • euclideanEntries (B z)) = _
  rw [real_inner_smul_left, real_inner_smul_right, euclideanEntries_inner,
    entryMatrix_euclideanEntries]
  ring

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B ∈ Z → ℝ^(ι × ι), we have

uniformTuple(((z ↦ A(z) - B(z)))) = uniformTuple(A) - uniformTuple(B).
-/
lemma uniformTuple_sub (A B : Z → Matrix ι ι ℝ) :
    uniformTuple (fun z => A z - B z) = uniformTuple A - uniformTuple B := by
  ext z p
  simp [uniformTuple, euclideanEntries, mul_sub]

/-- Upper support bound for the genuine joint nuclear ball. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For R ∈ ℝ; G ∈ MatrixTuple(Z, ι); W ∈ MatrixTuple(Z, ι), assume G ∈ jointNuclearBall(R). Then

inner(ℝ, G, W) ≤ R · tupleOperatorNorm(W).
-/
theorem jointNuclearBall_inner_le (R : ℝ) {G : MatrixTuple Z ι}
    (hG : G ∈ jointNuclearBall R) (W : MatrixTuple Z ι) :
    inner ℝ G W ≤ R * tupleOperatorNorm W := by
  rw [PiLp.inner_apply]
  calc
    (∑ z, inner ℝ (G z) (W z)) ≤
        ∑ z, blockNuclearNorm (G z) * tupleOperatorNorm W := by
      apply Finset.sum_le_sum
      intro z _
      rw [matrixEntries_inner]
      calc
        _ ≤ |countingPairing (entryMatrix (G z)) (entryMatrix (W z))| := le_abs_self _
        _ ≤ nuclearNorm (entryMatrix (G z)) * ‖entryMatrix (W z)‖ := abs_countingPairing_le _ _
        _ ≤ blockNuclearNorm (G z) * tupleOperatorNorm W :=
          mul_le_mul_of_nonneg_left (blockOperatorNorm_le_tuple W z) (nuclearNorm_nonneg _)
    _ = jointNuclearNorm G * tupleOperatorNorm W := by
      unfold jointNuclearNorm
      rw [Finset.sum_mul]
    _ ≤ R * tupleOperatorNorm W :=
      mul_le_mul_of_nonneg_right hG (norm_nonneg _)

section NonemptyBlocks

variable [Nonempty Z]

/-- A joint nuclear ball has support value `R * max_z opNorm(W_z)`. This theorem supplies the attaining point needed for the distance argument. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For R ∈ ℝ; W ∈ MatrixTuple(Z, ι), assume 0 ≤ R. Then

∃ B ∈ jointNuclearBall(Z = Z, ι = ι, R), inner(ℝ, B, W) = R · tupleOperatorNorm(W).
-/
theorem jointNuclearBall_support_witness (R : ℝ) (hR : 0 ≤ R) (W : MatrixTuple Z ι) :
    ∃ B ∈ jointNuclearBall (Z := Z) (ι := ι) R,
      inner ℝ B W = R * tupleOperatorNorm W := by
  classical
  obtain ⟨z, _, hz⟩ := Finset.exists_max_image Finset.univ
    (fun z => ‖entryMatrix (W z)‖) Finset.univ_nonempty
  have hmax : tupleOperatorNorm W = ‖entryMatrix (W z)‖ := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (entryMatrix (W z)))).2
      intro w
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hz w (Finset.mem_univ w)
    · simpa [tupleOperatorNorm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
        norm_le_pi_norm (fun w => ‖entryMatrix (W w)‖) z
  obtain ⟨b, hb, hpair⟩ := exists_blockNuclear_dualWitness (W z)
  let B : MatrixTuple Z ι := WithLp.toLp 2 (fun w => if w = z then R • b else 0)
  refine ⟨B, ?_, ?_⟩
  · change jointNuclearNorm B ≤ R
    have hsum : jointNuclearNorm B = R * blockNuclearNorm b := by
      unfold jointNuclearNorm
      rw [Finset.sum_eq_single z]
      · simp [B, blockNuclearNorm, nuclearNorm_smul, abs_of_nonneg hR]
      · intro w _ hw
        simp [B, hw, blockNuclearNorm]
      · simp
    rw [hsum]
    simpa using mul_le_mul_of_nonneg_left hb hR
  · rw [PiLp.inner_apply]
    rw [Finset.sum_eq_single z]
    · simp [B, hpair, hmax, real_inner_smul_left]
    · intro w _ hw
      simp [B, hw]
    · simp

/-- The dual test estimate bounds the distance of the actual closest point to the joint nuclear ball. Testing with the unnormalized residual avoids any division by a possibly zero counting-measure L2 norm. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For R, e ∈ ℝ; A, G ∈ MatrixTuple(Z, ι), assume 0 ≤ R; 0 ≤ e; G ∈ jointNuclearBall(R); ‖ A - G‖ = inf_(W ∈ jointNuclearBall(Z = Z, ι = ι, R)) (‖ A - W‖); ∀ W ∈ MatrixTuple(Z, ι), inner(ℝ, A, W) ≤ R · tupleOperatorNorm(W) + e · ‖ W‖. Then

‖ A - G‖ ≤ e.
-/
theorem jointNuclearProjection_distance_le (R e : ℝ) (hR : 0 ≤ R) (he : 0 ≤ e)
    {A G : MatrixTuple Z ι} (hG : G ∈ jointNuclearBall R)
    (hnearest : ‖A - G‖ = ⨅ W : jointNuclearBall (Z := Z) (ι := ι) R, ‖A - W‖)
    (htest : ∀ W : MatrixTuple Z ι,
      inner ℝ A W ≤ R * tupleOperatorNorm W + e * ‖W‖) :
    ‖A - G‖ ≤ e := by
  obtain ⟨B, hB, hpair⟩ := jointNuclearBall_support_witness R hR (A - G)
  have hvar : inner ℝ (A - G) (B - G) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero (F := MatrixTuple Z ι)
      (u := A) (v := G) (jointNuclearBall_convex R) hG).mp hnearest B hB
  rw [inner_sub_right, ← real_inner_comm (A - G) B, ← real_inner_comm (A - G) G] at hvar
  have htestD := htest (A - G)
  rw [← hpair] at htestD
  have hself : ‖A - G‖ ^ 2 = inner ℝ A (A - G) - inner ℝ G (A - G) := by
    rw [← real_inner_self_eq_norm_sq (A - G), inner_sub_left]
  exact projection_dual_scalar _ _ _ _ _ (norm_nonneg (A - G)) he hvar htestD hself

/-- Complete projection adapter used by nuclear compression: the uniform dual bound supplies the approximation error, while genuine nuclear-ball geometry supplies all blockwise counting-measure L2 contractions. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For R, e ∈ ℝ; A ∈ MatrixTuple(Z, ι), assume 0 ≤ R; 0 ≤ e; ∀ W ∈ MatrixTuple(Z, ι), inner(ℝ, A, W) ≤ R · tupleOperatorNorm(W) + e · ‖ W‖. Then

∃ G ∈ jointNuclearBall(Z = Z, ι = ι, R), (‖ A - G‖ = inf_(W ∈ jointNuclearBall(Z = Z, ι = ι, R)) (‖ A - W‖)) ∧ ‖ A - G‖ ≤ e ∧ (∀ z, (‖ G(z)‖)² ≤ inner(ℝ, A(z), G(z))) ∧ (∀ z, ‖ G(z)‖ ≤ ‖ A(z)‖).
-/
theorem exists_jointNuclearProjection_of_dual_bound (R e : ℝ)
    (hR : 0 ≤ R) (he : 0 ≤ e) (A : MatrixTuple Z ι)
    (htest : ∀ W : MatrixTuple Z ι,
      inner ℝ A W ≤ R * tupleOperatorNorm W + e * ‖W‖) :
    ∃ G ∈ jointNuclearBall (Z := Z) (ι := ι) R,
      (‖A - G‖ = ⨅ W : jointNuclearBall (Z := Z) (ι := ι) R, ‖A - W‖) ∧
      ‖A - G‖ ≤ e ∧
      (∀ z, ‖G z‖ ^ 2 ≤ inner ℝ (A z) (G z)) ∧
      (∀ z, ‖G z‖ ≤ ‖A z‖) := by
  obtain ⟨G, hG, hnearest, hinner, hblock⟩ := exists_jointNuclearProjection R hR A
  exact ⟨G, hG, hnearest, jointNuclearProjection_distance_le R e hR he hG hnearest htest,
    hinner, hblock⟩

/-- The compression dual estimate only needs to be checked on the joint counting-measure L2 unit ball. The support witness is chosen for the normalized residual, so no separate homogeneity theorem for the operator norm is needed. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For R, e ∈ ℝ; A, G ∈ MatrixTuple(Z, ι), assume 0 ≤ R; 0 ≤ e; G ∈ jointNuclearBall(R); ‖ A - G‖ = inf_(W ∈ jointNuclearBall(Z = Z, ι = ι, R)) (‖ A - W‖); ∀ W ∈ MatrixTuple(Z, ι), (‖ W‖ ≤ 1) ⇒ inner(ℝ, A, W) ≤ R · tupleOperatorNorm(W) + e. Then

‖ A - G‖ ≤ e.
-/
theorem jointNuclearProjection_distance_le_of_unit_tests (R e : ℝ)
    (hR : 0 ≤ R) (he : 0 ≤ e) {A G : MatrixTuple Z ι}
    (hG : G ∈ jointNuclearBall R)
    (hnearest : ‖A - G‖ = ⨅ W : jointNuclearBall (Z := Z) (ι := ι) R, ‖A - W‖)
    (htest : ∀ W : MatrixTuple Z ι, ‖W‖ ≤ 1 →
      inner ℝ A W ≤ R * tupleOperatorNorm W + e) :
    ‖A - G‖ ≤ e := by
  by_cases hzero : ‖A - G‖ = 0
  · simpa [hzero] using he
  let U : MatrixTuple Z ι := ‖A - G‖⁻¹ • (A - G)
  have hU : ‖U‖ = 1 := by
    simp [U, norm_smul, inv_mul_cancel₀ hzero]
  obtain ⟨B, hB, hpair⟩ := jointNuclearBall_support_witness R hR U
  have hvar : inner ℝ (A - G) (B - G) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero (F := MatrixTuple Z ι)
      (u := A) (v := G) (jointNuclearBall_convex R) hG).mp hnearest B hB
  rw [inner_sub_right] at hvar
  have hsupport : inner ℝ B U ≤ inner ℝ G U := by
    dsimp [U]
    rw [real_inner_smul_right, real_inner_smul_right,
      real_inner_comm (A - G) B, real_inner_comm (A - G) G]
    exact mul_le_mul_of_nonneg_left (sub_nonpos.mp hvar) (inv_nonneg.mpr (norm_nonneg _))
  have htestU := htest U (by rw [hU])
  rw [← hpair] at htestU
  have hresidual : inner ℝ (A - G) U = ‖A - G‖ := by
    dsimp [U]
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  rw [inner_sub_left] at hresidual
  exact projection_unit_scalar _ _ _ _ _ hsupport htestU hresidual

/-- Unit-test version of the nuclear projection adapter, with the same nearest-point and blockwise contraction guarantees. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For R, e ∈ ℝ; A ∈ MatrixTuple(Z, ι), assume 0 ≤ R; 0 ≤ e; ∀ W ∈ MatrixTuple(Z, ι), (‖ W‖ ≤ 1) ⇒ inner(ℝ, A, W) ≤ R · tupleOperatorNorm(W) + e. Then

∃ G ∈ jointNuclearBall(Z = Z, ι = ι, R), (‖ A - G‖ = inf_(W ∈ jointNuclearBall(Z = Z, ι = ι, R)) (‖ A - W‖)) ∧ ‖ A - G‖ ≤ e ∧ (∀ z, (‖ G(z)‖)² ≤ inner(ℝ, A(z), G(z))) ∧ (∀ z, ‖ G(z)‖ ≤ ‖ A(z)‖).
-/
theorem exists_jointNuclearProjection_of_unit_tests (R e : ℝ)
    (hR : 0 ≤ R) (he : 0 ≤ e) (A : MatrixTuple Z ι)
    (htest : ∀ W : MatrixTuple Z ι, ‖W‖ ≤ 1 →
      inner ℝ A W ≤ R * tupleOperatorNorm W + e) :
    ∃ G ∈ jointNuclearBall (Z := Z) (ι := ι) R,
      (‖A - G‖ = ⨅ W : jointNuclearBall (Z := Z) (ι := ι) R, ‖A - W‖) ∧
      ‖A - G‖ ≤ e ∧
      (∀ z, ‖G z‖ ^ 2 ≤ inner ℝ (A z) (G z)) ∧
      (∀ z, ‖G z‖ ≤ ‖A z‖) := by
  obtain ⟨G, hG, hnearest, hinner, hblock⟩ := exists_jointNuclearProjection R hR A
  exact ⟨G, hG, hnearest,
    jointNuclearProjection_distance_le_of_unit_tests R e hR he hG hnearest htest,
    hinner, hblock⟩

section NonemptyShares

variable [Nonempty ι]

omit [DecidableEq ι] [Fintype Z] [Nonempty Z] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For G ∈ MatrixTuple(Z, ι), we have

uniformTuple(((z ↦ |ι| · entryMatrix(G(z))))) = G.
-/
lemma uniformTuple_recover (G : MatrixTuple Z ι) :
    uniformTuple (fun z => (Fintype.card ι : ℝ) • entryMatrix (G z)) = G := by
  have hd : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  ext z p
  change (Fintype.card ι : ℝ)⁻¹ * ((Fintype.card ι : ℝ) * G z p) = G z p
  rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]

/-- Actual uniform-table version of nuclear compression. The test space uses normalized matrix entries; output tables keep the original entry scale. The error and every block contraction therefore use exactly `tableL2Norm`. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For R, e ∈ ℝ; A ∈ Z → ℝ^(ι × ι), assume 0 ≤ R; 0 ≤ e; ∀ W ∈ MatrixTuple(Z, ι), (‖ W‖ ≤ 1) ⇒ inner(ℝ, uniformTuple(A), W) ≤ R · tupleOperatorNorm(W) + e. Then

∃ G ∈ Z → ℝ^(ι × ι), (∑_z (‖ G(z)‖_*)) ≤ R ∧ √(∑_z ((‖ (A(z) - G(z))‖₂)²)) ≤ e ∧ (∑_z (tableL1((A(z) - G(z))))) ≤ √(|Z|) · e ∧ (∀ z, ‖ G(z)‖₂ ≤ ‖ A(z)‖₂).
-/
theorem exists_tableNuclearNormProjection_of_unit_tests (R e : ℝ)
    (hR : 0 ≤ R) (he : 0 ≤ e) (A : Z → Matrix ι ι ℝ)
    (htest : ∀ W : MatrixTuple Z ι, ‖W‖ ≤ 1 →
      inner ℝ (uniformTuple A) W ≤ R * tupleOperatorNorm W + e) :
    ∃ G : Z → Matrix ι ι ℝ,
      (∑ z, tableNuclearNorm (G z)) ≤ R ∧
      Real.sqrt (∑ z, tableL2Norm (A z - G z) ^ 2) ≤ e ∧
      (∑ z, tableL1 (A z - G z)) ≤ Real.sqrt (Fintype.card Z : ℝ) * e ∧
      (∀ z, tableL2Norm (G z) ≤ tableL2Norm (A z)) := by
  obtain ⟨P, hP, _, hdist, _, hblock⟩ :=
    exists_jointNuclearProjection_of_unit_tests R e hR he (uniformTuple A) htest
  let G : Z → Matrix ι ι ℝ := fun z => (Fintype.card ι : ℝ) • entryMatrix (P z)
  have hG : uniformTuple G = P := uniformTuple_recover P
  have hres : ‖uniformTuple (fun z => A z - G z)‖ ≤ e := by
    rw [uniformTuple_sub, hG]
    exact hdist
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · rw [← uniformTuple_jointNuclearNorm, hG]
    exact hP
  · rwa [uniformTuple_norm_eq_sqrt_sum] at hres
  · calc
      (∑ z, tableL1 (A z - G z)) ≤ ∑ z, tableL2Norm (A z - G z) :=
        Finset.sum_le_sum (fun z _ => tableL1_le_tableL2Norm _)
      _ = ∑ z, ‖uniformTuple (fun z => A z - G z) z‖ := by
        simp [uniformTuple_blockNorm]
      _ ≤ Real.sqrt (Fintype.card Z : ℝ) * ‖uniformTuple (fun z => A z - G z)‖ :=
        sum_blockNorm_le _
      _ ≤ Real.sqrt (Fintype.card Z : ℝ) * e :=
        mul_le_mul_of_nonneg_left hres (Real.sqrt_nonneg _)
  · intro z
    have hz := hblock z
    rw [← hG, uniformTuple_blockNorm, uniformTuple_blockNorm] at hz
    exact hz

/-- Table-only test interface: all dual hypotheses and output bounds use genuine matrix families in the uniform-table normalization. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For R, e ∈ ℝ; A ∈ Z → ℝ^(ι × ι), assume 0 ≤ R; 0 ≤ e; ∀ W ∈ Z → ℝ^(ι × ι), ((∑_z ((‖ W(z)‖₂)²)) ≤ 1) ⇒ inner(ℝ, uniformTuple(A), uniformTuple(W)) ≤ R · ‖ (z ↦ ‖ W(z)‖ₒₚ)‖ + e. Then

∃ G ∈ Z → ℝ^(ι × ι), (∑_z (‖ G(z)‖_*)) ≤ R ∧ √(∑_z ((‖ (A(z) - G(z))‖₂)²)) ≤ e ∧ (∑_z (tableL1((A(z) - G(z))))) ≤ √(|Z|) · e ∧ (∀ z, ‖ G(z)‖₂ ≤ ‖ A(z)‖₂).
-/
theorem exists_tableNuclearNormProjection_of_table_tests (R e : ℝ)
    (hR : 0 ≤ R) (he : 0 ≤ e) (A : Z → Matrix ι ι ℝ)
    (htest : ∀ W : Z → Matrix ι ι ℝ, (∑ z, tableL2Norm (W z) ^ 2) ≤ 1 →
      inner ℝ (uniformTuple A) (uniformTuple W) ≤
        R * ‖fun z => largestSingularCoefficient (W z)‖ + e) :
    ∃ G : Z → Matrix ι ι ℝ,
      (∑ z, tableNuclearNorm (G z)) ≤ R ∧
      Real.sqrt (∑ z, tableL2Norm (A z - G z) ^ 2) ≤ e ∧
      (∑ z, tableL1 (A z - G z)) ≤ Real.sqrt (Fintype.card Z : ℝ) * e ∧
      (∀ z, tableL2Norm (G z) ≤ tableL2Norm (A z)) := by
  apply exists_tableNuclearNormProjection_of_unit_tests R e hR he A
  intro Y hY
  let W : Z → Matrix ι ι ℝ := fun z => (Fintype.card ι : ℝ) • entryMatrix (Y z)
  have hW : uniformTuple W = Y := uniformTuple_recover Y
  have hnorm : (∑ z, tableL2Norm (W z) ^ 2) ≤ 1 := by
    rw [← uniformTuple_norm_sq, hW]
    nlinarith [norm_nonneg Y]
  have ht := htest W hnorm
  rw [hW, ← uniformTuple_operatorNorm W, hW] at ht
  exact ht

end NonemptyShares

end NonemptyBlocks

end

end TableAnalysis
