import Proofs.Compiler.GateApproximation.Interfaces.StrictTruncation
import Proofs.Compiler.GateApproximation.MatrixPhase.RefreshGramEstimates



/-!
# The polar test of the strict answer-table truncation

The direction coordinates include zeros for discarded singular directions. Their mean Gram is therefore a diagonal projection rather than an identity matrix on a subtype. This keeps exactly the same retained table and rank.
-/

set_option autoImplicit false

set_option maxHeartbeats 1800000

open scoped BigOperators Matrix Matrix.Norms.L2Operator RealInnerProductSpace

namespace CircuitCompiler.TruncatedAnswerNorm

open MatrixRefresh TableAnalysis RefreshAnalysis SingularTruncation

noncomputable section

variable {n : ℕ}

/- Mathematical definition (normal notation): For the k-th Euclidean singular value sₖ of an n × n matrix, define a selector equal to one if sₖ>n · β, and zero otherwise. Thus it selects precisely normalized coefficients exceeding β. -/
def strictKeep (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (k : Fin n) : ℝ :=
  if (n : ℝ) * β < (matrixSVD A).sigma k then 1 else 0

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; k ∈ {0,…,n-1}, we have

0 ≤ strictKeep(A, β, k).
-/
theorem strictKeep_nonneg (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (k : Fin n) :
    0 ≤ strictKeep A β k := by
  unfold strictKeep; split_ifs <;> norm_num

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; k ∈ {0,…,n-1}, we have

strictKeep(A, β, k) ≤ 1.
-/
theorem strictKeep_le_one (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (k : Fin n) :
    strictKeep A β k ≤ 1 := by
  unfold strictKeep; split_ifs <;> norm_num

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; k ∈ {0,…,n-1}, we have

(strictKeep(A, β, k))² = strictKeep(A, β, k).
-/
@[simp] theorem strictKeep_sq (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (k : Fin n) :
    strictKeep A β k ^ 2 = strictKeep A β k := by
  unfold strictKeep; split_ifs <;> norm_num

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; k ∈ {0,…,n-1}, we have

σ(matrixSVD(A))(k) · strictKeep(A, β, k) = strictSigma(A, β, k).
-/
theorem sigma_mul_keep (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (k : Fin n) :
    (matrixSVD A).sigma k * strictKeep A β k = strictSigma A β k := by
  unfold strictKeep strictSigma
  split_ifs <;> simp

/-
Mathematical definition (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ, define

finiteRank(A, β) := ∑ₖ (strictKeep(A, β, k)).
-/
def finiteRank (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) : ℝ :=
  ∑ k, strictKeep A β k

/-
Mathematical definition (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; i ∈ {0,…,n-1}, define

finiteUnitLeft(A, β, i) := WithLp.toLp(2, ((k ↦ √n · strictKeep(A, β, k) · left(matrixSVD(A))(k, i)))).
-/
def finiteUnitLeft (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun k => Real.sqrt (n : ℝ) * strictKeep A β k * (matrixSVD A).left k i)

/-
Mathematical definition (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; i ∈ {0,…,n-1}, define

finiteUnitRight(A, β, i) := WithLp.toLp(2, ((k ↦ √n · strictKeep(A, β, k) · right(matrixSVD(A))(k, i)))).
-/
def finiteUnitRight (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun k => Real.sqrt (n : ℝ) * strictKeep A β k * (matrixSVD A).right k i)

/-
Mathematical definition (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ, define

finitePolar(A, β) := svdMatrix(left(matrixSVD(A)), right(matrixSVD(A)), ((k ↦ n · strictKeep(A, β, k)))).
-/
def finitePolar (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  svdMatrix (matrixSVD A).left (matrixSVD A).right (fun k => (n : ℝ) * strictKeep A β k)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; i ∈ {0,…,n-1}, we have

(‖ finiteUnitLeft(A, β, i)‖)² = n · ∑ₖ (strictKeep(A, β, k) · (left(matrixSVD(A))(k, i))²) .
-/
theorem finiteUnitLeft_energy_eq (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (i : Fin n) :
    ‖finiteUnitLeft A β i‖ ^ 2 =
      (n : ℝ) * ∑ k, strictKeep A β k * (matrixSVD A).left k i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  simp only [finiteUnitLeft, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg n), strictKeep_sq, mul_assoc]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; i ∈ {0,…,n-1}, we have

(‖ finiteUnitRight(A, β, i)‖)² = n · ∑ₖ (strictKeep(A, β, k) · (right(matrixSVD(A))(k, i))²).
-/
theorem finiteUnitRight_energy_eq (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (i : Fin n) :
    ‖finiteUnitRight A β i‖ ^ 2 =
      (n : ℝ) * ∑ k, strictKeep A β k * (matrixSVD A).right k i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  simp only [finiteUnitRight, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg n), strictKeep_sq, mul_assoc]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; i, j ∈ {0,…,n-1}, we have

finitePolar(A, β, i, j) = inner(ℝ, finiteUnitLeft(A, β, i), finiteUnitRight(A, β, j)).
-/
theorem finitePolar_factorization (A : Matrix (Fin n) (Fin n) ℝ)
    (β : ℝ) (i j : Fin n) :
    finitePolar A β i j = inner ℝ (finiteUnitLeft A β i) (finiteUnitRight A β j) := by
  simp only [finitePolar, svdMatrix, finiteUnitLeft, finiteUnitRight,
    PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro k _
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
  have hk := strictKeep_sq A β k
  calc
    _ = (Real.sqrt (n : ℝ) ^ 2) * (strictKeep A β k ^ 2) *
        ((matrixSVD A).left k i * (matrixSVD A).right k j) := by rw [hs, hk]; ring
    _ = _ := by ring

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ, assume n ≠ 0. Then

normalizedGram(((i, k ↦ finiteUnitLeft(A, β, i, k)))) = Matrix.diagonal(strictKeep(A, β)).
-/
theorem finiteUnitLeft_gram [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) :
    normalizedGram (fun i k => finiteUnitLeft A β i k) = Matrix.diagonal (strictKeep A β) := by
  ext k l
  unfold normalizedGram finiteUnitLeft uavg
  simp only [Fintype.card_fin]
  calc
    _ = (n : ℝ)⁻¹ * (Real.sqrt (n : ℝ) ^ 2 *
        (strictKeep A β k * strictKeep A β l) *
        ∑ i, (matrixSVD A).left k i * (matrixSVD A).left l i) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Real.sq_sqrt (Nat.cast_nonneg _), orthonormalBasis_coordinate_inner]
      by_cases h : k = l
      · subst l
        simp only [ite_true, Matrix.diagonal_apply_eq, mul_one]
        rw [← pow_two, strictKeep_sq]
        field_simp [ne_of_gt (fin_card_real_pos (n := n))]
      · simp [h]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ, assume n ≠ 0. Then

normalizedGram(((i, k ↦ finiteUnitRight(A, β, i, k)))) = Matrix.diagonal(strictKeep(A, β)).
-/
theorem finiteUnitRight_gram [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) :
    normalizedGram (fun i k => finiteUnitRight A β i k) = Matrix.diagonal (strictKeep A β) := by
  ext k l
  unfold normalizedGram finiteUnitRight uavg
  simp only [Fintype.card_fin]
  calc
    _ = (n : ℝ)⁻¹ * (Real.sqrt (n : ℝ) ^ 2 *
        (strictKeep A β k * strictKeep A β l) *
        ∑ i, (matrixSVD A).right k i * (matrixSVD A).right l i) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Real.sq_sqrt (Nat.cast_nonneg _), orthonormalBasis_coordinate_inner]
      by_cases h : k = l
      · subst l
        simp only [ite_true, Matrix.diagonal_apply_eq, mul_one]
        rw [← pow_two, strictKeep_sq]
        field_simp [ne_of_gt (fin_card_real_pos (n := n))]
      · simp [h]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; k ∈ {0,…,n-1}, assume 0 ≤ β. Then

(n · β)² · strictKeep(A, β, k) ≤ (σ(matrixSVD(A))(k))².
-/
theorem cutoff_sq_mul_keep_le (A : Matrix (Fin n) (Fin n) ℝ)
    (β : ℝ) (hβ : 0 ≤ β) (k : Fin n) :
    ((n : ℝ) * β) ^ 2 * strictKeep A β k ≤ (matrixSVD A).sigma k ^ 2 := by
  unfold strictKeep
  split_ifs with hk
  · simpa only [mul_one] using
      pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg n) hβ) hk.le 2
  · simpa only [mul_zero] using sq_nonneg ((matrixSVD A).sigma k)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; i ∈ {0,…,n-1}, assume n ≠ 0; 0 < β. Then

(‖ finiteUnitLeft(A, β, i)‖)² ≤ (rowL2(A, i))² / β².
-/
theorem finiteUnitLeft_energy [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (hβ : 0 < β) (i : Fin n) :
    ‖finiteUnitLeft A β i‖ ^ 2 ≤ rowL2 A i ^ 2 / β ^ 2 := by
  have hn := fin_card_real_pos (n := n)
  have hs : ((n : ℝ) * β) ^ 2 *
      (∑ k, strictKeep A β k * (matrixSVD A).left k i ^ 2) ≤ ∑ j, A i j ^ 2 := by
    rw [matrixSVD_row_sq, Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (cutoff_sq_mul_keep_le A β hβ.le k) (sq_nonneg ((matrixSVD A).left k i)))
  rw [finiteUnitLeft_energy_eq, rowL2_sq_eq_counting]
  apply (le_div_iff₀ (sq_pos_of_pos hβ)).mpr
  apply (le_div_iff₀ hn).mpr
  nlinarith only [hs]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; i ∈ {0,…,n-1}, assume n ≠ 0; 0 < β. Then

(‖ finiteUnitRight(A, β, i)‖)² ≤ (columnL2(A, i))² / β².
-/
theorem finiteUnitRight_energy [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (hβ : 0 < β) (i : Fin n) :
    ‖finiteUnitRight A β i‖ ^ 2 ≤ columnL2 A i ^ 2 / β ^ 2 := by
  have hn := fin_card_real_pos (n := n)
  have hs : ((n : ℝ) * β) ^ 2 *
      (∑ k, strictKeep A β k * (matrixSVD A).right k i ^ 2) ≤ ∑ j, A j i ^ 2 := by
    rw [matrixSVD_column_sq, Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (cutoff_sq_mul_keep_le A β hβ.le k) (sq_nonneg ((matrixSVD A).right k i)))
  rw [finiteUnitRight_energy_eq, columnL2_sq_eq_counting]
  apply (le_div_iff₀ (sq_pos_of_pos hβ)).mpr
  apply (le_div_iff₀ hn).mpr
  nlinarith only [hs]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ, assume n ≠ 0. Then

finiteRank(A, β) · β ≤ ‖ strictFinitePart(A, β)‖_*.
-/
theorem finiteRank_mul_cutoff [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) :
    finiteRank A β * β ≤ tableNuclearNorm (strictFinitePart A β) := by
  rw [strictFinitePart_nuclear_eq]
  apply (le_div_iff₀ (fin_card_real_pos (n := n))).mpr
  unfold finiteRank
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  unfold strictKeep strictSigma
  split_ifs with hk
  · simpa only [one_mul, mul_one, mul_comm] using hk.le
  · simp

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ, assume n ≠ 0. Then

pairing(A, finitePolar(A, β)) = ‖ strictFinitePart(A, β)‖_*.
-/
theorem finitePolar_pairing [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) :
    pairing A (finitePolar A β) = tableNuclearNorm (strictFinitePart A β) := by
  rw [pairing_eq_countingPairing_div_card, (matrixSVD A).countingPairing_eq_sum,
    strictFinitePart_nuclear_eq]
  simp only [finitePolar, svdMatrix_map_basis, inner_smul_right,
    (matrixSVD A).left.inner_eq_ite, if_true, mul_one, Fintype.card_fin]
  have hs : (∑ k, (matrixSVD A).sigma k * ((n : ℝ) * strictKeep A β k)) =
      (n : ℝ) * ∑ k, strictSigma A β k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← sigma_mul_keep]
    ring
  rw [hs]
  have hn : (n : ℝ) ≠ 0 := ne_of_gt (fin_card_real_pos (n := n))
  field_simp

variable {I : Type*} [Fintype I] [Nonempty I]

/-
Mathematical definition (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, define

strictRank(A, β) := finiteRank(svdFiniteTable(A), β).
-/
def strictRank (A : Matrix I I ℝ) (β : ℝ) : ℝ := finiteRank (svdFiniteTable A) β

/-
Mathematical definition (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; i ∈ I, define

strictUnitLeft(A, β, i) := finiteUnitLeft(svdFiniteTable(A), β, Fintype.equivFin(I, i)).
-/
def strictUnitLeft (A : Matrix I I ℝ) (β : ℝ) (i : I) :
    EuclideanSpace ℝ (Fin (Fintype.card I)) :=
  finiteUnitLeft (svdFiniteTable A) β (Fintype.equivFin I i)

/-
Mathematical definition (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; i ∈ I, define

strictUnitRight(A, β, i) := finiteUnitRight(svdFiniteTable(A), β, Fintype.equivFin(I, i)).
-/
def strictUnitRight (A : Matrix I I ℝ) (β : ℝ) (i : I) :
    EuclideanSpace ℝ (Fin (Fintype.card I)) :=
  finiteUnitRight (svdFiniteTable A) β (Fintype.equivFin I i)

/-
Mathematical definition (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, define

strictPolar(A, β) := reindexTable(finitePolar(svdFiniteTable(A), β), (Fintype.equivFin(I))⁻¹, (Fintype.equivFin(I))⁻¹).
-/
def strictPolar (A : Matrix I I ℝ) (β : ℝ) : Matrix I I ℝ :=
  reindexTable (finitePolar (svdFiniteTable A) β)
    (Fintype.equivFin I).symm (Fintype.equivFin I).symm

omit [Nonempty I] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; i, j ∈ I, we have

strictPolar(A, β, i, j) = inner(ℝ, strictUnitLeft(A, β, i), strictUnitRight(A, β, j)).
-/
theorem strictPolar_factorization (A : Matrix I I ℝ) (β : ℝ) (i j : I) :
    strictPolar A β i j = inner ℝ (strictUnitLeft A β i) (strictUnitRight A β j) :=
  finitePolar_factorization _ _ _ _

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

normalizedGram(((i, k ↦ strictUnitLeft(A, β, i, k)))) = Matrix.diagonal(strictKeep(svdFiniteTable(A), β)).
-/
theorem strictUnitLeft_gram (A : Matrix I I ℝ) (β : ℝ) :
    normalizedGram (fun i k => strictUnitLeft A β i k) =
      Matrix.diagonal (strictKeep (svdFiniteTable A) β) := by
  letI : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  ext k l
  unfold normalizedGram strictUnitLeft
  rw [uavg_equiv (Fintype.equivFin I) (fun i =>
    finiteUnitLeft (svdFiniteTable A) β i k * finiteUnitLeft (svdFiniteTable A) β i l)]
  exact congrFun (congrFun (finiteUnitLeft_gram (svdFiniteTable A) β) k) l

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

normalizedGram(((i, k ↦ strictUnitRight(A, β, i, k)))) = Matrix.diagonal(strictKeep(svdFiniteTable(A), β)).
-/
theorem strictUnitRight_gram (A : Matrix I I ℝ) (β : ℝ) :
    normalizedGram (fun i k => strictUnitRight A β i k) =
      Matrix.diagonal (strictKeep (svdFiniteTable A) β) := by
  letI : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  ext k l
  unfold normalizedGram strictUnitRight
  rw [uavg_equiv (Fintype.equivFin I) (fun i =>
    finiteUnitRight (svdFiniteTable A) β i k * finiteUnitRight (svdFiniteTable A) β i l)]
  exact congrFun (congrFun (finiteUnitRight_gram (svdFiniteTable A) β) k) l

omit [Nonempty I] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

‖ Matrix.diagonal(strictKeep(svdFiniteTable(A), β))‖ ≤ 1.
-/
theorem strictKeep_diagonal_norm (A : Matrix I I ℝ) (β : ℝ) :
    ‖Matrix.diagonal (strictKeep (svdFiniteTable A) β)‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (strictKeep_nonneg _ _ k)]
  exact strictKeep_le_one _ _ k

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

‖ normalizedGram(((i, k ↦ strictUnitLeft(A, β, i, k))))‖ ≤ 1.
-/
theorem strictUnitLeft_gram_norm (A : Matrix I I ℝ) (β : ℝ) :
    ‖normalizedGram (fun i k => strictUnitLeft A β i k)‖ ≤ 1 := by
  rw [strictUnitLeft_gram]
  exact strictKeep_diagonal_norm _ _

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

‖ normalizedGram(((i, k ↦ strictUnitRight(A, β, i, k))))‖ ≤ 1.
-/
theorem strictUnitRight_gram_norm (A : Matrix I I ℝ) (β : ℝ) :
    ‖normalizedGram (fun i k => strictUnitRight A β i k)‖ ≤ 1 := by
  rw [strictUnitRight_gram]
  exact strictKeep_diagonal_norm _ _

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

𝔼ᵢ [(‖ strictUnitLeft(A, β, i)‖)²] = strictRank(A, β).
-/
theorem strictUnitLeft_mean_energy (A : Matrix I I ℝ) (β : ℝ) :
    uavg (fun i => ‖strictUnitLeft A β i‖ ^ 2) = strictRank A β := by
  simp_rw [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  rw [uavg_sum]
  unfold strictRank finiteRank
  apply Finset.sum_congr rfl
  intro k _
  have h := congrFun (congrFun (strictUnitLeft_gram A β) k) k
  simpa only [normalizedGram, Matrix.diagonal_apply_eq, pow_two] using h

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

𝔼ᵢ [(‖ strictUnitRight(A, β, i)‖)²] = strictRank(A, β).
-/
theorem strictUnitRight_mean_energy (A : Matrix I I ℝ) (β : ℝ) :
    uavg (fun i => ‖strictUnitRight A β i‖ ^ 2) = strictRank A β := by
  simp_rw [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  rw [uavg_sum]
  unfold strictRank finiteRank
  apply Finset.sum_congr rfl
  intro k _
  have h := congrFun (congrFun (strictUnitRight_gram A β) k) k
  simpa only [normalizedGram, Matrix.diagonal_apply_eq, pow_two] using h

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; i ∈ I, assume 0 < β; ∀ i, j, |A(i, j)| ≤ 1. Then

(‖ strictUnitLeft(A, β, i)‖)² ≤ 1 / β².
-/
theorem strictUnitLeft_energy (A : Matrix I I ℝ) (β : ℝ) (hβ : 0 < β)
    (hA : ∀ i j, |A i j| ≤ 1) (i : I) : ‖strictUnitLeft A β i‖ ^ 2 ≤ 1 / β ^ 2 := by
  letI : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  apply (finiteUnitLeft_energy _ _ hβ _).trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg β)
  simpa only [one_pow] using (sq_le_sq₀ (rowL2_nonneg (svdFiniteTable A) _) zero_le_one).2
    (rowL2_le_one_of_entry_bound _ (fun x y => hA _ _) _)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; i ∈ I, assume 0 < β; ∀ i, j, |A(i, j)| ≤ 1. Then

(‖ strictUnitRight(A, β, i)‖)² ≤ 1 / β².
-/
theorem strictUnitRight_energy (A : Matrix I I ℝ) (β : ℝ) (hβ : 0 < β)
    (hA : ∀ i j, |A i j| ≤ 1) (i : I) : ‖strictUnitRight A β i‖ ^ 2 ≤ 1 / β ^ 2 := by
  letI : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  apply (finiteUnitRight_energy _ _ hβ _).trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg β)
  simpa only [one_pow] using (sq_le_sq₀ (columnL2_nonneg (svdFiniteTable A) _) zero_le_one).2
    (columnL2_le_one_of_entry_bound _ (fun x y => hA _ _) _)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

strictRank(A, β) · β ≤ ‖ strictTruncation(A, β)‖_*.
-/
theorem strictRank_mul_cutoff [DecidableEq I] (A : Matrix I I ℝ) (β : ℝ) :
    strictRank A β * β ≤ tableNuclearNorm (strictTruncation A β) := by
  letI : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  unfold strictTruncation
  rw [reindexTable_tableNuclearNorm]
  exact finiteRank_mul_cutoff _ _

omit [Nonempty I] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

0 ≤ strictRank(A, β).
-/
theorem strictRank_nonneg (A : Matrix I I ℝ) (β : ℝ) : 0 ≤ strictRank A β := by
  unfold strictRank finiteRank
  exact Finset.sum_nonneg (fun k _ => strictKeep_nonneg _ _ k)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

pairing(A, strictPolar(A, β)) = ‖ strictTruncation(A, β)‖_*.
-/
theorem strictPolar_pairing [DecidableEq I] (A : Matrix I I ℝ) (β : ℝ) :
    pairing A (strictPolar A β) = tableNuclearNorm (strictTruncation A β) := by
  letI : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  have hr := reindexTable_pairing (svdFiniteTable A) (finitePolar (svdFiniteTable A) β)
    (Fintype.equivFin I).symm (Fintype.equivFin I).symm
  simpa only [strictPolar, strictTruncation, svdFiniteTable, reindexTable_inverse,
    reindexTable_tableNuclearNorm] using hr.trans (finitePolar_pairing _ _)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; i, j ∈ I, assume 0 < β; ∀ i, j, |A(i, j)| ≤ 1. Then

|strictPolar(A, β, i, j)| ≤ 1 / β².
-/
theorem strictPolar_entry (A : Matrix I I ℝ) (β : ℝ) (hβ : 0 < β)
    (hA : ∀ i j, |A i j| ≤ 1) (i j : I) : |strictPolar A β i j| ≤ 1 / β ^ 2 := by
  rw [strictPolar_factorization]
  have hl := strictUnitLeft_energy A β hβ hA i
  have hr := strictUnitRight_energy A β hβ hA j
  have h := abs_real_inner_le_norm (strictUnitLeft A β i) (strictUnitRight A β j)
  have hh : ‖strictUnitLeft A β i‖ * ‖strictUnitRight A β j‖ ≤ 1 / β ^ 2 := by
    nlinarith [sq_nonneg (‖strictUnitLeft A β i‖ - ‖strictUnitRight A β j‖)]
  exact h.trans hh

end

end CircuitCompiler.TruncatedAnswerNorm
