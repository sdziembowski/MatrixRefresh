import Proofs.Compiler.GateApproximation.MatrixPhase.SVD



/-!
# Reference Gram bounds of the concrete retained singular factors
-/
set_option autoImplicit false

set_option maxHeartbeats 1500000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

section Finite

variable {n : ℕ} [NeZero n]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; p, q ∈ TableRetainedDirection(A, β), we have

𝔼ᵢ [tableLeftFeature(A, β, i, p) · tableLeftFeature(A, β, i, q)] = { tableSingularValue(A, p) if p = q,; 0 otherwise }.
-/
theorem tableLeftFeature_covariance (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ)
    (p q : TableRetainedDirection A β) :
    uavg (fun i => tableLeftFeature A β i p * tableLeftFeature A β i q) =
      if p = q then tableSingularValue A p.val else 0 := by
  classical
  unfold tableLeftFeature spectralLeftFeature uavg
  simp only [Fintype.card_fin, PiLp.toLp_apply]
  calc
    _ = (n : ℝ)⁻¹ * (Real.sqrt ((matrixSVD A).sigma p.val) *
        Real.sqrt ((matrixSVD A).sigma q.val) *
        ∑ i, (matrixSVD A).left p.val i * (matrixSVD A).left q.val i) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [orthonormalBasis_coordinate_inner]
      by_cases h : p = q
      · subst q
        simp only [if_pos rfl]
        rw [Real.mul_self_sqrt ((matrixSVD A).nonneg p.val)]
        simp [tableSingularValue, div_eq_mul_inv, mul_comm]
      · have hh : p.val ≠ q.val := fun he => h (Subtype.ext he)
        simp [h, hh]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ; p, q ∈ TableRetainedDirection(A, β), we have

𝔼ᵢ [tableRightFeature(A, β, i, p) · tableRightFeature(A, β, i, q)] = { tableSingularValue(A, p) if p = q,; 0 otherwise }.
-/
theorem tableRightFeature_covariance (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ)
    (p q : TableRetainedDirection A β) :
    uavg (fun i => tableRightFeature A β i p * tableRightFeature A β i q) =
      if p = q then tableSingularValue A p.val else 0 := by
  classical
  unfold tableRightFeature spectralRightFeature uavg
  simp only [Fintype.card_fin, PiLp.toLp_apply]
  calc
    _ = (n : ℝ)⁻¹ * (Real.sqrt ((matrixSVD A).sigma p.val) *
        Real.sqrt ((matrixSVD A).sigma q.val) *
        ∑ i, (matrixSVD A).right p.val i * (matrixSVD A).right q.val i) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [orthonormalBasis_coordinate_inner]
      by_cases h : p = q
      · subst q
        simp only [if_pos rfl]
        rw [Real.mul_self_sqrt ((matrixSVD A).nonneg p.val)]
        simp [tableSingularValue, div_eq_mul_inv, mul_comm]
      · have hh : p.val ≠ q.val := fun he => h (Subtype.ext he)
        simp [h, hh]

end Finite

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

normalizedGram(((i, p ↦ refreshSVDLeft(A, β, i, p)))) = Matrix.diagonal(((p ↦ tableSingularValue(svdFiniteTable(A), p)))).
-/
theorem refreshSVDLeft_gram (A : Matrix I I ℝ) (β : ℝ) :
    normalizedGram (fun i p => refreshSVDLeft A β i p) =
      Matrix.diagonal (fun p => tableSingularValue (svdFiniteTable A) p.val) := by
  classical
  letI : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  ext p q
  unfold normalizedGram refreshSVDLeft
  rw [uavg_equiv (Fintype.equivFin I) (fun i =>
    tableLeftFeature (svdFiniteTable A) β i p * tableLeftFeature (svdFiniteTable A) β i q)]
  simpa only [Matrix.diagonal_apply] using tableLeftFeature_covariance (svdFiniteTable A) β p q

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

normalizedGram(((i, p ↦ refreshSVDRight(A, β, i, p)))) = Matrix.diagonal(((p ↦ tableSingularValue(svdFiniteTable(A), p)))).
-/
theorem refreshSVDRight_gram (A : Matrix I I ℝ) (β : ℝ) :
    normalizedGram (fun i p => refreshSVDRight A β i p) =
      Matrix.diagonal (fun p => tableSingularValue (svdFiniteTable A) p.val) := by
  classical
  letI : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  ext p q
  unfold normalizedGram refreshSVDRight
  rw [uavg_equiv (Fintype.equivFin I) (fun i =>
    tableRightFeature (svdFiniteTable A) β i p * tableRightFeature (svdFiniteTable A) β i q)]
  simpa only [Matrix.diagonal_apply] using tableRightFeature_covariance (svdFiniteTable A) β p q

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

‖ Matrix.diagonal(((p ∈ RefreshSVDIndex(A, β) ↦ tableSingularValue(svdFiniteTable(A), p))))‖ ≤ ‖ A‖ₒₚ.
-/
theorem retained_diagonal_norm_le (A : Matrix I I ℝ) (β : ℝ) :
    ‖Matrix.diagonal (fun p : RefreshSVDIndex A β =>
      tableSingularValue (svdFiniteTable A) p.val)‖ ≤ largestSingularCoefficient A := by
  classical
  letI : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  rw [Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (largestSingularCoefficient_nonneg A)).2
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg (tableSingularValue_nonneg _ _)]
  exact (tableSingularValue_le_largestSingularCoefficient _ _).trans_eq (reindexTable_largestSingularCoefficient _ _ _)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

‖ normalizedGram(((i, p ↦ refreshSVDLeft(A, β, i, p))))‖ ≤ ‖ A‖ₒₚ.
-/
theorem refreshSVDLeft_gram_norm (A : Matrix I I ℝ) (β : ℝ) :
    ‖normalizedGram (fun i p => refreshSVDLeft A β i p)‖ ≤ largestSingularCoefficient A := by
  rw [refreshSVDLeft_gram]
  exact retained_diagonal_norm_le A β

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

‖ normalizedGram(((i, p ↦ refreshSVDRight(A, β, i, p))))‖ ≤ ‖ A‖ₒₚ.
-/
theorem refreshSVDRight_gram_norm (A : Matrix I I ℝ) (β : ℝ) :
    ‖normalizedGram (fun i p => refreshSVDRight A β i p)‖ ≤ largestSingularCoefficient A := by
  rw [refreshSVDRight_gram]
  exact retained_diagonal_norm_le A β

section Tensor

variable {F P : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype P] [DecidableEq P] {n : ℕ}

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ ∈ GateSide(F, n, (n · n)) → P → ℝ, we have

jointMeanGram(((x, u, p ↦ Φ((x, u), p)))) = (Complex.ofReal_*normalizedGram(Φ)).
-/
theorem jointMeanGram_ofReal (Φ : GateSide F n (n*n) → P → ℝ) :
    jointMeanGram (fun x u p => (Φ (x,u) p : ℂ)) =
      (normalizedGram Φ).map Complex.ofReal := by
  ext p q
  apply Complex.ext
  · simp only [jointMeanGram, complexAverage_re, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      neg_zero, mul_zero, sub_zero, Matrix.map_apply, normalizedGram]
    exact (uavg_prod (fun z : GateSide F n (n*n) => Φ z p * Φ z q)).symm
  · simp [jointMeanGram, complexAverage_im]

/-- The retained SVD factors meet both genuine Gram hypotheses of the random refresh estimate, with no input assumptions about those Gram matrices. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))); β ∈ ℝ, assume |F| = 2; 2 ≤ n; 0 < β; ∀ i, j, |A(i, j)| ≤ 1. Then

𝔼_(M ∈ GL_(n · n)(F)) [GateTruncation.opNorm(graphRestriction(inputTensor, inputTensor, (Complex.ofReal_*refreshSVDPart(A, β)), M))] ≤ ‖ A‖ₒₚ + √6 / (|F|ⁿ · β).
-/
theorem tensorSVDPart_large_mean_binary (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (A : Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℝ)
    (β : ℝ) (hβ : 0 < β) (hA : ∀ i j, |A i j| ≤ 1) :
    uavg (fun M : Refresh.«GL» F (n*n) =>
      GateTruncation.opNorm (graphRestriction inputTensor inputTensor
        ((refreshSVDPart A β).map Complex.ofReal) M)) ≤
      largestSingularCoefficient A + Real.sqrt 6 / ((vectorCard F n : ℝ) * β) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  letI : Nonempty (U F (n*n)) := ⟨unitShare ⟨0, by nlinarith⟩⟩
  let ξ := fun (x : U F n × U F n) (u : U F (n*n))
    (p : RefreshSVDIndex A β) => (refreshSVDLeft A β (x,u) p : ℂ)
  let ζ := fun (x : U F n × U F n) (u : U F (n*n))
    (p : RefreshSVDIndex A β) => (refreshSVDRight A β (x,u) p : ℂ)
  have hξ : ‖jointMeanGram ξ‖ ≤ largestSingularCoefficient A := by
    rw [show ξ = (fun x u p => (refreshSVDLeft A β (x,u) p : ℂ)) by rfl,
      jointMeanGram_ofReal (fun i p => refreshSVDLeft A β i p), complexMatrix_ofReal_norm]
    exact refreshSVDLeft_gram_norm A β
  have hζ : ‖jointMeanGram ζ‖ ≤ largestSingularCoefficient A := by
    rw [show ζ = (fun x u p => (refreshSVDRight A β (x,u) p : ℂ)) by rfl,
      jointMeanGram_ofReal (fun i p => refreshSVDRight A β i p), complexMatrix_ofReal_norm]
    exact refreshSVDRight_gram_norm A β
  have hξpoint : ∀ x u, jointFeatureEnergy ξ x u ≤ 1 / β := by
    intro x u
    simpa only [jointFeatureEnergy, ξ, Complex.norm_real, PiLp.norm_sq_eq_of_L2] using
      refreshSVDLeft_energy A β hβ hA (x,u)
  have hζpoint : ∀ x u, jointFeatureEnergy ζ x u ≤ 1 / β := by
    intro x u
    simpa only [jointFeatureEnergy, ζ, Complex.norm_real, PiLp.norm_sq_eq_of_L2] using
      refreshSVDRight_energy A β hβ hA (x,u)
  have htable : tensorFactorTable ξ ζ = (refreshSVDPart A β).map Complex.ofReal := by
    ext x y
    simp only [tensorFactorTable, ξ, ζ, Matrix.map_apply, refreshSVDPart_factorization,
      PiLp.inner_apply, RCLike.inner_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    simp only [starRingEnd_apply, star_trivial]
    ring
  rw [← htable]
  exact tensor_large_part_mean_binary hq hn ξ ζ (largestSingularCoefficient A) β hβ hξ hζ hξpoint hζpoint

end Tensor

end

end CircuitCompiler.RefreshAnalysis
