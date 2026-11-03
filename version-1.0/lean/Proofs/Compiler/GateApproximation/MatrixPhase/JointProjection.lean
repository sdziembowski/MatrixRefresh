import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Maps.Proper.Basic
import Proofs.Compiler.Foundations.LinearAlgebra.NuclearBall



/-!
# The weighted projection certificate for the joint-port approximation

The validity density vanishes off the refresh relation. Thus its weighted `L₂` geometry is a seminorm, and the unweighted projection theorem cannot be applied directly. We prove compactness of the actual joint nuclear ball and project onto its image under a diagonal weight operator. Zero weights are allowed throughout.
-/

set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler

open TableAnalysis

noncomputable section

variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype Z]

/-- The finite coordinate representation of a tuple of real matrices. -/
/- Mathematical definition (normal notation): View a finite family of matrices as the array of its entries indexed by an answer and a row-column pair. This coordinate identification is linear. -/
def entryTupleLinear : MatrixTuple Z ι →ₗ[ℝ] (Z → ι × ι → ℝ) where
  toFun G z p := G z p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq ι] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

entryTupleLinear(Z = Z, ι = ι) is injective.
-/
lemma entryTupleLinear_injective :
    Function.Injective (entryTupleLinear (Z := Z) (ι := ι)) := by
  intro G H h
  ext z p
  exact congrFun (congrFun h z) p

/-- Nuclear-budget sets are compact in the finite-dimensional entry space. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For R ∈ ℝ, we have

IsCompact(jointNuclearBall(Z = Z, ι = ι, R)) .
-/
theorem jointNuclearBall_compact (R : ℝ) :
    IsCompact (jointNuclearBall (Z := Z) (ι := ι) R) := by
  let bound : ι × ι → ℝ := fun p => R * ‖(Matrix.single p.1 p.2 1 : Matrix ι ι ℝ)‖
  have he := LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr (entryTupleLinear_injective (Z := Z) (ι := ι)))
  have hc := he.isProperMap.isCompact_preimage
    (isCompact_univ_pi (fun _ : Z => isCompact_univ_pi (fun p : ι × ι =>
      isCompact_Icc (a := -bound p) (b := bound p))))
  apply hc.of_isClosed_subset (jointNuclearBall_closed R)
  intro G hG z _ p _
  change -bound p ≤ G z p ∧ G z p ≤ bound p
  apply abs_le.mp
  have hb : blockNuclearNorm (G z) ≤ R :=
    (Finset.single_le_sum (fun w _ => nuclearNorm_nonneg
      (entryMatrix (G w))) (Finset.mem_univ z)).trans hG
  have hp := abs_countingPairing_le (entryMatrix (G z))
    (Matrix.single p.1 p.2 1)
  have hp' : |G z p| ≤ blockNuclearNorm (G z) *
      ‖(Matrix.single p.1 p.2 1 : Matrix ι ι ℝ)‖ := by
    simpa [countingPairing, entryMatrix, Matrix.single_apply, eq_comm, ite_and,
      blockNuclearNorm] using hp
  exact hp'.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

/-- Coordinatewise multiplication by real weights on matrix tuples. -/
/- Mathematical definition (normal notation): Multiply every entry of a matrix family by its fixed real coordinate weight: (W A)_z(i,j) = w_z(i,j)A_z(i,j). This is a real-linear map. -/
def weightTupleLinear (w : Z → ι × ι → ℝ) :
    MatrixTuple Z ι →ₗ[ℝ] MatrixTuple Z ι where
  toFun A := WithLp.toLp 2 (fun z => WithLp.toLp 2 (fun p => w z p * A z p))
  map_add' A B := by ext z p; exact mul_add _ _ _
  map_smul' c A := by
    ext z p
    change w z p * (c * A z p) = c * (w z p * A z p)
    ring

/-- Continuous version of the finite-dimensional diagonal weight operator. -/
/-
Mathematical definition (normal notation): For w ∈ Z → ι × ι → ℝ, define

weightTuple(w) := toContinuousLinearMap(weightTupleLinear(w)).
-/
def weightTuple (w : Z → ι × ι → ℝ) :
    MatrixTuple Z ι →L[ℝ] MatrixTuple Z ι :=
  (weightTupleLinear w).toContinuousLinearMap

omit [DecidableEq ι] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For w ∈ Z → ι × ι → ℝ; A ∈ MatrixTuple(Z, ι); z ∈ Z; p ∈ ι × ι, we have

weightTuple(w, A, z, p) = w(z, p) · A(z, p).
-/
@[simp] theorem weightTuple_apply (w : Z → ι × ι → ℝ)
    (A : MatrixTuple Z ι) (z : Z) (p : ι × ι) :
    weightTuple w A z p = w z p * A z p :=
  rfl

omit [DecidableEq ι] in
/-- Real diagonal multiplication is self-adjoint, including zero weights. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For w ∈ Z → ι × ι → ℝ; A, B ∈ MatrixTuple(Z, ι), we have

inner(ℝ, weightTuple(w, A), B) = inner(ℝ, A, weightTuple(w, B)).
-/
theorem weightTuple_self_adjoint (w : Z → ι × ι → ℝ)
    (A B : MatrixTuple Z ι) :
    inner ℝ (weightTuple w A) B = inner ℝ A (weightTuple w B) := by
  simp only [PiLp.inner_apply, weightTuple_apply, RCLike.inner_apply,
    conj_trivial, mul_assoc, mul_left_comm]

/-- Projection onto the weighted image of the nuclear ball. The dual tests use exactly the weighted unit seminorm, and the operator term contains two weight factors, corresponding to the density `D` when `w = sqrt D`. No strict positivity or invertibility of the weights is required. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For w ∈ Z → ι × ι → ℝ; R, e ∈ ℝ; A ∈ MatrixTuple(Z, ι), assume Z ≠ ∅; 0 ≤ R; 0 ≤ e; ∀ W ∈ MatrixTuple(Z, ι), (‖ weightTuple(w, W)‖ ≤ 1) ⇒ inner(ℝ, weightTuple(w, A), weightTuple(w, W)) ≤ R · tupleOperatorNorm(weightTuple(w, weightTuple(w, W))) + e. Then

∃ G ∈ jointNuclearBall(Z = Z, ι = ι, R), ‖ weightTuple(w, (A - G))‖ ≤ e.
-/
theorem exists_weighted_jointNuclearProjection [Nonempty Z]
    (w : Z → ι × ι → ℝ) (R e : ℝ) (hR : 0 ≤ R) (he : 0 ≤ e)
    (A : MatrixTuple Z ι)
    (htest : ∀ W : MatrixTuple Z ι, ‖weightTuple w W‖ ≤ 1 →
      inner ℝ (weightTuple w A) (weightTuple w W) ≤
        R * tupleOperatorNorm (weightTuple w (weightTuple w W)) + e) :
    ∃ G ∈ jointNuclearBall (Z := Z) (ι := ι) R,
      ‖weightTuple w (A - G)‖ ≤ e := by
  let T := weightTuple w
  let S := T '' jointNuclearBall (Z := Z) (ι := ι) R
  have hcompact : IsCompact S := (jointNuclearBall_compact R).image T.continuous
  have hnonempty : S.Nonempty := (jointNuclearBall_nonempty R hR).image T
  have hconv : Convex ℝ S := (jointNuclearBall_convex R).linear_image T.toLinearMap
  obtain ⟨P, hP, hnearest⟩ := exists_norm_eq_iInf_of_complete_convex
    hnonempty hcompact.isClosed.isComplete hconv (T A)
  obtain ⟨G, hG, rfl⟩ := hP
  refine ⟨G, hG, ?_⟩
  change ‖T (A - G)‖ ≤ e
  by_cases hzero : ‖T (A - G)‖ = 0
  · simpa only [hzero] using he
  let W : MatrixTuple Z ι := ‖T (A - G)‖⁻¹ • (A - G)
  have hTW : ‖T W‖ = 1 := by
    rw [show T W = ‖T (A - G)‖⁻¹ • T (A - G) from map_smul T _ _]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ hzero]
  obtain ⟨B, hB, hpair⟩ := jointNuclearBall_support_witness R hR (T (T W))
  have hvar := (norm_eq_iInf_iff_real_inner_le_zero hconv
    (show T G ∈ S from ⟨G, hG, rfl⟩)).1 hnearest (T B) ⟨B, hB, rfl⟩
  have hsupport : inner ℝ (T B) (T W) ≤ inner ℝ (T G) (T W) := by
    dsimp [W]
    rw [map_smul, real_inner_smul_right, real_inner_smul_right]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg _))
    rw [map_sub] at *
    rw [inner_sub_right] at hvar
    have hv := sub_nonpos.mp hvar
    simpa only [real_inner_comm] using hv
  have ht := htest W (le_of_eq hTW)
  change inner ℝ (T A) (T W) ≤ R * tupleOperatorNorm (T (T W)) + e at ht
  have hp : inner ℝ B (T (T W)) = inner ℝ (T B) (T W) :=
    (weightTuple_self_adjoint w B (T W)).symm
  rw [← hpair, hp] at ht
  have hres : inner ℝ (T A - T G) (T W) = ‖T (A - G)‖ := by
    dsimp [W]
    rw [map_smul, ← map_sub, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  rw [inner_sub_left] at hres
  change ‖T (A - G)‖ ≤ e
  linarith

omit [DecidableEq ι] in
/-- The weighted tuple norm is the explicit sum of squared weighted entries. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For w ∈ Z → ι × ι → ℝ; A ∈ MatrixTuple(Z, ι), we have

(‖ weightTuple(w, A)‖)² = ∑_z (∑ₚ ((w(z, p))² · (A(z, p))²)).
-/
theorem weightTuple_norm_sq (w : Z → ι × ι → ℝ) (A : MatrixTuple Z ι) :
    ‖weightTuple w A‖ ^ 2 = ∑ z, ∑ p, w z p ^ 2 * A z p ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro z _
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [weightTuple_apply, Real.norm_eq_abs, sq_abs, mul_pow]

omit [DecidableEq ι] in
/-- The density-weighted pairing uses the density once, rather than its square. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D ∈ Z → ι × ι → ℝ; A, W ∈ MatrixTuple(Z, ι), assume ∀ z, p, 0 ≤ D(z, p). Then

inner(ℝ, weightTuple(((z, p ↦ √(D(z, p)))), A), weightTuple(((z, p ↦ √(D(z, p)))), W)) = ∑_z (∑ₚ (D(z, p) · A(z, p) · W(z, p))).
-/
theorem sqrtDensity_pair (D : Z → ι × ι → ℝ) (hD : ∀ z p, 0 ≤ D z p)
    (A W : MatrixTuple Z ι) :
    inner ℝ (weightTuple (fun z p => Real.sqrt (D z p)) A)
        (weightTuple (fun z p => Real.sqrt (D z p)) W) =
      ∑ z, ∑ p, D z p * A z p * W z p := by
  simp only [PiLp.inner_apply, weightTuple_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro p _
  calc
    _ = Real.sqrt (D z p) ^ 2 * A z p * W z p := by ring
    _ = _ := by rw [Real.sq_sqrt (hD z p)]

omit [DecidableEq ι] in
/-- Two square-root-density weightings are exactly multiplication by the density. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D ∈ Z → ι × ι → ℝ; W ∈ MatrixTuple(Z, ι), assume ∀ z, p, 0 ≤ D(z, p). Then

weightTuple(((z, p ↦ √(D(z, p)))), weightTuple(((z, p ↦ √(D(z, p)))), W)) = weightTuple(D, W).
-/
theorem sqrtDensity_twice (D : Z → ι × ι → ℝ) (hD : ∀ z p, 0 ≤ D z p)
    (W : MatrixTuple Z ι) :
    weightTuple (fun z p => Real.sqrt (D z p))
        (weightTuple (fun z p => Real.sqrt (D z p)) W) = weightTuple D W := by
  ext z p
  simp only [weightTuple_apply, ← mul_assoc, ← pow_two, Real.sq_sqrt (hD z p)]

/-- Explicit-density form of the weighted projection certificate. The density may vanish on arbitrary entries. This is the final geometric step in the joint-port lemma; its probabilistic dual estimate remains a separate theorem. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D ∈ Z → ι × ι → ℝ; R, e ∈ ℝ; A ∈ MatrixTuple(Z, ι), assume Z ≠ ∅; ∀ z, p, 0 ≤ D(z, p); 0 ≤ R; 0 ≤ e; ∀ W ∈ MatrixTuple(Z, ι), ((∑_z (∑ₚ (D(z, p) · (W(z, p))²))) ≤ 1) ⇒ (∑_z (∑ₚ (D(z, p) · A(z, p) · W(z, p)))) ≤ R · tupleOperatorNorm(weightTuple(D, W)) + e. Then

∃ G ∈ jointNuclearBall(Z = Z, ι = ι, R), √(∑_z (∑ₚ (D(z, p) · (A(z, p) - G(z, p))²))) ≤ e.
-/
theorem exists_density_jointNuclearProjection [Nonempty Z]
    (D : Z → ι × ι → ℝ) (hD : ∀ z p, 0 ≤ D z p)
    (R e : ℝ) (hR : 0 ≤ R) (he : 0 ≤ e) (A : MatrixTuple Z ι)
    (htest : ∀ W : MatrixTuple Z ι, (∑ z, ∑ p, D z p * W z p ^ 2) ≤ 1 →
      (∑ z, ∑ p, D z p * A z p * W z p) ≤
        R * tupleOperatorNorm (weightTuple D W) + e) :
    ∃ G ∈ jointNuclearBall (Z := Z) (ι := ι) R,
      Real.sqrt (∑ z, ∑ p, D z p * (A z p - G z p) ^ 2) ≤ e := by
  let w := fun z p => Real.sqrt (D z p)
  have hnorm (W : MatrixTuple Z ι) :
      ‖weightTuple w W‖ ^ 2 = ∑ z, ∑ p, D z p * W z p ^ 2 := by
    rw [weightTuple_norm_sq]
    simp only [w, Real.sq_sqrt (hD _ _)]
  obtain ⟨G, hG, herr⟩ := exists_weighted_jointNuclearProjection w R e hR he A (by
    intro W hW
    rw [sqrtDensity_pair D hD, sqrtDensity_twice D hD]
    apply htest W
    rw [← hnorm W]
    nlinarith [norm_nonneg (weightTuple w W)])
  refine ⟨G, hG, ?_⟩
  have hs : (∑ z, ∑ p, D z p * (A z p - G z p) ^ 2) =
      ‖weightTuple w (A - G)‖ ^ 2 := (hnorm (A - G)).symm
  rw [hs, Real.sqrt_sq (norm_nonneg _)]
  exact herr

section Tables

variable [Nonempty ι] [Nonempty Z]

/-- Density-weighted bilinear pairing of table families under uniform measure. -/
/-
Mathematical definition (normal notation): For D ∈ ℝ^(ι × ι); A, W ∈ Z → ℝ^(ι × ι), define

densityTablePair(D, A, W) := ∑_z (MatrixRefresh.uavg(((p ∈ ι × ι ↦ D((p)₁, (p)₂) · A(z, (p)₁, (p)₂) · W(z, (p)₁, (p)₂))))).
-/
def densityTablePair (D : Matrix ι ι ℝ) (A W : Z → Matrix ι ι ℝ) : ℝ :=
  ∑ z, MatrixRefresh.uavg (fun p : ι × ι => D p.1 p.2 * A z p.1 p.2 * W z p.1 p.2)

/-- Uniform table normalization transports the density-weighted pairing exactly. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D ∈ ℝ^(ι × ι); A, W ∈ Z → ℝ^(ι × ι), we have

(∑_z (∑_(p ∈ ι × ι) (D((p)₁, (p)₂) · uniformTuple(A, z, p) · uniformTuple(W, z, p)))) = densityTablePair(D, A, W).
-/
theorem uniformTuple_densityPair (D : Matrix ι ι ℝ) (A W : Z → Matrix ι ι ℝ) :
    (∑ z, ∑ p : ι × ι, D p.1 p.2 * uniformTuple A z p * uniformTuple W z p) =
      densityTablePair D A W := by
  unfold densityTablePair MatrixRefresh.uavg
  simp only [Fintype.card_prod, Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  change D p.1 p.2 * ((Fintype.card ι : ℝ)⁻¹ * A z p.1 p.2) *
    ((Fintype.card ι : ℝ)⁻¹ * W z p.1 p.2) = _
  simp only [mul_inv_rev]
  ring

/-- Multiplication by the density commutes with uniform normalization. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D ∈ ℝ^(ι × ι); W ∈ Z → ℝ^(ι × ι), we have

weightTuple(((x₁, p ↦ D((p)₁, (p)₂))), uniformTuple(W)) = uniformTuple(((z ↦ D ⊙ W(z)))).
-/
theorem weightTuple_uniformTuple (D : Matrix ι ι ℝ) (W : Z → Matrix ι ι ℝ) :
    weightTuple (fun _ p => D p.1 p.2) (uniformTuple W) =
      uniformTuple (fun z => D ⊙ W z) := by
  ext z p
  change D p.1 p.2 * ((Fintype.card ι : ℝ)⁻¹ * W z p.1 p.2) =
    (Fintype.card ι : ℝ)⁻¹ * (D p.1 p.2 * W z p.1 p.2)
  ring

/-- The table-normalized weighted projection certificate used by the paper. The conclusion measures error only on the support of the density, while its nuclear budget is the ordinary uniform-table nuclear norm. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D ∈ ℝ^(ι × ι); R, e ∈ ℝ; A ∈ Z → ℝ^(ι × ι), assume ∀ i, j, 0 ≤ D(i, j); 0 ≤ R; 0 ≤ e; ∀ W ∈ Z → ℝ^(ι × ι), (densityTablePair(D, W, W) ≤ 1) ⇒ densityTablePair(D, A, W) ≤ R · ‖ (z ↦ ‖ (D ⊙ W(z))‖ₒₚ)‖ + e. Then

∃ G ∈ Z → ℝ^(ι × ι), (∑_z (‖ G(z)‖_*)) ≤ R ∧ √(densityTablePair(D, ((z ↦ A(z) - G(z))), ((z ↦ A(z) - G(z))))) ≤ e.
-/
theorem exists_density_tableNuclearNormProjection
    (D : Matrix ι ι ℝ) (hD : ∀ i j, 0 ≤ D i j)
    (R e : ℝ) (hR : 0 ≤ R) (he : 0 ≤ e) (A : Z → Matrix ι ι ℝ)
    (htest : ∀ W : Z → Matrix ι ι ℝ, densityTablePair D W W ≤ 1 →
      densityTablePair D A W ≤ R * ‖fun z => largestSingularCoefficient (D ⊙ W z)‖ + e) :
    ∃ G : Z → Matrix ι ι ℝ,
      (∑ z, tableNuclearNorm (G z)) ≤ R ∧
      Real.sqrt (densityTablePair D (fun z => A z - G z) (fun z => A z - G z)) ≤ e := by
  obtain ⟨P, hP, herr⟩ := exists_density_jointNuclearProjection
    (fun _ : Z => fun p : ι × ι => D p.1 p.2) (fun _ p => hD p.1 p.2)
    R e hR he (uniformTuple A) (by
      intro U hU
      let W : Z → Matrix ι ι ℝ := fun z => (Fintype.card ι : ℝ) • entryMatrix (U z)
      have hW : uniformTuple W = U := uniformTuple_recover U
      have htestW := htest W (by
        rw [← uniformTuple_densityPair, hW]
        simpa only [pow_two, mul_assoc] using hU)
      rw [← uniformTuple_densityPair, hW, ← uniformTuple_operatorNorm,
        ← weightTuple_uniformTuple, hW] at htestW
      exact htestW)
  let G : Z → Matrix ι ι ℝ := fun z => (Fintype.card ι : ℝ) • entryMatrix (P z)
  have hG : uniformTuple G = P := uniformTuple_recover P
  refine ⟨G, ?_, ?_⟩
  · rw [← uniformTuple_jointNuclearNorm, hG]
    exact hP
  · rw [← uniformTuple_densityPair, uniformTuple_sub, hG]
    simpa only [PiLp.sub_apply, pow_two, mul_assoc] using herr

end Tables

end

end CircuitCompiler
