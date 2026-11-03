import Proofs.Compiler.GateApproximation.MatrixPhase.Binary
import Proofs.Compiler.GateApproximation.MatrixPhase.CycleNorm
import Proofs.Compiler.GateApproximation.MatrixPhase.ResidualGeometry
import Proofs.Compiler.GateApproximation.MatrixPhase.SVDResidual
import Proofs.Compiler.GateApproximation.MatrixPhase.Threshold



/-!
# Concrete tensor SVD split at the feature-count threshold

The SVD part, residual and threshold are constructed here. The only remaining analytic input to the operator assembly is the residual fourth-moment estimate.
-/
set_option autoImplicit false

set_option maxHeartbeats 1500000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-
Mathematical definition (normal notation): For F a set; n ∈ ℕ, assume F is finite. define

tensorShareCount(n) := (|F|ⁿ - 1)².
-/
def tensorShareCount (F : Type*) [Fintype F] (n : ℕ) : ℝ := ((vectorCard F n : ℝ)-1)^2

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume |F| = 2. Then

inputTensor(F = F, n = n) is injective.
-/
theorem inputTensor_injective_binary (hq : fieldCard F = 2) :
    Function.Injective (inputTensor (F := F) (n := n)) := by
  intro x y hxy
  have hp : NonzeroProportional (tensorVector x.1.val x.2.val)
      (tensorVector y.1.val y.2.val) :=
    ⟨1, one_ne_zero, by simpa only [inputTensor, one_smul] using congrArg Subtype.val hxy⟩
  obtain ⟨⟨c,hc,hx⟩,⟨d,hd,hy⟩⟩ := (tensorVector_proportional_iff y.1 y.2 x.1 x.2).1 hp
  rw [binary_nonzero_eq_one hq c hc, one_smul] at hx
  rw [binary_nonzero_eq_one hq d hd, one_smul] at hy
  exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

1 ≤ tensorShareCount(F, n) ∧ √(tensorShareCount(F, n)) ≤ |F|ⁿ ∧ tensorShareCount(F, n) ≤ |F|^(n · n).
-/
theorem tensorShareCount_geometry (hn : 2 ≤ n) :
    1 ≤ tensorShareCount F n ∧ Real.sqrt (tensorShareCount F n) ≤ (vectorCard F n : ℝ) ∧
      tensorShareCount F n ≤ (vectorCard F (n*n) : ℝ) := by
  have hN := vectorCard_real_ge_four (F := F) hn
  have hp : (vectorCard F n : ℝ)^2 ≤ (vectorCard F (n*n) : ℝ) := by
    have hnat : (fieldCard F ^ n)^2 ≤ fieldCard F ^ (n*n) := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (fieldCard_pos (F := F)) (by nlinarith)
    exact_mod_cast hnat
  unfold tensorShareCount
  refine ⟨by nlinarith, ?_, by nlinarith⟩
  rw [Real.sqrt_sq (by linarith : 0 ≤ (vectorCard F n : ℝ)-1)]
  linarith

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

tensorShareCount(F, n) = |(U(F, n) × U(F, n))|.
-/
theorem tensorShareCount_card :
    tensorShareCount F n = (Fintype.card (U F n × U F n) : ℝ) := by
  simp only [tensorShareCount, Fintype.card_prod, Nat.cast_mul, card_U_real, pow_two]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))); M ∈ GL_(n · n)(F), we have

GateTruncation.opNorm(graphRestriction(inputTensor, inputTensor, (Complex.ofReal_*A), M)) = ‖ tensorRestriction(A, M)‖ₒₚ.
-/
theorem tensorRestriction_op_complex
    (A : Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℝ) (M : Refresh.«GL» F (n*n)) :
    GateTruncation.opNorm (graphRestriction inputTensor inputTensor (A.map Complex.ofReal) M) =
      largestSingularCoefficient (tensorRestriction A M) := by
  have he : graphRestriction inputTensor inputTensor (A.map Complex.ofReal) M =
      (tensorRestriction A M).map Complex.ofReal := rfl
  rw [he, GateTruncation.opNorm, largestSingularCoefficient, complexMatrix_ofReal_norm]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))), assume |F| = 2; 2 ≤ n; ∀ i, j, |A(i, j)| ≤ 1. Then

‖ supportedSVDResidual(inputTensor, inputTensor, A, refreshThreshold(tensorShareCount(F, n)))‖ₒₚ ≤ 3 · refreshThreshold(tensorShareCount(F, n)).
-/
theorem tensor_residual_op_at_threshold (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (A : Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) :
    largestSingularCoefficient (supportedSVDResidual inputTensor inputTensor A
      (refreshThreshold (tensorShareCount F n))) ≤ 3 * refreshThreshold (tensorShareCount F n) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  have hg := tensorShareCount_geometry (F := F) hn
  have hD : 0 < tensorShareCount F n := lt_of_lt_of_le zero_lt_one hg.1
  have hβ := refreshThreshold_pos hD
  have h := supportedSVDResidual_op hq inputTensor inputTensor A _ hβ hA
  have hQ := vectorCard_real_ge_four (F := F) (show 2 ≤ n*n by nlinarith)
  have hm := binary_mask_threshold_bound hD (by linarith : 2 ≤ (vectorCard F (n*n) : ℝ)) hg.2.2
  have heq : ((fieldCard F ^ (n*n)-1 : ℕ) : ℝ) = (vectorCard F (n*n) : ℝ)-1 := by
    exact_mod_cast Nat.cast_sub (Nat.one_le_pow _ _ (fieldCard_pos (F := F)))
  rw [heq] at h
  have hdiv := div_le_div_of_nonneg_right hm hβ.le
  have hc : (2 * refreshThreshold (tensorShareCount F n)^2) /
      refreshThreshold (tensorShareCount F n) = 2 * refreshThreshold (tensorShareCount F n) := by
    field_simp
  change largestSingularCoefficient _ ≤ _ at h
  rw [hc] at hdiv
  exact h.trans (by dsimp only [vectorCard] at hdiv ⊢; linarith)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))), assume |F| = 2; 2 ≤ n; ∀ i, j, |A(i, j)| ≤ 1. Then

𝔼_(M ∈ GL_(n · n)(F)) [‖ tensorRestriction(refreshSVDPart(A, refreshThreshold(tensorShareCount(F, n))), M)‖ₒₚ] ≤ ‖ A‖ₒₚ + √6 · refreshThreshold(tensorShareCount(F, n)).
-/
theorem tensor_large_at_threshold (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (A : Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) :
    uavg (fun M : Refresh.«GL» F (n*n) =>
      largestSingularCoefficient (tensorRestriction (refreshSVDPart A (refreshThreshold (tensorShareCount F n))) M)) ≤
      largestSingularCoefficient A + Real.sqrt 6 * refreshThreshold (tensorShareCount F n) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  letI : Nonempty (U F (n*n)) := ⟨unitShare ⟨0, by nlinarith⟩⟩
  have hg := tensorShareCount_geometry (F := F) hn
  have hD : 0 < tensorShareCount F n := lt_of_lt_of_le zero_lt_one hg.1
  have h := tensorSVDPart_large_mean_binary hq hn A _ (refreshThreshold_pos hD) hA
  simp_rw [tensorRestriction_op_complex] at h
  apply h.trans
  have hb := mul_le_mul_of_nonneg_left (gram_threshold_bound hD hg.2.1) (Real.sqrt_nonneg 6)
  simpa only [mul_one_div, add_comm] using add_le_add_left hb (largestSingularCoefficient A)

/-- The SVD residual has all three quantitative bounds used by the four-cycle calculation, with the concrete constant three in the operator bound. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Over the binary field with n ≥ 2, put D = (2ⁿ-1)², β = D^(−1/4), and E = A-2 · project(A^(≥ β)), using tensor-share consistency. If every entry of A has absolute value at most one, then

C₄(E) ≤ 9 · β² · ‖E‖₂².

This auxiliary estimate uses the non-strict spectral part.
-/
theorem tensor_residual_cycle_at_threshold (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (A : Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) :
    let β := refreshThreshold (tensorShareCount F n)
    let E := supportedSVDResidual inputTensor inputTensor A β
    fourCycle E ≤ 3^2 * β^2 * uavg (fun x => uavg (fun y => E x y ^ 2)) := by
  dsimp only
  have h := tensor_residual_op_at_threshold hq hn A hA
  have hs := pow_le_pow_left₀ (largestSingularCoefficient_nonneg _) h 2
  have he := uavg_nonneg (fun x => uavg_nonneg (fun y => sq_nonneg
    (supportedSVDResidual inputTensor inputTensor A (refreshThreshold (tensorShareCount F n)) x y)))
  have hc := (fourCycle_le_op_sq_energy _).trans (mul_le_mul_of_nonneg_right hs he)
  simpa only [mul_pow] using hc

/-- All SVD and numerical inputs are discharged; only the explicit residual moment of the actual refresh graph remains to be supplied by rank counting. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Over the binary field with n ≥ 2, let |A| ≤ 1, D = (2ⁿ-1)², β = D^(−1/4), and E = A-2 · project(A^(≥ β)). Assume the explicit fourth-moment estimate

𝔼_M [‖E^M‖ₒₚ⁴] ≤ 64C₄(E)+168/D(1+2/β)² · ‖E‖₂².

Then the tensor-refresh table satisfies

𝔼_M [‖A^M‖ₒₚ] ≤ 2 · ‖A‖ₒₚ+(2√6+96) · D^(−1/8).

The fourth-moment inequality is a hypothesis of this assembly lemma.
-/
theorem tensor_operator_from_residual_moment (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (A : Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℝ)
    (hA : ∀ i j, |A i j| ≤ 1)
    (hmoment : let D := tensorShareCount F n
      let β := refreshThreshold D
      let E := supportedSVDResidual inputTensor inputTensor A β
      uavg (fun M : Refresh.«GL» F (n*n) => largestSingularCoefficient (tensorRestriction E M)^4) ≤
        64 * fourCycle E + 168 / D * (1+2/β)^2 *
          uavg (fun x => uavg (fun y => E x y ^ 2))) :
    uavg (fun M : Refresh.«GL» F (n*n) => largestSingularCoefficient (tensorRestriction A M)) ≤
      2 * largestSingularCoefficient A + (2 * Real.sqrt 6 + 96) * tensorShareCount F n ^ (-(1/8 : ℝ)) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  letI : Nonempty (U F (n*n)) := ⟨unitShare ⟨0, by nlinarith⟩⟩
  let D := tensorShareCount F n
  let β := refreshThreshold D
  let E := supportedSVDResidual inputTensor inputTensor A β
  have hD : 1 ≤ D := (tensorShareCount_geometry (F := F) hn).1
  have hβ : 0 < β := refreshThreshold_pos (lt_of_lt_of_le zero_lt_one hD)
  have hβ1 : β ≤ 1 := refreshThreshold_le_one hD
  have hentry : β^2 * (1+2/β)^2 ≤ 9 := by
    have heq : β^2 * (1+2/β)^2 = (β+2)^2 := by field_simp
    rw [heq]
    nlinarith
  have hsplit (M : Refresh.«GL» F (n*n)) :
      largestSingularCoefficient (tensorRestriction A M) ≤
        2 * largestSingularCoefficient (tensorRestriction (refreshSVDPart A β) M) +
          largestSingularCoefficient (tensorRestriction E M) := by
    have h := supportedSVDResidual_graph_triangle inputTensor inputTensor A β M
    simpa only [tensorRestriction_op_complex] using h
  have hlarge := tensor_large_at_threshold hq hn A hA
  have henergy := supportedSVDResidual_energy inputTensor inputTensor A β hA
  have hcycle := tensor_residual_cycle_at_threshold hq hn A hA
  have h := operator_mean_at_feature_count
    (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n*n)))
    (fun M => largestSingularCoefficient (tensorRestriction A M))
    (fun M => largestSingularCoefficient (tensorRestriction (refreshSVDPart A β) M))
    (fun M => largestSingularCoefficient (tensorRestriction E M))
    D (largestSingularCoefficient A) (Real.sqrt 6) 3 (fourCycle E) (1+2/β)
    (uavg (fun x => uavg (fun y => E x y ^ 2)))
    hD (Real.sqrt_nonneg _) (by norm_num) (fun M => largestSingularCoefficient_nonneg _) hsplit
    (by simpa only [uavg_eq_expect_uniform] using hlarge)
    (uavg_nonneg (fun x => uavg_nonneg (fun y => sq_nonneg _))) henergy hcycle hentry
    (by simpa only [uavg_eq_expect_uniform] using hmoment)
  norm_num only [show (24 : ℝ)*(3+1)=96 by norm_num] at h
  simpa only [uavg_eq_expect_uniform] using h

end

end CircuitCompiler.RefreshAnalysis
