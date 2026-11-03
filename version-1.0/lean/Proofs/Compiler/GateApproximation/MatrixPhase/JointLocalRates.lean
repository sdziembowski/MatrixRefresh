import Proofs.Compiler.GateApproximation.MatrixPhase.JointLocalOperator
import Proofs.Compiler.GateApproximation.MatrixPhase.JointParameters



/-!
# Field-only rates for the actual local graph estimate

The tenth-root choice is inserted into the proved spectral and graph bounds. All constants below depend on the field alone.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler

open Refresh MatrixRefresh TableAnalysis GateTruncation

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-
Mathematical definition (normal notation): For F a set, assume F is finite. define

jointVarianceConstant := 4 · (|F| - 1)² + 2 · (|F| - 1).
-/
def jointVarianceConstant (F : Type*) [Fintype F] : ℝ :=
  4 * ((fieldCard F : ℝ) - 1) ^ 2 + 2 * ((fieldCard F : ℝ) - 1)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

0 ≤ jointVarianceConstant(F).
-/
lemma jointVarianceConstant_nonneg : 0 ≤ jointVarianceConstant F := by
  have hq := fieldCard_cast_ge_two (F := F)
  have hq1 : 0 ≤ (fieldCard F : ℝ) - 1 := by linarith
  unfold jointVarianceConstant
  positivity

/-
Mathematical definition (normal notation): For F a set; H ∈ ℝ, assume F is finite. define

jointGramRateConstant(H) := 2 · √H · fourthRoot((2 · jointVarianceConstant(F) · H)) + √(2 · jointVarianceConstant(F) · H).
-/
def jointGramRateConstant (F : Type*) [Fintype F] (H : ℝ) : ℝ :=
  2 * Real.sqrt H * fourthRoot (2 * jointVarianceConstant F * H) +
    Real.sqrt (2 * jointVarianceConstant F * H)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r, H ∈ ℝ, assume 2 ≤ n; 1 ≤ r; 0 ≤ H; |F|ⁿ = r¹⁰. Then

jointGramCost(F, n, (r² / (1 / r²)), (H / (1 / r²))) ≤ jointGramRateConstant(F, H) / r .
-/
theorem jointGramCost_tenth_root_le (hn : 2 ≤ n) (r H : ℝ) (hr : 1 ≤ r) (hH : 0 ≤ H)
    (hN : (vectorCard F n : ℝ) = r ^ 10) :
    jointGramCost F n (r ^ 2 / (1 / r ^ 2)) (H / (1 / r ^ 2)) ≤
      jointGramRateConstant F H / r := by
  have hr0 : 0 < r := by linarith
  have hrne := hr0.ne'
  have hC : 0 ≤ jointVarianceConstant F := jointVarianceConstant_nonneg
  have hmix : jointVarianceCoefficient F n ≤ jointVarianceConstant F / r ^ 20 := by
    have h := jointVarianceCoefficient_le (F := F) hn
    rw [hN] at h
    convert h using 1 <;> unfold jointVarianceConstant <;> ring
  have hV : 2 * jointVarianceCoefficient F n * (r ^ 2 / (1 / r ^ 2)) *
      (H / (1 / r ^ 2)) ≤ (2 * jointVarianceConstant F * H) / r ^ 8 := by
    calc
      _ ≤ 2 * (jointVarianceConstant F / r ^ 20) * (r ^ 2 / (1 / r ^ 2)) *
          (H / (1 / r ^ 2)) := by gcongr
      _ = (2 * jointVarianceConstant F * H) / r ^ 14 := by field_simp <;> ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ hr (by decide : 8 ≤ 14))
  have hroot : Real.sqrt ((2 * jointVarianceConstant F * H) / r ^ 8) =
      Real.sqrt (2 * jointVarianceConstant F * H) / r ^ 4 := by
    rw [Real.sqrt_div (by positivity), show r ^ 8 = (r ^ 4) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  have hrootroot : Real.sqrt (Real.sqrt ((2 * jointVarianceConstant F * H) / r ^ 8)) =
      fourthRoot (2 * jointVarianceConstant F * H) / r ^ 2 := by
    rw [hroot, Real.sqrt_div (Real.sqrt_nonneg _), show r ^ 4 = (r ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
    rfl
  have htrace : Real.sqrt (H / (1 / r ^ 2)) = Real.sqrt H * r := by
    rw [show H / (1 / r ^ 2) = H * r ^ 2 by field_simp,
      Real.sqrt_mul hH, Real.sqrt_sq hr0.le]
  have hfirst : 2 * Real.sqrt (H / (1 / r ^ 2)) *
      Real.sqrt (Real.sqrt (2 * jointVarianceCoefficient F n * (r ^ 2 / (1 / r ^ 2)) *
        (H / (1 / r ^ 2)))) ≤
      (2 * Real.sqrt H * fourthRoot (2 * jointVarianceConstant F * H)) / r := by
    apply (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hV)) (by positivity)).trans_eq
    rw [htrace, hrootroot]
    field_simp
  have hsecond : Real.sqrt (2 * jointVarianceCoefficient F n * (r ^ 2 / (1 / r ^ 2)) *
      (H / (1 / r ^ 2))) ≤ Real.sqrt (2 * jointVarianceConstant F * H) / r := by
    apply (Real.sqrt_le_sqrt hV).trans
    rw [hroot]
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hr0
      (by simpa using pow_le_pow_right₀ hr (by decide : 1 ≤ 4))
  exact (add_le_add hfirst hsecond).trans_eq (by unfold jointGramRateConstant; ring)

/-
Mathematical definition (normal notation): For F a set; H ∈ ℝ, assume F is a field; F is finite. define

jointOperatorRateConstant(H) := |F| · jointGramRateConstant(F, H) + |F| · fourthRoot(H) + 2 · fourthRoot(tensorCycleErrorConstant(F)).
-/
def jointOperatorRateConstant (F : Type*) [Field F] [Fintype F] [DecidableEq F] (H : ℝ) : ℝ :=
  (fieldCard F : ℝ) * jointGramRateConstant F H + (fieldCard F : ℝ) * fourthRoot H +
    2 * fourthRoot (tensorCycleErrorConstant F)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

(|F|ⁿ)² ≤ |F|^(n · n).
-/
lemma tensor_card_square_le (hn : 2 ≤ n) : (vectorCard F n : ℝ) ^ 2 ≤ (vectorCard F (n * n) : ℝ) := by
  have hpow : vectorCard F n ^ 2 ≤ vectorCard F (n * n) := by
    unfold vectorCard
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by have := fieldCard_ge_two (F := F); omega) (by nlinarith)
  exact_mod_cast hpow

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r, H ∈ ℝ, assume 2 ≤ n; 1 ≤ r; 0 ≤ H; |F|ⁿ = r¹⁰. Then

jointOperatorError(F, n, r, (r³), (1 / r²), H) ≤ jointOperatorRateConstant(F, H) / r.
-/
theorem jointOperatorError_tenth_root_le (hn : 2 ≤ n) (r H : ℝ) (hr : 1 ≤ r) (hH : 0 ≤ H)
    (hN : (vectorCard F n : ℝ) = r ^ 10) :
    jointOperatorError F n r (r ^ 3) (1 / r ^ 2) H ≤ jointOperatorRateConstant F H / r := by
  have hr0 : 0 < r := by linarith
  have hQ : (vectorCard F n : ℝ) ^ 2 ≤ (vectorCard F (n * n) : ℝ) := tensor_card_square_le hn
  have hp := joint_parameter_terms r (vectorCard F n : ℝ) (vectorCard F (n * n) : ℝ) hr hN hQ
  dsimp only at hp
  have hg := jointGramCost_tenth_root_le hn r H hr hH hN
  have hbeta : Real.sqrt (1 / r ^ 2) = 1 / r := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one, Real.sqrt_sq hr0.le]
  have hcap := hp.2.2.2.2.2.2.2.2.1
  have hcyc : fourthRoot (tensorCycleErrorConstant F) / Real.sqrt (vectorCard F n : ℝ) *
      (r ^ 3 + r ^ 2 / (1 / r ^ 2)) ≤ 2 * fourthRoot (tensorCycleErrorConstant F) / r := by
    have h := mul_le_mul_of_nonneg_left hcap (show 0 ≤ fourthRoot (tensorCycleErrorConstant F) by
      unfold fourthRoot; positivity)
    convert h using 1 <;> ring
  unfold jointOperatorError
  rw [hbeta]
  have h := add_le_add (mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg (fieldCard F) : (0 : ℝ) ≤ _))
    (add_le_add (le_refl ((fieldCard F : ℝ) * (1 / r) * fourthRoot H)) hcyc)
  exact h.trans_eq (by unfold jointOperatorRateConstant; ring)

/-
Mathematical definition (normal notation): For F a set; H ∈ ℝ, assume F is a field; F is finite. define

jointGraphRateConstant(H) := 2 · |F| + 2 · (|F|)² + jointOperatorRateConstant(F, H).
-/
def jointGraphRateConstant (F : Type*) [Field F] [Fintype F] [DecidableEq F] (H : ℝ) : ℝ :=
  2 * (fieldCard F : ℝ) + 2 * (fieldCard F : ℝ) ^ 2 + jointOperatorRateConstant F H

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For H ∈ ℝ, we have

0 ≤ jointGraphRateConstant(F, H).
-/
lemma jointGraphRateConstant_nonneg (H : ℝ) : 0 ≤ jointGraphRateConstant F H := by
  unfold jointGraphRateConstant jointOperatorRateConstant jointGramRateConstant fourthRoot
  positivity

/-- Final normalized graph estimate with a field-only rate, retaining the rectangle weight only on the leading operator term. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ψ ∈ AddChar(F, ℂ); A ∈ ℂ^(((U(F, n) × U(F, n)) × U(F, (n · n))) × ((U(F, n) × U(F, n)) × U(F, (n · n)))); r, H, T ∈ ℝ; w ∈ GL_(n · n)(F) → ℝ, assume 2 ≤ n; ψ.IsPrimitive; 1 ≤ r; |F|ⁿ = r¹⁰; 0 ≤ H; energy(A) ≤ H; opNorm(A) ≤ T; ∀ i, j, (graphConstraint(inputTensor, inputTensor, i, j) ≠ 0) ⇒ A(i, j) = 0; ∀ M, 0 ≤ w(M); ∀ M, w(M) ≤ 1. Then

𝔼_M [w(M) · opNorm(graphRestriction(inputTensor, inputTensor, capped(A, r, (r³)), M))] ≤ |F| · T · 𝔼ᵤ [w(u)] + jointGraphRateConstant(F, H) / r.
-/
theorem joint_capped_graph_weighted_rate (hn : 2 ≤ n) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (A : Matrix ((U F n × U F n) × U F (n * n)) ((U F n × U F n) × U F (n * n)) ℂ)
    (r H T : ℝ) (hr : 1 ≤ r) (hN : (vectorCard F n : ℝ) = r ^ 10) (hH : 0 ≤ H)
    (henergy : energy A ≤ H) (hop : opNorm A ≤ T)
    (hsupport : ∀ i j, graphConstraint inputTensor inputTensor i j ≠ 0 → A i j = 0)
    (w : Refresh.«GL» F (n * n) → ℝ) (hw0 : ∀ M, 0 ≤ w M) (hw1 : ∀ M, w M ≤ 1) :
    uavg (fun M => w M * opNorm (graphRestriction inputTensor inputTensor (capped A r (r ^ 3)) M)) ≤
      (fieldCard F : ℝ) * T * uavg w + jointGraphRateConstant F H / r := by
  have hr0 : 0 < r := by linarith
  have hq0 : 0 ≤ (fieldCard F : ℝ) := Nat.cast_nonneg _
  have h := joint_capped_graph_weighted hn ψ hψ A r (r ^ 3) (1 / r ^ 2) H T
    (by positivity) (by positivity) hH henergy hop hsupport w hw0 hw1
  have he := jointOperatorError_tenth_root_le hn r H hr hH hN
  have hp := joint_parameter_terms r (vectorCard F n : ℝ) (vectorCard F (n * n) : ℝ) hr hN (tensor_card_square_le hn)
  dsimp only at hp
  have hcap := hp.2.2.1
  have hbeta := hp.2.2.2.1
  have hcross := hp.2.2.2.2.1
  have hwmean : 0 ≤ uavg w := uavg_nonneg hw0
  have hwmean1 : uavg w ≤ 1 := by simpa only [uavg_const] using uavg_mono hw1
  have hsmall : r ^ 2 / r ^ 3 + 1 / r ^ 2 +
      (fieldCard F : ℝ) * (2 / Real.sqrt (vectorCard F (n * n) : ℝ)) * (r ^ 2 / (1 / r ^ 2)) ≤
      (2 + 2 * (fieldCard F : ℝ)) / r := by
    have hx := mul_le_mul_of_nonneg_left hcross (show 0 ≤ 2 * (fieldCard F : ℝ) by positivity)
    have hs := add_le_add (add_le_add hcap hbeta) hx
    convert hs using 1 <;> ring
  have hlead : (fieldCard F : ℝ) * (T + r ^ 2 / r ^ 3 + 1 / r ^ 2 +
      (fieldCard F : ℝ) * (2 / Real.sqrt (vectorCard F (n * n) : ℝ)) * (r ^ 2 / (1 / r ^ 2))) * uavg w ≤
      (fieldCard F : ℝ) * T * uavg w + (2 * (fieldCard F : ℝ) + 2 * (fieldCard F : ℝ) ^ 2) / r := by
    have hs := mul_le_mul_of_nonneg_left hsmall hq0
    have hsw := mul_le_mul_of_nonneg_right hs hwmean
    have hw' := mul_le_mul_of_nonneg_left hwmean1
      (show 0 ≤ (fieldCard F : ℝ) * ((2 + 2 * (fieldCard F : ℝ)) / r) by positivity)
    convert add_le_add (le_refl ((fieldCard F : ℝ) * T * uavg w)) (hsw.trans hw') using 1 <;> ring
  exact h.trans ((add_le_add hlead he).trans_eq (by unfold jointGraphRateConstant; ring))

end

end CircuitCompiler
