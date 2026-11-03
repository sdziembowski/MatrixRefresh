import Proofs.Compiler.GateApproximation.MatrixPhase.Complexification
import Proofs.Compiler.GateApproximation.MatrixPhase.GateDualBounds
import Proofs.Compiler.GateApproximation.MatrixPhase.JointDualTruncation



/-!
# The actual joint-port approximation theorem

The common conditional leakage probability table is approximated on all three ports. The proof combines the actual shared-matrix dual estimate with the weighted real nuclear-ball projection. No input plaintext is fixed in construction.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler

open Refresh MatrixRefresh TableAnalysis GateTruncation

noncomputable section

variable {F Z : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype Z] [Nonempty Z]

/-
Mathematical definition (normal notation): For F a set, assume F is a field; F is finite. define

jointApproximationConstant := √(2 · (|F| + 1)) + (|F| + 1) + jointDualRateConstant(F, (|F| + 1)).
-/
def jointApproximationConstant (F : Type*) [Field F] [Fintype F] [DecidableEq F] : ℝ :=
  Real.sqrt (2 * ((fieldCard F : ℝ) + 1)) + ((fieldCard F : ℝ) + 1) +
    jointDualRateConstant F ((fieldCard F : ℝ) + 1)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

0 < jointApproximationConstant(F).
-/
theorem jointApproximationConstant_pos : 0 < jointApproximationConstant F := by
  have hq : 0 ≤ (fieldCard F : ℝ) := Nat.cast_nonneg _
  have hd := jointDualRateConstant_nonneg (F := F) ((fieldCard F : ℝ) + 1)
  have hs := Real.sqrt_nonneg (2 * ((fieldCard F : ℝ) + 1))
  unfold jointApproximationConstant
  linarith

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z); z ∈ Z; i, j ∈ GateSide(F, n, (n · n)), we have

0 ≤ groupedMatrixAnswerProb(p, z, i, j) ∧ groupedMatrixAnswerProb(p, z, i, j) ≤ 1.
-/
lemma groupedMatrixAnswerProb_bounds {n : ℕ}
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) Z)
    (z : Z) (i j : GateSide F n (n * n)) :
    0 ≤ groupedMatrixAnswerProb p z i j ∧ groupedMatrixAnswerProb p z i j ≤ 1 := by
  constructor
  · exact matrixAnswerProb_nonneg p _ _ _ z
  · have h := Finset.single_le_sum (s := Finset.univ)
      (fun z _ => matrixAnswerProb_nonneg p ⟨i.1.1,j.1.1⟩ ⟨i.1.2,j.1.2⟩ ⟨i.2,j.2⟩ z)
      (Finset.mem_univ z)
    exact h.trans (matrixAnswerProb_sum_le p _ _ _)

/-- The real dual inequality for the genuine matrix-leakage probability table. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z); r ∈ ℝ; W ∈ Z → ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))), assume 2 ≤ n; 1 ≤ r; |F|ⁿ = r¹⁰; densityTablePair(gateDensity, W, W) ≤ 1. Then

densityTablePair(gateDensity, groupedMatrixAnswerProb(p), W) ≤ √(|Z|) · ‖ (z ↦ ‖ (gateDensity ⊙ W(z))‖ₒₚ)‖ + jointApproximationConstant(F) · |Z| / r.
-/
theorem joint_port_dual {n : ℕ} (hn : 2 ≤ n)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) Z)
    (r : ℝ) (hr : 1 ≤ r) (hN : (vectorCard F n : ℝ) = r ^ 10)
    (W : Z → Matrix (GateSide F n (n * n)) (GateSide F n (n * n)) ℝ)
    (hW : densityTablePair gateDensity W W ≤ 1) :
    densityTablePair gateDensity (groupedMatrixAnswerProb p) W ≤
      Real.sqrt (Fintype.card Z : ℝ) * ‖fun z => largestSingularCoefficient (gateDensity ⊙ W z)‖ +
        jointApproximationConstant F * Fintype.card Z / r := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  letI : Nonempty (U F (n * n)) := ⟨unitShare ⟨0, by nlinarith⟩⟩
  have hm : 2 ≤ n * n := by nlinarith
  have hr0 : 0 < r := by linarith
  let H : ℝ := (fieldCard F : ℝ) + 1
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let V : Z → Matrix (GateSide F n (n * n)) (GateSide F n (n * n)) ℝ :=
    fun z => gateDensity ⊙ W z
  let VC := fun z => (V z).map Complex.ofReal
  let T := ‖fun z => largestSingularCoefficient (V z)‖
  have henergy : (∑ z, energy (VC z)) ≤ H := by
    exact density_test_family_energy gateDensity W H hH (gateDensity_nonneg hm) (gateDensity_le hm) hW
  have hleaf (z : Z) : energy (VC z) ≤ H := by
    apply (Finset.single_le_sum (s := Finset.univ) (fun z _ =>
      uavg_nonneg (fun i => GateTruncation.rowEnergy_nonneg (VC z) i)) (Finset.mem_univ z)).trans henergy
  have hop (z : Z) : opNorm (VC z) ≤ T := by
    unfold opNorm
    rw [show VC z = (V z).map Complex.ofReal by rfl, complexMatrix_ofReal_norm]
    change largestSingularCoefficient (V z) ≤ T
    simpa only [Real.norm_eq_abs, abs_of_nonneg (largestSingularCoefficient_nonneg _)] using
      norm_le_pi_norm (fun z => largestSingularCoefficient (V z)) z
  have hsupport (z : Z) (i j : GateSide F n (n * n))
      (hij : graphConstraint inputTensor inputTensor i j ≠ 0) : VC z i j = 0 := by
    have he : dot i.2.val j.2.val ≠ portProduct i j := by
      intro he
      apply hij
      change dot (tensorVector i.1.1.val i.1.2.val) (tensorVector j.1.1.val j.1.2.val) -
        dot i.2.val j.2.val = 0
      rw [tensorVector_dot]
      exact sub_eq_zero.mpr he.symm
    simp [VC, V, Matrix.map_apply, Matrix.hadamard_apply, gateDensity, encodingDensity, he]
  have htrim := density_test_trim_pairing gateDensity (gateDensity_nonneg hm)
    (jointPortDistribution (F := F) hn hm)
    (fun f => jointPortDistribution_expect hn hm (fun i j => f (i,j)))
    (jointPortDistribution_left_marginal hn hm) (jointPortDistribution_right_marginal hn hm)
    W (groupedMatrixAnswerProb p) (groupedMatrixAnswerProb_bounds p) r H hr0 hH henergy hW
  have hcap := real_cap_pairing_loss VC (groupedMatrixAnswerProb p) (groupedMatrixAnswerProb_bounds p)
    r (r ^ 3) H (by positivity) henergy
  have hmain := capped_answer_table_family_bound hn (fieldCharacter F) fieldCharacter_primitive p
    VC r H T hr hN hH (norm_nonneg _) hleaf hop hsupport
  change answerTablePairing (groupedMatrixAnswerProb p)
    (fun z i j => (capped (VC z) r (r ^ 3) i j).re) ≤
      Real.sqrt (Fintype.card Z : ℝ) * T + (Fintype.card Z : ℝ) * jointDualRateConstant F H / r at hmain
  have hcapcost : H / r ^ 3 ≤ H / r := div_le_div_of_nonneg_left hH hr0
    (by simpa only [pow_one] using pow_le_pow_right₀ hr (by decide : 1 ≤ 3))
  have hcard : (1 : ℝ) ≤ Fintype.card Z := by exact_mod_cast Fintype.card_pos
  have hrest : Real.sqrt (2 * H) / r + H / r ≤
      (Fintype.card Z : ℝ) * (Real.sqrt (2 * H) + H) / r := by
    have h := mul_le_mul_of_nonneg_right hcard
      (show 0 ≤ (Real.sqrt (2 * H) + H) / r by positivity)
    convert h using 1 <;> ring
  change densityTablePair gateDensity (groupedMatrixAnswerProb p) W ≤
    Real.sqrt (Fintype.card Z : ℝ) * T + jointApproximationConstant F * Fintype.card Z / r
  have hconst : jointApproximationConstant F = Real.sqrt (2 * H) + H + jointDualRateConstant F H := rfl
  rw [hconst]
  change densityTablePair gateDensity (groupedMatrixAnswerProb p) W ≤
      answerTablePairing (groupedMatrixAnswerProb p) (fun z i j => (trim (VC z) r i j).re) +
        Real.sqrt (2 * H) / r at htrim
  have hsum : densityTablePair gateDensity (groupedMatrixAnswerProb p) W ≤
      (Real.sqrt (Fintype.card Z : ℝ) * T + (Fintype.card Z : ℝ) * jointDualRateConstant F H / r) +
        (Real.sqrt (2 * H) / r + H / r) := by linarith
  exact hsum.trans ((add_le_add le_rfl hrest).trans_eq (by ring))

/-- Common real approximating tables for the actual all-port conditional matrix-answer probability table. Their construction does not depend on either input secret. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z), assume 2 ≤ n. Then

∃ G ∈ Z → ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))), (∑_z (‖ G(z)‖_*)) ≤ √(|Z|) ∧ √(densityTablePair(gateDensity, ((z, i, j ↦ groupedMatrixAnswerProb(p, z, i, j) - G(z, i, j))), ((z, i, j ↦ groupedMatrixAnswerProb(p, z, i, j) - G(z, i, j))))) ≤ jointApproximationConstant(F) · |Z| · (|F|ⁿ)^(−((1 / 10))).
-/
theorem exists_jointPort_approximation {n : ℕ} (hn : 2 ≤ n)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) Z) :
    ∃ G : Z → Matrix (GateSide F n (n * n)) (GateSide F n (n * n)) ℝ,
      (∑ z, tableNuclearNorm (G z)) ≤ Real.sqrt (Fintype.card Z : ℝ) ∧
      Real.sqrt (densityTablePair gateDensity
        (fun z i j => groupedMatrixAnswerProb p z i j - G z i j)
        (fun z i j => groupedMatrixAnswerProb p z i j - G z i j)) ≤
        jointApproximationConstant F * Fintype.card Z * (vectorCard F n : ℝ) ^ (-(1 / 10) : ℝ) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  letI : Nonempty (U F (n * n)) := ⟨unitShare ⟨0, by nlinarith⟩⟩
  have hm : 2 ≤ n * n := by nlinarith
  have hN4 := vectorCard_real_ge_four (F := F) hn
  have hN0 : 0 ≤ (vectorCard F n : ℝ) := by positivity
  obtain ⟨hr, hpow⟩ := tenth_root_parameters (vectorCard F n : ℝ) (by linarith)
  apply exists_density_tableNuclearNormProjection gateDensity (gateDensity_nonneg hm)
    (Real.sqrt (Fintype.card Z : ℝ))
    (jointApproximationConstant F * Fintype.card Z * (vectorCard F n : ℝ) ^ (-(1 / 10) : ℝ))
    (Real.sqrt_nonneg _) (by have := jointApproximationConstant_pos (F := F); positivity)
    (groupedMatrixAnswerProb p)
  intro W hW
  have h := joint_port_dual hn p ((vectorCard F n : ℝ) ^ (1 / 10 : ℝ)) hr hpow W hW
  simpa only [Real.rpow_neg hN0, div_eq_mul_inv] using h

/-- The same field-only constant can be used for both displayed bounds in the manuscript's joint-port approximation lemma. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z), assume 2 ≤ n. Then

∃ G ∈ Z → ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))), (∑_z (‖ G(z)‖_*)) ≤ jointApproximationConstant(F) · √(|Z|) ∧ √(densityTablePair(gateDensity, ((z, i, j ↦ groupedMatrixAnswerProb(p, z, i, j) - G(z, i, j))), ((z, i, j ↦ groupedMatrixAnswerProb(p, z, i, j) - G(z, i, j))))) ≤ jointApproximationConstant(F) · |Z| · (|F|ⁿ)^(−((1 / 10))).
-/
theorem jointPort_approximation {n : ℕ} (hn : 2 ≤ n)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) Z) :
    ∃ G : Z → Matrix (GateSide F n (n * n)) (GateSide F n (n * n)) ℝ,
      (∑ z, tableNuclearNorm (G z)) ≤ jointApproximationConstant F * Real.sqrt (Fintype.card Z : ℝ) ∧
      Real.sqrt (densityTablePair gateDensity
        (fun z i j => groupedMatrixAnswerProb p z i j - G z i j)
        (fun z i j => groupedMatrixAnswerProb p z i j - G z i j)) ≤
        jointApproximationConstant F * Fintype.card Z * (vectorCard F n : ℝ) ^ (-(1 / 10) : ℝ) := by
  obtain ⟨G, hG, he⟩ := exists_jointPort_approximation hn p
  refine ⟨G, hG.trans ?_, he⟩
  have hC : 1 ≤ jointApproximationConstant F := by
    have hq := fieldCard_cast_ge_two (F := F)
    have hs := Real.sqrt_nonneg (2 * ((fieldCard F : ℝ) + 1))
    have hd := jointDualRateConstant_nonneg (F := F) ((fieldCard F : ℝ) + 1)
    unfold jointApproximationConstant
    linarith
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg (Fintype.card Z : ℝ))

end

end CircuitCompiler
