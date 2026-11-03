import Proofs.Compiler.GateApproximation.MatrixPhase.GateDensity
import Proofs.Compiler.GateApproximation.MatrixPhase.GateTruncation
import Proofs.Compiler.GateApproximation.MatrixPhase.JointGramRestriction
import Proofs.Compiler.GateApproximation.MatrixPhase.Moments



/-!
# Gram perturbation bounds for the tensor operator estimate

A common bound on the norms of the two reference Grams gives linear dependence on their deviations. The actual tensor-matrix variance theorem supplies these deviations. `Proofs/Compiler/GateApproximation/MatrixPhase/SVDGram.lean` instantiates the reference-Gram and feature-energy bounds for the concrete singular-value truncation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis GateTruncation

noncomputable section

/-- Cauchy--Schwarz/AM--GM at the synthesis level: common reference-Gram bound `θ` gives an additive half-sum of deviations, rather than their square roots. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For I,J,P a set; A ∈ ℂ^(I × P); B ∈ ℂ^(J × P); S, T ∈ ℂ^(P × P); θ, u, v ∈ ℝ, assume I is finite; J is finite; P is finite; ‖ S‖ ≤ θ; ‖ T‖ ≤ θ; ‖ Aᴴ · A - S‖ ≤ u; ‖ Bᴴ · B - T‖ ≤ v. Then

‖ A · Bᴴ‖ ≤ θ + (u + v) / 2.
-/
theorem product_norm_le_reference_gram
    {I J P : Type*} [Fintype I] [Fintype J] [Fintype P]
    [DecidableEq I] [DecidableEq J] [DecidableEq P]
    (A : Matrix I P ℂ) (B : Matrix J P ℂ) (S T : Matrix P P ℂ)
    (θ u v : ℝ) (hS : ‖S‖ ≤ θ) (hT : ‖T‖ ≤ θ)
    (hu : ‖Aᴴ * A - S‖ ≤ u) (hv : ‖Bᴴ * B - T‖ ≤ v) :
    ‖A * Bᴴ‖ ≤ θ + (u + v) / 2 := by
  have hA := norm_sub_norm_le (Aᴴ * A) S
  have hB := norm_sub_norm_le (Bᴴ * B) T
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hA hB
  have hp := Matrix.l2_opNorm_mul A Bᴴ
  rw [Matrix.l2_opNorm_conjTranspose] at hp
  nlinarith [sq_nonneg (‖A‖ - ‖B‖)]

variable {F P : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype P] [DecidableEq P] {n : ℕ}

/-
Mathematical definition (normal notation): For ξ, ζ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ, define

tensorFactorTable(ξ, ζ) := (x, y ↦ ∑ₚ (ξ((x)₁, (x)₂, p) · star(ζ((y)₁, (y)₂, p)))).
-/
def tensorFactorTable
    (ξ ζ : (U F n × U F n) → U F (n*n) → P → ℂ) :
    Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℂ :=
  fun x y => ∑ p, ξ x.1 x.2 p * star (ζ y.1 y.2 p)

/-- The restricted synthesis product is the actual normalized refresh table. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ, ζ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; M ∈ GL_(n · n)(F), assume 2 ≤ n. Then

‖ jointRowSynthesis(ξ, M) · jointColumnSynthesis(ζ, M, ᴴ)‖ = opNorm(graphRestriction(inputTensor, inputTensor, tensorFactorTable(ξ, ζ), M)) .
-/
theorem tensor_synthesis_product_norm (hn : 2 ≤ n)
    (ξ ζ : (U F n × U F n) → U F (n*n) → P → ℂ)
    (M : Refresh.«GL» F (n*n)) :
    ‖jointRowSynthesis ξ M * (jointColumnSynthesis ζ M)ᴴ‖ =
      opNorm (graphRestriction inputTensor inputTensor (tensorFactorTable ξ ζ) M) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  rw [jointRowSynthesis, jointColumnSynthesis, normalizedComplexFeatures_product_norm]
  rfl

/-- The actual tensor graph obeys the improved pointwise Gram estimate. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ, ζ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; θ ∈ ℝ; M ∈ GL_(n · n)(F), assume 2 ≤ n; ‖ jointMeanGram(ξ)‖ ≤ θ; ‖ jointMeanGram(ζ)‖ ≤ θ. Then

opNorm(graphRestriction(inputTensor, inputTensor, tensorFactorTable(ξ, ζ), M)) ≤ θ + (√(jointRowGramDeviationSq(ξ, M)) + √(∑ₚ (∑_q ((‖ jointColumnGram(ζ, M, p, q) - jointMeanGram(ζ, p, q)‖)²)))) / 2.
-/
theorem tensor_large_part_pointwise (hn : 2 ≤ n)
    (ξ ζ : (U F n × U F n) → U F (n*n) → P → ℂ) (θ : ℝ)
    (hξ : ‖jointMeanGram ξ‖ ≤ θ) (hζ : ‖jointMeanGram ζ‖ ≤ θ)
    (M : Refresh.«GL» F (n*n)) :
    opNorm (graphRestriction inputTensor inputTensor (tensorFactorTable ξ ζ) M) ≤
      θ + (Real.sqrt (jointRowGramDeviationSq ξ M) +
        Real.sqrt (∑ p, ∑ q, ‖jointColumnGram ζ M p q - jointMeanGram ζ p q‖ ^ 2)) / 2 := by
  rw [← tensor_synthesis_product_norm hn]
  apply product_norm_le_reference_gram _ _ (jointMeanGram ξ) (jointMeanGram ζ)
    θ _ _ hξ hζ
  · rw [jointRowSynthesis_gram hn]
    exact Real.le_sqrt_of_sq_le (complex_rectangular_norm_sq_le _)
  · rw [jointColumnSynthesis_gram hn]
    exact Real.le_sqrt_of_sq_le (complex_rectangular_norm_sq_le _)

/-- Actual GL averaging of the large part with a shared reference-Gram bound. For SVD factors, the hypotheses hold with `L=1/β` and `θ=‖F‖op`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ, ζ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; θ, L ∈ ℝ, assume 2 ≤ n; 0 ≤ L; ‖ jointMeanGram(ξ)‖ ≤ θ; ‖ jointMeanGram(ζ)‖ ≤ θ; ∀ x, u, jointFeatureEnergy(ξ, x, u) ≤ L; ∀ x, u, jointFeatureEnergy(ζ, x, u) ≤ L. Then

𝔼_(M ∈ GL_(n · n)(F)) [opNorm(graphRestriction(inputTensor, inputTensor, tensorFactorTable(ξ, ζ), M))] ≤ θ + √(jointVarianceCoefficient(F, n)) · L.
-/
theorem tensor_large_part_mean (hn : 2 ≤ n)
    (ξ ζ : (U F n × U F n) → U F (n*n) → P → ℂ) (θ L : ℝ)
    (hL : 0 ≤ L)
    (hξ : ‖jointMeanGram ξ‖ ≤ θ) (hζ : ‖jointMeanGram ζ‖ ≤ θ)
    (hξpoint : ∀ x u, jointFeatureEnergy ξ x u ≤ L)
    (hζpoint : ∀ x u, jointFeatureEnergy ζ x u ≤ L) :
    uavg (fun M : Refresh.«GL» F (n*n) =>
      opNorm (graphRestriction inputTensor inputTensor (tensorFactorTable ξ ζ) M)) ≤
        θ + Real.sqrt (jointVarianceCoefficient F n) * L := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  letI : Nonempty (U F (n*n)) := ⟨unitShare ⟨0, by nlinarith⟩⟩
  have hκ := jointVarianceCoefficient_nonneg (F := F) hn
  have hξavg : uavg (fun x => uavg (fun u => jointFeatureEnergy ξ x u)) ≤ L := by
    exact (uavg_mono (fun x => (uavg_mono (hξpoint x)).trans_eq (uavg_const L))).trans_eq
      (uavg_const L)
  have hζavg : uavg (fun x => uavg (fun u => jointFeatureEnergy ζ x u)) ≤ L := by
    exact (uavg_mono (fun x => (uavg_mono (hζpoint x)).trans_eq (uavg_const L))).trans_eq
      (uavg_const L)
  have hξvar := (joint_row_Gram_variance_le_energy hn ξ L hξpoint).trans
    (mul_le_mul_of_nonneg_left hξavg (mul_nonneg hκ hL))
  have hζvar := (joint_column_Gram_variance_le_energy hn ζ L hζpoint).trans
    (mul_le_mul_of_nonneg_left hζavg (mul_nonneg hκ hL))
  let u := fun M : Refresh.«GL» F (n*n) => Real.sqrt (jointRowGramDeviationSq ξ M)
  let v := fun M : Refresh.«GL» F (n*n) => Real.sqrt
    (∑ p, ∑ q, ‖jointColumnGram ζ M p q - jointMeanGram ζ p q‖ ^ 2)
  have hu : uavg (fun M => u M ^ 2) ≤ jointVarianceCoefficient F n * L ^ 2 := by
    have hu0 (M : Refresh.«GL» F (n*n)) : 0 ≤ jointRowGramDeviationSq ξ M := by
      unfold jointRowGramDeviationSq
      positivity
    simp only [u, Real.sq_sqrt (hu0 _)]
    simpa only [mul_assoc, ← pow_two] using hξvar
  have hv : uavg (fun M => v M ^ 2) ≤ jointVarianceCoefficient F n * L ^ 2 := by
    simpa only [v, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
      (fun _ _ => sq_nonneg _))), mul_assoc, ← pow_two] using hζvar
  have h := gram_mean_of_second_moments (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n*n)))
    (fun M => opNorm (graphRestriction inputTensor inputTensor (tensorFactorTable ξ ζ) M))
    u v θ _ _ (tensor_large_part_pointwise hn ξ ζ θ hξ hζ)
    (by simpa only [uavg_eq_expect_uniform] using hu)
    (by simpa only [uavg_eq_expect_uniform] using hv)
  rw [← uavg_eq_expect_uniform, Real.sqrt_mul hκ, Real.sqrt_sq hL] at h
  linarith

/-- The binary tensor large-part cost has the current `1/(N β)` scale. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ, ζ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; θ, β ∈ ℝ, assume |F| = 2; 2 ≤ n; 0 < β; ‖ jointMeanGram(ξ)‖ ≤ θ; ‖ jointMeanGram(ζ)‖ ≤ θ; ∀ x, u, jointFeatureEnergy(ξ, x, u) ≤ 1 / β; ∀ x, u, jointFeatureEnergy(ζ, x, u) ≤ 1 / β. Then

𝔼_(M ∈ GL_(n · n)(F)) [opNorm(graphRestriction(inputTensor, inputTensor, tensorFactorTable(ξ, ζ), M))] ≤ θ + √6 / (|F|ⁿ · β).
-/
theorem tensor_large_part_mean_binary (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (ξ ζ : (U F n × U F n) → U F (n*n) → P → ℂ) (θ β : ℝ)
    (hβ : 0 < β)
    (hξ : ‖jointMeanGram ξ‖ ≤ θ) (hζ : ‖jointMeanGram ζ‖ ≤ θ)
    (hξpoint : ∀ x u, jointFeatureEnergy ξ x u ≤ 1 / β)
    (hζpoint : ∀ x u, jointFeatureEnergy ζ x u ≤ 1 / β) :
    uavg (fun M : Refresh.«GL» F (n*n) =>
      opNorm (graphRestriction inputTensor inputTensor (tensorFactorTable ξ ζ) M)) ≤
        θ + Real.sqrt 6 / ((vectorCard F n : ℝ) * β) := by
  have h := tensor_large_part_mean hn ξ ζ θ (1 / β) (by positivity)
    hξ hζ hξpoint hζpoint
  have hκ := jointVarianceCoefficient_le (F := F) hn
  rw [hq] at hκ
  norm_num at hκ
  have hroot := Real.sqrt_le_sqrt hκ
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 6),
    Real.sqrt_sq (Nat.cast_nonneg _)] at hroot
  have hterm := mul_le_mul_of_nonneg_right hroot (by positivity : (0 : ℝ) ≤ 1 / β)
  exact h.trans (add_le_add le_rfl (hterm.trans_eq (by ring)))

end

end CircuitCompiler.RefreshAnalysis
