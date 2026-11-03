import Proofs.Compiler.GateApproximation.MatrixPhase.JointGramRestriction
import Proofs.Compiler.GateApproximation.MatrixPhase.JointGraphCycle
import Proofs.Compiler.GateApproximation.MatrixPhase.JointTwistBound
import Proofs.Compiler.GateApproximation.MatrixPhase.JointUniformExtraction



/-!
# Actual graph restriction bounds for the extracted blocks

This file identifies the normalized synthesis products with the extracted tables and their refresh graph restrictions, then inserts the proved budgets.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler

open Refresh MatrixRefresh TableAnalysis GateTruncation

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

variable {P : Type*} [Fintype P] [DecidableEq P]

/-
Mathematical definition (normal notation): For ξ, ζ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ, define

jointFeatureTable(ξ, ζ) := (i, j ↦ ∑ₚ (ξ((i)₁, (i)₂, p) · star(ζ((j)₁, (j)₂, p)))).
-/
def jointFeatureTable (ξ ζ : (U F n × U F n) → U F (n * n) → P → ℂ) :
    Matrix ((U F n × U F n) × U F (n * n)) ((U F n × U F n) × U F (n * n)) ℂ :=
  fun i j => ∑ p, ξ i.1 i.2 p * star (ζ j.1 j.2 p)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ, ζ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ, assume 2 ≤ n. Then

‖ jointReferenceSynthesis(ξ) · jointReferenceSynthesis(ζ, ᴴ)‖ = opNorm(jointFeatureTable(ξ, ζ)).
-/
theorem jointReferenceSynthesis_product_norm (hn : 2 ≤ n)
    (ξ ζ : (U F n × U F n) → U F (n * n) → P → ℂ) :
    ‖jointReferenceSynthesis ξ * (jointReferenceSynthesis ζ)ᴴ‖ =
      opNorm (jointFeatureTable ξ ζ) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  letI : Nonempty (U F (n * n)) := ⟨unitShare ⟨0, by nlinarith⟩⟩
  rw [jointReferenceSynthesis, jointReferenceSynthesis, normalizedComplexFeatures_product_norm]
  rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ, ζ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; M ∈ GL_(n · n)(F), assume 2 ≤ n. Then

‖ jointRowSynthesis(ξ, M) · jointColumnSynthesis(ζ, M, ᴴ)‖ = opNorm(graphRestriction(inputTensor, inputTensor, jointFeatureTable(ξ, ζ), M)) .
-/
theorem jointGraphSynthesis_product_norm (hn : 2 ≤ n)
    (ξ ζ : (U F n × U F n) → U F (n * n) → P → ℂ) (M : Refresh.«GL» F (n * n)) :
    ‖jointRowSynthesis ξ M * (jointColumnSynthesis ζ M)ᴴ‖ =
      opNorm (graphRestriction inputTensor inputTensor (jointFeatureTable ξ ζ) M) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  rw [jointRowSynthesis, jointColumnSynthesis, normalizedComplexFeatures_product_norm]
  rfl

/-- Graph norm estimate for arbitrary finite feature families with explicit budgets. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ, ζ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; H, G, D ∈ ℝ, assume 2 ≤ n; 0 ≤ H; 0 ≤ G; ∀ x, u, jointFeatureEnergy(ξ, x, u) ≤ H; ∀ x, u, jointFeatureEnergy(ζ, x, u) ≤ H; 𝔼ₓ [𝔼ᵤ [jointFeatureEnergy(ξ, x, u)]] ≤ G; 𝔼ₓ [𝔼ᵤ [jointFeatureEnergy(ζ, x, u)]] ≤ G; opNorm(jointFeatureTable(ξ, ζ)) ≤ D. Then

𝔼_M [opNorm(graphRestriction(inputTensor, inputTensor, jointFeatureTable(ξ, ζ), M))] ≤ D + 2 · √G · √(√(2 · jointVarianceCoefficient(F, n) · H · G)) + √(2 · jointVarianceCoefficient(F, n) · H · G).
-/
theorem joint_feature_graph_norm_mean (hn : 2 ≤ n)
    (ξ ζ : (U F n × U F n) → U F (n * n) → P → ℂ)
    (H G D : ℝ) (hH : 0 ≤ H) (hG : 0 ≤ G)
    (hξ : ∀ x u, jointFeatureEnergy ξ x u ≤ H)
    (hζ : ∀ x u, jointFeatureEnergy ζ x u ≤ H)
    (hξmean : uavg (fun x => uavg (fun u => jointFeatureEnergy ξ x u)) ≤ G)
    (hζmean : uavg (fun x => uavg (fun u => jointFeatureEnergy ζ x u)) ≤ G)
    (hD : opNorm (jointFeatureTable ξ ζ) ≤ D) :
    uavg (fun M => opNorm (graphRestriction inputTensor inputTensor (jointFeatureTable ξ ζ) M)) ≤
      D + 2 * Real.sqrt G * Real.sqrt (Real.sqrt (2 * jointVarianceCoefficient F n * H * G)) +
        Real.sqrt (2 * jointVarianceCoefficient F n * H * G) := by
  have h := joint_restricted_feature_norm_average_le_of_budgets hn ξ ζ H G D hH hG
    hξ hζ hξmean hζmean (by rwa [jointReferenceSynthesis_product_norm hn])
  simpa only [jointGraphSynthesis_product_norm hn] using h

variable {C : Type*} [DecidableEq C]

/-- The actual retained terms satisfy the graph bound, even though their features need not be orthogonal within a twist block. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ts ∈ TwistedTerm(((U(F, n) × U(F, n)) × U(F, (n · n))), C)*; c ∈ C; H, G, D ∈ ℝ, assume 2 ≤ n; ∀ t ∈ ts, 0 ≤ t.magnitude ∧ ‖ t.left‖ = 1 ∧ ‖ t.right‖ = 1; 0 ≤ H; 0 ≤ G; ∀ i, sum((((t ↦ (‖ t.leftFeature(i)‖)²))_*ts)) ≤ H; ∀ j, sum((((t ↦ (‖ t.rightFeature(j)‖)²))_*ts)) ≤ H; sum((TwistedTerm.magnitude_*ts)) / |((U(F, n) × U(F, n)) × U(F, (n · n)))| ≤ G; opNorm(extractedBlock(ts, c)) ≤ D. Then

𝔼_M [opNorm(graphRestriction(inputTensor, inputTensor, extractedBlock(ts, c), M))] ≤ D + 2 · √G · √(√(2 · jointVarianceCoefficient(F, n) · H · G)) + √(2 · jointVarianceCoefficient(F, n) · H · G).
-/
theorem joint_extractedBlock_graph_norm_mean (hn : 2 ≤ n)
    (ts : List (TwistedTerm ((U F n × U F n) × U F (n * n)) C))
    (ht : ∀ t ∈ ts, 0 ≤ t.magnitude ∧ ‖t.left‖ = 1 ∧ ‖t.right‖ = 1)
    (c : C) (H G D : ℝ) (hH : 0 ≤ H) (hG : 0 ≤ G)
    (hleft : ∀ i, (ts.map (fun t => ‖t.leftFeature i‖ ^ 2)).sum ≤ H)
    (hright : ∀ j, (ts.map (fun t => ‖t.rightFeature j‖ ^ 2)).sum ≤ H)
    (hmass : (ts.map TwistedTerm.magnitude).sum /
      Fintype.card ((U F n × U F n) × U F (n * n)) ≤ G)
    (hD : opNorm (extractedBlock ts c) ≤ D) :
    uavg (fun M => opNorm (graphRestriction inputTensor inputTensor (extractedBlock ts c) M)) ≤
      D + 2 * Real.sqrt G * Real.sqrt (Real.sqrt (2 * jointVarianceCoefficient F n * H * G)) +
        Real.sqrt (2 * jointVarianceCoefficient F n * H * G) := by
  let ξ := fun x u p => extractedLeftFeatures ts c (x, u) p
  let ζ := fun x u p => extractedRightFeatures ts c (x, u) p
  have htable : jointFeatureTable ξ ζ = extractedBlock ts c :=
    (extractedBlock_eq_features ts (fun t hm => (ht t hm).1) c).symm
  have hξ (x) (u) : jointFeatureEnergy ξ x u = ‖extractedLeftFeatures ts c (x, u)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]; rfl
  have hζ (x) (u) : jointFeatureEnergy ζ x u = ‖extractedRightFeatures ts c (x, u)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]; rfl
  have hmeans := extractedFeatures_uniform_energy_le ts ht c
  have h := joint_feature_graph_norm_mean hn ξ ζ H G D hH hG
    (fun x u => (hξ x u).trans_le ((extractedLeftFeatures_norm_sq_le ts c (x, u)).trans (hleft _)))
    (fun x u => (hζ x u).trans_le ((extractedRightFeatures_norm_sq_le ts c (x, u)).trans (hright _)))
    (by simpa only [hξ, uavg_prod] using hmeans.1.trans hmass)
    (by simpa only [hζ, uavg_prod] using hmeans.2.trans hmass)
    (by rwa [htable])
  simpa only [htable] using h

/-- Positive-excess version needed for matrix-dependent rectangle weights. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ts ∈ TwistedTerm(((U(F, n) × U(F, n)) × U(F, (n · n))), C)*; c ∈ C; H, G, D ∈ ℝ, assume 2 ≤ n; ∀ t ∈ ts, 0 ≤ t.magnitude ∧ ‖ t.left‖ = 1 ∧ ‖ t.right‖ = 1; 0 ≤ H; ∀ i, sum((((t ↦ (‖ t.leftFeature(i)‖)²))_*ts)) ≤ H; ∀ j, sum((((t ↦ (‖ t.rightFeature(j)‖)²))_*ts)) ≤ H; sum((TwistedTerm.magnitude_*ts)) / |((U(F, n) × U(F, n)) × U(F, (n · n)))| ≤ G; opNorm(extractedBlock(ts, c)) ≤ D. Then

𝔼_M [max{(opNorm(graphRestriction(inputTensor, inputTensor, extractedBlock(ts, c), M)) - D), 0}] ≤ 2 · √G · √(√(2 · jointVarianceCoefficient(F, n) · H · G)) + √(2 · jointVarianceCoefficient(F, n) · H · G).
-/
theorem joint_extractedBlock_graph_excess_mean (hn : 2 ≤ n)
    (ts : List (TwistedTerm ((U F n × U F n) × U F (n * n)) C))
    (ht : ∀ t ∈ ts, 0 ≤ t.magnitude ∧ ‖t.left‖ = 1 ∧ ‖t.right‖ = 1)
    (c : C) (H G D : ℝ) (hH : 0 ≤ H)
    (hleft : ∀ i, (ts.map (fun t => ‖t.leftFeature i‖ ^ 2)).sum ≤ H)
    (hright : ∀ j, (ts.map (fun t => ‖t.rightFeature j‖ ^ 2)).sum ≤ H)
    (hmass : (ts.map TwistedTerm.magnitude).sum /
      Fintype.card ((U F n × U F n) × U F (n * n)) ≤ G)
    (hD : opNorm (extractedBlock ts c) ≤ D) :
    uavg (fun M => max (opNorm (graphRestriction inputTensor inputTensor (extractedBlock ts c) M) - D) 0) ≤
      2 * Real.sqrt G * Real.sqrt (Real.sqrt (2 * jointVarianceCoefficient F n * H * G)) +
        Real.sqrt (2 * jointVarianceCoefficient F n * H * G) := by
  let ξ := fun x u p => extractedLeftFeatures ts c (x, u) p
  let ζ := fun x u p => extractedRightFeatures ts c (x, u) p
  have htable : jointFeatureTable ξ ζ = extractedBlock ts c :=
    (extractedBlock_eq_features ts (fun t hm => (ht t hm).1) c).symm
  have hξ (x) (u) : jointFeatureEnergy ξ x u = ‖extractedLeftFeatures ts c (x, u)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]; rfl
  have hζ (x) (u) : jointFeatureEnergy ζ x u = ‖extractedRightFeatures ts c (x, u)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]; rfl
  have hmeans := extractedFeatures_uniform_energy_le ts ht c
  have h := joint_restricted_feature_excess_average_le hn ξ ζ H G D hH
    (fun x u => (hξ x u).trans_le ((extractedLeftFeatures_norm_sq_le ts c (x, u)).trans (hleft _)))
    (fun x u => (hζ x u).trans_le ((extractedRightFeatures_norm_sq_le ts c (x, u)).trans (hright _)))
    (by simpa only [hξ, uavg_prod] using hmeans.1.trans hmass)
    (by simpa only [hζ, uavg_prod] using hmeans.2.trans hmass)
    (by rwa [jointReferenceSynthesis_product_norm hn, htable])
  simpa only [jointGraphSynthesis_product_norm hn, htable] using h

end

end CircuitCompiler
