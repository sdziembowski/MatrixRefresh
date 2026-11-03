import Proofs.Compiler.GateApproximation.MatrixPhase.JointAverages
import Proofs.Compiler.GateApproximation.MatrixPhase.JointFourCycle
import Proofs.Compiler.GateApproximation.MatrixPhase.JointGram
import Proofs.Compiler.GateApproximation.MatrixPhase.JointGramPerturbation



/-!
# Uniformly normalized synthesis and actual restricted-table bounds

The synthesis normalization connects the abstract Gram perturbation theorem to the actual product reference distribution and the shared-matrix joint-port graph.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {X Y P : Type*} [Fintype X] [Fintype Y] [Fintype P]
  [DecidableEq X] [DecidableEq Y] [DecidableEq P]

/-- Rectangular complex operator norm squared is bounded by its entry energy. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(X × P), we have

(‖ A‖)² ≤ ∑ₓ (∑ₚ ((‖ A(x, p)‖)²)).
-/
theorem complex_rectangular_norm_sq_le (A : Matrix X P ℂ) :
    ‖A‖ ^ 2 ≤ ∑ x, ∑ p, ‖A x p‖ ^ 2 := by
  let H : ℝ := ∑ x, ∑ p, ‖A x p‖ ^ 2
  have hH : 0 ≤ H := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hop : ‖A‖ ≤ Real.sqrt H := by
    rw [Matrix.l2_opNorm_def]
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
    change ‖A.toEuclideanLin x‖ ^ 2 ≤ (Real.sqrt H * ‖x‖) ^ 2
    rw [PiLp.norm_sq_eq_of_L2, mul_pow, Real.sq_sqrt hH]
    change (∑ i, ‖∑ p, A i p * x p‖ ^ 2) ≤ _
    have hrow (i : X) : ‖∑ p, A i p * x p‖ ^ 2 ≤ (∑ p, ‖A i p‖ ^ 2) * ‖x‖ ^ 2 := by
      let r : EuclideanSpace ℂ P := WithLp.toLp 2 (fun p => star (A i p))
      have h := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) r x) 2
      simpa [r, PiLp.inner_apply, RCLike.inner_apply, PiLp.norm_sq_eq_of_L2,
        mul_pow, mul_comm] using h
    calc
      _ ≤ ∑ i, (∑ p, ‖A i p‖ ^ 2) * ‖x‖ ^ 2 := Finset.sum_le_sum (fun i _ => hrow i)
      _ = H * ‖x‖ ^ 2 := by rw [← Finset.sum_mul]
  exact (pow_le_pow_left₀ (norm_nonneg _) hop 2).trans_eq (Real.sq_sqrt hH)

/-- Synthesis matrix for uniformly weighted feature rows. -/
/-
Mathematical definition (normal notation): For Φ ∈ ℂ^(X × P), define

normalizedComplexFeatures(Φ) := (√(|X|))⁻¹ · Φ.
-/
def normalizedComplexFeatures (Φ : Matrix X P ℂ) : Matrix X P ℂ :=
  (Real.sqrt (Fintype.card X : ℝ))⁻¹ • Φ

/-- Its Gram is exactly the uniform feature Gram. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ ∈ ℂ^(X × P), assume X ≠ ∅. Then

normalizedComplexFeatures(Φ, ᴴ) · normalizedComplexFeatures(Φ) = (p, q ↦ complexAverage(((x ↦ star(Φ(x, p)) · Φ(x, q))))).
-/
theorem normalizedComplexFeatures_gram [Nonempty X] (Φ : Matrix X P ℂ) :
    (normalizedComplexFeatures Φ)ᴴ * normalizedComplexFeatures Φ =
      fun p q => complexAverage (fun x => star (Φ x p) * Φ x q) := by
  have hd : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : (Real.sqrt (Fintype.card X : ℝ))⁻¹ ^ 2 = (Fintype.card X : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hd.le]
  ext p q
  simp only [normalizedComplexFeatures, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.smul_apply, star_smul, star_trivial, complexAverage, smul_eq_mul,
    Complex.real_smul, Complex.ofReal_inv, Finset.mul_sum]
  have hs' : ((Real.sqrt (Fintype.card X : ℝ) : ℂ)⁻¹) ^ 2 =
      ((Fintype.card X : ℝ)⁻¹ : ℂ) := by exact_mod_cast hs
  apply Finset.sum_congr rfl
  intro x _
  rw [← hs']
  simp only [star_mul, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  ring

/-- The mean total feature energy controls synthesis norm without a rank factor. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ ∈ ℂ^(X × P), assume X ≠ ∅. Then

(‖ normalizedComplexFeatures(Φ)‖)² ≤ 𝔼ₓ [∑ₚ ((‖ Φ(x, p)‖)²)].
-/
theorem normalizedComplexFeatures_norm_sq_le [Nonempty X] (Φ : Matrix X P ℂ) :
    ‖normalizedComplexFeatures Φ‖ ^ 2 ≤ uavg (fun x => ∑ p, ‖Φ x p‖ ^ 2) := by
  have hd : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : (Real.sqrt (Fintype.card X : ℝ))⁻¹ ^ 2 = (Fintype.card X : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hd.le]
  have h := complex_rectangular_norm_sq_le (normalizedComplexFeatures Φ)
  simpa only [normalizedComplexFeatures, Matrix.smul_apply, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, hs, uavg, Finset.mul_sum] using h

/-- A complex feature table in the singular-product convention. -/
/-
Mathematical definition (normal notation): For Φ, Ψ ∈ ℂ^(X × P), define

uniformFeatureTable(Φ, Ψ) := Φ · Ψᴴ.
-/
def uniformFeatureTable (Φ Ψ : Matrix X P ℂ) : Matrix X X ℂ := Φ * Ψᴴ

/-- Products of normalized synthesis matrices represent the uniformly weighted table operator. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ, Ψ ∈ ℂ^(X × P), assume X ≠ ∅. Then

normalizedComplexFeatures(Φ) · normalizedComplexFeatures(Ψ, ᴴ) = (|X|)⁻¹ · uniformFeatureTable(Φ, Ψ).
-/
theorem normalizedComplexFeatures_product [Nonempty X] (Φ Ψ : Matrix X P ℂ) :
    normalizedComplexFeatures Φ * (normalizedComplexFeatures Ψ)ᴴ =
      (Fintype.card X : ℝ)⁻¹ • uniformFeatureTable Φ Ψ := by
  have hd : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : (Real.sqrt (Fintype.card X : ℝ))⁻¹ ^ 2 = (Fintype.card X : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hd.le]
  simp only [normalizedComplexFeatures, Matrix.conjTranspose_smul, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_two, hs, uniformFeatureTable]

/-- The corresponding operator norm has precisely the uniform `1/card` scaling. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ, Ψ ∈ ℂ^(X × P), assume X ≠ ∅. Then

‖ normalizedComplexFeatures(Φ) · normalizedComplexFeatures(Ψ, ᴴ)‖ = ‖ uniformFeatureTable(Φ, Ψ)‖ / |X|.
-/
theorem normalizedComplexFeatures_product_norm [Nonempty X] (Φ Ψ : Matrix X P ℂ) :
    ‖normalizedComplexFeatures Φ * (normalizedComplexFeatures Ψ)ᴴ‖ =
      ‖uniformFeatureTable Φ Ψ‖ / Fintype.card X := by
  rw [normalizedComplexFeatures_product, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  ring

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ X × Y → ℂ, we have

complexAverage(f) = complexAverage(((x ↦ complexAverage(((y ↦ f((x, y)))))))).
-/
lemma complexAverage_prod (f : X × Y → ℂ) :
    complexAverage f = complexAverage (fun x => complexAverage (fun y => f (x, y))) := by
  apply Complex.ext
  · simp only [complexAverage_re]
    exact uavg_prod _
  · simp only [complexAverage_im]
    exact uavg_prod _

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- Mean synthesis matrix, with both old shares and the new share free. -/
/-
Mathematical definition (normal notation): For ξ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ, define

jointReferenceSynthesis(ξ) := normalizedComplexFeatures(((x, p ↦ ξ((x)₁, (x)₂, p)))).
-/
def jointReferenceSynthesis (ξ : (U F n × U F n) → U F (n * n) → P → ℂ) :
    Matrix ((U F n × U F n) × U F (n * n)) P ℂ :=
  normalizedComplexFeatures (fun x p => ξ x.1 x.2 p)

/-- Left synthesis matrix on the actual shared-matrix graph. -/
/-
Mathematical definition (normal notation): For ξ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; M ∈ GL_(n · n)(F), define

jointRowSynthesis(ξ, M) := normalizedComplexFeatures(((x, p ↦ ξ(x, rowRefresh(inputTensor(x), M), p)))).
-/
def jointRowSynthesis (ξ : (U F n × U F n) → U F (n * n) → P → ℂ)
    (M : Refresh.«GL» F (n * n)) : Matrix (U F n × U F n) P ℂ :=
  normalizedComplexFeatures (fun x p => ξ x (rowRefresh (inputTensor x) M) p)

/-- Right synthesis matrix on the same graph, using the inverse matrix. -/
/-
Mathematical definition (normal notation): For ξ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; M ∈ GL_(n · n)(F), define

jointColumnSynthesis(ξ, M) := normalizedComplexFeatures(((x, p ↦ ξ(x, columnRefresh(inputTensor(x), M), p)))).
-/
def jointColumnSynthesis (ξ : (U F n × U F n) → U F (n * n) → P → ℂ)
    (M : Refresh.«GL» F (n * n)) : Matrix (U F n × U F n) P ℂ :=
  normalizedComplexFeatures (fun x p => ξ x (columnRefresh (inputTensor x) M) p)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ, assume 2 ≤ n. Then

jointReferenceSynthesis(ξ, ᴴ) · jointReferenceSynthesis(ξ) = jointMeanGram(ξ).
-/
lemma jointReferenceSynthesis_gram (hn : 2 ≤ n)
    (ξ : (U F n × U F n) → U F (n * n) → P → ℂ) :
    (jointReferenceSynthesis ξ)ᴴ * jointReferenceSynthesis ξ = jointMeanGram ξ := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  letI : Nonempty (U F (n * n)) := ⟨unitShare ⟨0, by nlinarith⟩⟩
  rw [jointReferenceSynthesis, normalizedComplexFeatures_gram]
  ext p q
  exact complexAverage_prod _

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; M ∈ GL_(n · n)(F), assume 2 ≤ n. Then

jointRowSynthesis(ξ, M, ᴴ) · jointRowSynthesis(ξ, M) = jointRowGram(ξ, M) .
-/
lemma jointRowSynthesis_gram (hn : 2 ≤ n)
    (ξ : (U F n × U F n) → U F (n * n) → P → ℂ) (M : Refresh.«GL» F (n * n)) :
    (jointRowSynthesis ξ M)ᴴ * jointRowSynthesis ξ M = jointRowGram ξ M := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  exact normalizedComplexFeatures_gram _

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; M ∈ GL_(n · n)(F), assume 2 ≤ n. Then

jointColumnSynthesis(ξ, M, ᴴ) · jointColumnSynthesis(ξ, M) = jointColumnGram(ξ, M).
-/
lemma jointColumnSynthesis_gram (hn : 2 ≤ n)
    (ξ : (U F n × U F n) → U F (n * n) → P → ℂ) (M : Refresh.«GL» F (n * n)) :
    (jointColumnSynthesis ξ M)ᴴ * jointColumnSynthesis ξ M = jointColumnGram ξ M := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  exact normalizedComplexFeatures_gram _

/-- Counting L2 deviation of the row Gram matrix bounds its operator-norm deviation. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; M ∈ GL_(n · n)(F), we have

‖ jointRowGram(ξ, M) - jointMeanGram(ξ)‖ ≤ √(jointRowGramDeviationSq(ξ, M)).
-/
lemma jointRowGram_norm_sub_le (ξ : (U F n × U F n) → U F (n * n) → P → ℂ)
    (M : Refresh.«GL» F (n * n)) :
    ‖jointRowGram ξ M - jointMeanGram ξ‖ ≤ Real.sqrt (jointRowGramDeviationSq ξ M) := by
  have h := complexMatrix_norm_sq_le_L2Sq (jointRowGram ξ M - jointMeanGram ξ)
  have he : complexMatrixL2Sq (jointRowGram ξ M - jointMeanGram ξ) =
      jointRowGramDeviationSq ξ M := by
    unfold complexMatrixL2Sq jointRowGramDeviationSq
    simp only [Matrix.sub_apply]
    rw [Finset.sum_comm]
  rw [he] at h
  simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt h

/-- Total mean feature energy bounds the mean synthesis norm. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ, assume 2 ≤ n. Then

‖ jointReferenceSynthesis(ξ)‖ ≤ √(𝔼ₓ [𝔼ᵤ [jointFeatureEnergy(ξ, x, u)]]).
-/
lemma jointReferenceSynthesis_norm_le (hn : 2 ≤ n)
    (ξ : (U F n × U F n) → U F (n * n) → P → ℂ) :
    ‖jointReferenceSynthesis ξ‖ ≤
      Real.sqrt (uavg (fun x => uavg (fun u => jointFeatureEnergy ξ x u))) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  letI : Nonempty (U F (n * n)) := ⟨unitShare ⟨0, by nlinarith⟩⟩
  have h := normalizedComplexFeatures_norm_sq_le (fun (x : (U F n × U F n) × U F (n * n)) p =>
    ξ x.1 x.2 p)
  rw [uavg_prod] at h
  change ‖jointReferenceSynthesis ξ‖ ^ 2 ≤ _ at h
  simpa only [Real.sqrt_sq (norm_nonneg _), jointFeatureEnergy] using Real.sqrt_le_sqrt h

/-- Direct application of the nonorthogonal perturbation theorem to the actual left/right shared-matrix restrictions. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ, ζ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; M ∈ GL_(n · n)(F); u, v ∈ ℝ, assume 2 ≤ n; 0 ≤ u; 0 ≤ v; ‖ jointRowGram(ξ, M) - jointMeanGram(ξ)‖ ≤ u; ‖ jointColumnGram(ζ, M) - jointMeanGram(ζ)‖ ≤ v. Then

‖ jointRowSynthesis(ξ, M) · jointColumnSynthesis(ζ, M, ᴴ)‖ ≤ ‖ jointReferenceSynthesis(ξ) · jointReferenceSynthesis(ζ, ᴴ)‖ + √v · ‖ jointReferenceSynthesis(ξ)‖ + √u · ‖ jointReferenceSynthesis(ζ)‖ + √u · √v.
-/
theorem joint_restricted_feature_norm_le (hn : 2 ≤ n)
    (ξ ζ : (U F n × U F n) → U F (n * n) → P → ℂ)
    (M : Refresh.«GL» F (n * n)) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hξ : ‖jointRowGram ξ M - jointMeanGram ξ‖ ≤ u)
    (hζ : ‖jointColumnGram ζ M - jointMeanGram ζ‖ ≤ v) :
    ‖jointRowSynthesis ξ M * (jointColumnSynthesis ζ M)ᴴ‖ ≤
      ‖jointReferenceSynthesis ξ * (jointReferenceSynthesis ζ)ᴴ‖ +
      Real.sqrt v * ‖jointReferenceSynthesis ξ‖ +
      Real.sqrt u * ‖jointReferenceSynthesis ζ‖ + Real.sqrt u * Real.sqrt v := by
  apply complex_gram_product_perturbation _ _ _ _ u v hu hv
  · simpa only [jointRowSynthesis_gram hn, jointReferenceSynthesis_gram hn] using hξ
  · simpa only [jointColumnSynthesis_gram hn, jointReferenceSynthesis_gram hn] using hζ

/-- The actual expected restricted feature-table norm, with its Gram variance inserted and the two fourth-root costs averaged by finite Cauchy--Schwarz. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ, ζ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; L ∈ ℝ, assume 2 ≤ n; ∀ x, u, jointFeatureEnergy(ξ, x, u) ≤ L; ∀ x, u, jointFeatureEnergy(ζ, x, u) ≤ L. Then

Let V := jointVarianceCoefficient(F, n) · L · (𝔼ₓ [𝔼ᵤ [jointFeatureEnergy(ξ, x, u)]] + 𝔼ₓ [𝔼ᵤ [jointFeatureEnergy(ζ, x, u)]]); 𝔼_M [‖ jointRowSynthesis(ξ, M) · jointColumnSynthesis(ζ, M, ᴴ)‖] ≤ ‖ jointReferenceSynthesis(ξ) · jointReferenceSynthesis(ζ, ᴴ)‖ + (‖ jointReferenceSynthesis(ξ)‖ + ‖ jointReferenceSynthesis(ζ)‖) · √(√V) + √V.
-/
theorem joint_restricted_feature_norm_average_le (hn : 2 ≤ n)
    (ξ ζ : (U F n × U F n) → U F (n * n) → P → ℂ)
    (L : ℝ) (hξ : ∀ x u, jointFeatureEnergy ξ x u ≤ L)
    (hζ : ∀ x u, jointFeatureEnergy ζ x u ≤ L) :
    let V := jointVarianceCoefficient F n * L *
      (uavg (fun x => uavg (fun u => jointFeatureEnergy ξ x u)) +
       uavg (fun x => uavg (fun u => jointFeatureEnergy ζ x u)))
    uavg (fun M => ‖jointRowSynthesis ξ M * (jointColumnSynthesis ζ M)ᴴ‖) ≤
      ‖jointReferenceSynthesis ξ * (jointReferenceSynthesis ζ)ᴴ‖ +
      (‖jointReferenceSynthesis ξ‖ + ‖jointReferenceSynthesis ζ‖) *
        Real.sqrt (Real.sqrt V) + Real.sqrt V := by
  intro V
  let f := fun M : Refresh.«GL» F (n * n) => Real.sqrt (jointRowGramDeviationSq ξ M)
  let h := fun M : Refresh.«GL» F (n * n) => Real.sqrt (jointRowGramDeviationSq ζ (inverseTransposeEquiv M))
  have hξn (M : Refresh.«GL» F (n * n)) : 0 ≤ jointRowGramDeviationSq ξ M :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hζn (M : Refresh.«GL» F (n * n)) : 0 ≤ jointRowGramDeviationSq ζ M :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have htotal := joint_Gram_variance_le_energy hn ξ ζ L hξ hζ
  simp_rw [jointColumnGram_eq_row] at htotal
  change uavg (jointRowGramDeviationSq ξ) +
    uavg (fun M => jointRowGramDeviationSq ζ (inverseTransposeEquiv M)) ≤ V at htotal
  have hVf : uavg (fun M => f M ^ 2) ≤ V := by
    simp only [f, Real.sq_sqrt (hξn _)]
    have hn := uavg_nonneg (fun M => hζn (inverseTransposeEquiv M))
    linarith
  have hVh : uavg (fun M => h M ^ 2) ≤ V := by
    simp only [h, Real.sq_sqrt (hζn _)]
    have hn := uavg_nonneg hξn
    linarith
  apply joint_average_perturbation_bound _ f h _ _ _ V (norm_nonneg _) (norm_nonneg _)
    (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _) hVf hVh
  intro M
  have hleft := jointRowGram_norm_sub_le ξ M
  have hright : ‖jointColumnGram ζ M - jointMeanGram ζ‖ ≤ h M := by
    simpa only [h, jointColumnGram_eq_row] using jointRowGram_norm_sub_le ζ (inverseTransposeEquiv M)
  have hp := joint_restricted_feature_norm_le hn ξ ζ M (f M) (h M)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hleft hright
  convert hp using 1 <;> ring

/-- A convenient budget form separates pointwise feature energy, mean trace, and the norm of the unrestrained table. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ, ζ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; H, G, D ∈ ℝ, assume 2 ≤ n; 0 ≤ H; 0 ≤ G; ∀ x, u, jointFeatureEnergy(ξ, x, u) ≤ H; ∀ x, u, jointFeatureEnergy(ζ, x, u) ≤ H; 𝔼ₓ [𝔼ᵤ [jointFeatureEnergy(ξ, x, u)]] ≤ G; 𝔼ₓ [𝔼ᵤ [jointFeatureEnergy(ζ, x, u)]] ≤ G; ‖ jointReferenceSynthesis(ξ) · jointReferenceSynthesis(ζ, ᴴ)‖ ≤ D. Then

𝔼_M [‖ jointRowSynthesis(ξ, M) · jointColumnSynthesis(ζ, M, ᴴ)‖] ≤ D + 2 · √G · √(√(2 · jointVarianceCoefficient(F, n) · H · G)) + √(2 · jointVarianceCoefficient(F, n) · H · G).
-/
theorem joint_restricted_feature_norm_average_le_of_budgets (hn : 2 ≤ n)
    (ξ ζ : (U F n × U F n) → U F (n * n) → P → ℂ)
    (H G D : ℝ) (hH : 0 ≤ H) (hG : 0 ≤ G)
    (hξ : ∀ x u, jointFeatureEnergy ξ x u ≤ H)
    (hζ : ∀ x u, jointFeatureEnergy ζ x u ≤ H)
    (hξmean : uavg (fun x => uavg (fun u => jointFeatureEnergy ξ x u)) ≤ G)
    (hζmean : uavg (fun x => uavg (fun u => jointFeatureEnergy ζ x u)) ≤ G)
    (hD : ‖jointReferenceSynthesis ξ * (jointReferenceSynthesis ζ)ᴴ‖ ≤ D) :
    uavg (fun M => ‖jointRowSynthesis ξ M * (jointColumnSynthesis ζ M)ᴴ‖) ≤
      D + 2 * Real.sqrt G * Real.sqrt (Real.sqrt (2 * jointVarianceCoefficient F n * H * G)) +
        Real.sqrt (2 * jointVarianceCoefficient F n * H * G) := by
  have h := joint_restricted_feature_norm_average_le hn ξ ζ H hξ hζ
  dsimp only at h
  have hV : jointVarianceCoefficient F n * H *
      (uavg (fun x => uavg (fun u => jointFeatureEnergy ξ x u)) +
       uavg (fun x => uavg (fun u => jointFeatureEnergy ζ x u))) ≤
      2 * jointVarianceCoefficient F n * H * G := by
    have he : uavg (fun x => uavg (fun u => jointFeatureEnergy ξ x u)) +
        uavg (fun x => uavg (fun u => jointFeatureEnergy ζ x u)) ≤ 2 * G := by linarith
    have hm := mul_le_mul_of_nonneg_left he
      (mul_nonneg (jointVarianceCoefficient_nonneg (F := F) hn) hH)
    nlinarith
  have hξnorm := (jointReferenceSynthesis_norm_le hn ξ).trans (Real.sqrt_le_sqrt hξmean)
  have hζnorm := (jointReferenceSynthesis_norm_le hn ζ).trans (Real.sqrt_le_sqrt hζmean)
  apply h.trans
  apply add_le_add
  · apply add_le_add hD
    exact mul_le_mul (by linarith : ‖jointReferenceSynthesis ξ‖ + ‖jointReferenceSynthesis ζ‖ ≤
        2 * Real.sqrt G) (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hV))
      (Real.sqrt_nonneg _) (by positivity)
  · exact Real.sqrt_le_sqrt hV

/-- The averaged positive excess retains a pointwise leading term. This is what permits the rectangle weights to sum to `sqrt(K)` in the dual bound. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ, ζ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; H, G, D ∈ ℝ, assume 2 ≤ n; 0 ≤ H; ∀ x, u, jointFeatureEnergy(ξ, x, u) ≤ H; ∀ x, u, jointFeatureEnergy(ζ, x, u) ≤ H; 𝔼ₓ [𝔼ᵤ [jointFeatureEnergy(ξ, x, u)]] ≤ G; 𝔼ₓ [𝔼ᵤ [jointFeatureEnergy(ζ, x, u)]] ≤ G; ‖ jointReferenceSynthesis(ξ) · jointReferenceSynthesis(ζ, ᴴ)‖ ≤ D. Then

𝔼_M [max{(‖ jointRowSynthesis(ξ, M) · jointColumnSynthesis(ζ, M, ᴴ)‖ - D), 0}] ≤ 2 · √G · √(√(2 · jointVarianceCoefficient(F, n) · H · G)) + √(2 · jointVarianceCoefficient(F, n) · H · G).
-/
theorem joint_restricted_feature_excess_average_le (hn : 2 ≤ n)
    (ξ ζ : (U F n × U F n) → U F (n * n) → P → ℂ)
    (H G D : ℝ) (hH : 0 ≤ H)
    (hξ : ∀ x u, jointFeatureEnergy ξ x u ≤ H)
    (hζ : ∀ x u, jointFeatureEnergy ζ x u ≤ H)
    (hξmean : uavg (fun x => uavg (fun u => jointFeatureEnergy ξ x u)) ≤ G)
    (hζmean : uavg (fun x => uavg (fun u => jointFeatureEnergy ζ x u)) ≤ G)
    (hD : ‖jointReferenceSynthesis ξ * (jointReferenceSynthesis ζ)ᴴ‖ ≤ D) :
    uavg (fun M => max (‖jointRowSynthesis ξ M * (jointColumnSynthesis ζ M)ᴴ‖ - D) 0) ≤
      2 * Real.sqrt G * Real.sqrt (Real.sqrt (2 * jointVarianceCoefficient F n * H * G)) +
        Real.sqrt (2 * jointVarianceCoefficient F n * H * G) := by
  let V := 2 * jointVarianceCoefficient F n * H * G
  let f := fun M : Refresh.«GL» F (n * n) => Real.sqrt (jointRowGramDeviationSq ξ M)
  let g := fun M : Refresh.«GL» F (n * n) =>
    Real.sqrt (jointRowGramDeviationSq ζ (inverseTransposeEquiv M))
  have hξn (M : Refresh.«GL» F (n * n)) : 0 ≤ jointRowGramDeviationSq ξ M :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hζn (M : Refresh.«GL» F (n * n)) : 0 ≤ jointRowGramDeviationSq ζ M :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have htotal := joint_Gram_variance_le_energy hn ξ ζ H hξ hζ
  simp_rw [jointColumnGram_eq_row] at htotal
  have hbudget : jointVarianceCoefficient F n * H *
      (uavg (fun x => uavg (fun u => jointFeatureEnergy ξ x u)) +
       uavg (fun x => uavg (fun u => jointFeatureEnergy ζ x u))) ≤ V := by
    have hsum : uavg (fun x => uavg (fun u => jointFeatureEnergy ξ x u)) +
        uavg (fun x => uavg (fun u => jointFeatureEnergy ζ x u)) ≤ 2 * G := by linarith
    have hm := mul_le_mul_of_nonneg_left hsum
      (mul_nonneg (jointVarianceCoefficient_nonneg (F := F) hn) hH)
    dsimp [V]
    nlinarith
  have htotal' := htotal.trans hbudget
  change uavg (jointRowGramDeviationSq ξ) +
    uavg (fun M => jointRowGramDeviationSq ζ (inverseTransposeEquiv M)) ≤ V at htotal'
  have hVf : uavg (fun M => f M ^ 2) ≤ V := by
    simp only [f, Real.sq_sqrt (hξn _)]
    have hn := uavg_nonneg (fun M => hζn (inverseTransposeEquiv M))
    linarith
  have hVg : uavg (fun M => g M ^ 2) ≤ V := by
    simp only [g, Real.sq_sqrt (hζn _)]
    have hn := uavg_nonneg hξn
    linarith
  have hξnorm := (jointReferenceSynthesis_norm_le hn ξ).trans (Real.sqrt_le_sqrt hξmean)
  have hζnorm := (jointReferenceSynthesis_norm_le hn ζ).trans (Real.sqrt_le_sqrt hζmean)
  have hav := joint_average_perturbation_bound
    (fun M => max (‖jointRowSynthesis ξ M * (jointColumnSynthesis ζ M)ᴴ‖ - D) 0)
    f g 0 (Real.sqrt G) (Real.sqrt G) V (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _) hVf hVg (by
      intro M
      have hright : ‖jointColumnGram ζ M - jointMeanGram ζ‖ ≤ g M := by
        simpa only [g, jointColumnGram_eq_row] using
          jointRowGram_norm_sub_le ζ (inverseTransposeEquiv M)
      have hp := joint_restricted_feature_norm_le hn ξ ζ M (f M) (g M)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (jointRowGram_norm_sub_le ξ M) hright
      apply max_le
      · have hleft' := mul_le_mul_of_nonneg_left hξnorm (Real.sqrt_nonneg (g M))
        have hright' := mul_le_mul_of_nonneg_left hζnorm (Real.sqrt_nonneg (f M))
        nlinarith
      · positivity)
  simpa only [zero_add, ← two_mul] using hav

end

end CircuitCompiler
