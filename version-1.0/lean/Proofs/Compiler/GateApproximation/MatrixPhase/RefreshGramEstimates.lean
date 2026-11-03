import Proofs.Compiler.GateApproximation.MatrixPhase.ResidualGeometry
import Proofs.Compiler.GateApproximation.MatrixPhase.SVDGram
import Proofs.Compiler.GateApproximation.MatrixPhase.RefreshGramVariance



/-!
# Large singular-value part under an injective-feature refresh

Both feature maps may be arbitrary binary injections and need not agree. The resulting estimate therefore includes the augmented NAND tensor.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis GateTruncation

noncomputable section

variable {F X P : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype X] [DecidableEq X] [Nonempty X] [Fintype P] [DecidableEq P] {m : ℕ}

/-
Mathematical definition (normal notation): For ξ, ζ ∈ X → U(F, m) → P → ℂ, define

featureFactorTable(ξ, ζ) := (x, y ↦ ∑ₚ (ξ((x)₁, (x)₂, p) · star(ζ((y)₁, (y)₂, p)))).
-/
def featureFactorTable (ξ ζ : X → U F m → P → ℂ) :
    Matrix (X × U F m) (X × U F m) ℂ :=
  fun x y => ∑ p, ξ x.1 x.2 p * star (ζ y.1 y.2 p)

/-
Mathematical definition (normal notation): For a ∈ X → U(F, m); ξ ∈ X → U(F, m) → P → ℂ; M ∈ GLₘ(F), define

featureRowSynthesis(a, ξ, M) := normalizedComplexFeatures(((x, p ↦ ξ(x, rowRefresh(a(x), M), p)))).
-/
def featureRowSynthesis (a : X → U F m) (ξ : X → U F m → P → ℂ)
    (M : Refresh.«GL» F m) : Matrix X P ℂ :=
  normalizedComplexFeatures (fun x p => ξ x (rowRefresh (a x) M) p)

/-
Mathematical definition (normal notation): For a ∈ X → U(F, m); ξ ∈ X → U(F, m) → P → ℂ; M ∈ GLₘ(F), define

featureColumnSynthesis(a, ξ, M) := normalizedComplexFeatures(((x, p ↦ ξ(x, columnRefresh(a(x), M), p)))).
-/
def featureColumnSynthesis (a : X → U F m) (ξ : X → U F m → P → ℂ)
    (M : Refresh.«GL» F m) : Matrix X P ℂ :=
  normalizedComplexFeatures (fun x p => ξ x (columnRefresh (a x) M) p)

omit [Fintype F] [DecidableEq F] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m); ξ ∈ X → U(F, m) → P → ℂ; M ∈ GLₘ(F), we have

featureRowSynthesis(a, ξ, M, ᴴ) · featureRowSynthesis(a, ξ, M) = featureRowGram(a, ξ, M).
-/
lemma featureRowSynthesis_gram (a : X → U F m) (ξ : X → U F m → P → ℂ)
    (M : Refresh.«GL» F m) :
    (featureRowSynthesis a ξ M)ᴴ * featureRowSynthesis a ξ M = featureRowGram a ξ M :=
  normalizedComplexFeatures_gram _

omit [Fintype F] [DecidableEq F] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m); ξ ∈ X → U(F, m) → P → ℂ; M ∈ GLₘ(F), we have

featureColumnSynthesis(a, ξ, M, ᴴ) · featureColumnSynthesis(a, ξ, M) = featureColumnGram(a, ξ, M).
-/
lemma featureColumnSynthesis_gram (a : X → U F m) (ξ : X → U F m → P → ℂ)
    (M : Refresh.«GL» F m) :
    (featureColumnSynthesis a ξ M)ᴴ * featureColumnSynthesis a ξ M = featureColumnGram a ξ M :=
  normalizedComplexFeatures_gram _

omit [Fintype F] [DecidableEq F] in
/-- The restricted synthesis product is the actual normalized refresh table. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); ξ, ζ ∈ X → U(F, m) → P → ℂ; M ∈ GLₘ(F), we have

‖ featureRowSynthesis(a, ξ, M) · featureColumnSynthesis(b, ζ, M, ᴴ)‖ = opNorm(graphRestriction(a, b, featureFactorTable(ξ, ζ), M)).
-/
theorem feature_synthesis_product_norm (a b : X → U F m)
    (ξ ζ : X → U F m → P → ℂ) (M : Refresh.«GL» F m) :
    ‖featureRowSynthesis a ξ M * (featureColumnSynthesis b ζ M)ᴴ‖ =
      opNorm (graphRestriction a b (featureFactorTable ξ ζ) M) := by
  rw [featureRowSynthesis, featureColumnSynthesis, normalizedComplexFeatures_product_norm]
  rfl

/-- A common reference-Gram bound makes the restricted cost additive in the deviations. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); ξ, ζ ∈ X → U(F, m) → P → ℂ; θ ∈ ℝ; M ∈ GLₘ(F), assume ‖ featureMeanGram(ξ)‖ ≤ θ; ‖ featureMeanGram(ζ)‖ ≤ θ. Then

opNorm(graphRestriction(a, b, featureFactorTable(ξ, ζ), M)) ≤ θ + (√(featureRowGramDeviationSq(a, ξ, M)) + √(∑ₚ (∑_q ((‖ featureColumnGram(b, ζ, M, p, q) - featureMeanGram(ζ, p, q)‖)²)))) / 2.
-/
theorem feature_large_part_pointwise (a b : X → U F m)
    (ξ ζ : X → U F m → P → ℂ) (θ : ℝ)
    (hξ : ‖featureMeanGram ξ‖ ≤ θ) (hζ : ‖featureMeanGram ζ‖ ≤ θ)
    (M : Refresh.«GL» F m) :
    opNorm (graphRestriction a b (featureFactorTable ξ ζ) M) ≤
      θ + (Real.sqrt (featureRowGramDeviationSq a ξ M) +
        Real.sqrt (∑ p, ∑ q, ‖featureColumnGram b ζ M p q - featureMeanGram ζ p q‖ ^ 2)) / 2 := by
  rw [← feature_synthesis_product_norm]
  apply product_norm_le_reference_gram _ _ (featureMeanGram ξ) (featureMeanGram ζ)
    θ _ _ hξ hζ
  · rw [featureRowSynthesis_gram]
    exact Real.le_sqrt_of_sq_le (complex_rectangular_norm_sq_le _)
  · rw [featureColumnSynthesis_gram]
    exact Real.le_sqrt_of_sq_le (complex_rectangular_norm_sq_le _)

/-- Actual GL averaging of the large part with a shared reference-Gram bound. For SVD factors, the hypotheses hold with `L=1/β` and `θ=‖F‖op`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); ξ, ζ ∈ X → U(F, m) → P → ℂ; θ, L ∈ ℝ, assume |F| = 2; 2 ≤ m; a is injective; b is injective; 0 ≤ L; ‖ featureMeanGram(ξ)‖ ≤ θ; ‖ featureMeanGram(ζ)‖ ≤ θ; ∀ x, u, featureEnergy(ξ, x, u) ≤ L; ∀ x, u, featureEnergy(ζ, x, u) ≤ L. Then

𝔼_(M ∈ GLₘ(F)) [opNorm(graphRestriction(a, b, featureFactorTable(ξ, ζ), M))] ≤ θ + √(featureVarianceCoefficient(F, X, m)) · L.
-/
theorem feature_large_part_mean (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (ξ ζ : X → U F m → P → ℂ) (θ L : ℝ)
    (hL : 0 ≤ L)
    (hξ : ‖featureMeanGram ξ‖ ≤ θ) (hζ : ‖featureMeanGram ζ‖ ≤ θ)
    (hξpoint : ∀ x u, featureEnergy ξ x u ≤ L)
    (hζpoint : ∀ x u, featureEnergy ζ x u ≤ L) :
    uavg (fun M : Refresh.«GL» F m =>
      opNorm (graphRestriction a b (featureFactorTable ξ ζ) M)) ≤
        θ + Real.sqrt (featureVarianceCoefficient F X m) * L := by
  letI : Nonempty (U F m) := ⟨unitShare ⟨0, by omega⟩⟩
  have hκ := featureVarianceCoefficient_nonneg (F := F) (X := X) hm
  have hξavg : uavg (fun x => uavg (fun u => featureEnergy ξ x u)) ≤ L := by
    exact (uavg_mono (fun x => (uavg_mono (hξpoint x)).trans_eq (uavg_const L))).trans_eq
      (uavg_const L)
  have hζavg : uavg (fun x => uavg (fun u => featureEnergy ζ x u)) ≤ L := by
    exact (uavg_mono (fun x => (uavg_mono (hζpoint x)).trans_eq (uavg_const L))).trans_eq
      (uavg_const L)
  have hξvar := (feature_row_Gram_variance_le_energy hq hm a ha ξ L hξpoint).trans
    (mul_le_mul_of_nonneg_left hξavg (mul_nonneg hκ hL))
  have hζvar := (feature_column_Gram_variance_le_energy hq hm b hb ζ L hζpoint).trans
    (mul_le_mul_of_nonneg_left hζavg (mul_nonneg hκ hL))
  let u := fun M : Refresh.«GL» F m => Real.sqrt (featureRowGramDeviationSq a ξ M)
  let v := fun M : Refresh.«GL» F m => Real.sqrt
    (∑ p, ∑ q, ‖featureColumnGram b ζ M p q - featureMeanGram ζ p q‖ ^ 2)
  have hu : uavg (fun M => u M ^ 2) ≤ featureVarianceCoefficient F X m * L ^ 2 := by
    have hu0 (M : Refresh.«GL» F m) : 0 ≤ featureRowGramDeviationSq a ξ M := by
      unfold featureRowGramDeviationSq
      positivity
    simp only [u, Real.sq_sqrt (hu0 _)]
    simpa only [mul_assoc, ← pow_two] using hξvar
  have hv : uavg (fun M => v M ^ 2) ≤ featureVarianceCoefficient F X m * L ^ 2 := by
    simpa only [v, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
      (fun _ _ => sq_nonneg _))), mul_assoc, ← pow_two] using hζvar
  have h := gram_mean_of_second_moments (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F m))
    (fun M => opNorm (graphRestriction a b (featureFactorTable ξ ζ) M))
    u v θ _ _ (feature_large_part_pointwise a b ξ ζ θ hξ hζ)
    (by simpa only [uavg_eq_expect_uniform] using hu)
    (by simpa only [uavg_eq_expect_uniform] using hv)
  rw [← uavg_eq_expect_uniform, Real.sqrt_mul hκ, Real.sqrt_sq hL] at h
  linarith

/-- Generic binary large-part estimate in terms of the number of old inputs. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); ξ, ζ ∈ X → U(F, m) → P → ℂ; θ, β ∈ ℝ, assume |F| = 2; 2 ≤ m; a is injective; b is injective; 0 < β; ‖ featureMeanGram(ξ)‖ ≤ θ; ‖ featureMeanGram(ζ)‖ ≤ θ; ∀ x, u, featureEnergy(ξ, x, u) ≤ 1 / β; ∀ x, u, featureEnergy(ζ, x, u) ≤ 1 / β. Then

𝔼_(M ∈ GLₘ(F)) [opNorm(graphRestriction(a, b, featureFactorTable(ξ, ζ), M))] ≤ θ + √3 / (√(|X|) · β).
-/
theorem feature_large_part_mean_binary (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (ξ ζ : X → U F m → P → ℂ) (θ β : ℝ) (hβ : 0 < β)
    (hξ : ‖featureMeanGram ξ‖ ≤ θ) (hζ : ‖featureMeanGram ζ‖ ≤ θ)
    (hξpoint : ∀ x u, featureEnergy ξ x u ≤ 1 / β)
    (hζpoint : ∀ x u, featureEnergy ζ x u ≤ 1 / β) :
    uavg (fun M : Refresh.«GL» F m =>
      opNorm (graphRestriction a b (featureFactorTable ξ ζ) M)) ≤
        θ + Real.sqrt 3 / (Real.sqrt (Fintype.card X : ℝ) * β) := by
  have h := feature_large_part_mean hq hm a b ha hb ξ ζ θ (1 / β)
    (by positivity) hξ hζ hξpoint hζpoint
  have hroot := Real.sqrt_le_sqrt (featureVarianceCoefficient_le hq hm a ha)
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 3)] at hroot
  have hterm := mul_le_mul_of_nonneg_right hroot (by positivity : (0 : ℝ) ≤ 1 / β)
  exact h.trans (add_le_add le_rfl (hterm.trans_eq (by ring)))

omit [DecidableEq X] [Nonempty X] [Fintype P] [DecidableEq P] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ ∈ (X × U(F, m)) → P → ℝ, we have

featureMeanGram(((x, u, p ↦ Φ((x, u), p)))) = (Complex.ofReal_*normalizedGram(Φ)).
-/
theorem featureMeanGram_ofReal (Φ : (X × U F m) → P → ℝ) :
    featureMeanGram (fun x u p => (Φ (x,u) p : ℂ)) =
      (normalizedGram Φ).map Complex.ofReal := by
  ext p q
  apply Complex.ext
  · simp only [featureMeanGram, complexAverage_re, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      neg_zero, mul_zero, sub_zero, Matrix.map_apply, normalizedGram]
    exact (uavg_prod (fun z : (X × U F m) => Φ z p * Φ z q)).symm
  · simp [featureMeanGram, complexAverage_im]

/-- The retained SVD factors meet both genuine Gram hypotheses of the random refresh estimate, with no input assumptions about those Gram matrices. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); A ∈ ℝ^((X × U(F, m)) × (X × U(F, m))); β ∈ ℝ, assume |F| = 2; 2 ≤ m; a is injective; b is injective; 0 < β; ∀ i, j, |A(i, j)| ≤ 1. Then

𝔼_(M ∈ GLₘ(F)) [GateTruncation.opNorm(graphRestriction(a, b, (Complex.ofReal_*refreshSVDPart(A, β)), M))] ≤ ‖ A‖ₒₚ + √3 / (√(|X|) · β).
-/
theorem featureSVDPart_large_mean_complex_binary (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (A : Matrix (X × U F m) (X × U F m) ℝ)
    (β : ℝ) (hβ : 0 < β) (hA : ∀ i j, |A i j| ≤ 1) :
    uavg (fun M : Refresh.«GL» F m =>
      GateTruncation.opNorm (graphRestriction a b
        ((refreshSVDPart A β).map Complex.ofReal) M)) ≤
      largestSingularCoefficient A + Real.sqrt 3 / (Real.sqrt (Fintype.card X : ℝ) * β) := by
  letI : Nonempty (U F m) := ⟨unitShare ⟨0, by omega⟩⟩
  let ξ := fun (x : X) (u : U F m)
    (p : RefreshSVDIndex A β) => (refreshSVDLeft A β (x,u) p : ℂ)
  let ζ := fun (x : X) (u : U F m)
    (p : RefreshSVDIndex A β) => (refreshSVDRight A β (x,u) p : ℂ)
  have hξ : ‖featureMeanGram ξ‖ ≤ largestSingularCoefficient A := by
    rw [show ξ = (fun x u p => (refreshSVDLeft A β (x,u) p : ℂ)) by rfl,
      featureMeanGram_ofReal (fun i p => refreshSVDLeft A β i p), complexMatrix_ofReal_norm]
    exact refreshSVDLeft_gram_norm A β
  have hζ : ‖featureMeanGram ζ‖ ≤ largestSingularCoefficient A := by
    rw [show ζ = (fun x u p => (refreshSVDRight A β (x,u) p : ℂ)) by rfl,
      featureMeanGram_ofReal (fun i p => refreshSVDRight A β i p), complexMatrix_ofReal_norm]
    exact refreshSVDRight_gram_norm A β
  have hξpoint : ∀ x u, featureEnergy ξ x u ≤ 1 / β := by
    intro x u
    simpa only [featureEnergy, ξ, Complex.norm_real, PiLp.norm_sq_eq_of_L2] using
      refreshSVDLeft_energy A β hβ hA (x,u)
  have hζpoint : ∀ x u, featureEnergy ζ x u ≤ 1 / β := by
    intro x u
    simpa only [featureEnergy, ζ, Complex.norm_real, PiLp.norm_sq_eq_of_L2] using
      refreshSVDRight_energy A β hβ hA (x,u)
  have htable : featureFactorTable ξ ζ = (refreshSVDPart A β).map Complex.ofReal := by
    ext x y
    simp only [featureFactorTable, ξ, ζ, Matrix.map_apply, refreshSVDPart_factorization,
      PiLp.inner_apply, RCLike.inner_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    simp only [starRingEnd_apply, star_trivial]
    ring
  rw [← htable]
  exact feature_large_part_mean_binary hq hm a b ha hb ξ ζ (largestSingularCoefficient A) β hβ hξ hζ hξpoint hζpoint

omit [Fintype F] [DecidableEq F] [Nonempty X] in
/-- The normalized complex graph norm agrees with the real-table convention. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); A ∈ ℝ^((X × U(F, m)) × (X × U(F, m))); M ∈ GLₘ(F), we have

opNorm(graphRestriction(a, b, (Complex.ofReal_*A), M)) = ‖ refreshTable(a, b, A, M)‖ₒₚ.
-/
theorem refreshTable_op_complex (a b : X → U F m)
    (A : Matrix (X × U F m) (X × U F m) ℝ) (M : Refresh.«GL» F m) :
    opNorm (graphRestriction a b (A.map Complex.ofReal) M) =
      largestSingularCoefficient (refreshTable a b A M) := by
  have he : graphRestriction a b (A.map Complex.ofReal) M =
      Matrix.map (refreshTable a b A M) Complex.ofReal := rfl
  rw [he]
  unfold opNorm TableAnalysis.largestSingularCoefficient
  rw [complexMatrix_ofReal_norm]

/-- The retained genuine SVD part satisfies the generic injective-feature estimate. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); A ∈ ℝ^((X × U(F, m)) × (X × U(F, m))); β ∈ ℝ, assume |F| = 2; 2 ≤ m; a is injective; b is injective; 0 < β; ∀ i, j, |A(i, j)| ≤ 1. Then

𝔼_(M ∈ GLₘ(F)) [‖ refreshTable(a, b, refreshSVDPart(A, β), M)‖ₒₚ] ≤ ‖ A‖ₒₚ + √3 / (√(|X|) · β).
-/
theorem featureSVDPart_large_mean_binary (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (A : Matrix (X × U F m) (X × U F m) ℝ)
    (β : ℝ) (hβ : 0 < β) (hA : ∀ i j, |A i j| ≤ 1) :
    uavg (fun M : Refresh.«GL» F m =>
      largestSingularCoefficient (refreshTable a b (refreshSVDPart A β) M)) ≤
      largestSingularCoefficient A + Real.sqrt 3 / (Real.sqrt (Fintype.card X : ℝ) * β) := by
  have h := featureSVDPart_large_mean_complex_binary hq hm a b ha hb A β hβ hA
  simpa only [refreshTable_op_complex] using h

end

end CircuitCompiler.RefreshAnalysis
