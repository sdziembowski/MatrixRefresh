import Proofs.Compiler.Foundations.LinearAlgebra.GramMixing
import Proofs.Compiler.Foundations.LinearAlgebra.SchurMultiplier
import Proofs.Compiler.Foundations.LinearAlgebra.TableGeometry



/-!
# Product-feature operator bounds and rectangle deviations

Feature Grams use normalized uniform state measure. Operator and L2 norms on their finite feature indices use counting measure. The table is scaled by `1 / card X`, exactly the operator convention for uniform tables.
-/

set_option autoImplicit false

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace TableAnalysis

open MatrixRefresh Refresh

noncomputable section

variable {X P : Type*} [Fintype X] [Fintype P] [DecidableEq X] [DecidableEq P]

/-- The uniformly normalized feature Gram matrix. -/
/-
Mathematical definition (normal notation): The normalized Gram matrix of a factor matrix Φ is

Gram(Φ)ᵢⱼ := 𝔼_(x ← X) [Φ(x,i) · Φ(x,j)].
-/
def normalizedGram (Φ : Matrix X P ℝ) : Matrix P P ℝ :=
  fun p q => uavg (fun x => Φ x p * Φ x q)

/-
Mathematical definition (normal notation): Measure the deviation of the normalized Gram matrix from orthonormality by

‖Gram(Φ)-I‖_(op,Euclidean).
-/
def gramOpDeviation (Φ : Matrix X P ℝ) : ℝ := ‖normalizedGram Φ - 1‖

/-- Euclidean features scaled to represent normalized state measure. -/
/-
Mathematical definition (normal notation): Normalize a factor matrix by its number of rows:

A(x,j) := |X|^(−1/2) · Φ(x,j).

Then Aᵀ · A is the normalized Gram matrix. If X is empty, the scaling factor is defined as 0.
-/
def normalizedFeatures (Φ : Matrix X P ℝ) : Matrix X P ℝ :=
  (Real.sqrt (Fintype.card X : ℝ))⁻¹ • Φ

omit [Fintype P] [DecidableEq X] [DecidableEq P] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ ∈ ℝ^(X × P), assume X ≠ ∅. Then

normalizedFeatures(Φ, ᴴ) · normalizedFeatures(Φ) = normalizedGram(Φ) .
-/
theorem normalizedFeatures_gram [Nonempty X] (Φ : Matrix X P ℝ) :
    (normalizedFeatures Φ)ᴴ * normalizedFeatures Φ = normalizedGram Φ := by
  have hd : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  have hinv : (Real.sqrt (Fintype.card X : ℝ))⁻¹ *
      (Real.sqrt (Fintype.card X : ℝ))⁻¹ = (Fintype.card X : ℝ)⁻¹ := by
    rw [← pow_two, inv_pow, Real.sq_sqrt hd.le]
  ext p q
  simp only [normalizedFeatures, normalizedGram, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_trivial, uavg]
  calc
    _ = ((Real.sqrt (Fintype.card X : ℝ))⁻¹ *
        (Real.sqrt (Fintype.card X : ℝ))⁻¹) * ∑ x, Φ x p * Φ x q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [hinv]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

‖ 1‖ ≤ 1.
-/
theorem matrix_identity_norm_le_one : ‖(1 : Matrix P P ℝ)‖ ≤ 1 := by
  rcases isEmpty_or_nonempty P with hP | hP
  · letI := hP
    have h : (1 : Matrix P P ℝ) = 0 := Subsingleton.elim _ _
    rw [h, norm_zero]
    norm_num
  · letI := hP
    simp

omit [DecidableEq X] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ ∈ ℝ^(X × P), we have

‖ normalizedGram(Φ)‖ ≤ 1 + gramOpDeviation(Φ).
-/
theorem normalizedGram_norm_le (Φ : Matrix X P ℝ) :
    ‖normalizedGram Φ‖ ≤ 1 + gramOpDeviation Φ := by
  have hI : ‖(1 : Matrix P P ℝ)‖ ≤ (1 : ℝ) := matrix_identity_norm_le_one
  have h := norm_sub_norm_le (normalizedGram Φ) (1 : Matrix P P ℝ)
  change ‖normalizedGram Φ‖ - ‖(1 : Matrix P P ℝ)‖ ≤ gramOpDeviation Φ at h
  linarith

omit [DecidableEq X] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ ∈ ℝ^(X × P), assume X ≠ ∅. Then

‖ normalizedFeatures(Φ)‖ ≤ √(1 + gramOpDeviation(Φ)).
-/
theorem normalizedFeatures_norm_le [Nonempty X] (Φ : Matrix X P ℝ) :
    ‖normalizedFeatures Φ‖ ≤ Real.sqrt (1 + gramOpDeviation Φ) := by
  have h := normalizedGram_norm_le Φ
  rw [← normalizedFeatures_gram Φ, Matrix.l2_opNorm_conjTranspose_mul_self] at h
  have hroot := Real.sqrt_le_sqrt h
  simpa only [← pow_two, Real.sqrt_sq (norm_nonneg _)] using hroot

/-- A table factored through diagonal feature coefficients. -/
/-
Mathematical definition (normal notation): For factor matrices Φ,Ψ and arbitrary real coefficients cⱼ, form the real table

F(x,y) := ∑ⱼ cⱼ · Φ(x,j) · Ψ(y,j).

It need not be a probability table.
-/
def weightedProductTable (Φ Ψ : Matrix X P ℝ) (c : P → ℝ) : Matrix X X ℝ :=
  fun x y => ∑ p, c p * Φ x p * Ψ y p

omit [DecidableEq X] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ, Ψ ∈ ℝ^(X × P); c ∈ P → ℝ, assume X ≠ ∅. Then

(|X|)⁻¹ · weightedProductTable(Φ, Ψ, c) = normalizedFeatures(Φ) · Matrix.diagonal(c) · normalizedFeatures(Ψ, ᴴ).
-/
theorem normalized_weightedProductTable [Nonempty X] (Φ Ψ : Matrix X P ℝ) (c : P → ℝ) :
    (Fintype.card X : ℝ)⁻¹ • weightedProductTable Φ Ψ c =
      normalizedFeatures Φ * Matrix.diagonal c * (normalizedFeatures Ψ)ᴴ := by
  have hd : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : (Real.sqrt (Fintype.card X : ℝ))⁻¹ ^ 2 = (Fintype.card X : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hd.le]
  ext x y
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, normalizedFeatures,
    Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
    star_trivial, weightedProductTable, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [← hs]
  ring

/-- The feature-Gram bound for the uniform table operator. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ, Ψ ∈ ℝ^(X × P); c ∈ P → ℝ, assume X ≠ ∅. Then

‖ (|X|)⁻¹ · weightedProductTable(Φ, Ψ, c)‖ ≤ ‖ c‖ · √((1 + gramOpDeviation(Φ)) · (1 + gramOpDeviation(Ψ))).
-/
theorem weightedProductTable_operator_le [Nonempty X] (Φ Ψ : Matrix X P ℝ) (c : P → ℝ) :
    ‖(Fintype.card X : ℝ)⁻¹ • weightedProductTable Φ Ψ c‖ ≤
      ‖c‖ * Real.sqrt ((1 + gramOpDeviation Φ) * (1 + gramOpDeviation Ψ)) := by
  rw [normalized_weightedProductTable Φ Ψ c]
  calc
    _ ≤ (‖normalizedFeatures Φ‖ * ‖Matrix.diagonal c‖) * ‖(normalizedFeatures Ψ)ᴴ‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ = (‖normalizedFeatures Φ‖ * ‖c‖) * ‖normalizedFeatures Ψ‖ := by
      rw [Matrix.l2_opNorm_diagonal, Matrix.l2_opNorm_conjTranspose]
    _ ≤ (Real.sqrt (1 + gramOpDeviation Φ) * ‖c‖) *
        Real.sqrt (1 + gramOpDeviation Ψ) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (normalizedFeatures_norm_le Φ) (norm_nonneg _)
      · exact normalizedFeatures_norm_le Ψ
      · exact norm_nonneg _
      · exact mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul (by unfold gramOpDeviation; positivity)]
      ring

/-- Arithmetic--geometric mean keeps only additive Gram deviations. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ ℝ, assume 0 ≤ a; 0 ≤ b. Then

√((1 + a) · (1 + b)) ≤ 1 + (a + b) / 2.
-/
theorem sqrt_one_add_mul_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt ((1 + a) * (1 + b)) ≤ 1 + (a + b) / 2 := by
  have h := Real.sq_sqrt (mul_nonneg (by linarith : 0 ≤ 1 + a) (by linarith : 0 ≤ 1 + b))
  have hs := sq_nonneg (a - b)
  have ht : 0 ≤ 1 + (a + b) / 2 := by linarith
  nlinarith [Real.sqrt_nonneg ((1 + a) * (1 + b))]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ, Ψ ∈ ℝ^(X × P); c ∈ P → ℝ, assume X ≠ ∅. Then

‖ (|X|)⁻¹ · weightedProductTable(Φ, Ψ, c)‖ ≤ ‖ c‖ · (1 + (gramOpDeviation(Φ) + gramOpDeviation(Ψ)) / 2).
-/
theorem weightedProductTable_operator_le_additive [Nonempty X]
    (Φ Ψ : Matrix X P ℝ) (c : P → ℝ) :
    ‖(Fintype.card X : ℝ)⁻¹ • weightedProductTable Φ Ψ c‖ ≤
      ‖c‖ * (1 + (gramOpDeviation Φ + gramOpDeviation Ψ) / 2) :=
  (weightedProductTable_operator_le Φ Ψ c).trans
    (mul_le_mul_of_nonneg_left (sqrt_one_add_mul_le _ _ (norm_nonneg _) (norm_nonneg _))
      (norm_nonneg _))

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ, Ψ ∈ ℝ^(X × P); c ∈ P → ℝ, assume X ≠ ∅. Then

‖ weightedProductTable(Φ, Ψ, c)‖ₒₚ ≤ ‖ c‖ · (1 + (gramOpDeviation(Φ) + gramOpDeviation(Ψ)) / 2).
-/
theorem weightedProductTable_largestSingularCoefficient_le [Nonempty X]
    (Φ Ψ : Matrix X P ℝ) (c : P → ℝ) :
    largestSingularCoefficient (weightedProductTable Φ Ψ c) ≤
      ‖c‖ * (1 + (gramOpDeviation Φ + gramOpDeviation Ψ) / 2) := by
  have h := weightedProductTable_operator_le_additive Φ Ψ c
  have hd : 0 ≤ (Fintype.card X : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  simpa only [largestSingularCoefficient, norm_smul, Real.norm_eq_abs, abs_of_nonneg hd,
    div_eq_mul_inv, mul_comm] using h

section ProductFeatures

variable {I J G : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The paired feature index uses counting measure. Each coordinate is a product of two uniformly normalized orthonormal family coordinates. -/
/-
Mathematical definition (normal notation): For e ∈ FiniteRefresh(X, G); u ∈ I → X → ℝ; x ∈ J → X → ℝ; g ∈ G, define

productFeatures(e, u, x, g) := (l, p ↦ u((p)₁, l) · x((p)₂, e(g, l))).
-/
def productFeatures (e : FiniteRefresh X G) (u : I → X → ℝ)
    (x : J → X → ℝ) (g : G) : Matrix X (I × J) ℝ :=
  fun l p => u p.1 l * x p.2 (e g l)

omit [DecidableEq X] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ FiniteRefresh(X, G); u ∈ I → X → ℝ; x ∈ J → X → ℝ; g ∈ G, we have

normalizedGram(productFeatures(e, u, x, g)) = featureGram(e, u, x, g).
-/
theorem productFeatures_gram (e : FiniteRefresh X G) (u : I → X → ℝ)
    (x : J → X → ℝ) (g : G) :
    normalizedGram (productFeatures e u x g) = featureGram e u x g := by
  ext p q
  unfold normalizedGram productFeatures featureGram
  congr 1
  funext l
  ring

/-- A table's orthogonal expansion with the uniform normalization of its singular vectors. No positivity of the coefficients is needed here. -/
/-
Mathematical definition (normal notation): For u, v ∈ I → X → ℝ; σ ∈ I → ℝ, define

lowRankTable(u, v, σ) := (l, r ↦ ∑ᵢ (σ(i) · u(i, l) · v(i, r))).
-/
def lowRankTable (u v : I → X → ℝ) (σ : I → ℝ) : Matrix X X ℝ :=
  fun l r => ∑ i, σ i * u i l * v i r

omit [Fintype X] [DecidableEq X] [DecidableEq I] [DecidableEq J] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e, f ∈ FiniteRefresh(X, G); u, v ∈ I → X → ℝ; x, y ∈ J → X → ℝ; σ ∈ I → ℝ; τ ∈ J → ℝ; g ∈ G, we have

weightedProductTable(productFeatures(e, u, x, g), productFeatures(f, v, y, g), ((p ↦ σ((p)₁) · τ((p)₂)))) = (l, r ↦ lowRankTable(u, v, σ, l, r) · lowRankTable(x, y, τ, e(g, l), f(g, r))).
-/
theorem productFeatures_table (e f : FiniteRefresh X G)
    (u v : I → X → ℝ) (x y : J → X → ℝ)
    (σ : I → ℝ) (τ : J → ℝ) (g : G) :
    weightedProductTable (productFeatures e u x g) (productFeatures f v y g)
      (fun p => σ p.1 * τ p.2) =
      fun l r => lowRankTable u v σ l r * lowRankTable x y τ (e g l) (f g r) := by
  ext l r
  simp only [weightedProductTable, productFeatures, lowRankTable, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq I] [DecidableEq J] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For σ ∈ I → ℝ; τ ∈ J → ℝ; S, T ∈ ℝ, assume 0 ≤ S; 0 ≤ T; ∀ i, |σ(i)| ≤ S; ∀ j, |τ(j)| ≤ T. Then

‖ ((p ∈ I × J ↦ σ((p)₁) · τ((p)₂)))‖ ≤ S · T.
-/
theorem product_coefficient_norm_le (σ : I → ℝ) (τ : J → ℝ)
    (S T : ℝ) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hσ : ∀ i, |σ i| ≤ S) (hτ : ∀ j, |τ j| ≤ T) :
    ‖(fun p : I × J => σ p.1 * τ p.2)‖ ≤ S * T := by
  apply pi_norm_le_iff_of_nonneg (mul_nonneg hS hT) |>.mpr
  intro p
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hσ p.1) (hτ p.2) (abs_nonneg _) hS

/-- A low-rank product-table operator bound, with the exact `1/card X` operator normalization and no independence assumption on the two actions. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e, f ∈ FiniteRefresh(X, G); u, v ∈ I → X → ℝ; x, y ∈ J → X → ℝ; σ ∈ I → ℝ; τ ∈ J → ℝ; g ∈ G; S, T ∈ ℝ, assume X ≠ ∅; 0 ≤ S; 0 ≤ T; ∀ i, |σ(i)| ≤ S; ∀ j, |τ(j)| ≤ T. Then

‖ ((l, r ↦ lowRankTable(u, v, σ, l, r) · lowRankTable(x, y, τ, e(g, l), f(g, r))))‖ₒₚ ≤ S · T · (1 + (gramOpDeviation(productFeatures(e, u, x, g)) + gramOpDeviation(productFeatures(f, v, y, g))) / 2).
-/
theorem productFeatures_largestSingularCoefficient_le [Nonempty X]
    (e f : FiniteRefresh X G) (u v : I → X → ℝ) (x y : J → X → ℝ)
    (σ : I → ℝ) (τ : J → ℝ) (g : G)
    (S T : ℝ) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hσ : ∀ i, |σ i| ≤ S) (hτ : ∀ j, |τ j| ≤ T) :
    largestSingularCoefficient (fun l r => lowRankTable u v σ l r *
      lowRankTable x y τ (e g l) (f g r)) ≤
      S * T * (1 + (gramOpDeviation (productFeatures e u x g) +
        gramOpDeviation (productFeatures f v y g)) / 2) := by
  rw [← productFeatures_table e f u v x y σ τ g]
  exact (weightedProductTable_largestSingularCoefficient_le _ _ _).trans
    (mul_le_mul_of_nonneg_right (product_coefficient_norm_le σ τ S T hS hT hσ hτ)
      (by unfold gramOpDeviation; positivity))

end ProductFeatures

omit [DecidableEq X] in
/-- Counting-measure L2 control of a rectangular Euclidean operator. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For B ∈ ℝ^(X × P), we have

‖ B‖ ≤ √(∑ₓ (∑ₚ ((B(x, p))²))).
-/
theorem matrix_operator_le_countingL2 (B : Matrix X P ℝ) :
    ‖B‖ ≤ Real.sqrt (∑ x, ∑ p, B x p ^ 2) := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  change ‖(EuclideanSpace.equiv X ℝ).symm (B *ᵥ v)‖ ^ 2 ≤
    (Real.sqrt (∑ x, ∑ p, B x p ^ 2) * ‖v‖) ^ 2
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ ∑ x, (∑ p, B x p ^ 2) * (∑ p, (v p) ^ 2) := by
      apply Finset.sum_le_sum
      intro x _
      exact Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
        (r := fun p => B x p * v p) (f := fun p => B x p ^ 2)
        (g := fun p => (v p) ^ 2) (fun _ _ => sq_nonneg _)
        (fun _ _ => sq_nonneg _) (by intro p _; ring)
    _ = _ := by
      rw [← Finset.sum_mul, mul_pow, Real.sq_sqrt (by positivity),
        EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]

omit [DecidableEq X] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For B ∈ ℝ^(X × P), we have

(‖ B‖)² ≤ ∑ₓ (∑ₚ ((B(x, p))²)).
-/
theorem matrix_operator_sq_le_countingL2Sq (B : Matrix X P ℝ) :
    ‖B‖ ^ 2 ≤ ∑ x, ∑ p, B x p ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg B) (matrix_operator_le_countingL2 B) 2
  rwa [Real.sq_sqrt (by positivity)] at h


/-
Mathematical statement (normal notation): For every real square table F,

‖F‖ₒₚ ≤ ‖F‖₂.

Both sides use the paper's uniform normalization.
-/
theorem largestSingularCoefficient_le_tableL2Norm (B : Matrix X X ℝ) : largestSingularCoefficient B ≤ tableL2Norm B := by
  unfold largestSingularCoefficient tableL2Norm
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h := matrix_operator_le_countingL2 B
  rw [← entryVector_norm_sq, Real.sqrt_sq (norm_nonneg _)] at h
  exact h

section ProductDeviation

variable {I J G : Type*} [Fintype I] [Fintype J] [Fintype G]
  [DecidableEq I] [DecidableEq J]

omit [Fintype G] [DecidableEq X] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ FiniteRefresh(X, G); u ∈ I → X → ℝ; x ∈ J → X → ℝ; g ∈ G, we have

(gramOpDeviation(productFeatures(e, u, x, g)))² ≤ gramDeviationSq(e, u, x, g).
-/
theorem productFeatures_deviation_sq_le (e : FiniteRefresh X G)
    (u : I → X → ℝ) (x : J → X → ℝ) (g : G) :
    gramOpDeviation (productFeatures e u x g) ^ 2 ≤ gramDeviationSq e u x g := by
  have h := matrix_operator_sq_le_countingL2Sq
    (normalizedGram (productFeatures e u x g) - 1)
  rw [productFeatures_gram] at h
  have hid : ∀ p q : I × J, (1 : Matrix (I × J) (I × J) ℝ) p q = indexDelta p q := by
    intro p q
    by_cases hpq : p = q <;> simp [Matrix.one_apply, indexDelta, hpq]
  convert! h using 1 <;>
    simp [gramOpDeviation, productFeatures_gram, gramDeviationSq]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change (featureGram e u x g a b - indexDelta a b) ^ 2 =
    (featureGram e u x g a b - (1 : Matrix (I × J) (I × J) ℝ) a b) ^ 2
  rw [hid]

omit [DecidableEq X] in
/-- The actual GL mixing adapters discharge `VarianceMixing`; passing to operator deviation loses nothing beyond domination by the counting-measure L2 norm. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ FiniteRefresh(X, G); κ ∈ ℝ; u ∈ I → X → ℝ; x ∈ J → X → ℝ, assume VarianceMixing(e, κ); OrthonormalFamily(u); OrthonormalFamily(x). Then

𝔼_g [(gramOpDeviation(productFeatures(e, u, x, g)))²] ≤ κ · factorEnergySecondMoment(u) · factorEnergySecondMoment(x).
-/
theorem productFeatures_deviation_mean_sq_le (e : FiniteRefresh X G)
    (κ : ℝ) (hmix : VarianceMixing e κ)
    (u : I → X → ℝ) (x : J → X → ℝ)
    (hu : OrthonormalFamily u) (hx : OrthonormalFamily x) :
    uavg (fun g => gramOpDeviation (productFeatures e u x g) ^ 2) ≤
      κ * factorEnergySecondMoment u * factorEnergySecondMoment x :=
  (uavg_mono (fun g => productFeatures_deviation_sq_le e u x g)).trans
    (gramDeviationSq_mean_le e κ hmix u x hu hx)

omit [DecidableEq X] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ FiniteRefresh(X, G); κ ∈ ℝ; u ∈ I → X → ℝ; x ∈ J → X → ℝ; H, Jbound, α, β ∈ ℝ, assume 0 ≤ κ; VarianceMixing(e, κ); OrthonormalFamily(u); OrthonormalFamily(x); 0 < α; 0 < β; |I| ≤ 1 / α²; |J| ≤ 1 / β²; ∀ l, factorEnergy(u, l) ≤ H² / α²; ∀ l, factorEnergy(x, l) ≤ Jbound² / β². Then

𝔼_g [(gramOpDeviation(productFeatures(e, u, x, g)))²] ≤ κ · H² · Jbound² / (α⁴ · β⁴).
-/
theorem productFeatures_deviation_mean_sq_le_truncated (e : FiniteRefresh X G)
    (κ : ℝ) (hκ : 0 ≤ κ) (hmix : VarianceMixing e κ)
    (u : I → X → ℝ) (x : J → X → ℝ)
    (hu : OrthonormalFamily u) (hx : OrthonormalFamily x)
    (H Jbound α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (huRank : (Fintype.card I : ℝ) ≤ 1 / α ^ 2)
    (hxRank : (Fintype.card J : ℝ) ≤ 1 / β ^ 2)
    (huLev : ∀ l, factorEnergy u l ≤ H ^ 2 / α ^ 2)
    (hxLev : ∀ l, factorEnergy x l ≤ Jbound ^ 2 / β ^ 2) :
    uavg (fun g => gramOpDeviation (productFeatures e u x g) ^ 2) ≤
      κ * H ^ 2 * Jbound ^ 2 / (α ^ 4 * β ^ 4) :=
  (uavg_mono (fun g => productFeatures_deviation_sq_le e u x g)).trans
    (gramDeviationSq_mean_le_truncated e κ hκ hmix u x hu hx H Jbound α β
      hα hβ huRank hxRank huLev hxLev)

end ProductDeviation

section RectangleAveraging

variable {Z G : Type*} [Fintype Z] [Fintype G]

/-- The weight of a rectangle is the product of its marginal `L²` sizes. -/
/-
Mathematical definition (normal notation): For f, g ∈ X → ℝ, define

rectangleWeight(f, g) := ‖ f‖₂ · ‖ g‖₂.
-/
def rectangleWeight (f g : X → ℝ) : ℝ := signedL2 f * signedL2 g

omit [DecidableEq X] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f, g ∈ X → ℝ, we have

0 ≤ rectangleWeight(f, g).
-/
theorem rectangleWeight_nonneg (f g : X → ℝ) : 0 ≤ rectangleWeight f g :=
  mul_nonneg (signedL2_nonneg f) (signedL2_nonneg g)

omit [DecidableEq X] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f, g ∈ X → ℝ, we have

(rectangleWeight(f, g))² = ‖ f‖₂² · ‖ g‖₂².
-/
theorem rectangleWeight_sq (f g : X → ℝ) :
    rectangleWeight f g ^ 2 = signedL2Sq f * signedL2Sq g := by
  rw [rectangleWeight, mul_pow, signedL2_sq, signedL2_sq]

omit [DecidableEq X] in
/-- Disjoint indicator rectangles covering the entire product space have squared weights summing to one. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f, g ∈ Z → X → ℝ, assume X ≠ ∅; ∀ z, x, (f(z, x))² = f(z, x); ∀ z, x, (g(z, x))² = g(z, x); ∀ x, y, ∑_z (f(z, x) · g(z, y)) = 1. Then

∑_z ((rectangleWeight(f(z), g(z)))²) = 1.
-/
theorem rectangleWeight_sum_sq [Nonempty X]
    (f g : Z → X → ℝ)
    (hf : ∀ z x, f z x ^ 2 = f z x) (hg : ∀ z x, g z x ^ 2 = g z x)
    (hcover : ∀ x y, ∑ z, f z x * g z y = 1) :
    ∑ z, rectangleWeight (f z) (g z) ^ 2 = 1 := by
  simp only [rectangleWeight_sq, signedL2Sq]
  simp_rw [hf, hg]
  calc
    _ = ∑ z, uavg (fun x => uavg (fun y => f z x * g z y)) := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [uavg_const_mul, uavg_mul_const]
    _ = uavg (fun x => uavg (fun y => ∑ z, f z x * g z y)) := by
      simp only [uavg_sum]
    _ = 1 := by simp only [hcover, uavg_const]

/-- Weighted error averaging is Cauchy--Schwarz on the joint answer/action space. The weights and errors can be arbitrarily dependent. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For w, a ∈ Z → G → ℝ; e ∈ ℝ, assume G ≠ ∅; ∀ g, ∑_z ((w(z, g))²) = 1; ∀ z, 𝔼_g [(a(z, g))²] ≤ e². Then

(𝔼_g [∑_z (w(z, g) · a(z, g))])² ≤ |Z| · e².
-/
theorem weighted_deviation_mean_sq_le [Nonempty G]
    (w a : Z → G → ℝ) (e : ℝ)
    (hw : ∀ g, ∑ z, w z g ^ 2 = 1)
    (ha : ∀ z, uavg (fun g => a z g ^ 2) ≤ e ^ 2) :
    (uavg (fun g => ∑ z, w z g * a z g)) ^ 2 ≤ (Fintype.card Z : ℝ) * e ^ 2 := by
  have h := sum_expect_mul_sq_le (FiniteDistribution.uniform : FiniteDistribution G) w a
  rw [familyRms_sq, familyRms_sq] at h
  simp only [← uavg_eq_expect_uniform, hw, uavg_const, one_mul] at h
  have he : uavg (fun g => ∑ z, a z g ^ 2) ≤ (Fintype.card Z : ℝ) * e ^ 2 := by
    rw [uavg_sum]
    calc
      _ ≤ ∑ _z : Z, e ^ 2 := Finset.sum_le_sum (fun z _ => ha z)
      _ = _ := by simp
  rw [uavg_sum]
  exact h.trans he

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For w, a ∈ Z → G → ℝ; e ∈ ℝ, assume G ≠ ∅; 0 ≤ e; ∀ g, ∑_z ((w(z, g))²) = 1; ∀ z, 𝔼_g [(a(z, g))²] ≤ e². Then

𝔼_g [∑_z (w(z, g) · a(z, g))] ≤ √(|Z|) · e.
-/
theorem weighted_deviation_mean_le [Nonempty G]
    (w a : Z → G → ℝ) (e : ℝ) (he : 0 ≤ e)
    (hw : ∀ g, ∑ z, w z g ^ 2 = 1)
    (ha : ∀ z, uavg (fun g => a z g ^ 2) ≤ e ^ 2) :
    uavg (fun g => ∑ z, w z g * a z g) ≤ Real.sqrt (Fintype.card Z : ℝ) * e := by
  have h := weighted_deviation_mean_sq_le w a e hw ha
  have hs := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card Z) : (0 : ℝ) ≤ Fintype.card Z)
  have hn := mul_nonneg (Real.sqrt_nonneg (Fintype.card Z : ℝ)) he
  nlinarith

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For w ∈ Z → ℝ, assume ∑_z ((w(z))²) = 1. Then

∑_z (w(z)) ≤ √(|Z|).
-/
theorem weights_sum_le_sqrt_card (w : Z → ℝ) (hw : ∑ z, w z ^ 2 = 1) :
    ∑ z, w z ≤ Real.sqrt (Fintype.card Z : ℝ) := by
  have h := sum_bounded_mul_sq_le (fun _ : Z => (1 : ℝ)) w (by simp)
  simp only [one_mul, hw, mul_one] at h
  have hs := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card Z) : (0 : ℝ) ≤ Fintype.card Z)
  nlinarith [Real.sqrt_nonneg (Fintype.card Z : ℝ)]

/-- Simultaneous left/right errors add without any independence hypothesis. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For w, a, b ∈ Z → G → ℝ; e ∈ ℝ, assume G ≠ ∅; 0 ≤ e; ∀ g, ∑_z ((w(z, g))²) = 1; ∀ z, 𝔼_g [(a(z, g))²] ≤ e²; ∀ z, 𝔼_g [(b(z, g))²] ≤ e². Then

𝔼_g [∑_z (w(z, g) · (1 + (a(z, g) + b(z, g)) / 2))] ≤ √(|Z|) · (1 + e).
-/
theorem weighted_one_add_deviation_mean_le [Nonempty G]
    (w a b : Z → G → ℝ) (e : ℝ) (he : 0 ≤ e)
    (hw : ∀ g, ∑ z, w z g ^ 2 = 1)
    (ha : ∀ z, uavg (fun g => a z g ^ 2) ≤ e ^ 2)
    (hb : ∀ z, uavg (fun g => b z g ^ 2) ≤ e ^ 2) :
    uavg (fun g => ∑ z, w z g * (1 + (a z g + b z g) / 2)) ≤
      Real.sqrt (Fintype.card Z : ℝ) * (1 + e) := by
  have h0 : uavg (fun g => ∑ z, w z g) ≤ Real.sqrt (Fintype.card Z : ℝ) := by
    exact (uavg_mono (fun g => weights_sum_le_sqrt_card (fun z => w z g) (hw g))).trans_eq
      (uavg_const _)
  have h1 := weighted_deviation_mean_le w a e he hw ha
  have h2 := weighted_deviation_mean_le w b e he hw hb
  have hrewrite : uavg (fun g => ∑ z, w z g * (1 + (a z g + b z g) / 2)) =
      uavg (fun g => ∑ z, w z g) +
      (uavg (fun g => ∑ z, w z g * a z g) +
        uavg (fun g => ∑ z, w z g * b z g)) / 2 := by
    simp only [div_eq_mul_inv, ← mul_assoc, mul_add, mul_one,
      Finset.sum_add_distrib, ← Finset.sum_mul, uavg_add, uavg_mul_const]
  rw [hrewrite]
  linarith

/-- The averaged rectangle-weighted product-table estimate used by the compression dual pairing. The table bound may depend on the same action as the rectangle partition and the two Gram deviations. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For w, a, b, k ∈ Z → G → ℝ; C, e ∈ ℝ, assume G ≠ ∅; 0 ≤ C; 0 ≤ e; ∀ z, g, 0 ≤ w(z, g); ∀ g, ∑_z ((w(z, g))²) = 1; ∀ z, 𝔼_g [(a(z, g))²] ≤ e²; ∀ z, 𝔼_g [(b(z, g))²] ≤ e²; ∀ z, g, k(z, g) ≤ C · (1 + (a(z, g) + b(z, g)) / 2). Then

𝔼_g [∑_z (w(z, g) · k(z, g))] ≤ C · √(|Z|) · (1 + e).
-/
theorem weighted_table_mean_le [Nonempty G]
    (w a b k : Z → G → ℝ) (C e : ℝ) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hwpos : ∀ z g, 0 ≤ w z g) (hw : ∀ g, ∑ z, w z g ^ 2 = 1)
    (ha : ∀ z, uavg (fun g => a z g ^ 2) ≤ e ^ 2)
    (hb : ∀ z, uavg (fun g => b z g ^ 2) ≤ e ^ 2)
    (hk : ∀ z g, k z g ≤ C * (1 + (a z g + b z g) / 2)) :
    uavg (fun g => ∑ z, w z g * k z g) ≤
      C * Real.sqrt (Fintype.card Z : ℝ) * (1 + e) := by
  calc
    _ ≤ uavg (fun g => ∑ z, w z g * (C * (1 + (a z g + b z g) / 2))) :=
      uavg_mono (fun g => Finset.sum_le_sum
        (fun z _ => mul_le_mul_of_nonneg_left (hk z g) (hwpos z g)))
    _ = C * uavg (fun g => ∑ z, w z g * (1 + (a z g + b z g) / 2)) := by
      rw [← uavg_const_mul]
      apply uavg_congr
      intro g
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ C * (Real.sqrt (Fintype.card Z : ℝ) * (1 + e)) :=
      mul_le_mul_of_nonneg_left (weighted_one_add_deviation_mean_le w a b e he hw ha hb) hC
    _ = _ := by ring

/-- The uniform table action has operator norm `largestSingularCoefficient`. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): For a real table K and real function g, let (T_Kg)(ℓ) := 𝔼ᵣ [K(ℓ,r) · g(r)]. Then ‖T_Kg‖₂² ≤ ‖K‖ₒₚ² · ‖g‖₂², with uniform normalization throughout. -/
theorem uniform_action_signedL2_sq_le (K : Matrix X X ℝ) (g : X → ℝ) :
    signedL2Sq (fun l => uavg (fun r => K l r * g r)) ≤
      largestSingularCoefficient K ^ 2 * signedL2Sq g := by
  have h := sum_sq_matrix_action_le K g
  have hscaled := mul_le_mul_of_nonneg_left h
    (by positivity : 0 ≤ (Fintype.card X : ℝ)⁻¹ ^ 3)
  unfold signedL2Sq uavg largestSingularCoefficient
  simp only [mul_pow, ← Finset.mul_sum]
  convert hscaled using 1 <;> ring

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K ∈ ℝ^(X × X); g ∈ X → ℝ, we have

‖ ((l ↦ 𝔼ᵣ [K(l, r) · g(r)]))‖₂ ≤ ‖ K‖ₒₚ · ‖ g‖₂.
-/
theorem uniform_action_signedL2_le (K : Matrix X X ℝ) (g : X → ℝ) :
    signedL2 (fun l => uavg (fun r => K l r * g r)) ≤ largestSingularCoefficient K * signedL2 g := by
  have h := uniform_action_signedL2_sq_le K g
  rw [← signedL2_sq, ← signedL2_sq] at h
  have hp := mul_nonneg (largestSingularCoefficient_nonneg K) (signedL2_nonneg g)
  nlinarith [signedL2_nonneg (fun l => uavg (fun r => K l r * g r))]

/-- Testing a table on a rectangle costs precisely the product of its two marginal sizes. This is the normalized operator-dual pairing. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K ∈ ℝ^(X × X); f, g ∈ X → ℝ, assume X ≠ ∅. Then

|pairing(K, ((l, r ↦ f(l) · g(r))))| ≤ rectangleWeight(f, g) · ‖ K‖ₒₚ.
-/
theorem abs_rectanglePairing_le [Nonempty X] (K : Matrix X X ℝ) (f g : X → ℝ) :
    |pairing K (fun l r => f l * g r)| ≤ rectangleWeight f g * largestSingularCoefficient K := by
  have hcs := expect_mul_sq_le (FiniteDistribution.uniform : FiniteDistribution X) f
    (fun l => uavg (fun r => K l r * g r))
  simp only [← uavg_eq_expect_uniform] at hcs
  have hact := uniform_action_signedL2_le K g
  have hpair : pairing K (fun l r => f l * g r) =
      uavg (fun l => f l * uavg (fun r => K l r * g r)) := by
    unfold pairing
    apply uavg_congr
    intro l
    rw [← uavg_const_mul]
    apply uavg_congr
    intro r
    ring
  rw [hpair]
  have hf := signedL2_nonneg f
  have hg := signedL2_nonneg g
  have hk := largestSingularCoefficient_nonneg K
  change _ ≤ signedL2Sq f * signedL2Sq _ at hcs
  rw [← signedL2_sq, ← signedL2_sq] at hcs
  have hact2 := pow_le_pow_left₀ (signedL2_nonneg _) hact 2
  have hbound := hcs.trans (mul_le_mul_of_nonneg_left hact2 (sq_nonneg (signedL2 f)))
  unfold rectangleWeight
  nlinarith [abs_nonneg (uavg (fun l => f l * uavg (fun r => K l r * g r))),
    sq_abs (uavg (fun l => f l * uavg (fun r => K l r * g r))),
    mul_nonneg (mul_nonneg hf hg) hk]

/-- The complete rectangle pairing estimate. This version exposes the same joint randomness in the local rectangles, table, and Gram errors. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f, g ∈ Z → G → X → ℝ; K ∈ Z → G → ℝ^(X × X); a, b ∈ Z → G → ℝ; C, e ∈ ℝ, assume X ≠ ∅; G ≠ ∅; 0 ≤ C; 0 ≤ e; ∀ z, M, x, (f(z, M, x))² = f(z, M, x); ∀ z, M, x, (g(z, M, x))² = g(z, M, x); ∀ M, l, r, ∑_z (f(z, M, l) · g(z, M, r)) = 1; ∀ z, 𝔼_M [(a(z, M))²] ≤ e²; ∀ z, 𝔼_M [(b(z, M))²] ≤ e²; ∀ z, M, ‖ K(z, M)‖ₒₚ ≤ C · (1 + (a(z, M) + b(z, M)) / 2). Then

|𝔼_M [∑_z (pairing(K(z, M), ((l, r ↦ f(z, M, l) · g(z, M, r)))))]| ≤ C · √(|Z|) · (1 + e).
-/
theorem rectanglePairing_mean_le [Nonempty X] [Nonempty G]
    (f g : Z → G → X → ℝ) (K : Z → G → Matrix X X ℝ)
    (a b : Z → G → ℝ) (C e : ℝ) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hf : ∀ z M x, f z M x ^ 2 = f z M x)
    (hg : ∀ z M x, g z M x ^ 2 = g z M x)
    (hcover : ∀ M l r, ∑ z, f z M l * g z M r = 1)
    (ha : ∀ z, uavg (fun M => a z M ^ 2) ≤ e ^ 2)
    (hb : ∀ z, uavg (fun M => b z M ^ 2) ≤ e ^ 2)
    (hK : ∀ z M, largestSingularCoefficient (K z M) ≤ C * (1 + (a z M + b z M) / 2)) :
    |uavg (fun M => ∑ z, pairing (K z M) (fun l r => f z M l * g z M r))| ≤
      C * Real.sqrt (Fintype.card Z : ℝ) * (1 + e) := by
  let w : Z → G → ℝ := fun z M => rectangleWeight (f z M) (g z M)
  have hw : ∀ M, ∑ z, w z M ^ 2 = 1 := by
    intro M
    exact rectangleWeight_sum_sq (fun z => f z M) (fun z => g z M)
      (fun z x => hf z M x) (fun z x => hg z M x) (hcover M)
  calc
    _ ≤ uavg (fun M => |∑ z, pairing (K z M) (fun l r => f z M l * g z M r)|) :=
      abs_uavg_le _
    _ ≤ uavg (fun M => ∑ z, |pairing (K z M) (fun l r => f z M l * g z M r)|) :=
      uavg_mono (fun M => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ uavg (fun M => ∑ z, w z M * largestSingularCoefficient (K z M)) :=
      uavg_mono (fun M => Finset.sum_le_sum
        (fun z _ => abs_rectanglePairing_le (K z M) (f z M) (g z M)))
    _ ≤ _ := weighted_table_mean_le w a b (fun z M => largestSingularCoefficient (K z M)) C e hC he
      (fun z M => rectangleWeight_nonneg _ _) hw ha hb hK

end RectangleAveraging

section GLRectangles

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {n : ℕ} {Z : Type*} [Fintype Z]

/-
Mathematical definition (normal notation): For p ∈ GLRectanglePartition(F, n, Z); z ∈ Z; M ∈ GLₙ(F), define

glRectangleWeight(p, z, M) := rectangleWeight(((l ↦ { 1 if p.left(z, M, l),; 0 otherwise })), ((r ↦ { 1 if p.right(z, M, r),; 0 otherwise }))).
-/
def glRectangleWeight (p : GLRectanglePartition F n Z) (z : Z)
    (M : Refresh.«GL» F n) : ℝ :=
  rectangleWeight (fun l => if p.left z M l then 1 else 0)
    (fun r => if p.right z M r then 1 else 0)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ GLRectanglePartition(F, n, Z); z ∈ Z; M ∈ GLₙ(F), we have

0 ≤ glRectangleWeight(p, z, M).
-/
theorem glRectangleWeight_nonneg (p : GLRectanglePartition F n Z)
    (z : Z) (M : Refresh.«GL» F n) : 0 ≤ glRectangleWeight p z M :=
  rectangleWeight_nonneg _ _

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ GLRectanglePartition(F, n, Z); M ∈ GLₙ(F), assume U(F, n) ≠ ∅. Then

∑_z ((glRectangleWeight(p, z, M))²) = 1.
-/
theorem glRectangleWeight_sum_sq [Nonempty (U F n)]
    (p : GLRectanglePartition F n Z) (M : Refresh.«GL» F n) :
    ∑ z, glRectangleWeight p z M ^ 2 = 1 := by
  apply rectangleWeight_sum_sq
    (fun z l => if p.left z M l then 1 else 0)
    (fun z r => if p.right z M r then 1 else 0)
  · intro z l
    split_ifs <;> norm_num
  · intro z r
    split_ifs <;> norm_num
  · intro l r
    exact p.complete M ⟨l, r⟩

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ GLRectanglePartition(F, n, Z); M ∈ GLₙ(F), assume U(F, n) ≠ ∅. Then

∑_z (glRectangleWeight(p, z, M)) ≤ √(|Z|) .
-/
theorem glRectangleWeight_sum_le [Nonempty (U F n)]
    (p : GLRectanglePartition F n Z) (M : Refresh.«GL» F n) :
    ∑ z, glRectangleWeight p z M ≤ Real.sqrt (Fintype.card Z : ℝ) :=
  weights_sum_le_sqrt_card _ (glRectangleWeight_sum_sq p M)

end GLRectangles

end

end TableAnalysis
