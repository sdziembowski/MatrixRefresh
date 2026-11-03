import Proofs.Refreshing.LocalTables
import Mathlib.Analysis.Matrix.PosDef

/-!
# Spectral truncation of finite real tables

The right singular directions are constructed from Mathlib's spectral theorem for the actual Gram matrix FᵀF. No singular-value decomposition is assumed. A cutoff at eigenvalue beta² |X||Y| is the cutoff at probability-normalized singular coefficient beta. This file establishes the row projection and its probability-normalized contraction, the first projection estimate in the local refreshing proof.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
open Matrix WithLp

namespace RefreshingProof.Local

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

/-- The actual right Gram matrix of a real table. -/
def rightGram (F : Table X Y) : Matrix Y Y ℝ := (Matrix.of F)ᴴ * Matrix.of F

omit [Fintype Y] [DecidableEq Y] in
/-- The Gram matrix is Hermitian, by its algebraic construction. -/
theorem rightGram_isHermitian (F : Table X Y) : (rightGram F).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_self (Matrix.of F)

/-- Right singular directions, supplied by the spectral theorem for FᵀF. -/
def rightSingularBasis (F : Table X Y) : OrthonormalBasis Y ℝ (EuclideanSpace ℝ Y) :=
  (rightGram_isHermitian F).eigenvectorBasis

/-- Eigenvalues of FᵀF. Their square roots are the ordinary singular values. -/
def rightEigenvalue (F : Table X Y) (j : Y) : ℝ :=
  (rightGram_isHermitian F).eigenvalues j

/-- Every eigenvalue of the right Gram operator is nonnegative. -/
theorem rightEigenvalue_nonneg (F : Table X Y) (j : Y) : 0 ≤ rightEigenvalue F j :=
  Matrix.eigenvalues_conjTranspose_mul_self_nonneg (Matrix.of F) j

/-- The constructed right directions are actual eigenvectors of FᵀF. -/
theorem rightSingularBasis_eigenvector (F : Table X Y) (j : Y) :
    rightGram F *ᵥ ⇑(rightSingularBasis F j) =
      rightEigenvalue F j • ⇑(rightSingularBasis F j) :=
  (rightGram_isHermitian F).mulVec_eigenvectorBasis j

/-- The paper's singular-coefficient normalization. -/
def normalizedSingularCoefficient (F : Table X Y) (j : Y) : ℝ :=
  Real.sqrt (rightEigenvalue F j) /
    Real.sqrt ((Fintype.card X : ℝ) * (Fintype.card Y : ℝ))

/-- Every probability-normalized singular coefficient is nonnegative. -/
theorem normalizedSingularCoefficient_nonneg (F : Table X Y) (j : Y) :
    0 ≤ normalizedSingularCoefficient F j := by
  unfold normalizedSingularCoefficient
  positivity

/-- Strict threshold cutoff on the normalized singular coefficients. -/
def retainedDirections (F : Table X Y) (beta : ℝ) : Finset Y :=
  Finset.univ.filter fun j => beta < normalizedSingularCoefficient F j

/-- Finite coordinate projection in an existing orthonormal basis. -/
def coordinateProjection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis Y ℝ E) (I : Finset Y) (z : E) : E :=
  ∑ j ∈ I, (inner ℝ (b j) z) • b j

omit [DecidableEq Y] in
/-- Pythagoras for the actual retained coordinates. -/
theorem coordinateProjection_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : OrthonormalBasis Y ℝ E) (I : Finset Y) (z : E) :
    ‖coordinateProjection b I z‖ ^ 2 = ∑ j ∈ I, (inner ℝ (b j) z) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simpa only [coordinateProjection, starRingEnd_apply, star_trivial, pow_two] using
    b.orthonormal.inner_sum (fun j => (inner ℝ (b j) z)) (fun j => (inner ℝ (b j) z)) I

omit [DecidableEq Y] in
/-- Every finite coordinate projection contracts squared Euclidean norm. -/
theorem coordinateProjection_norm_sq_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : OrthonormalBasis Y ℝ E) (I : Finset Y) (z : E) :
    ‖coordinateProjection b I z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  rw [coordinateProjection_norm_sq]
  simpa only [Real.norm_eq_abs, sq_abs] using b.orthonormal.sum_inner_products_le (s := I) z

/-- A row of the table regarded as an ordinary Euclidean vector. -/
def euclideanRow (F : Table X Y) (x : X) : EuclideanSpace ℝ Y := toLp 2 (F x)

/-- The actual right spectral truncation of F at threshold beta. -/
def spectralTruncation (F : Table X Y) (beta : ℝ) : Table X Y :=
  fun x y => coordinateProjection (rightSingularBasis F) (retainedDirections F beta)
    (euclideanRow F x) y

/-- Full expansion in the constructed right singular basis. This is derived from Mathlib's basis construction, with no assumed expansion hypothesis. -/
theorem right_singular_expansion (F : Table X Y) (x : X) (y : Y) :
    F x y = (∑ j : Y, (inner ℝ (rightSingularBasis F j) (euclideanRow F x)) •
      rightSingularBasis F j) y := by
  rw [(rightSingularBasis F).sum_repr']
  rfl

/-- Row Pythagoras for the truncated table. -/
theorem spectralTruncation_row_norm_sq (F : Table X Y) (beta : ℝ) (x : X) :
    (∑ y, spectralTruncation F beta x y ^ 2) =
      ∑ j ∈ retainedDirections F beta, (inner ℝ (rightSingularBasis F j) (euclideanRow F x)) ^ 2 := by
  rw [← coordinateProjection_norm_sq]
  exact (EuclideanSpace.real_norm_sq_eq _).symm

/-- The actual spectral truncation contracts the squared norm of every row. -/
theorem spectralTruncation_row_sum_sq_le (F : Table X Y) (beta : ℝ) (x : X) :
    (∑ y, spectralTruncation F beta x y ^ 2) ≤ ∑ y, F x y ^ 2 := by
  have h := coordinateProjection_norm_sq_le (rightSingularBasis F)
    (retainedDirections F beta) (euclideanRow F x)
  simpa only [EuclideanSpace.real_norm_sq_eq, spectralTruncation,
    euclideanRow, PiLp.toLp_apply] using h

/-- The probability-normalized row contraction used in the paper's row-projection bound. -/
theorem spectralTruncation_row_average_sq_le (F : Table X Y) (beta : ℝ) (x : X) :
    average (fun y => spectralTruncation F beta x y ^ 2) ≤
      average (fun y => F x y ^ 2) :=
  mul_le_mul_of_nonneg_left (spectralTruncation_row_sum_sq_le F beta x)
    (inv_nonneg.mpr (Nat.cast_nonneg _))


/-- Ordinary Euclidean inner products on real coordinate vectors. -/
theorem real_euclidean_inner {ι : Type*} [Fintype ι]
    (u v : EuclideanSpace ℝ ι) :
    inner ℝ u v = (⇑u) ⬝ᵥ (⇑v) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  exact dotProduct_comm _ _

/-- Images of the actual right singular directions under the table. -/
def leftImage (F : Table X Y) (j : Y) : EuclideanSpace ℝ X :=
  toLp 2 ((Matrix.of F) *ᵥ ⇑(rightSingularBasis F j))

/-- The row expansion coefficient is the corresponding image coordinate. -/
theorem leftImage_apply (F : Table X Y) (j : Y) (x : X) :
    leftImage F j x = inner ℝ (rightSingularBasis F j) (euclideanRow F x) := by
  rw [real_euclidean_inner]
  change (F x) ⬝ᵥ ⇑(rightSingularBasis F j) = _
  exact dotProduct_comm _ _

/-- The images of distinct right singular directions are orthogonal, and the squared image norm equals the associated Gram eigenvalue. -/
theorem leftImage_inner (F : Table X Y) (j k : Y) :
    inner ℝ (leftImage F j) (leftImage F k) =
      if j = k then rightEigenvalue F j else 0 := by
  rw [real_euclidean_inner]
  change ((Matrix.of F) *ᵥ ⇑(rightSingularBasis F j)) ⬝ᵥ
      ((Matrix.of F) *ᵥ ⇑(rightSingularBasis F k)) = _
  calc
    _ = ⇑(rightSingularBasis F j) ⬝ᵥ ((Matrix.of F)ᵀ *ᵥ
        ((Matrix.of F) *ᵥ ⇑(rightSingularBasis F k))) := by
      symm
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = ⇑(rightSingularBasis F j) ⬝ᵥ (rightGram F *ᵥ ⇑(rightSingularBasis F k)) := by
      rw [Matrix.mulVec_mulVec]
      simp only [rightGram, Matrix.conjTranspose_eq_transpose_of_trivial]
    _ = ⇑(rightSingularBasis F j) ⬝ᵥ
        (rightEigenvalue F k • ⇑(rightSingularBasis F k)) := by
      rw [rightSingularBasis_eigenvector]
    _ = rightEigenvalue F k * inner ℝ (rightSingularBasis F j) (rightSingularBasis F k) := by
      rw [dotProduct_smul, real_euclidean_inner, smul_eq_mul]
    _ = _ := by
      rw [(rightSingularBasis F).inner_eq_ite]
      split_ifs with h
      · subst k
        ring
      · simp

/-- Positive Gram directions, so division by the singular value is defined. -/
abbrev PositiveDirection (F : Table X Y) := {j : Y // 0 < rightEigenvalue F j}

/-- Actual unit left singular vectors, obtained by normalizing the positive images of the actual right singular vectors. -/
def leftSingularVector (F : Table X Y) (j : PositiveDirection F) : EuclideanSpace ℝ X :=
  (Real.sqrt (rightEigenvalue F j.val))⁻¹ • leftImage F j.val

/-- The normalized positive left singular vectors are orthonormal. -/
theorem leftSingularVector_orthonormal (F : Table X Y) :
    Orthonormal ℝ (leftSingularVector F) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  simp only [leftSingularVector, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial, leftImage_inner]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    have hspos : 0 < Real.sqrt (rightEigenvalue F i.val) := Real.sqrt_pos.mpr i.property
    have hsq := Real.sq_sqrt (le_of_lt i.property)
    field_simp [ne_of_gt hspos]
    nlinarith
  · have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    simp only [hval, hij, ite_false, mul_zero]


/-- A column expressed using any subset of the right singular directions. -/
def columnProjection (F : Table X Y) (I : Finset Y) (y : Y) : EuclideanSpace ℝ X :=
  ∑ j ∈ I, (rightSingularBasis F j y) • leftImage F j

/-- The same spectral truncation has the expected column expansion in actual left images of the right singular vectors. -/
theorem spectralTruncation_column_expansion (F : Table X Y) (beta : ℝ) (x : X) (y : Y) :
    spectralTruncation F beta x y = columnProjection F (retainedDirections F beta) y x := by
  simp only [spectralTruncation, coordinateProjection, columnProjection,
    ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [leftImage_apply]
  ring

/-- Full columns are reconstructed by the actual Gram eigenbasis. -/
theorem full_column_expansion (F : Table X Y) (x : X) (y : Y) :
    F x y = columnProjection F Finset.univ y x := by
  rw [right_singular_expansion F x y]
  simp only [columnProjection, ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [leftImage_apply]
  ring

/-- Orthogonality of the left images yields column Pythagoras with Gram weights. The weights are actual nonnegative eigenvalues of FᵀF. -/
theorem columnProjection_norm_sq (F : Table X Y) (I : Finset Y) (y : Y) :
    ‖columnProjection F I y‖ ^ 2 =
      ∑ j ∈ I, (rightSingularBasis F j y) ^ 2 * rightEigenvalue F j := by
  rw [← real_inner_self_eq_norm_sq]
  unfold columnProjection
  simp only [sum_inner, inner_smul_left, starRingEnd_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [inner_sum, inner_smul_right, leftImage_inner]
  rw [Finset.sum_eq_single j]
  · simp
    ring
  · intro k hk hkj
    simp only [Ne.symm hkj, ite_false, mul_zero]
  · exact fun hn => False.elim (hn hj)

/-- Spectral truncation contracts the squared norm of each column, not merely the total Frobenius norm. -/
theorem spectralTruncation_column_sum_sq_le (F : Table X Y) (beta : ℝ) (y : Y) :
    (∑ x, spectralTruncation F beta x y ^ 2) ≤ ∑ x, F x y ^ 2 := by
  have hs : (∑ j ∈ retainedDirections F beta,
      (rightSingularBasis F j y) ^ 2 * rightEigenvalue F j) ≤
      ∑ j : Y, (rightSingularBasis F j y) ^ 2 * rightEigenvalue F j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro j hj hjnot
    exact mul_nonneg (sq_nonneg _) (rightEigenvalue_nonneg F j)
  rw [← columnProjection_norm_sq, ← columnProjection_norm_sq] at hs
  simpa only [EuclideanSpace.real_norm_sq_eq, ← spectralTruncation_column_expansion,
    ← full_column_expansion] using hs

/-- The probability-normalized column contraction used by the local proof. -/
theorem spectralTruncation_column_average_sq_le (F : Table X Y) (beta : ℝ) (y : Y) :
    average (fun x => spectralTruncation F beta x y ^ 2) ≤
      average (fun x => F x y ^ 2) :=
  mul_le_mul_of_nonneg_left (spectralTruncation_column_sum_sq_le F beta y)
    (inv_nonneg.mpr (Nat.cast_nonneg _))


/-- Probability-normalized coordinate functions: unit Euclidean vectors become unit functions for the uniform probability measure. -/
def probabilityCoordinates {ι : Type*} [Fintype ι] (z : EuclideanSpace ℝ ι) : ι → ℝ :=
  fun i => Real.sqrt (Fintype.card ι : ℝ) * z i

/-- Probability normalization preserves inner products after converting Euclidean coordinates to functions on a nonempty finite set. -/
theorem probabilityCoordinates_average_inner {ι : Type*} [Fintype ι] [Nonempty ι]
    (u v : EuclideanSpace ℝ ι) :
    average (fun i => probabilityCoordinates u i * probabilityCoordinates v i) =
      inner ℝ u v := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have heq : (fun i => probabilityCoordinates u i * probabilityCoordinates v i) =
      (fun i => (Fintype.card ι : ℝ) * (u i * v i)) := by
    funext i
    unfold probabilityCoordinates
    calc
      _ = (Real.sqrt (Fintype.card ι : ℝ)) ^ 2 * (u i * v i) := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [heq, average_smul, real_euclidean_inner]
  unfold average dotProduct
  field_simp [hc]

/-- Probability-normalized left singular functions. Zero singular directions are given the zero left function by the reciprocal convention. -/
def normalizedLeftFunction (F : Table X Y) (j : Y) : X → ℝ :=
  probabilityCoordinates ((Real.sqrt (rightEigenvalue F j))⁻¹ • leftImage F j)

/-- Probability-normalized right singular functions. -/
def normalizedRightFunction (F : Table X Y) (j : Y) : Y → ℝ :=
  probabilityCoordinates (rightSingularBasis F j)

/-- Positive left singular functions are orthonormal under the uniform measure. -/
theorem normalizedLeftFunction_orthonormal [Nonempty X] (F : Table X Y)
    (i j : PositiveDirection F) :
    average (fun x => normalizedLeftFunction F i.val x * normalizedLeftFunction F j.val x) =
      if i = j then 1 else 0 := by
  change average (fun x => probabilityCoordinates (leftSingularVector F i) x *
    probabilityCoordinates (leftSingularVector F j) x) = _
  rw [probabilityCoordinates_average_inner]
  exact orthonormal_iff_ite.mp (leftSingularVector_orthonormal F) i j

/-- Right singular functions are orthonormal under the uniform measure. -/
theorem normalizedRightFunction_orthonormal [Nonempty Y] (F : Table X Y) (i j : Y) :
    average (fun y => normalizedRightFunction F i y * normalizedRightFunction F j y) =
      if i = j then 1 else 0 := by
  rw [normalizedRightFunction, normalizedRightFunction, probabilityCoordinates_average_inner]
  exact (rightSingularBasis F).inner_eq_ite i j

/-- Squared Euclidean norm of an actual left image. -/
theorem leftImage_norm_sq (F : Table X Y) (j : Y) :
    ‖leftImage F j‖ ^ 2 = rightEigenvalue F j := by
  rw [← real_inner_self_eq_norm_sq, leftImage_inner]
  simp

/-- Zero singular directions contribute no image and hence no table term. -/
theorem leftImage_eq_zero_of_eigenvalue_eq_zero (F : Table X Y) (j : Y)
    (h : rightEigenvalue F j = 0) : leftImage F j = 0 := by
  apply norm_eq_zero.mp
  have hs := leftImage_norm_sq F j
  rw [h] at hs
  nlinarith [norm_nonneg (leftImage F j)]

/-- The normalized singular coefficient times the left function is exactly the row expansion coefficient divided by sqrt(|Y|), including zero directions. -/
theorem normalized_coefficient_left [Nonempty X] [Nonempty Y]
    (F : Table X Y) (j : Y) (x : X) :
    normalizedSingularCoefficient F j * normalizedLeftFunction F j x =
      leftImage F j x / Real.sqrt (Fintype.card Y : ℝ) := by
  have hx : 0 < Real.sqrt (Fintype.card X : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hy : 0 < Real.sqrt (Fintype.card Y : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hroot : Real.sqrt ((Fintype.card X : ℝ) * (Fintype.card Y : ℝ)) =
      Real.sqrt (Fintype.card X : ℝ) * Real.sqrt (Fintype.card Y : ℝ) :=
    Real.sqrt_mul (Nat.cast_nonneg _) _
  by_cases hj : 0 < rightEigenvalue F j
  · have hjroot : 0 < Real.sqrt (rightEigenvalue F j) := Real.sqrt_pos.mpr hj
    unfold normalizedSingularCoefficient normalizedLeftFunction probabilityCoordinates
    rw [hroot]
    simp only [PiLp.smul_apply, smul_eq_mul]
    field_simp [ne_of_gt hx, ne_of_gt hy, ne_of_gt hjroot]
  · have hz : rightEigenvalue F j = 0 := le_antisymm (le_of_not_gt hj) (rightEigenvalue_nonneg F j)
    have himage := leftImage_eq_zero_of_eigenvalue_eq_zero F j hz
    simp [normalizedSingularCoefficient, normalizedLeftFunction, probabilityCoordinates, hz, himage]

/-- Each normalized product term is the actual right-basis expansion term. -/
theorem normalized_singular_product [Nonempty X] [Nonempty Y]
    (F : Table X Y) (j : Y) (x : X) (y : Y) :
    normalizedSingularCoefficient F j * normalizedLeftFunction F j x *
      normalizedRightFunction F j y = leftImage F j x * rightSingularBasis F j y := by
  rw [normalized_coefficient_left]
  unfold normalizedRightFunction probabilityCoordinates
  have hy : Real.sqrt (Fintype.card Y : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos))
  field_simp [hy]

/-- Actual finite probability-normalized singular expansion of every real table. The positive left functions and all right functions have the orthonormality properties above; zero singular directions have zero contribution. -/
theorem normalized_singular_expansion [Nonempty X] [Nonempty Y]
    (F : Table X Y) (x : X) (y : Y) :
    F x y = ∑ j : Y, normalizedSingularCoefficient F j * normalizedLeftFunction F j x *
      normalizedRightFunction F j y := by
  rw [right_singular_expansion F x y]
  simp only [ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [normalized_singular_product, leftImage_apply]

/-- The actual strict spectral truncation has the corresponding normalized singular product expansion. -/
theorem spectralTruncation_normalized_expansion [Nonempty X] [Nonempty Y]
    (F : Table X Y) (beta : ℝ) (x : X) (y : Y) :
    spectralTruncation F beta x y = ∑ j ∈ retainedDirections F beta,
      normalizedSingularCoefficient F j * normalizedLeftFunction F j x * normalizedRightFunction F j y := by
  simp only [spectralTruncation, coordinateProjection, ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [normalized_singular_product, leftImage_apply]


/-- Balanced factors of the actual normalized singular expansion. -/
def leftBalancedFactor (F : Table X Y) (j : Y) (x : X) : ℝ :=
  Real.sqrt (normalizedSingularCoefficient F j) * normalizedLeftFunction F j x

/-- The right singular function scaled by the square root of its singular coefficient. -/
def rightBalancedFactor (F : Table X Y) (j : Y) (y : Y) : ℝ :=
  Real.sqrt (normalizedSingularCoefficient F j) * normalizedRightFunction F j y

/-- The squared left balanced factor is its singular coefficient times the squared normalized left singular function. -/
theorem leftBalancedFactor_sq (F : Table X Y) (j : Y) (x : X) :
    leftBalancedFactor F j x ^ 2 =
      normalizedSingularCoefficient F j * normalizedLeftFunction F j x ^ 2 := by
  unfold leftBalancedFactor
  rw [mul_pow, Real.sq_sqrt (normalizedSingularCoefficient_nonneg F j)]

/-- The squared right balanced factor is its singular coefficient times the squared normalized right singular function. -/
theorem rightBalancedFactor_sq (F : Table X Y) (j : Y) (y : Y) :
    rightBalancedFactor F j y ^ 2 =
      normalizedSingularCoefficient F j * normalizedRightFunction F j y ^ 2 := by
  unfold rightBalancedFactor
  rw [mul_pow, Real.sq_sqrt (normalizedSingularCoefficient_nonneg F j)]

/-- Balanced products reproduce the actual singular terms. -/
theorem balancedFactor_product (F : Table X Y) (j : Y) (x : X) (y : Y) :
    leftBalancedFactor F j x * rightBalancedFactor F j y =
      normalizedSingularCoefficient F j * normalizedLeftFunction F j x * normalizedRightFunction F j y := by
  unfold leftBalancedFactor rightBalancedFactor
  calc
    _ = (Real.sqrt (normalizedSingularCoefficient F j)) ^ 2 *
      (normalizedLeftFunction F j x * normalizedRightFunction F j y) := by ring
    _ = _ := by rw [Real.sq_sqrt (normalizedSingularCoefficient_nonneg F j)]; ring

/-- Actual balanced product representation of the strict spectral truncation. -/
theorem spectralTruncation_balanced_expansion [Nonempty X] [Nonempty Y]
    (F : Table X Y) (beta : ℝ) (x : X) (y : Y) :
    spectralTruncation F beta x y = ∑ j ∈ retainedDirections F beta,
      leftBalancedFactor F j x * rightBalancedFactor F j y := by
  rw [spectralTruncation_normalized_expansion]
  exact Finset.sum_congr rfl fun j _ => (balancedFactor_product F j x y).symm

/-- Nuclear norm of the actual spectral truncation: the sum of its nonnegative probability-normalized singular coefficients. -/
def truncatedNuclearNorm (F : Table X Y) (beta : ℝ) : ℝ :=
  ∑ j ∈ retainedDirections F beta, normalizedSingularCoefficient F j

/-- Factor energies of the chosen actual balanced representation. -/
def leftFactorEnergy (F : Table X Y) (beta : ℝ) (x : X) : ℝ :=
  ∑ j ∈ retainedDirections F beta, leftBalancedFactor F j x ^ 2

/-- The pointwise sum of squared right balanced factors retained at threshold β. -/
def rightFactorEnergy (F : Table X Y) (beta : ℝ) (y : Y) : ℝ :=
  ∑ j ∈ retainedDirections F beta, rightBalancedFactor F j y ^ 2

/-- Uniform averages commute with finite sums. -/
theorem average_sum {α ι : Type*} [Fintype α] (I : Finset ι) (f : ι → α → ℝ) :
    average (fun a => ∑ j ∈ I, f j a) = ∑ j ∈ I, average (f j) := by
  simp only [average, Finset.mul_sum]
  exact Finset.sum_comm

/-- Each balanced left factor has mean square equal to its actual singular coefficient, including zero singular directions. -/
theorem leftBalancedFactor_average_sq [Nonempty X] (F : Table X Y) (j : Y) :
    average (fun x => leftBalancedFactor F j x ^ 2) = normalizedSingularCoefficient F j := by
  by_cases hj : 0 < rightEigenvalue F j
  · have hu := normalizedLeftFunction_orthonormal F (⟨j, hj⟩ : PositiveDirection F) ⟨j, hj⟩
    simp only [ite_true, ← pow_two] at hu
    simp only [leftBalancedFactor_sq, average_smul]
    rw [hu, mul_one]
  · have hz : rightEigenvalue F j = 0 := le_antisymm (le_of_not_gt hj) (rightEigenvalue_nonneg F j)
    simp [leftBalancedFactor, normalizedSingularCoefficient, hz, average]

/-- Each balanced right factor has mean square equal to its actual singular coefficient. -/
theorem rightBalancedFactor_average_sq [Nonempty Y] (F : Table X Y) (j : Y) :
    average (fun y => rightBalancedFactor F j y ^ 2) = normalizedSingularCoefficient F j := by
  have hu := normalizedRightFunction_orthonormal F j j
  simp only [ite_true, ← pow_two] at hu
  simp only [rightBalancedFactor_sq, average_smul]
  rw [hu, mul_one]

/-- Mean left energy equals the actual truncated nuclear norm. -/
theorem leftFactorEnergy_average [Nonempty X] (F : Table X Y) (beta : ℝ) :
    average (leftFactorEnergy F beta) = truncatedNuclearNorm F beta := by
  unfold leftFactorEnergy truncatedNuclearNorm
  rw [average_sum]
  exact Finset.sum_congr rfl fun j _ => leftBalancedFactor_average_sq F j

/-- Mean right energy equals the same actual truncated nuclear norm. -/
theorem rightFactorEnergy_average [Nonempty Y] (F : Table X Y) (beta : ℝ) :
    average (rightFactorEnergy F beta) = truncatedNuclearNorm F beta := by
  unfold rightFactorEnergy truncatedNuclearNorm
  rw [average_sum]
  exact Finset.sum_congr rfl fun j _ => rightBalancedFactor_average_sq F j

/-- The retained normalized coefficient squares equal the actual row norm. -/
theorem normalized_retained_row_sq [Nonempty X] [Nonempty Y]
    (F : Table X Y) (beta : ℝ) (x : X) :
    (∑ j ∈ retainedDirections F beta,
      normalizedSingularCoefficient F j ^ 2 * normalizedLeftFunction F j x ^ 2) =
        average (fun y => spectralTruncation F beta x y ^ 2) := by
  have hc (j : Y) : normalizedSingularCoefficient F j ^ 2 * normalizedLeftFunction F j x ^ 2 =
      (Fintype.card Y : ℝ)⁻¹ * leftImage F j x ^ 2 := by
    rw [← mul_pow, normalized_coefficient_left, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  simp_rw [hc]
  rw [← Finset.mul_sum]
  unfold average
  rw [spectralTruncation_row_norm_sq]
  congr 1

/-- The retained normalized coefficient squares also equal the actual column norm. -/
theorem normalized_retained_column_sq [Nonempty X] [Nonempty Y]
    (F : Table X Y) (beta : ℝ) (y : Y) :
    (∑ j ∈ retainedDirections F beta,
      normalizedSingularCoefficient F j ^ 2 * normalizedRightFunction F j y ^ 2) =
        average (fun x => spectralTruncation F beta x y ^ 2) := by
  have hx : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hy : (Fintype.card Y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hc (j : Y) : normalizedSingularCoefficient F j ^ 2 * normalizedRightFunction F j y ^ 2 =
      (Fintype.card X : ℝ)⁻¹ * ((rightSingularBasis F j y) ^ 2 * rightEigenvalue F j) := by
    unfold normalizedSingularCoefficient normalizedRightFunction probabilityCoordinates
    rw [div_pow, mul_pow, Real.sq_sqrt (rightEigenvalue_nonneg F j),
      Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
      Real.sq_sqrt (Nat.cast_nonneg _)]
    field_simp [hx, hy]
  simp_rw [hc]
  rw [← Finset.mul_sum]
  rw [← columnProjection_norm_sq]
  unfold average
  rw [EuclideanSpace.real_norm_sq_eq]
  congr 1
  exact Finset.sum_congr rfl fun x _ => by rw [← spectralTruncation_column_expansion]

/-- Pointwise energy control of the actual balanced left factors, derived from the actual row contraction and the strict spectral cutoff. -/
theorem leftFactorEnergy_le [Nonempty X] [Nonempty Y]
    (F : Table X Y) {beta : ℝ} (hbeta : 0 < beta) (x : X)
    (hrow : average (fun y => F x y ^ 2) ≤ 1) :
    leftFactorEnergy F beta x ≤ 1 / beta := by
  unfold leftFactorEnergy
  simp only [leftBalancedFactor_sq]
  apply retained_weighted_energy _ _ _ hbeta
  · intro j hj
    exact le_of_lt ((Finset.mem_filter.mp hj).2)
  · rw [normalized_retained_row_sq]
    exact (spectralTruncation_row_average_sq_le F beta x).trans hrow

/-- The corresponding pointwise right factor energy control. -/
theorem rightFactorEnergy_le [Nonempty X] [Nonempty Y]
    (F : Table X Y) {beta : ℝ} (hbeta : 0 < beta) (y : Y)
    (hcolumn : average (fun x => F x y ^ 2) ≤ 1) :
    rightFactorEnergy F beta y ≤ 1 / beta := by
  unfold rightFactorEnergy
  simp only [rightBalancedFactor_sq]
  apply retained_weighted_energy _ _ _ hbeta
  · intro j hj
    exact le_of_lt ((Finset.mem_filter.mp hj).2)
  · rw [normalized_retained_column_sq]
    exact (spectralTruncation_column_average_sq_le F beta y).trans hcolumn

/-- Monotonicity of the probability-normalized finite average. -/
theorem average_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : average f ≤ average g :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => h a)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- The actual spectral truncation contracts the entire probability-normalized squared L₂ norm, as required by the paper's rectangle L₂ bound. -/
theorem spectralTruncation_normSq_le (F : Table X Y) (beta : ℝ) :
    normSq (spectralTruncation F beta) ≤ normSq F := by
  unfold normSq pairing
  simp only [← pow_two]
  exact average_mono (spectralTruncation_row_average_sq_le F beta)

/-- A bounded probability table has row norm at most one after truncation. -/
theorem spectralTruncation_row_average_sq_le_one [Nonempty Y]
    (F : Table X Y) (beta : ℝ) (hF : ∀ x y, |F x y| ≤ 1) (x : X) :
    average (fun y => spectralTruncation F beta x y ^ 2) ≤ 1 := by
  have hrow : average (fun y => F x y ^ 2) ≤ average (fun _ : Y => (1 : ℝ)) := by
    apply average_mono
    intro y
    have hs := (sq_le_sq₀ (abs_nonneg (F x y)) (by norm_num : (0 : ℝ) ≤ 1)).mpr (hF x y)
    simpa only [sq_abs, one_pow] using hs
  have hcard : (Fintype.card Y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hconst : average (fun _ : Y => (1 : ℝ)) = 1 := by
    simp [average, hcard]
  exact (spectralTruncation_row_average_sq_le F beta x).trans (hconst ▸ hrow)

end RefreshingProof.Local
