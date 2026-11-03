import Proofs.Refreshing.LocalSVD

/-!
# Operator, entry, and four-cycle bounds for actual spectral parts

All singular functions and coefficients in this file are the actual objects constructed in `LocalSVD`. No spectral expansion or Bessel bound is assumed.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
open Matrix WithLp

namespace RefreshingProof.Local

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

/-- The table entries are controlled by the energies of their actual balanced factors. -/
theorem spectralTruncation_entry_sq_le [Nonempty X] [Nonempty Y]
    (F : Table X Y) (beta : ℝ) (x : X) (y : Y) :
    spectralTruncation F beta x y ^ 2 ≤ leftFactorEnergy F beta x * rightFactorEnergy F beta y := by
  rw [spectralTruncation_balanced_expansion]
  exact Finset.sum_mul_sq_le_sq_mul_sq (retainedDirections F beta)
    (fun j => leftBalancedFactor F j x) (fun j => rightBalancedFactor F j y)

/-- The pointwise entry bound used for the residual's max norm. -/
theorem spectralTruncation_entry_abs_le [Nonempty X] [Nonempty Y]
    (F : Table X Y) {beta : ℝ} (hbeta : 0 < beta) (x : X) (y : Y)
    (hrow : average (fun z => F x z ^ 2) ≤ 1)
    (hcolumn : average (fun z => F z y ^ 2) ≤ 1) :
    |spectralTruncation F beta x y| ≤ 1 / beta := by
  have hL := leftFactorEnergy_le F hbeta x hrow
  have hR := rightFactorEnergy_le F hbeta y hcolumn
  have hL0 : 0 ≤ leftFactorEnergy F beta x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hR0 : 0 ≤ rightFactorEnergy F beta y := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hm := mul_le_mul hL hR hR0 (le_of_lt (one_div_pos.mpr hbeta))
  have hs := (spectralTruncation_entry_sq_le F beta x y).trans hm
  apply (sq_le_sq₀ (abs_nonneg _) (le_of_lt (one_div_pos.mpr hbeta))).mp
  rw [sq_abs]
  simpa only [pow_two] using hs

/-- Functions on a finite probability space as normalized Euclidean vectors. -/
def probabilityVector {ι : Type*} [Fintype ι] (f : ι → ℝ) : EuclideanSpace ℝ ι :=
  (Real.sqrt (Fintype.card ι : ℝ))⁻¹ • toLp 2 f

/-- Converting a function to its probability-normalized Euclidean vector and back recovers every coordinate. -/
theorem probabilityCoordinates_probabilityVector {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) : probabilityCoordinates (probabilityVector f) = f := by
  funext i
  unfold probabilityCoordinates probabilityVector
  simp only [PiLp.smul_apply, smul_eq_mul]
  have hc : Real.sqrt (Fintype.card ι : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos))
  field_simp [hc]

/-- Normalized vectorization turns the probability pairing into Euclidean inner product. -/
theorem probability_pairing_vector {ι : Type*} [Fintype ι] [Nonempty ι]
    (z : EuclideanSpace ℝ ι) (f : ι → ℝ) :
    average (fun i => probabilityCoordinates z i * f i) = inner ℝ z (probabilityVector f) := by
  have h := probabilityCoordinates_average_inner z (probabilityVector f)
  simpa only [probabilityCoordinates_probabilityVector] using h

/-- The squared Euclidean norm of a probability-normalized vector equals the uniform mean of its squared coordinates. -/
theorem probabilityVector_norm_sq {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    ‖probabilityVector f‖ ^ 2 = average (fun i => f i ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, ← probabilityCoordinates_average_inner]
  simp only [probabilityCoordinates_probabilityVector, pow_two]

/-- Correlation of a test function with an actual normalized left singular function. -/
def leftTestCoefficient (F : Table X Y) (f : X → ℝ) (j : Y) : ℝ :=
  average (fun x => normalizedLeftFunction F j x * f x)

/-- The uniform correlation of a test function with one normalized right singular function. -/
def rightTestCoefficient (F : Table X Y) (g : Y → ℝ) (j : Y) : ℝ :=
  average (fun y => normalizedRightFunction F j y * g y)

/-- Zero singular directions have identically zero left test coefficients. -/
theorem leftTestCoefficient_eq_zero (F : Table X Y) (f : X → ℝ) (j : Y)
    (hj : ¬ 0 < rightEigenvalue F j) : leftTestCoefficient F f j = 0 := by
  have hz : rightEigenvalue F j = 0 := le_antisymm (le_of_not_gt hj) (rightEigenvalue_nonneg F j)
  simp [leftTestCoefficient, normalizedLeftFunction, probabilityCoordinates, hz, average]

/-- Bessel's inequality for the actual left singular functions, including any zero directions (whose coefficients are zero). -/
theorem leftTestCoefficient_bessel [Nonempty X] (F : Table X Y) (f : X → ℝ) (I : Finset Y) :
    (∑ j ∈ I, leftTestCoefficient F f j ^ 2) ≤ average (fun x => f x ^ 2) := by
  classical
  let p : Y → Prop := fun j => 0 < rightEigenvalue F j
  have hp (j : PositiveDirection F) :
      inner ℝ (leftSingularVector F j) (probabilityVector f) = leftTestCoefficient F f j.val := by
    symm
    exact probability_pairing_vector (leftSingularVector F j) f
  have h := (leftSingularVector_orthonormal F).sum_inner_products_le
    (s := I.subtype p) (probabilityVector f)
  simp only [Real.norm_eq_abs, sq_abs, hp, probabilityVector_norm_sq] at h
  have hsub : (∑ j ∈ I.subtype p, leftTestCoefficient F f j.val ^ 2) =
      ∑ j ∈ I.filter p, leftTestCoefficient F f j ^ 2 :=
    Finset.sum_subtype_eq_sum_filter (s := I) (fun j => leftTestCoefficient F f j ^ 2)
  rw [hsub] at h
  have heq : (∑ j ∈ I.filter p, leftTestCoefficient F f j ^ 2) =
      ∑ j ∈ I, leftTestCoefficient F f j ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j hj hjnot
    have hjp : ¬ p j := fun hpj => hjnot (Finset.mem_filter.mpr ⟨hj, hpj⟩)
    rw [leftTestCoefficient_eq_zero F f j hjp]
    norm_num
  rw [heq] at h
  exact h

/-- Bessel's inequality for the actual right singular basis. -/
theorem rightTestCoefficient_bessel [Nonempty Y] (F : Table X Y) (g : Y → ℝ) (I : Finset Y) :
    (∑ j ∈ I, rightTestCoefficient F g j ^ 2) ≤ average (fun y => g y ^ 2) := by
  have hp (j : Y) : inner ℝ (rightSingularBasis F j) (probabilityVector g) =
      rightTestCoefficient F g j := (probability_pairing_vector (rightSingularBasis F j) g).symm
  have h := (rightSingularBasis F).orthonormal.sum_inner_products_le
    (s := I) (probabilityVector g)
  simpa only [Real.norm_eq_abs, sq_abs, hp, probabilityVector_norm_sq] using h

/-- An actual selected part of the normalized singular expansion. -/
def spectralPart (F : Table X Y) (I : Finset Y) : Table X Y :=
  fun x y => ∑ j ∈ I, normalizedSingularCoefficient F j *
    normalizedLeftFunction F j x * normalizedRightFunction F j y

/-- Pulling a constant out of the right side of a uniform average. -/
theorem average_mul_right {α : Type*} [Fintype α] (f : α → ℝ) (c : ℝ) :
    average (fun a => f a * c) = average f * c := by
  unfold average
  rw [← Finset.sum_mul]
  ring

/-- Pairing a selected spectral part with a product test gives the actual singular coefficient pairing. -/
theorem spectralPart_pairing (F : Table X Y) (I : Finset Y) (f : X → ℝ) (g : Y → ℝ) :
    pairing (spectralPart F I) (fun x y => f x * g y) =
      ∑ j ∈ I, normalizedSingularCoefficient F j * leftTestCoefficient F f j * rightTestCoefficient F g j := by
  unfold pairing spectralPart
  simp only [Finset.sum_mul, average_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = average (fun x => average (fun y => normalizedSingularCoefficient F j *
        ((normalizedLeftFunction F j x * f x) * (normalizedRightFunction F j y * g y)))) := by
      apply average_congr
      intro x
      apply average_congr
      intro y
      ring
    _ = _ := by
      simp only [average_smul]
      rw [average_mul_right]
      unfold leftTestCoefficient rightTestCoefficient
      ring

/-- A uniform bound on the actual selected singular coefficients gives the probability-normalized operator bound. -/
theorem spectralPart_pairing_sq_le [Nonempty X] [Nonempty Y]
    (F : Table X Y) (I : Finset Y) (f : X → ℝ) (g : Y → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hσ : ∀ j ∈ I, normalizedSingularCoefficient F j ≤ M) :
    pairing (spectralPart F I) (fun x y => f x * g y) ^ 2 ≤
      M ^ 2 * average (fun x => f x ^ 2) * average (fun y => g y ^ 2) := by
  rw [spectralPart_pairing]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq I
    (fun j => normalizedSingularCoefficient F j * leftTestCoefficient F f j)
    (rightTestCoefficient F g)
  have hfirst : (∑ j ∈ I, (normalizedSingularCoefficient F j * leftTestCoefficient F f j) ^ 2) ≤
      M ^ 2 * average (fun x => f x ^ 2) := by
    calc
      _ = ∑ j ∈ I, normalizedSingularCoefficient F j ^ 2 * leftTestCoefficient F f j ^ 2 := by
        simp only [mul_pow]
      _ ≤ ∑ j ∈ I, M ^ 2 * leftTestCoefficient F f j ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact (sq_le_sq₀ (normalizedSingularCoefficient_nonneg F j) hM).mpr (hσ j hj)
      _ = M ^ 2 * ∑ j ∈ I, leftTestCoefficient F f j ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (leftTestCoefficient_bessel F f I) (sq_nonneg _)
  have hsecond := rightTestCoefficient_bessel F g I
  have hp := mul_le_mul hfirst hsecond (Finset.sum_nonneg fun j _ => sq_nonneg _)
    (mul_nonneg (sq_nonneg M) (average_nonneg fun x => sq_nonneg (f x)))
  exact hcs.trans hp

/-- Root form of the actual selected-part operator bound. -/
theorem spectralPart_pairing_abs_le [Nonempty X] [Nonempty Y]
    (F : Table X Y) (I : Finset Y) (f : X → ℝ) (g : Y → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hσ : ∀ j ∈ I, normalizedSingularCoefficient F j ≤ M) :
    |pairing (spectralPart F I) (fun x y => f x * g y)| ≤
      M * Real.sqrt (average (fun x => f x ^ 2)) * Real.sqrt (average (fun y => g y ^ 2)) := by
  calc
    _ ≤ Real.sqrt (M ^ 2 * average (fun x => f x ^ 2) * average (fun y => g y ^ 2)) :=
      Real.abs_le_sqrt (spectralPart_pairing_sq_le F I f g hM hσ)
    _ = _ := by
      rw [Real.sqrt_mul (mul_nonneg (sq_nonneg M) (average_nonneg fun x => sq_nonneg (f x))),
        Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM]

/-- Discarded singular directions, including zero directions when beta ≥ 0. -/
def discardedDirections (F : Table X Y) (beta : ℝ) : Finset Y :=
  Finset.univ.filter fun j => normalizedSingularCoefficient F j ≤ beta

/-- The actual discarded table is F minus its actual strict spectral truncation. -/
theorem discarded_spectralPart [Nonempty X] [Nonempty Y]
    (F : Table X Y) (beta : ℝ) (x : X) (y : Y) :
    spectralPart F (discardedDirections F beta) x y = F x y - spectralTruncation F beta x y := by
  have hsum := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j => beta < normalizedSingularCoefficient F j)
    (fun j => normalizedSingularCoefficient F j * normalizedLeftFunction F j x * normalizedRightFunction F j y)
  rw [← normalized_singular_expansion F x y] at hsum
  rw [spectralTruncation_normalized_expansion]
  simp only [not_lt] at hsum
  unfold spectralPart discardedDirections retainedDirections
  linarith

/-- The largest singular coefficient of the actual discarded table is at most beta, expressed directly as its product-test operator bound. -/
theorem discarded_pairing_abs_le [Nonempty X] [Nonempty Y]
    (F : Table X Y) {beta : ℝ} (hbeta : 0 ≤ beta) (f : X → ℝ) (g : Y → ℝ) :
    |pairing (fun x y => F x y - spectralTruncation F beta x y) (fun x y => f x * g y)| ≤
      beta * Real.sqrt (average (fun x => f x ^ 2)) * Real.sqrt (average (fun y => g y ^ 2)) := by
  have ht : (fun x y => F x y - spectralTruncation F beta x y) =
      spectralPart F (discardedDirections F beta) := by
    funext x y
    exact (discarded_spectralPart F beta x y).symm
  rw [ht]
  exact spectralPart_pairing_abs_le F _ f g hbeta fun j hj => (Finset.mem_filter.mp hj).2

/-- Weighted left singular functions have diagonal covariance even when zero directions are present. -/
theorem weightedLeftFunction_inner [Nonempty X]
    (F : Table X Y) (i j : Y) :
    average (fun x => (normalizedSingularCoefficient F i * normalizedLeftFunction F i x) *
      (normalizedSingularCoefficient F j * normalizedLeftFunction F j x)) =
        if i = j then normalizedSingularCoefficient F i ^ 2 else 0 := by
  have hp : average (fun x => (normalizedSingularCoefficient F i * normalizedLeftFunction F i x) *
      (normalizedSingularCoefficient F j * normalizedLeftFunction F j x)) =
      (normalizedSingularCoefficient F i * normalizedSingularCoefficient F j) *
        average (fun x => normalizedLeftFunction F i x * normalizedLeftFunction F j x) := by
    rw [← average_smul]
    apply average_congr
    intro x
    ring
  rw [hp]
  by_cases hi : 0 < rightEigenvalue F i
  · by_cases hj : 0 < rightEigenvalue F j
    · have hon := normalizedLeftFunction_orthonormal F (⟨i, hi⟩ : PositiveDirection F) ⟨j, hj⟩
      rw [hon]
      by_cases hij : i = j
      · subst j
        simp
        ring
      · have hv : (⟨i, hi⟩ : PositiveDirection F) ≠ ⟨j, hj⟩ := fun h => hij (congrArg Subtype.val h)
        simp [hij, hv]
    · have hz : rightEigenvalue F j = 0 := le_antisymm (le_of_not_gt hj) (rightEigenvalue_nonneg F j)
      have hne : i ≠ j := by intro hij; subst j; linarith
      simp [normalizedSingularCoefficient, hz, hne]
  · have hz : rightEigenvalue F i = 0 := le_antisymm (le_of_not_gt hi) (rightEigenvalue_nonneg F i)
    simp [normalizedSingularCoefficient, hz]

/-- Exact normalized column Gram expansion of any actual selected spectral part. -/
theorem spectralPart_column_gram [Nonempty X]
    (F : Table X Y) (I : Finset Y) (y₁ y₂ : Y) :
    average (fun x => spectralPart F I x y₁ * spectralPart F I x y₂) =
      ∑ j ∈ I, normalizedSingularCoefficient F j ^ 2 *
        normalizedRightFunction F j y₁ * normalizedRightFunction F j y₂ := by
  have hp (i j : Y) : average (fun x =>
      (normalizedSingularCoefficient F i * normalizedLeftFunction F i x * normalizedRightFunction F i y₁) *
      (normalizedSingularCoefficient F j * normalizedLeftFunction F j x * normalizedRightFunction F j y₂)) =
      (normalizedRightFunction F i y₁ * normalizedRightFunction F j y₂) *
        (if i = j then normalizedSingularCoefficient F i ^ 2 else 0) := by
    rw [← weightedLeftFunction_inner, ← average_smul]
    apply average_congr
    intro x
    ring
  unfold spectralPart
  simp only [Finset.sum_mul, Finset.mul_sum, average_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [hp]
  rw [Finset.sum_eq_single i]
  · simp
    ring
  · intro j hj hji
    simp [hji]
  · exact fun hn => False.elim (hn hi)

/-- Parseval for any finite linear combination of the actual normalized right singular functions. -/
theorem normalizedRightFunction_combination_sq [Nonempty Y]
    (F : Table X Y) (I : Finset Y) (c : Y → ℝ) :
    average (fun y => (∑ j ∈ I, c j * normalizedRightFunction F j y) ^ 2) = ∑ j ∈ I, c j ^ 2 := by
  have hp (i j : Y) : average (fun y =>
      (c i * normalizedRightFunction F i y) * (c j * normalizedRightFunction F j y)) =
      (c i * c j) * (if i = j then 1 else 0) := by
    rw [← normalizedRightFunction_orthonormal F i j, ← average_smul]
    apply average_congr
    intro y
    ring
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, average_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [hp]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · exact fun hn => False.elim (hn hi)

/-- Exact normalized squared L₂ norm of an actual selected spectral part. -/
theorem spectralPart_normSq [Nonempty X] [Nonempty Y]
    (F : Table X Y) (I : Finset Y) :
    normSq (spectralPart F I) = ∑ j ∈ I, normalizedSingularCoefficient F j ^ 2 := by
  unfold normSq pairing
  rw [average_comm]
  simp_rw [spectralPart_column_gram]
  rw [average_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hu := normalizedRightFunction_orthonormal F j j
  simp only [ite_true, ← pow_two] at hu
  calc
    _ = normalizedSingularCoefficient F j ^ 2 *
        average (fun y => normalizedRightFunction F j y ^ 2) := by
      rw [← average_smul]
      apply average_congr
      intro y
      ring
    _ = _ := by rw [hu, mul_one]

/-- Exact four-cycle identity for an actual selected spectral part. -/
theorem spectralPart_fourCycle [Nonempty X] [Nonempty Y]
    (F : Table X Y) (I : Finset Y) :
    fourCycle (spectralPart F I) = ∑ j ∈ I, normalizedSingularCoefficient F j ^ 4 := by
  rw [fourCycle_column_gram]
  simp_rw [spectralPart_column_gram]
  simp_rw [normalizedRightFunction_combination_sq]
  rw [average_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hu := normalizedRightFunction_orthonormal F j j
  simp only [ite_true, ← pow_two] at hu
  calc
    _ = normalizedSingularCoefficient F j ^ 4 *
        average (fun y => normalizedRightFunction F j y ^ 2) := by
      rw [← average_smul]
      apply average_congr
      intro y
      ring
    _ = _ := by rw [hu, mul_one]

/-- The actual spectral fourth moment is bounded by the squared largest selected coefficient times the actual L₂ squared norm. -/
theorem spectralPart_fourCycle_le [Nonempty X] [Nonempty Y]
    (F : Table X Y) (I : Finset Y) {M : ℝ} (hM : 0 ≤ M)
    (hσ : ∀ j ∈ I, normalizedSingularCoefficient F j ≤ M) :
    fourCycle (spectralPart F I) ≤ M ^ 2 * normSq (spectralPart F I) := by
  rw [spectralPart_fourCycle, spectralPart_normSq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hs := (sq_le_sq₀ (normalizedSingularCoefficient_nonneg F j) hM).mpr (hσ j hj)
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (normalizedSingularCoefficient F j))
  nlinarith

/-- In particular, the actual discarded table has four-cycle moment at most beta² times its actual L₂ squared norm. -/
theorem discarded_fourCycle_le [Nonempty X] [Nonempty Y]
    (F : Table X Y) {beta : ℝ} (hbeta : 0 ≤ beta) :
    fourCycle (fun x y => F x y - spectralTruncation F beta x y) ≤
      beta ^ 2 * normSq (fun x y => F x y - spectralTruncation F beta x y) := by
  have ht : (fun x y => F x y - spectralTruncation F beta x y) =
      spectralPart F (discardedDirections F beta) := by
    funext x y
    exact (discarded_spectralPart F beta x y).symm
  rw [ht]
  exact spectralPart_fourCycle_le F _ hbeta fun j hj => (Finset.mem_filter.mp hj).2

/-- The actual largest probability-normalized singular coefficient. -/
def largestSingularCoefficient [Nonempty Y] (F : Table X Y) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (normalizedSingularCoefficient F)

/-- Every probability-normalized singular coefficient is at most the largest such coefficient. -/
theorem normalizedSingularCoefficient_le_largest [Nonempty Y] (F : Table X Y) (j : Y) :
    normalizedSingularCoefficient F j ≤ largestSingularCoefficient F :=
  Finset.le_sup' (normalizedSingularCoefficient F) (Finset.mem_univ j)

/-- The largest probability-normalized singular coefficient is nonnegative. -/
theorem largestSingularCoefficient_nonneg [Nonempty Y] (F : Table X Y) :
    0 ≤ largestSingularCoefficient F := by
  let j : Y := Classical.choice ‹Nonempty Y›
  exact (normalizedSingularCoefficient_nonneg F j).trans (normalizedSingularCoefficient_le_largest F j)

/-- The complete selected part is the actual original table. -/
theorem spectralPart_univ [Nonempty X] [Nonempty Y] (F : Table X Y) :
    spectralPart F Finset.univ = F := by
  funext x y
  exact (normalized_singular_expansion F x y).symm

/-- The four-cycle/singular-maximum inequality for every actual finite real table. -/
theorem fourCycle_le_largest_sq_mul_normSq [Nonempty X] [Nonempty Y] (F : Table X Y) :
    fourCycle F ≤ largestSingularCoefficient F ^ 2 * normSq F := by
  have h := spectralPart_fourCycle_le F Finset.univ (largestSingularCoefficient_nonneg F)
    (fun j _ => normalizedSingularCoefficient_le_largest F j)
  simpa only [spectralPart_univ] using h

/-- Testing a positive singular direction against its two unit singular functions recovers the actual normalized singular coefficient. -/
theorem pairing_singular_functions [Nonempty X] [Nonempty Y]
    (F : Table X Y) (j : Y) (hj : 0 < rightEigenvalue F j) :
    pairing F (fun x y => normalizedLeftFunction F j x * normalizedRightFunction F j y) =
      normalizedSingularCoefficient F j := by
  have hp := spectralPart_pairing F Finset.univ (normalizedLeftFunction F j) (normalizedRightFunction F j)
  rw [spectralPart_univ] at hp
  rw [hp]
  have hr (k : Y) : rightTestCoefficient F (normalizedRightFunction F j) k =
      if k = j then 1 else 0 := normalizedRightFunction_orthonormal F k j
  have hl : leftTestCoefficient F (normalizedLeftFunction F j) j = 1 := by
    simpa only [leftTestCoefficient, ite_true] using
      normalizedLeftFunction_orthonormal F (⟨j, hj⟩ : PositiveDirection F) ⟨j, hj⟩
  simp_rw [hr]
  rw [Finset.sum_eq_single j]
  · simp [hl]
  · intro k hk hkj
    simp [hkj]
  · exact fun hn => False.elim (hn (Finset.mem_univ j))

/-- Product-test operator bounds control every actual singular coefficient. This is the direction needed for the residual's singular-maximum estimate. -/
theorem singularCoefficient_le_of_unit_product_pairings [Nonempty X] [Nonempty Y]
    (F : Table X Y) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ (f : X → ℝ) (g : Y → ℝ),
      average (fun x => f x ^ 2) ≤ 1 → average (fun y => g y ^ 2) ≤ 1 →
      |pairing F (fun x y => f x * g y)| ≤ M) (j : Y) :
    normalizedSingularCoefficient F j ≤ M := by
  by_cases hj : 0 < rightEigenvalue F j
  · have hl : average (fun x => normalizedLeftFunction F j x ^ 2) = 1 := by
      simpa only [ite_true, ← pow_two] using
        normalizedLeftFunction_orthonormal F (⟨j, hj⟩ : PositiveDirection F) ⟨j, hj⟩
    have hr : average (fun y => normalizedRightFunction F j y ^ 2) = 1 := by
      simpa only [ite_true, ← pow_two] using normalizedRightFunction_orthonormal F j j
    have ht := h (normalizedLeftFunction F j) (normalizedRightFunction F j) (le_of_eq hl) (le_of_eq hr)
    rw [pairing_singular_functions F j hj,
      abs_of_nonneg (normalizedSingularCoefficient_nonneg F j)] at ht
    exact ht
  · have hz : rightEigenvalue F j = 0 := le_antisymm (le_of_not_gt hj) (rightEigenvalue_nonneg F j)
    simpa only [normalizedSingularCoefficient, hz, Real.sqrt_zero, zero_div] using hM

/-- Any unit-product operator bound gives the actual four-cycle estimate; no unproved relation between operator norm and singular coefficients is used. -/
theorem fourCycle_le_of_unit_product_pairings [Nonempty X] [Nonempty Y]
    (F : Table X Y) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ (f : X → ℝ) (g : Y → ℝ),
      average (fun x => f x ^ 2) ≤ 1 → average (fun y => g y ^ 2) ≤ 1 →
      |pairing F (fun x y => f x * g y)| ≤ M) :
    fourCycle F ≤ M ^ 2 * normSq F := by
  have hb := spectralPart_fourCycle_le F Finset.univ hM
    (fun j _ => singularCoefficient_le_of_unit_product_pairings F hM h j)
  simpa only [spectralPart_univ] using hb

omit [DecidableEq Y] in
/-- The inner product with an actual coordinate projection equals its squared norm; this supplies the truncation orthogonality in the residual identity. -/
theorem coordinateProjection_inner_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : OrthonormalBasis Y ℝ E) (I : Finset Y) (z : E) :
    inner ℝ z (coordinateProjection b I z) = ‖coordinateProjection b I z‖ ^ 2 := by
  rw [coordinateProjection_norm_sq]
  unfold coordinateProjection
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [inner_smul_right, real_inner_comm z (b j)]
  ring

/-- The actual spectral truncation satisfies the exact orthogonal-projection pairing needed by `residual_identity`; no orthogonality hypothesis is assumed. -/
theorem pairing_spectralTruncation_eq_normSq (F : Table X Y) (beta : ℝ) :
    pairing F (spectralTruncation F beta) = normSq (spectralTruncation F beta) := by
  unfold normSq pairing
  apply average_congr
  intro x
  have h := coordinateProjection_inner_self (rightSingularBasis F)
    (retainedDirections F beta) (euclideanRow F x)
  rw [EuclideanSpace.real_norm_sq_eq] at h
  have hs : (∑ y, F x y * spectralTruncation F beta x y) =
      ∑ y, spectralTruncation F beta x y * spectralTruncation F beta x y := by
    simpa only [real_euclidean_inner, dotProduct,
      euclideanRow, PiLp.toLp_apply, spectralTruncation, pow_two] using h
  exact congrArg (fun r : ℝ => (Fintype.card Y : ℝ)⁻¹ * r) hs

/-- The exact actual-table L₂ coefficient identity. -/
theorem normSq_eq_sum_singular_sq [Nonempty X] [Nonempty Y] (F : Table X Y) :
    normSq F = ∑ j : Y, normalizedSingularCoefficient F j ^ 2 := by
  have h := spectralPart_normSq F Finset.univ
  simpa only [spectralPart_univ] using h

/-- The exact actual-table four-cycle coefficient identity. -/
theorem fourCycle_eq_sum_singular_fourth [Nonempty X] [Nonempty Y] (F : Table X Y) :
    fourCycle F = ∑ j : Y, normalizedSingularCoefficient F j ^ 4 := by
  have h := spectralPart_fourCycle F Finset.univ
  simpa only [spectralPart_univ] using h

end RefreshingProof.Local
