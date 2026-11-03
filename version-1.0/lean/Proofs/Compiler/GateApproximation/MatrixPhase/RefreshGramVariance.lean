import Proofs.Compiler.GateApproximation.MatrixPhase.JointGram
import Proofs.Compiler.GateApproximation.MatrixPhase.Counting



/-!
# Gram variance for injective maps to binary nonzero shares

The old input carrier and refreshed dimension are independent.  Distinct distinct binary nonzero shares are nonproportional, so the general heterogeneous covariance theorem has collision row mass one.  In particular these estimates apply to augmented tensor shares as well as ordinary refreshes.
-/
set_option autoImplicit false

set_option maxHeartbeats 1500000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {F X P : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype X] [Nonempty X] [Fintype P] {m : ℕ}

/-- Collision and independent-pair contributions to the actual GL variance. -/
/-
Mathematical definition (normal notation): The variance coefficient is

η := 1/|X|+mix(𝔽,m),

where mix is the previously defined nonzero-share mixing coefficient. The first term accounts for identical old inputs.
-/
def featureVarianceCoefficient (F X : Type*) [Fintype F] [Fintype X] (m : ℕ) : ℝ :=
  1 / (Fintype.card X : ℝ) + mixingCoefficient F m

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ m. Then

0 ≤ featureVarianceCoefficient(F, X, m).
-/
theorem featureVarianceCoefficient_nonneg (hm : 2 ≤ m) :
    0 ≤ featureVarianceCoefficient F X m :=
  add_nonneg (by positivity) (mixingCoefficient_nonneg hm)

omit [DecidableEq F] in
/-- Over a binary field, proportional nonzero vectors are equal. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u, v ∈ U(F, m), assume |F| = 2. Then

projectiveRel(u, v) ⇔ u = v.
-/
theorem binary_projectiveRel_iff (hq : fieldCard F = 2) (u v : U F m) :
    projectiveRel u v ↔ u = v := by
  constructor
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      intro h
      exact v.property (by simpa [h] using hc)
    rw [binary_nonzero_eq_one hq c hc0, one_smul] at hc
    exact (Subtype.ext hc).symm
  · rintro rfl
    exact ⟨1, by simp⟩

omit [DecidableEq F] [Nonempty X] in
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m); x ∈ X, assume |F| = 2; a is injective. Then

∑_y (projectiveIndicator(a(x), a(y))) = 1.
-/
theorem injective_feature_projective_row_sum (hq : fieldCard F = 2)
    (a : X → U F m) (ha : Function.Injective a) (x : X) :
    ∑ y, projectiveIndicator (a x) (a y) = 1 := by
  classical
  simp only [projectiveIndicator, binary_projectiveRel_iff hq, ha.eq_iff]
  simp

/-- Cardinality of the injective old features absorbs the off-diagonal term. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m), assume |F| = 2; 2 ≤ m; a is injective. Then

featureVarianceCoefficient(F, X, m) ≤ 3 / |X|.
-/
theorem featureVarianceCoefficient_le (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a : X → U F m) (ha : Function.Injective a) :
    featureVarianceCoefficient F X m ≤ 3 / (Fintype.card X : ℝ) := by
  have hD : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcard : (Fintype.card X : ℝ) ≤ (vectorCard F m : ℝ) - 1 := by
    rw [← card_U_real]
    exact_mod_cast Fintype.card_le_of_injective a ha
  have hQ := vectorCard_real_ge_four (F := F) hm
  have hden : 0 < (vectorCard F m : ℝ) - 2 := by linarith
  have hmix : mixingCoefficient F m ≤ 2 / (Fintype.card X : ℝ) := by
    unfold mixingCoefficient
    rw [hq]
    norm_num only [Nat.cast_ofNat, sub_self, zero_add, show (2 : ℝ) - 1 = 1 by norm_num]
    apply (div_le_div_iff₀ hden hD).mpr
    nlinarith
  calc
    featureVarianceCoefficient F X m ≤ 1 / (Fintype.card X : ℝ) + 2 / (Fintype.card X : ℝ) :=
      add_le_add le_rfl hmix
    _ = _ := by ring

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m); f ∈ X → U(F, m) → ℝ, assume |F| = 2; 2 ≤ m; a is injective. Then

𝔼_(M ∈ GLₘ(F)) [(𝔼ₓ [f(x, rowRefresh(a(x), M))] - 𝔼ₓ [𝔼_b [f(x, b)]])²] ≤ featureVarianceCoefficient(F, X, m) · 𝔼ₓ [𝔼ᵤ [(f(x, u))²]].
-/
theorem feature_row_variance (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a : X → U F m) (ha : Function.Injective a) (f : X → U F m → ℝ) :
    uavg (fun M : Refresh.«GL» F m =>
      (uavg (fun x => f x (rowRefresh (a x) M)) - uavg (fun x => uavg (f x))) ^ 2) ≤
      featureVarianceCoefficient F X m * uavg (fun x => uavg (fun u => f x u ^ 2)) := by
  exact heterogeneous_row_variance_uncentered hm a f 1 (by norm_num)
    (injective_feature_projective_row_sum hq a ha)

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m); f ∈ X → U(F, m) → ℂ, assume |F| = 2; 2 ≤ m; a is injective. Then

𝔼_(M ∈ GLₘ(F)) [(‖ complexAverage(((x ↦ f(x, rowRefresh(a(x), M))))) - complexAverage(((x ↦ complexAverage(f(x)))))‖)²] ≤ featureVarianceCoefficient(F, X, m) · 𝔼ₓ [𝔼ᵤ [(‖ f(x, u)‖)²]].
-/
theorem feature_complex_row_variance (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a : X → U F m) (ha : Function.Injective a) (f : X → U F m → ℂ) :
    uavg (fun M : Refresh.«GL» F m =>
      ‖complexAverage (fun x => f x (rowRefresh (a x) M)) -
        complexAverage (fun x => complexAverage (f x))‖ ^ 2) ≤
      featureVarianceCoefficient F X m * uavg (fun x => uavg (fun u => ‖f x u‖ ^ 2)) := by
  have hr := feature_row_variance hq hm a ha (fun x u => (f x u).re)
  have hi := feature_row_variance hq hm a ha (fun x u => (f x u).im)
  simp only [complex_norm_sq, Complex.sub_re, Complex.sub_im, complexAverage_re,
    complexAverage_im, uavg_add]
  nlinarith

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m); f ∈ X → U(F, m) → ℂ, assume |F| = 2; 2 ≤ m; a is injective. Then

𝔼_(M ∈ GLₘ(F)) [(‖ complexAverage(((x ↦ f(x, columnRefresh(a(x), M))))) - complexAverage(((x ↦ complexAverage(f(x)))))‖)²] ≤ featureVarianceCoefficient(F, X, m) · 𝔼ₓ [𝔼ᵤ [(‖ f(x, u)‖)²]].
-/
theorem feature_complex_column_variance (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a : X → U F m) (ha : Function.Injective a) (f : X → U F m → ℂ) :
    uavg (fun M : Refresh.«GL» F m =>
      ‖complexAverage (fun x => f x (columnRefresh (a x) M)) -
        complexAverage (fun x => complexAverage (f x))‖ ^ 2) ≤
      featureVarianceCoefficient F X m * uavg (fun x => uavg (fun u => ‖f x u‖ ^ 2)) := by
  simp_rw [columnRefresh_eq_rowRefresh]
  rw [uavg_equiv inverseTransposeEquiv (fun M =>
    ‖complexAverage (fun x => f x (rowRefresh (a x) M)) -
      complexAverage (fun x => complexAverage (f x))‖ ^ 2)]
  exact feature_complex_row_variance hq hm a ha f

/-- Pointwise sum of squared norms of all features. -/
/-
Mathematical definition (normal notation): For a family of complex coordinates ξₚ(x,u), define its pointwise energy by

e(x,u) := ∑ₚ |ξₚ(x,u)|².
-/
def featureEnergy (ξ : X → U F m → P → ℂ)
    (x : X) (u : U F m) : ℝ := ∑ p, ‖ξ x u p‖ ^ 2

/-- Gram matrix under the product reference distribution. -/
/-
Mathematical definition (normal notation): Define the reference Gram matrix by uniformly averaging over independent old data x and new nonzero share u:

G̅_(p,q) := 𝔼_(x,u) [overline(ξₚ(x,u)) · ξ_q(x,u)].
-/
def featureMeanGram (ξ : X → U F m → P → ℂ) : Matrix P P ℂ :=
  fun p q => complexAverage (fun x => complexAverage (fun u => star (ξ x u p) * ξ x u q))

/-- Gram matrix after restricting the new share to `a(X)M`. -/
/-
Mathematical definition (normal notation): For a fixed invertible matrix M, define

G^M_(p,q) := 𝔼ₓ [overline(ξₚ(x,a(x) · M)) · ξ_q(x,a(x) · M)].

The average is over the old-data carrier; the new share is determined by refreshing.
-/
def featureRowGram (a : X → U F m) (ξ : X → U F m → P → ℂ)
    (M : Refresh.«GL» F m) : Matrix P P ℂ :=
  fun p q => complexAverage (fun x =>
    star (ξ x (rowRefresh (a x) M) p) * ξ x (rowRefresh (a x) M) q)

omit [Nonempty X] [Fintype P] in
/-- The average restricted Gram is exactly the Gram matrix for the product distribution. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m); ξ ∈ X → U(F, m) → P → ℂ; p, q ∈ P, we have

complexAverage(((M ↦ featureRowGram(a, ξ, M, p, q)))) = featureMeanGram(ξ, p, q).
-/
theorem featureRowGram_expect (a : X → U F m) (ξ : X → U F m → P → ℂ) (p q : P) :
    complexAverage (fun M => featureRowGram a ξ M p q) = featureMeanGram ξ p q := by
  unfold featureRowGram featureMeanGram
  rw [complexAverage_comm]
  congr 1
  funext x
  exact complexAverage_random_rowRefresh (a x) (fun u => star (ξ x u p) * ξ x u q)

/-- The right feature Gram uses the actual inverse-column refresh. -/
/-
Mathematical definition (normal notation): For a fixed invertible matrix M, define the column-side Gram matrix by

G^M_(p,q) := 𝔼ₓ [overline(ξₚ(x,M⁻¹ · a(x))) · ξ_q(x,M⁻¹ · a(x))].
-/
def featureColumnGram (a : X → U F m) (ξ : X → U F m → P → ℂ)
    (M : Refresh.«GL» F m) : Matrix P P ℂ :=
  fun p q => complexAverage (fun x =>
    star (ξ x (columnRefresh (a x) M) p) * ξ x (columnRefresh (a x) M) q)

omit [Fintype F] [DecidableEq F] [Nonempty X] [Fintype P] in
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m); ξ ∈ X → U(F, m) → P → ℂ; M ∈ GLₘ(F), we have

featureColumnGram(a, ξ, M) = featureRowGram(a, ξ, inverseTransposeEquiv(M)).
-/
lemma featureColumnGram_eq_row (a : X → U F m) (ξ : X → U F m → P → ℂ)
    (M : Refresh.«GL» F m) :
    featureColumnGram a ξ M = featureRowGram a ξ (inverseTransposeEquiv M) := by
  ext p q
  simp only [featureColumnGram, featureRowGram, columnRefresh_eq_rowRefresh]

/-- Squared counting L2 deviation: sum the squared entry magnitudes over factor indices. -/
/-
Mathematical definition (normal notation): The squared deviation of the refreshed Gram matrix from its mean is the unnormalized sum

D(M) := ∑_(p,q) |G^M_(p,q)-G̅_(p,q)|².

This sum is over factor indices, not a uniform table average.
-/
def featureRowGramDeviationSq (a : X → U F m) (ξ : X → U F m → P → ℂ)
    (M : Refresh.«GL» F m) : ℝ :=
  ∑ p, ∑ q, ‖featureRowGram a ξ M p q - featureMeanGram ξ p q‖ ^ 2

omit [Fintype F] [DecidableEq F] [Fintype X] [Nonempty X] in
/-- The squared counting L2 norm of a rank-one Gram matrix equals the square of its factor energy. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ ∈ X → U(F, m) → P → ℂ; x ∈ X; u ∈ U(F, m), we have

(featureEnergy(ξ, x, u))² = ∑ₚ (∑_q ((‖ star(ξ(x, u, p)) · ξ(x, u, q)‖)²)).
-/
lemma featureEnergy_sq (ξ : X → U F m → P → ℂ)
    (x : X) (u : U F m) :
    featureEnergy ξ x u ^ 2 = ∑ p, ∑ q, ‖star (ξ x u p) * ξ x u q‖ ^ 2 := by
  simp only [featureEnergy, pow_two, Finset.sum_mul, Finset.mul_sum, norm_mul, norm_star]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Actual Gram variance with no orthogonality hypothesis on extracted features. -/

/-
Mathematical statement (normal notation): Work over the binary field, with m ≥ 2 and injective a:X → 𝔽₂ᵐ ∖ {0}. Let e(x,u) = ∑ₚ |ξₚ(x,u)|², let G̅ be the independently averaged Gram matrix, and let η = 1/|X|+mix(𝔽₂,m). For the row-side refresh Gram matrix,

𝔼_M [∑_(p,q) |G^M_(p,q)-G̅_(p,q)|²] ≤ η · 𝔼_(x,u) [e(x,u)²].
-/
theorem feature_row_Gram_variance_le (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a : X → U F m) (ha : Function.Injective a)
    (ξ : X → U F m → P → ℂ) :
    uavg (featureRowGramDeviationSq a ξ) ≤
      featureVarianceCoefficient F X m * uavg (fun x => uavg (fun u => featureEnergy ξ x u ^ 2)) := by
  calc
    _ = ∑ p, ∑ q, uavg (fun M => ‖featureRowGram a ξ M p q - featureMeanGram ξ p q‖ ^ 2) := by
      unfold featureRowGramDeviationSq
      rw [uavg_sum]
      apply Finset.sum_congr rfl
      intro p _
      exact uavg_sum _
    _ ≤ ∑ p, ∑ q, featureVarianceCoefficient F X m *
        uavg (fun x => uavg (fun u => ‖star (ξ x u p) * ξ x u q‖ ^ 2)) := by
      exact Finset.sum_le_sum (fun p _ => Finset.sum_le_sum
        (fun q _ => feature_complex_row_variance hq hm a ha (fun x u => star (ξ x u p) * ξ x u q)))
    _ = _ := by
      simp_rw [featureEnergy_sq, uavg_sum]
      simp only [Finset.mul_sum]

/-- Pointwise feature control turns the fourth moment into the trace budget. -/

/-
Mathematical statement (normal notation): Work over the binary field, with m ≥ 2 and injective a:X → 𝔽₂ᵐ ∖ {0}. Let e(x,u) = ∑ₚ |ξₚ(x,u)|², let G̅ be the independently averaged Gram matrix, and let η = 1/|X|+mix(𝔽₂,m). If e(x,u) ≤ L everywhere, then the row-side refresh Gram matrix satisfies

𝔼_M [∑_(p,q) |G^M_(p,q)-G̅_(p,q)|²] ≤ η · L · 𝔼_(x,u) [e(x,u)].
-/
theorem feature_row_Gram_variance_le_energy (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a : X → U F m) (ha : Function.Injective a)
    (ξ : X → U F m → P → ℂ)
    (L : ℝ) (hL : ∀ x u, featureEnergy ξ x u ≤ L) :
    uavg (featureRowGramDeviationSq a ξ) ≤ featureVarianceCoefficient F X m * L *
      uavg (fun x => uavg (fun u => featureEnergy ξ x u)) := by
  apply (feature_row_Gram_variance_le hq hm a ha ξ).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (featureVarianceCoefficient_nonneg hm)
  calc
    _ ≤ uavg (fun x => uavg (fun u => L * featureEnergy ξ x u)) := by
      apply uavg_mono
      intro x
      apply uavg_mono
      intro u
      have hnonneg : 0 ≤ featureEnergy ξ x u := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      nlinarith [mul_le_mul_of_nonneg_right (hL x u) hnonneg]
    _ = _ := by simp_rw [uavg_const_mul]

/-- The column Gram obeys the identical energy estimate under the same GL distribution. -/

/-
Mathematical statement (normal notation): Work over the binary field, with m ≥ 2 and injective a:X → 𝔽₂ᵐ ∖ {0}. Let e(x,u) = ∑ₚ |ξₚ(x,u)|², let G̅ be the independently averaged Gram matrix, and let η = 1/|X|+mix(𝔽₂,m). If e(x,u) ≤ L everywhere, then the column-side refresh Gram matrix satisfies

𝔼_M [∑_(p,q) |G^M_(p,q)-G̅_(p,q)|²] ≤ η · L · 𝔼_(x,u) [e(x,u)].
-/
theorem feature_column_Gram_variance_le_energy (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a : X → U F m) (ha : Function.Injective a)
    (ξ : X → U F m → P → ℂ)
    (L : ℝ) (hL : ∀ x u, featureEnergy ξ x u ≤ L) :
    uavg (fun M => ∑ p, ∑ q, ‖featureColumnGram a ξ M p q - featureMeanGram ξ p q‖ ^ 2) ≤
      featureVarianceCoefficient F X m * L *
        uavg (fun x => uavg (fun u => featureEnergy ξ x u)) := by
  simp_rw [featureColumnGram_eq_row]
  change uavg (fun M => featureRowGramDeviationSq a ξ (inverseTransposeEquiv M)) ≤ _
  rw [uavg_equiv inverseTransposeEquiv (featureRowGramDeviationSq a ξ)]
  exact feature_row_Gram_variance_le_energy hq hm a ha ξ L hL

end

end CircuitCompiler.RefreshAnalysis
