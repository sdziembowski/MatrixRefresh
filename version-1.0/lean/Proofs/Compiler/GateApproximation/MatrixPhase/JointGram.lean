import Proofs.Compiler.GateApproximation.MatrixPhase.JointMixing
import Proofs.Compiler.GateApproximation.MatrixPhase.JointTwisted



/-!
# Complex feature-Gram variance on the actual joint-port graph

The feature family need not be orthogonal. Each complex Gram entry is treated using the actual heterogeneous scalar variance, then all entries are summed.
-/

set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace CircuitCompiler

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {X : Type*} [Fintype X]

/-- Uniform finite average of a complex-valued function. -/
/-
Mathematical definition (normal notation): For f ∈ X → ℂ, define

complexAverage(f) := (|X|)⁻¹ · ∑ₓ (f(x)).
-/
def complexAverage (f : X → ℂ) : ℂ := (Fintype.card X : ℝ)⁻¹ • ∑ x, f x

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ X → ℂ, we have

re(complexAverage(f)) = 𝔼ₓ [re(f(x))].
-/
lemma complexAverage_re (f : X → ℂ) : (complexAverage f).re = uavg (fun x => (f x).re) := by
  simp [complexAverage, uavg]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ X → ℂ, we have

im(complexAverage(f)) = 𝔼ₓ [im(f(x))].
-/
lemma complexAverage_im (f : X → ℂ) : (complexAverage f).im = uavg (fun x => (f x).im) := by
  simp [complexAverage, uavg]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For z ∈ ℂ, we have

(‖ z‖)² = (z.re)² + (z.im)².
-/
lemma complex_norm_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, pow_two]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- The exact collision/mixing coefficient for the two old input shares. -/
/-
Mathematical definition (normal notation): For F a set; n ∈ ℕ, assume F is a field; F is finite. define

jointVarianceCoefficient(n) := (|F| - 1)² / (|U(F, n)|)² + mixingCoefficient(F, (n · n)).
-/
def jointVarianceCoefficient (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) : ℝ :=
  ((fieldCard F - 1 : ℕ) : ℝ) ^ 2 / (Fintype.card (U F n) : ℝ) ^ 2 +
    mixingCoefficient F (n * n)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

0 ≤ jointVarianceCoefficient(F, n).
-/
lemma jointVarianceCoefficient_nonneg (hn : 2 ≤ n) : 0 ≤ jointVarianceCoefficient F n := by
  apply add_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
  apply mixingCoefficient_nonneg
  nlinarith

/-- The exact coefficient is `O_q(N⁻²)`, with an explicit field-only constant. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

jointVarianceCoefficient(F, n) ≤ (4 · (|F| - 1)² + 2 · (|F| - 1)) / (|F|ⁿ)².
-/
theorem jointVarianceCoefficient_le (hn : 2 ≤ n) :
    jointVarianceCoefficient F n ≤
      (4 * ((fieldCard F : ℝ) - 1) ^ 2 + 2 * ((fieldCard F : ℝ) - 1)) / (vectorCard F n : ℝ) ^ 2 := by
  have hq := fieldCard_cast_ge_two (F := F)
  have hN := vectorCard_real_ge_four (F := F) hn
  have hdim : 2 ≤ n * n := by nlinarith
  have hQq := vectorCard_real_ge_two_mul_fieldCard (F := F) hdim
  have hpow : vectorCard F n ^ 2 ≤ vectorCard F (n * n) := by
    unfold vectorCard
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by have := fieldCard_ge_two (F := F); omega) (by nlinarith)
  have hQ : (vectorCard F n : ℝ) ^ 2 ≤ (vectorCard F (n * n) : ℝ) := by exact_mod_cast hpow
  have hNsq : 0 < (vectorCard F n : ℝ) ^ 2 := sq_pos_of_pos (by linarith)
  have hNm : 0 < ((vectorCard F n : ℝ) - 1) ^ 2 := sq_pos_of_pos (by linarith)
  have hQm : 0 < (vectorCard F (n * n) : ℝ) - (fieldCard F : ℝ) := by nlinarith
  have h₁ : ((fieldCard F : ℝ) - 1) ^ 2 / ((vectorCard F n : ℝ) - 1) ^ 2 ≤
      4 * ((fieldCard F : ℝ) - 1) ^ 2 / (vectorCard F n : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ hNm hNsq).2
    have hd : (vectorCard F n : ℝ) ^ 2 ≤ 4 * ((vectorCard F n : ℝ) - 1) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hd (sq_nonneg ((fieldCard F : ℝ) - 1))]
  have h₂ : ((fieldCard F : ℝ) - 1) / ((vectorCard F (n * n) : ℝ) - (fieldCard F : ℝ)) ≤
      2 * ((fieldCard F : ℝ) - 1) / (vectorCard F n : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ hQm hNsq).2
    have hd : (vectorCard F n : ℝ) ^ 2 ≤ 2 * ((vectorCard F (n * n) : ℝ) - (fieldCard F : ℝ)) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hd (by linarith : 0 ≤ (fieldCard F : ℝ) - 1)]
  unfold jointVarianceCoefficient mixingCoefficient
  rw [card_U_real, Nat.cast_sub (by have := fieldCard_ge_two (F := F); omega), Nat.cast_one]
  exact (add_le_add h₁ h₂).trans_eq (by rw [add_div])

/-- Real and imaginary parts combine without an extra factor in the variance. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → ℂ, assume 2 ≤ n. Then

𝔼_(M ∈ GL_(n · n)(F)) [(‖ complexAverage(((x ↦ f(x, rowRefresh(inputTensor(x), M))))) - complexAverage(((x ↦ complexAverage(f(x)))))‖)²] ≤ jointVarianceCoefficient(F, n) · 𝔼ₓ [𝔼ᵤ [(‖ f(x, u)‖)²]].
-/
theorem joint_tensor_complex_row_variance (hn : 2 ≤ n)
    (f : (U F n × U F n) → U F (n * n) → ℂ) :
    uavg (fun M : Refresh.«GL» F (n * n) =>
      ‖complexAverage (fun x => f x (rowRefresh (inputTensor x) M)) -
        complexAverage (fun x => complexAverage (f x))‖ ^ 2) ≤
      jointVarianceCoefficient F n * uavg (fun x => uavg (fun u => ‖f x u‖ ^ 2)) := by
  have hr := joint_tensor_row_variance hn (fun x u => (f x u).re)
  have hi := joint_tensor_row_variance hn (fun x u => (f x u).im)
  simp only [complex_norm_sq, Complex.sub_re, Complex.sub_im, complexAverage_re,
    complexAverage_im, uavg_add]
  change _ ≤ jointVarianceCoefficient F n * _ at hr hi
  nlinarith

/-- The right new share is sampled by the inverse matrix; the same variance holds because inverse transpose permutes the general linear group. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → ℂ, assume 2 ≤ n. Then

𝔼_(M ∈ GL_(n · n)(F)) [(‖ complexAverage(((x ↦ f(x, columnRefresh(inputTensor(x), M))))) - complexAverage(((x ↦ complexAverage(f(x)))))‖)²] ≤ jointVarianceCoefficient(F, n) · 𝔼ₓ [𝔼ᵤ [(‖ f(x, u)‖)²]].
-/
theorem joint_tensor_complex_column_variance (hn : 2 ≤ n)
    (f : (U F n × U F n) → U F (n * n) → ℂ) :
    uavg (fun M : Refresh.«GL» F (n * n) =>
      ‖complexAverage (fun x => f x (columnRefresh (inputTensor x) M)) -
        complexAverage (fun x => complexAverage (f x))‖ ^ 2) ≤
      jointVarianceCoefficient F n * uavg (fun x => uavg (fun u => ‖f x u‖ ^ 2)) := by
  simp_rw [columnRefresh_eq_rowRefresh]
  rw [uavg_equiv inverseTransposeEquiv (fun M =>
    ‖complexAverage (fun x => f x (rowRefresh (inputTensor x) M)) -
      complexAverage (fun x => complexAverage (f x))‖ ^ 2)]
  exact joint_tensor_complex_row_variance hn f

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Y a set; f ∈ X → Y → ℂ, assume Y is finite. Then

complexAverage(((x ↦ complexAverage(f(x))))) = complexAverage(((y ↦ complexAverage(((x ↦ f(x, y))))))).
-/
lemma complexAverage_comm {Y : Type*} [Fintype Y] (f : X → Y → ℂ) :
    complexAverage (fun x => complexAverage (f x)) =
      complexAverage (fun y => complexAverage (fun x => f x y)) := by
  apply Complex.ext
  · simp only [complexAverage_re]
    exact uavg_comm _
  · simp only [complexAverage_im]
    exact uavg_comm _

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ U(F, n); f ∈ U(F, n) → ℂ, we have

complexAverage(((M ∈ GLₙ(F) ↦ f(rowRefresh(a, M))))) = complexAverage(f).
-/
lemma complexAverage_random_rowRefresh (a : U F n) (f : U F n → ℂ) :
    complexAverage (fun M : Refresh.«GL» F n => f (rowRefresh a M)) = complexAverage f := by
  apply Complex.ext
  · simp only [complexAverage_re]
    exact uavg_random_rowRefresh a (fun x => (f x).re)
  · simp only [complexAverage_im]
    exact uavg_random_rowRefresh a (fun x => (f x).im)

variable {P : Type*} [Fintype P]

/-- Pointwise sum of squared norms of all features. -/
/-
Mathematical definition (normal notation): For ξ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; x ∈ U(F, n) × U(F, n); u ∈ U(F, (n · n)), define

jointFeatureEnergy(ξ, x, u) := ∑ₚ ((‖ ξ(x, u, p)‖)²).
-/
def jointFeatureEnergy (ξ : (U F n × U F n) → U F (n * n) → P → ℂ)
    (x : U F n × U F n) (u : U F (n * n)) : ℝ := ∑ p, ‖ξ x u p‖ ^ 2

/-- Gram matrix under the product reference distribution. -/
/-
Mathematical definition (normal notation): For ξ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ, define

jointMeanGram(ξ) := (p, q ↦ complexAverage(((x ↦ complexAverage(((u ↦ star(ξ(x, u, p)) · ξ(x, u, q)))))))).
-/
def jointMeanGram (ξ : (U F n × U F n) → U F (n * n) → P → ℂ) : Matrix P P ℂ :=
  fun p q => complexAverage (fun x => complexAverage (fun u => star (ξ x u p) * ξ x u q))

/-- Gram matrix after restricting the new share to `a(X)M`. -/
/-
Mathematical definition (normal notation): For ξ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; M ∈ GL_(n · n)(F), define

jointRowGram(ξ, M) := (p, q ↦ complexAverage(((x ↦ star(ξ(x, rowRefresh(inputTensor(x), M), p)) · ξ(x, rowRefresh(inputTensor(x), M), q))))).
-/
def jointRowGram (ξ : (U F n × U F n) → U F (n * n) → P → ℂ)
    (M : Refresh.«GL» F (n * n)) : Matrix P P ℂ :=
  fun p q => complexAverage (fun x =>
    star (ξ x (rowRefresh (inputTensor x) M) p) * ξ x (rowRefresh (inputTensor x) M) q)

/-- The average restricted Gram is exactly the Gram matrix for the product distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; p, q ∈ P, we have

complexAverage(((M ↦ jointRowGram(ξ, M, p, q)))) = jointMeanGram(ξ, p, q).
-/
theorem jointRowGram_expect (ξ : (U F n × U F n) → U F (n * n) → P → ℂ) (p q : P) :
    complexAverage (fun M => jointRowGram ξ M p q) = jointMeanGram ξ p q := by
  unfold jointRowGram jointMeanGram
  rw [complexAverage_comm]
  congr 1
  funext x
  exact complexAverage_random_rowRefresh (inputTensor x) (fun u => star (ξ x u p) * ξ x u q)

/-- The right feature Gram uses the actual inverse-column refresh. -/
/-
Mathematical definition (normal notation): For ξ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; M ∈ GL_(n · n)(F), define

jointColumnGram(ξ, M) := (p, q ↦ complexAverage(((x ↦ star(ξ(x, columnRefresh(inputTensor(x), M), p)) · ξ(x, columnRefresh(inputTensor(x), M), q))))).
-/
def jointColumnGram (ξ : (U F n × U F n) → U F (n * n) → P → ℂ)
    (M : Refresh.«GL» F (n * n)) : Matrix P P ℂ :=
  fun p q => complexAverage (fun x =>
    star (ξ x (columnRefresh (inputTensor x) M) p) * ξ x (columnRefresh (inputTensor x) M) q)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; M ∈ GL_(n · n)(F), we have

jointColumnGram(ξ, M) = jointRowGram(ξ, inverseTransposeEquiv(M)).
-/
lemma jointColumnGram_eq_row (ξ : (U F n × U F n) → U F (n * n) → P → ℂ)
    (M : Refresh.«GL» F (n * n)) :
    jointColumnGram ξ M = jointRowGram ξ (inverseTransposeEquiv M) := by
  ext p q
  simp only [jointColumnGram, jointRowGram, columnRefresh_eq_rowRefresh]

/-- Squared counting L2 deviation: sum the squared entry magnitudes over factor indices. -/
/-
Mathematical definition (normal notation): For ξ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; M ∈ GL_(n · n)(F), define

jointRowGramDeviationSq(ξ, M) := ∑ₚ (∑_q ((‖ jointRowGram(ξ, M, p, q) - jointMeanGram(ξ, p, q)‖)²)).
-/
def jointRowGramDeviationSq (ξ : (U F n × U F n) → U F (n * n) → P → ℂ)
    (M : Refresh.«GL» F (n * n)) : ℝ :=
  ∑ p, ∑ q, ‖jointRowGram ξ M p q - jointMeanGram ξ p q‖ ^ 2

/-- The squared counting L2 norm of a rank-one Gram matrix equals the square of its factor energy. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; x ∈ U(F, n) × U(F, n); u ∈ U(F, (n · n)), we have

(jointFeatureEnergy(ξ, x, u))² = ∑ₚ (∑_q ((‖ star(ξ(x, u, p)) · ξ(x, u, q)‖)²)).
-/
lemma jointFeatureEnergy_sq (ξ : (U F n × U F n) → U F (n * n) → P → ℂ)
    (x : U F n × U F n) (u : U F (n * n)) :
    jointFeatureEnergy ξ x u ^ 2 = ∑ p, ∑ q, ‖star (ξ x u p) * ξ x u q‖ ^ 2 := by
  simp only [jointFeatureEnergy, pow_two, Finset.sum_mul, Finset.mul_sum, norm_mul, norm_star]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Actual Gram variance with no orthogonality hypothesis on extracted features. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ, assume 2 ≤ n. Then

𝔼ᵥ [jointRowGramDeviationSq(ξ, v)] ≤ jointVarianceCoefficient(F, n) · 𝔼ₓ [𝔼ᵤ [(jointFeatureEnergy(ξ, x, u))²]].
-/
theorem joint_row_Gram_variance_le (hn : 2 ≤ n)
    (ξ : (U F n × U F n) → U F (n * n) → P → ℂ) :
    uavg (jointRowGramDeviationSq ξ) ≤
      jointVarianceCoefficient F n * uavg (fun x => uavg (fun u => jointFeatureEnergy ξ x u ^ 2)) := by
  calc
    _ = ∑ p, ∑ q, uavg (fun M => ‖jointRowGram ξ M p q - jointMeanGram ξ p q‖ ^ 2) := by
      unfold jointRowGramDeviationSq
      rw [uavg_sum]
      apply Finset.sum_congr rfl
      intro p _
      exact uavg_sum _
    _ ≤ ∑ p, ∑ q, jointVarianceCoefficient F n *
        uavg (fun x => uavg (fun u => ‖star (ξ x u p) * ξ x u q‖ ^ 2)) := by
      exact Finset.sum_le_sum (fun p _ => Finset.sum_le_sum
        (fun q _ => joint_tensor_complex_row_variance hn (fun x u => star (ξ x u p) * ξ x u q)))
    _ = _ := by
      simp_rw [jointFeatureEnergy_sq, uavg_sum]
      simp only [Finset.mul_sum]

/-- Pointwise feature control turns the fourth moment into the trace budget. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; L ∈ ℝ, assume 2 ≤ n; ∀ x, u, jointFeatureEnergy(ξ, x, u) ≤ L. Then

𝔼ᵥ [jointRowGramDeviationSq(ξ, v)] ≤ jointVarianceCoefficient(F, n) · L · 𝔼ₓ [𝔼ᵤ [jointFeatureEnergy(ξ, x, u)]].
-/
theorem joint_row_Gram_variance_le_energy (hn : 2 ≤ n)
    (ξ : (U F n × U F n) → U F (n * n) → P → ℂ)
    (L : ℝ) (hL : ∀ x u, jointFeatureEnergy ξ x u ≤ L) :
    uavg (jointRowGramDeviationSq ξ) ≤ jointVarianceCoefficient F n * L *
      uavg (fun x => uavg (fun u => jointFeatureEnergy ξ x u)) := by
  apply (joint_row_Gram_variance_le hn ξ).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (jointVarianceCoefficient_nonneg hn)
  calc
    _ ≤ uavg (fun x => uavg (fun u => L * jointFeatureEnergy ξ x u)) := by
      apply uavg_mono
      intro x
      apply uavg_mono
      intro u
      have hnonneg : 0 ≤ jointFeatureEnergy ξ x u := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      nlinarith [mul_le_mul_of_nonneg_right (hL x u) hnonneg]
    _ = _ := by simp_rw [uavg_const_mul]

/-- The column Gram obeys the identical energy estimate under the same GL distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; L ∈ ℝ, assume 2 ≤ n; ∀ x, u, jointFeatureEnergy(ξ, x, u) ≤ L. Then

𝔼_M [∑ₚ (∑_q ((‖ jointColumnGram(ξ, M, p, q) - jointMeanGram(ξ, p, q)‖)²))] ≤ jointVarianceCoefficient(F, n) · L · 𝔼ₓ [𝔼ᵤ [jointFeatureEnergy(ξ, x, u)]].
-/
theorem joint_column_Gram_variance_le_energy (hn : 2 ≤ n)
    (ξ : (U F n × U F n) → U F (n * n) → P → ℂ)
    (L : ℝ) (hL : ∀ x u, jointFeatureEnergy ξ x u ≤ L) :
    uavg (fun M => ∑ p, ∑ q, ‖jointColumnGram ξ M p q - jointMeanGram ξ p q‖ ^ 2) ≤
      jointVarianceCoefficient F n * L *
        uavg (fun x => uavg (fun u => jointFeatureEnergy ξ x u)) := by
  simp_rw [jointColumnGram_eq_row]
  change uavg (fun M => jointRowGramDeviationSq ξ (inverseTransposeEquiv M)) ≤ _
  rw [uavg_equiv inverseTransposeEquiv (jointRowGramDeviationSq ξ)]
  exact joint_row_Gram_variance_le_energy hn ξ L hL

/-- Both feature Grams are controlled together with no independence assumption between their restrictions by the shared matrix. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ξ, ζ ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → P → ℂ; L ∈ ℝ, assume 2 ≤ n; ∀ x, u, jointFeatureEnergy(ξ, x, u) ≤ L; ∀ x, u, jointFeatureEnergy(ζ, x, u) ≤ L. Then

𝔼ᵥ [jointRowGramDeviationSq(ξ, v)] + 𝔼_M [∑ₚ (∑_q ((‖ jointColumnGram(ζ, M, p, q) - jointMeanGram(ζ, p, q)‖)²))] ≤ jointVarianceCoefficient(F, n) · L · (𝔼ₓ [𝔼ᵤ [jointFeatureEnergy(ξ, x, u)]] + 𝔼ₓ [𝔼ᵤ [jointFeatureEnergy(ζ, x, u)]]).
-/
theorem joint_Gram_variance_le_energy (hn : 2 ≤ n)
    (ξ ζ : (U F n × U F n) → U F (n * n) → P → ℂ)
    (L : ℝ) (hξ : ∀ x u, jointFeatureEnergy ξ x u ≤ L)
    (hζ : ∀ x u, jointFeatureEnergy ζ x u ≤ L) :
    uavg (jointRowGramDeviationSq ξ) +
      uavg (fun M => ∑ p, ∑ q, ‖jointColumnGram ζ M p q - jointMeanGram ζ p q‖ ^ 2) ≤
        jointVarianceCoefficient F n * L *
          (uavg (fun x => uavg (fun u => jointFeatureEnergy ξ x u)) +
           uavg (fun x => uavg (fun u => jointFeatureEnergy ζ x u))) := by
  have hl := joint_row_Gram_variance_le_energy hn ξ L hξ
  have hr := joint_column_Gram_variance_le_energy hn ζ L hζ
  nlinarith

end

end CircuitCompiler
