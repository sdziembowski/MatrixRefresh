import Proofs.Compiler.GateApproximation.MatrixPhase.JointPort
import Proofs.Compiler.Foundations.LinearAlgebra.Mixing



/-!
# Heterogeneous covariance for the joint-port feature Gram

The feature function may depend on the retained old input. We therefore bound covariance between two different centered functions, using the actual independent-pair orbit and the regular proportional relation.
-/

set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace CircuitCompiler

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- Mixed covariance of two possibly different functions under one shared GL matrix. -/
/-
Mathematical definition (normal notation): For f, g ∈ U(F, n) → ℝ; a, b ∈ U(F, n), define

rowCrossCovariance(f, g, a, b) := 𝔼_(M ∈ GLₙ(F)) [f(rowRefresh(a, M)) · g(rowRefresh(b, M))].
-/
def rowCrossCovariance (f g : U F n → ℝ) (a b : U F n) : ℝ :=
  uavg (fun M : Refresh.«GL» F n => f (rowRefresh a M) * g (rowRefresh b M))

/-- The elementary Cauchy--Schwarz/AM-GM bound on arbitrary pair covariances. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f, g ∈ U(F, n) → ℝ; a, b ∈ U(F, n), we have

|rowCrossCovariance(f, g, a, b)| ≤ (𝔼ᵤ [(f(u))²] + 𝔼ᵤ [(g(u))²]) / 2.
-/
theorem abs_rowCrossCovariance_le (f g : U F n → ℝ) (a b : U F n) :
    |rowCrossCovariance f g a b| ≤
      (uavg (fun u => f u ^ 2) + uavg (fun u => g u ^ 2)) / 2 := by
  have h := uavg_mul_sq_le
    (fun M : Refresh.«GL» F n => f (rowRefresh a M))
    (fun M : Refresh.«GL» F n => g (rowRefresh b M))
  rw [uavg_random_rowRefresh a (fun u => f u ^ 2),
    uavg_random_rowRefresh b (fun u => g u ^ 2)] at h
  change rowCrossCovariance f g a b ^ 2 ≤ _ at h
  have hf := uavg_nonneg (fun u => sq_nonneg (f u))
  have hg := uavg_nonneg (fun u => sq_nonneg (g u))
  have habs := sq_abs (rowCrossCovariance f g a b)
  nlinarith [sq_nonneg (uavg (fun u => f u ^ 2) - uavg (fun u => g u ^ 2)),
    abs_nonneg (rowCrossCovariance f g a b)]

/-- Simultaneous input rotation preserves the mixed covariance. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f, g ∈ U(F, n) → ℝ; a, b ∈ U(F, n); A ∈ GLₙ(F), we have

rowCrossCovariance(f, g, rowRefresh(a, A), rowRefresh(b, A)) = rowCrossCovariance(f, g, a, b).
-/
lemma rowCrossCovariance_refresh (f g : U F n → ℝ) (a b : U F n) (A : Refresh.«GL» F n) :
    rowCrossCovariance f g (rowRefresh a A) (rowRefresh b A) =
      rowCrossCovariance f g a b := by
  unfold rowCrossCovariance
  simp_rw [rowRefresh_mul]
  exact uavg_mulLeft A (fun M => f (rowRefresh a M) * g (rowRefresh b M))

/-- Independent old pairs have identical mixed covariances. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f, g ∈ U(F, n) → ℝ; a, b, a', b' ∈ U(F, n), assume ¬ (projectiveRel(a, b)); ¬ (projectiveRel(a', b')). Then

rowCrossCovariance(f, g, a, b) = rowCrossCovariance(f, g, a', b').
-/
lemma rowCrossCovariance_independent_eq (f g : U F n → ℝ)
    (a b a' b' : U F n) (hab : ¬ projectiveRel a b) (hab' : ¬ projectiveRel a' b') :
    rowCrossCovariance f g a b = rowCrossCovariance f g a' b' := by
  obtain ⟨M, ha, hb⟩ := exists_rowRefresh_pair_eq a b a' b'
    (pair_independent_of_not_projectiveRel a b hab)
    (pair_independent_of_not_projectiveRel a' b' hab')
  simpa only [ha, hb] using (rowCrossCovariance_refresh f g a b M).symm

/-- Centering the second function makes every covariance row sum zero. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f, g ∈ U(F, n) → ℝ; a ∈ U(F, n), assume 𝔼ᵤ [g(u)] = 0. Then

𝔼_b [rowCrossCovariance(f, g, a, b)] = 0.
-/
lemma rowCrossCovariance_row_mean_zero (f g : U F n → ℝ) (hg : uavg g = 0) (a : U F n) :
    uavg (fun b => rowCrossCovariance f g a b) = 0 := by
  unfold rowCrossCovariance
  rw [uavg_comm]
  simp_rw [uavg_const_mul, uavg_rowRefresh, hg, mul_zero]
  exact uavg_zero

/-- Away from the proportional relation the covariance has the sharper `(q−1)/(Q−q)` factor. No orthogonality between `f` and `g` is assumed. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f, g ∈ U(F, n) → ℝ; a, b ∈ U(F, n), assume 2 ≤ n; 𝔼ᵥ [g(v)] = 0; ¬ (projectiveRel(a, b)). Then

|rowCrossCovariance(f, g, a, b)| ≤ mixingCoefficient(F, n) · ((𝔼ᵤ [(f(u))²] + 𝔼ᵤ [(g(u))²]) / 2).
-/
theorem abs_rowCrossCovariance_independent_le (hn : 2 ≤ n) (f g : U F n → ℝ)
    (hg : uavg g = 0) (a b : U F n) (hab : ¬ projectiveRel a b) :
    |rowCrossCovariance f g a b| ≤ mixingCoefficient F n *
      ((uavg (fun u => f u ^ 2) + uavg (fun u => g u ^ 2)) / 2) := by
  classical
  letI : Nonempty (U F n) := ⟨a⟩
  have hz (l : U F n) : ∑ k, rowCrossCovariance f g l k = 0 := by
    have h := rowCrossCovariance_row_mean_zero f g hg l
    unfold uavg at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (U F n) ≠ 0)))
  have hD : 0 < (Fintype.card (U F n) : ℝ) - ((fieldCard F : ℝ) - 1) := by
    rw [card_U_real]
    have h := zeroFiber_denominator_pos (F := F) hn
    linarith
  have h := constant_off_relation_bound projectiveRel (rowCrossCovariance f g)
    ((fieldCard F : ℝ) - 1)
    ((uavg (fun u => f u ^ 2) + uavg (fun u => g u ^ 2)) / 2)
    (rowCrossCovariance f g a b) (fun l => projectiveIndicator_row_sum l) hz
    (abs_rowCrossCovariance_le f g)
    (fun l k hk => rowCrossCovariance_independent_eq f g l k a b hk hab) hD
  rw [card_U_real] at h
  convert h using 1
  unfold mixingCoefficient
  ring

section GeneralOldInputs

variable {X : Type*} [Fintype X] [Nonempty X]

/-- A regular symmetric table averages the arithmetic mean of endpoint energies to its row mass times the mean energy. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ X → X → ℝ; r ∈ ℝ; H ∈ X → ℝ, assume ∀ x, y, P(x, y) = P(y, x); ∀ x, ∑_y (P(x, y)) = r. Then

𝔼ₓ [𝔼_y [P(x, y) · ((H(x) + H(y)) / 2)]] = (r / |X|) · 𝔼ᵤ [H(u)].
-/
lemma regular_energy_average (P : X → X → ℝ) (r : ℝ)
    (hsym : ∀ x y, P x y = P y x) (hrow : ∀ x, ∑ y, P x y = r) (H : X → ℝ) :
    uavg (fun x => uavg (fun y => P x y * ((H x + H y) / 2))) =
      (r / Fintype.card X) * uavg H := by
  have hleft : (∑ x, ∑ y, P x y * H x) = r * ∑ x, H x := by
    simp_rw [← Finset.sum_mul, hrow, mul_comm r]
    rw [Finset.sum_mul]
  have hright : (∑ x, ∑ y, P x y * H y) = r * ∑ y, H y := by
    rw [Finset.sum_comm]
    simp_rw [hsym, ← Finset.sum_mul, hrow]
    rw [← Finset.mul_sum]
  unfold uavg
  simp only [← Finset.mul_sum]
  have hexpand : (∑ x, ∑ y, P x y * ((H x + H y) / 2)) = r * ∑ x, H x := by
    calc
      _ = ((∑ x, ∑ y, P x y * H x) + (∑ x, ∑ y, P x y * H y)) / 2 := by
        simp only [mul_add, add_div, mul_div_assoc, Finset.sum_add_distrib,
          Finset.sum_div]
      _ = _ := by rw [hleft, hright]; ring
  rw [hexpand]
  ring

/-- Exact expansion of the joint-input variance into heterogeneous covariances. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, n); f ∈ X → U(F, n) → ℝ, we have

𝔼_(M ∈ GLₙ(F)) [(𝔼ₓ [f(x, rowRefresh(a(x), M))])²] = 𝔼ₓ [𝔼_y [rowCrossCovariance(f(x), f(y), a(x), a(y))]].
-/
lemma heterogeneous_row_square_eq (a : X → U F n) (f : X → U F n → ℝ) :
    uavg (fun M : Refresh.«GL» F n => (uavg (fun x => f x (rowRefresh (a x) M))) ^ 2) =
      uavg (fun x => uavg (fun y => rowCrossCovariance (f x) (f y) (a x) (a y))) := by
  simp_rw [sq, uavg_mul_uavg]
  rw [uavg_comm]
  apply uavg_congr
  intro x
  rw [uavg_comm]
  rfl

/-- The full scalar variance estimate for arbitrary input-dependent centered functions, in terms of the exact number of proportional old inputs. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, n); f ∈ X → U(F, n) → ℝ; r ∈ ℝ, assume 2 ≤ n; ∀ x, 𝔼ᵥ [f(x, v)] = 0; ∀ x, ∑_y (projectiveIndicator(a(x), a(y))) = r. Then

𝔼_(M ∈ GLₙ(F)) [(𝔼ₓ [f(x, rowRefresh(a(x), M))])²] ≤ (r / |X| + mixingCoefficient(F, n)) · 𝔼ₓ [𝔼ᵤ [(f(x, u))²]].
-/
theorem heterogeneous_row_variance_le (hn : 2 ≤ n) (a : X → U F n)
    (f : X → U F n → ℝ) (hf : ∀ x, uavg (f x) = 0) (r : ℝ)
    (hrow : ∀ x, ∑ y, projectiveIndicator (a x) (a y) = r) :
    uavg (fun M : Refresh.«GL» F n => (uavg (fun x => f x (rowRefresh (a x) M))) ^ 2) ≤
      (r / Fintype.card X + mixingCoefficient F n) * uavg (fun x => uavg (fun u => f x u ^ 2)) := by
  classical
  let H := fun x => uavg (fun u => f x u ^ 2)
  let κ := mixingCoefficient F n
  let P : X → X → ℝ := fun x y => projectiveIndicator (a x) (a y) + κ
  have hκ : 0 ≤ κ := mixingCoefficient_nonneg hn
  have hH (x : X) : 0 ≤ H x := uavg_nonneg (fun _ => sq_nonneg _)
  have hbound (x y : X) : rowCrossCovariance (f x) (f y) (a x) (a y) ≤
      P x y * ((H x + H y) / 2) := by
    apply (le_abs_self _).trans
    by_cases h : projectiveRel (a x) (a y)
    · have h' := abs_rowCrossCovariance_le (f x) (f y) (a x) (a y)
      simp only [P, projectiveIndicator, h, if_true]
      change |rowCrossCovariance (f x) (f y) (a x) (a y)| ≤ (1 + κ) * ((H x + H y) / 2)
      nlinarith [mul_nonneg hκ (add_nonneg (hH x) (hH y))]
    · simpa only [P, projectiveIndicator, h, if_false, zero_add] using
        abs_rowCrossCovariance_independent_le hn (f x) (f y) (hf y) (a x) (a y) h
  have hsym (x y : X) : P x y = P y x := by
    simp only [P, projectiveIndicator_symm (a x) (a y)]
  have hProw (x : X) : ∑ y, P x y = r + κ * Fintype.card X := by
    simp only [P, Finset.sum_add_distrib, hrow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_comm κ]
  rw [heterogeneous_row_square_eq]
  calc
    _ ≤ uavg (fun x => uavg (fun y => P x y * ((H x + H y) / 2))) :=
      uavg_mono (fun x => uavg_mono (hbound x))
    _ = ((r + κ * Fintype.card X) / Fintype.card X) * uavg H :=
      regular_energy_average P _ hsym hProw H
    _ = _ := by
      have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      dsimp [κ, H]
      field_simp

/-- Centering in the output coordinate gives the variance around the product mean for arbitrary old-input-dependent test functions. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, n); f ∈ X → U(F, n) → ℝ; r ∈ ℝ, assume 2 ≤ n; 0 ≤ r; ∀ x, ∑_y (projectiveIndicator(a(x), a(y))) = r. Then

𝔼_(M ∈ GLₙ(F)) [(𝔼ₓ [f(x, rowRefresh(a(x), M))] - 𝔼ₓ [𝔼ₜ [f(x, t)]])²] ≤ (r / |X| + mixingCoefficient(F, n)) · 𝔼ₓ [𝔼ᵤ [(f(x, u))²]].
-/
theorem heterogeneous_row_variance_uncentered (hn : 2 ≤ n) (a : X → U F n)
    (f : X → U F n → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hrow : ∀ x, ∑ y, projectiveIndicator (a x) (a y) = r) :
    uavg (fun M : Refresh.«GL» F n =>
      (uavg (fun x => f x (rowRefresh (a x) M)) - uavg (fun x => uavg (f x))) ^ 2) ≤
      (r / Fintype.card X + mixingCoefficient F n) *
        uavg (fun x => uavg (fun u => f x u ^ 2)) := by
  letI : Nonempty (U F n) := ⟨a (Classical.choice inferInstance)⟩
  have h := heterogeneous_row_variance_le hn a (fun x => centered (f x))
    (fun x => centered_mean_zero (f x)) r hrow
  have he (M : Refresh.«GL» F n) :
      uavg (fun x => centered (f x) (rowRefresh (a x) M)) =
        uavg (fun x => f x (rowRefresh (a x) M)) - uavg (fun x => uavg (f x)) := by
    exact uavg_sub _ _
  simp_rw [he] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left
  · exact uavg_mono (fun x => centered_square_le (f x))
  · exact add_nonneg (div_nonneg hr (Nat.cast_nonneg _)) (mixingCoefficient_nonneg hn)

end GeneralOldInputs

/-- Tensor of the two retained nonzero input shares. -/
/-
Mathematical definition (normal notation): For x ∈ U(F, n) × U(F, n), define

inputTensor(x) := tensorVector((x)₁, (x)₂).
-/
def inputTensor (x : U F n × U F n) : U F (n * n) :=
  ⟨tensorVector x.1.val x.2.val, tensorVector_ne_zero x.1 x.2⟩

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For x, y ∈ U(F, n) × U(F, n), we have

projectiveRel(inputTensor(x), inputTensor(y)) ⇔ NonzeroProportional(tensorVector((y)₁, (y)₂), tensorVector((x)₁, (x)₂)).
-/
lemma projectiveRel_inputTensor_iff (x y : U F n × U F n) :
    projectiveRel (inputTensor x) (inputTensor y) ↔
      NonzeroProportional (tensorVector y.1.val y.2.val) (tensorVector x.1.val x.2.val) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_, hc⟩
    intro h
    exact (inputTensor y).property (by simpa [h] using hc)
  · rintro ⟨c, _, hc⟩
    exact ⟨c, hc⟩

/-- Exact regular degree of the tensor proportional relation. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For x ∈ U(F, n) × U(F, n), we have

(∑_(y ∈ U(F, n) × U(F, n)) (projectiveIndicator(inputTensor(x), inputTensor(y)))) = (|F| - 1)².
-/
lemma inputTensor_projective_row_sum (x : U F n × U F n) :
    (∑ y : U F n × U F n, projectiveIndicator (inputTensor x) (inputTensor y)) =
      ((fieldCard F - 1 : ℕ) : ℝ) ^ 2 := by
  classical
  have hcard : Fintype.card {y : U F n × U F n //
      projectiveRel (inputTensor x) (inputTensor y)} = (fieldCard F - 1) ^ 2 := by
    have he : {y : U F n × U F n // projectiveRel (inputTensor x) (inputTensor y)} ≃
        TensorProportionalFiber x.1 x.2 :=
      Equiv.subtypeEquivRight (fun y => projectiveRel_inputTensor_iff x y)
    rw [Fintype.card_congr he, ← Nat.card_eq_fintype_card]
    exact card_tensorProportionalFiber x.1 x.2
  have hc : (Fintype.card {y : U F n × U F n //
      projectiveRel (inputTensor x) (inputTensor y)} : ℝ) = ((fieldCard F - 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hcard
  simpa only [projectiveIndicator, Fintype.card_subtype, Finset.sum_boole,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hc

/-- The actual joint-port scalar variance, with the exact tensor collision fraction and the independent-output mixing coefficient. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ (U(F, n) × U(F, n)) → U(F, (n · n)) → ℝ, assume 2 ≤ n. Then

𝔼_(M ∈ GL_(n · n)(F)) [(𝔼ₓ [f(x, rowRefresh(inputTensor(x), M))] - 𝔼ₓ [𝔼ₐ [f(x, a)]])²] ≤ (((|F| - 1)² / (|U(F, n)|)²) + mixingCoefficient(F, (n · n))) · 𝔼ₓ [𝔼ᵤ [(f(x, u))²]].
-/
theorem joint_tensor_row_variance (hn : 2 ≤ n)
    (f : (U F n × U F n) → U F (n * n) → ℝ) :
    uavg (fun M : Refresh.«GL» F (n * n) =>
      (uavg (fun x => f x (rowRefresh (inputTensor x) M)) -
        uavg (fun x => uavg (f x))) ^ 2) ≤
      ((((fieldCard F - 1 : ℕ) : ℝ) ^ 2 / (Fintype.card (U F n) : ℝ) ^ 2) +
        mixingCoefficient F (n * n)) * uavg (fun x => uavg (fun u => f x u ^ 2)) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  have hdim : 2 ≤ n * n := by nlinarith
  have h := heterogeneous_row_variance_uncentered hdim inputTensor f
    (((fieldCard F - 1 : ℕ) : ℝ) ^ 2) (sq_nonneg _) inputTensor_projective_row_sum
  simpa only [Fintype.card_prod, Nat.cast_mul, pow_two] using h

end

end CircuitCompiler
