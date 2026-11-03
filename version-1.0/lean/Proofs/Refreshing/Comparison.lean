import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-!
# Finite comparison facts for the refreshing proof

This file proves the Cauchy–Schwarz replacement estimate and the final signed-measure hybrid summation in the paper. It does not assume that signed masses are positive or normalized. The hypotheses identifying a concrete refresh execution with these masses, and bounding each adaptive hybrid step, remain explicit in the statements below.
-/

noncomputable section
open scoped BigOperators

namespace RefreshingProof

/-- Eliminate one unsigned final answer before enumerating any other answers. The incoming weight may depend arbitrarily on the preceding history, and may even be signed. Normalization is required separately at every formal history. -/
theorem sum_last_answer {Z : Type*} [Fintype Z] (n : ℕ)
    (W : (Fin n → Z) → ℝ) (p : (Fin n → Z) → Z → ℝ)
    (hp : ∀ h, ∑ z, p h z = 1) :
    (∑ h : Fin (n + 1) → Z, W (Fin.init h) * p (Fin.init h) (h (Fin.last n))) =
      ∑ h : Fin n → Z, W h := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => Z)).sum_comp]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.init_snoc, Fin.snoc_last]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [← Finset.mul_sum, hp, mul_one]

/-- A normalized adaptive answer tree, written in the same tuple convention as the refreshing specification. -/
def adaptiveWeight {Z : Type*} (p : (i : ℕ) → (Fin i → Z) → Z → ℝ) :
    (n : ℕ) → (Fin n → Z) → ℝ
  | 0, _ => 1
  | n + 1, h => adaptiveWeight p n (Fin.init h) * p n (Fin.init h) (h (Fin.last n))

/-- Summing unsigned answers backwards removes a whole normalized adaptive suffix. This is valid even at histories that are unreachable in an execution. -/
theorem sum_adaptiveWeight {Z : Type*} [Fintype Z]
    (p : (i : ℕ) → (Fin i → Z) → Z → ℝ)
    (hp : ∀ i h, ∑ z, p i h z = 1) (n : ℕ) :
    ∑ h : Fin n → Z, adaptiveWeight p n h = 1 := by
  induction n with
  | zero => simp [adaptiveWeight]
  | succ n ih =>
      change (∑ h : Fin (n + 1) → Z,
        adaptiveWeight p n (Fin.init h) * p n (Fin.init h) (h (Fin.last n))) = 1
      rw [sum_last_answer n (adaptiveWeight p n) (p n) (hp n)]
      exact ih

/-- A chronological product of nonnegative adaptive answer weights is nonnegative. -/
theorem adaptiveWeight_nonneg {Z : Type*}
    (p : (i : ℕ) → (Fin i → Z) → Z → ℝ)
    (hp : ∀ i h z, 0 ≤ p i h z) (n : ℕ) (h : Fin n → Z) :
    0 ≤ adaptiveWeight p n h := by
  induction n with
  | zero => simp [adaptiveWeight]
  | succ n ih => exact mul_nonneg (ih _) (hp _ _ _)

/-- A finite weighted mean; the weights need not be normalized for Cauchy–Schwarz. -/
def weightedMean {Ω : Type*} [Fintype Ω] (w f : Ω → ℝ) : ℝ :=
  ∑ x, w x * f x

/-- Cauchy–Schwarz on one joint probability space. In particular, `f` and `g` may both depend on the common state between neighboring refresh rounds. -/
theorem weighted_cauchy_schwarz {Ω : Type*} [Fintype Ω]
    (w f g : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) :
    weightedMean w (fun x => |f x * g x|) ≤
      Real.sqrt (weightedMean w (fun x => f x ^ 2)) *
      Real.sqrt (weightedMean w (fun x => g x ^ 2)) := by
  unfold weightedMean
  calc
    ∑ x, w x * |f x * g x| =
        ∑ x, Real.sqrt (w x * f x ^ 2) * Real.sqrt (w x * g x ^ 2) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Real.sqrt_mul (hw x), Real.sqrt_mul (hw x),
        Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_mul]
      have hs := Real.sq_sqrt (hw x)
      nlinarith [mul_nonneg (abs_nonneg (f x)) (abs_nonneg (g x))]
    _ ≤ Real.sqrt (∑ x, w x * f x ^ 2) *
        Real.sqrt (∑ x, w x * g x ^ 2) := by
      simpa using
        Real.sum_sqrt_mul_sqrt_le Finset.univ
          (fun x => mul_nonneg (hw x) (sq_nonneg (f x)))
          (fun x => mul_nonneg (hw x) (sq_nonneg (g x)))

/-- The paper's replacement estimate: an error with L₂ norm at most ε, multiplied by a signed companion of L₂ norm at most six, costs at most 6ε. -/
theorem replacement_with_companion {Ω : Type*} [Fintype Ω]
    (w e g : Ω → ℝ) (ε : ℝ) (hw : ∀ x, 0 ≤ w x)
    (he : Real.sqrt (weightedMean w (fun x => e x ^ 2)) ≤ ε)
    (hg : Real.sqrt (weightedMean w (fun x => g x ^ 2)) ≤ 6) :
    weightedMean w (fun x => |e x * g x|) ≤ 6 * ε := by
  have hε : 0 ≤ ε := (Real.sqrt_nonneg _).trans he
  calc
    _ ≤ Real.sqrt (weightedMean w (fun x => e x ^ 2)) *
        Real.sqrt (weightedMean w (fun x => g x ^ 2)) :=
      weighted_cauchy_schwarz w e g hw
    _ ≤ ε * 6 := mul_le_mul he hg (Real.sqrt_nonneg _) hε
    _ = 6 * ε := mul_comm _ _

/-- The corresponding ε bound without a signed companion. -/
theorem replacement_without_companion {Ω : Type*} [Fintype Ω]
    (w e : Ω → ℝ) (ε : ℝ) (hw : ∀ x, 0 ≤ w x)
    (hnorm : weightedMean w (fun _ => 1) = 1)
    (he : Real.sqrt (weightedMean w (fun x => e x ^ 2)) ≤ ε) :
    weightedMean w (fun x => |e x|) ≤ ε := by
  have hcs := weighted_cauchy_schwarz w e (fun _ => 1) hw
  simpa only [mul_one, one_pow, hnorm, Real.sqrt_one, mul_one] using hcs.trans
    (mul_le_mul_of_nonneg_right he (Real.sqrt_nonneg (weightedMean w (fun _ => 1 ^ 2))))

/-- Unnormalized L₁ difference of finite real masses. -/
def massL1 {H : Type*} [Fintype H] (p q : H → ℝ) : ℝ := ∑ h, |p h - q h|

/-- The total absolute mass difference of a real weight with itself is zero. -/
@[simp] theorem massL1_self {H : Type*} [Fintype H] (p : H → ℝ) :
    massL1 p p = 0 := by simp [massL1]

/-- The total absolute difference of two finite real weights is nonnegative. -/
theorem massL1_nonneg {H : Type*} [Fintype H] (p q : H → ℝ) :
    0 ≤ massL1 p q := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- Triangle inequality applies equally to signed intermediate hybrid masses. -/
theorem massL1_triangle {H : Type*} [Fintype H] (p q r : H → ℝ) :
    massL1 p r ≤ massL1 p q + massL1 q r := by
  unfold massL1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun h _ => abs_sub_le (p h) (q h) (r h))

/-- A finite hybrid chain can be bounded by the sum of all of its steps. -/
theorem massL1_chain {H : Type*} [Fintype H] (Q : ℕ → H → ℝ) (m : ℕ) :
    massL1 (Q 0) (Q m) ≤ ∑ i ∈ Finset.range m, massL1 (Q i) (Q (i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        _ ≤ massL1 (Q 0) (Q m) + massL1 (Q m) (Q (m + 1)) := massL1_triangle _ _ _
        _ ≤ (∑ i ∈ Finset.range m, massL1 (Q i) (Q (i + 1))) +
            massL1 (Q m) (Q (m + 1)) := add_le_add ih le_rfl
        _ = _ := by rw [Finset.sum_range_succ]

/-- Uniformly bounded steps give the usual number-of-steps hybrid estimate. -/
theorem massL1_chain_uniform {H : Type*} [Fintype H] (Q : ℕ → H → ℝ)
    (m : ℕ) (b : ℝ) (hstep : ∀ i < m, massL1 (Q i) (Q (i + 1)) ≤ b) :
    massL1 (Q 0) (Q m) ≤ (m : ℝ) * b := by
  calc
    _ ≤ ∑ i ∈ Finset.range m, massL1 (Q i) (Q (i + 1)) := massL1_chain Q m
    _ ≤ ∑ _i ∈ Finset.range m, b := Finset.sum_le_sum (fun i hi => hstep i (Finset.mem_range.mp hi))
    _ = _ := by simp

/-- Insert the next signed round, change the intervening label, then restore the preceding true round. This is the three-move step in §4.5, once the local adaptive estimates (including answer enumeration) have been established. -/
theorem hybrid_step_of_three_moves {H : Type*} [Fintype H]
    (p u v q : H → ℝ) (k ε d : ℝ)
    (hinsert : massL1 p u ≤ 6 * k * ε)
    (hchange : massL1 u v ≤ 8 * k * d)
    (hrestore : massL1 v q ≤ 6 * k * ε) :
    massL1 p q ≤ k * (12 * ε + 8 * d) := by
  have h₁ := massL1_triangle p u q
  have h₂ := massL1_triangle u v q
  nlinarith

/-- The final scalar summation in §4.5. A concrete proof must establish all `hstep` inequalities using adaptive answer elimination and the local estimates. The factor one half is the conversion from signed L₁ distance to statistical distance; no normalization of intermediate masses is required. -/
theorem finite_refresh_hybrid_bound {H : Type*} [Fintype H]
    (T K : ℕ) (hT : 1 ≤ T) (ε d : ℝ) (hε : 0 ≤ ε) (hd : 0 ≤ d)
    (Q : ℕ → H → ℝ)
    (hstep : ∀ i < T + 1,
      massL1 (Q i) (Q (i + 1)) ≤ (K : ℝ) ^ 3 * (12 * ε + 8 * d)) :
    (1 / 2 : ℝ) * massL1 (Q 0) (Q (T + 1)) ≤
      12 * (T : ℝ) * (K : ℝ) ^ 3 * (ε + d) := by
  have hchain := massL1_chain_uniform Q (T + 1) _ hstep
  have hcount : ((T + 1 : ℕ) : ℝ) ≤ 2 * (T : ℝ) := by exact_mod_cast (by omega : T + 1 ≤ 2 * T)
  have hK : 0 ≤ (K : ℝ) ^ 3 := by positivity
  have hb : 0 ≤ (K : ℝ) ^ 3 * (12 * ε + 8 * d) := by positivity
  calc
    _ ≤ (1 / 2 : ℝ) * (((T + 1 : ℕ) : ℝ) * ((K : ℝ) ^ 3 * (12 * ε + 8 * d))) :=
      mul_le_mul_of_nonneg_left hchain (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (2 * (T : ℝ) * ((K : ℝ) ^ 3 * (12 * ε + 8 * d))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcount hb) (by norm_num)
    _ ≤ 12 * (T : ℝ) * (K : ℝ) ^ 3 * (ε + d) := by
      have hTd : 0 ≤ (T : ℝ) * (K : ℝ) ^ 3 * d := by positivity
      nlinarith

end RefreshingProof
