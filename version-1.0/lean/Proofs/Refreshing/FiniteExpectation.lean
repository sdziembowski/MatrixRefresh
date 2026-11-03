import Proofs.Refreshing.AdaptiveBlock

/-!
# Finite real expectation algebra for exact signed hybrid expansions
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RefreshingProof

/-- A real-valued expectation under a finite PMF; its argument may be signed. -/
def pmfMean {X : Type*} [Fintype X] (p : PMF X) (f : X → ℝ) : ℝ :=
  ∑ x, (p x).toReal * f x

/-- The real mass of a finite sequential sample is the sum of products of its real marginal and conditional masses. -/
theorem pmf_bind_toReal {X Y : Type*} [Fintype X] (p : PMF X) (q : X → PMF Y) (y : Y) :
    (p.bind q y).toReal = ∑ x, (p x).toReal * (q x y).toReal := by
  rw [PMF.bind_apply, tsum_fintype,
    ENNReal.toReal_sum (fun x _ => ENNReal.mul_ne_top (p.apply_ne_top x) ((q x).apply_ne_top y))]
  simp only [ENNReal.toReal_mul]

/-- The real mass of a finite pushforward sums the real source masses over its preimages. -/
theorem pmf_map_toReal {X Y : Type*} [Fintype X] [DecidableEq Y] (p : PMF X) (f : X → Y) (y : Y) :
    (p.map f y).toReal = ∑ x, if y = f x then (p x).toReal else 0 := by
  classical
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum (by
    intro x _
    split_ifs
    · exact p.apply_ne_top x
    · exact ENNReal.zero_ne_top)]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

/-- Expectation under a pushforward equals expectation of the composed function. -/
theorem pmfMean_map {X Y : Type*} [Fintype X] [Fintype Y]
    (p : PMF X) (f : X → Y) (g : Y → ℝ) :
    pmfMean (p.map f) g = pmfMean p (fun x => g (f x)) := by
  classical
  unfold pmfMean
  simp_rw [pmf_map_toReal, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

/-- Expectation of a sequential sample equals the iterated marginal and conditional expectations. -/
theorem pmfMean_bind {X Y : Type*} [Fintype X] [Fintype Y]
    (p : PMF X) (q : X → PMF Y) (f : Y → ℝ) :
    pmfMean (p.bind q) f = pmfMean p (fun x => pmfMean (q x) f) := by
  unfold pmfMean
  simp_rw [pmf_bind_toReal, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Finite PMF expectation preserves addition of real functions. -/
theorem pmfMean_add {X : Type*} [Fintype X] (p : PMF X) (f g : X → ℝ) :
    pmfMean p (fun x => f x + g x) = pmfMean p f + pmfMean p g := by
  simp [pmfMean, mul_add, Finset.sum_add_distrib]

/-- Finite PMF expectation preserves subtraction of real functions. -/
theorem pmfMean_sub {X : Type*} [Fintype X] (p : PMF X) (f g : X → ℝ) :
    pmfMean p (fun x => f x - g x) = pmfMean p f - pmfMean p g := by
  simp [pmfMean, mul_sub, Finset.sum_sub_distrib]

/-- A constant right multiplier factors out of finite PMF expectation. -/
theorem pmfMean_mul_const {X : Type*} [Fintype X] (p : PMF X) (f : X → ℝ) (c : ℝ) :
    pmfMean p (fun x => f x * c) = pmfMean p f * c := by
  simp [pmfMean, Finset.sum_mul, mul_assoc]

/-- A constant left multiplier factors out of finite PMF expectation. -/
theorem pmfMean_const_mul {X : Type*} [Fintype X] (p : PMF X) (f : X → ℝ) (c : ℝ) :
    pmfMean p (fun x => c * f x) = c * pmfMean p f := by
  simp only [pmfMean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Finite PMF expectation commutes with finite sums of real functions. -/
theorem pmfMean_sum {X Z : Type*} [Fintype X] [Fintype Z]
    (p : PMF X) (f : X → Z → ℝ) :
    pmfMean p (fun x => ∑ z, f x z) = ∑ z, pmfMean p (fun x => f x z) := by
  unfold pmfMean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The order of two independent finite PMF expectations may be exchanged. -/
theorem pmfMean_comm {X Y : Type*} [Fintype X] [Fintype Y]
    (p : PMF X) (q : PMF Y) (f : X → Y → ℝ) :
    pmfMean p (fun x => pmfMean q (f x)) =
      pmfMean q (fun y => pmfMean p (fun x => f x y)) := by
  unfold pmfMean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Integrate the hidden middle state before taking a two-round window error. Both answer functions may depend on their formal preceding answers. -/
theorem two_round_window_factorization {X B Z : Type*}
    [Fintype X] [Fintype B] [Fintype Z]
    (μX : PMF X) (μB : PMF B) (f : X → Z → ℝ)
    (g : X → Z → B → Z → ℝ) (tail : Z → B → Z → ℝ) :
    pmfMean μX (fun x => ∑ z₁, f x z₁ *
      pmfMean μB (fun b => ∑ z₂, g x z₁ b z₂ * tail z₁ b z₂)) =
      ∑ z₁, pmfMean μB (fun b => ∑ z₂,
        pmfMean μX (fun x => f x z₁ * g x z₁ b z₂) * tail z₁ b z₂) := by
  calc
    _ = ∑ z₁, pmfMean μX (fun x => pmfMean μB (fun b =>
        ∑ z₂, (f x z₁ * g x z₁ b z₂) * tail z₁ b z₂)) := by
      simp_rw [← pmfMean_const_mul, Finset.mul_sum, pmfMean_sum, mul_assoc]
    _ = ∑ z₁, pmfMean μB (fun b => pmfMean μX (fun x =>
        ∑ z₂, (f x z₁ * g x z₁ b z₂) * tail z₁ b z₂)) := by
      apply Finset.sum_congr rfl
      intro z₁ _
      exact pmfMean_comm _ _ _
    _ = _ := by simp_rw [pmfMean_sum, pmfMean_mul_const]

/-- Pointwise inequalities are preserved by finite PMF expectation. -/
theorem pmfMean_mono {X : Type*} [Fintype X] (p : PMF X) (f g : X → ℝ)
    (h : ∀ x, f x ≤ g x) : pmfMean p f ≤ pmfMean p g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) ENNReal.toReal_nonneg)

/-- Local insertion, label change, and restoration costs combine before the adaptive block is inserted into the full execution. -/
theorem local_three_move_bound {A B : Type*} [Fintype A] [Fintype B]
    (μA : PMF A) (μB : PMF B) (F₀ F₁ F₂ F₃ : A → B → ℝ)
    (ε d : ℝ)
    (h₀₁ : pmfMean μA (fun a => pmfMean μB (fun b => |F₀ a b - F₁ a b|)) ≤ 6 * ε)
    (h₁₂ : pmfMean μA (fun a => pmfMean μB (fun b => |F₁ a b - F₂ a b|)) ≤ 8 * d)
    (h₂₃ : pmfMean μA (fun a => pmfMean μB (fun b => |F₂ a b - F₃ a b|)) ≤ 6 * ε) :
    pmfMean μA (fun a => pmfMean μB (fun b => |F₀ a b - F₃ a b|)) ≤
      12 * ε + 8 * d := by
  have hpoint (a : A) (b : B) : |F₀ a b - F₃ a b| ≤
      |F₀ a b - F₁ a b| + |F₁ a b - F₂ a b| + |F₂ a b - F₃ a b| := by
    have h₁ := abs_sub_le (F₀ a b) (F₁ a b) (F₃ a b)
    have h₂ := abs_sub_le (F₁ a b) (F₂ a b) (F₃ a b)
    linarith
  have hbound := pmfMean_mono μA _ _ (fun a => pmfMean_mono μB _ _ (hpoint a))
  simp_rw [pmfMean_add] at hbound
  linarith

end RefreshingProof
