import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.InitialDiscrepancy
import Proofs.Compiler.Foundations.MatrixRefreshing.Probability.FiniteDistribution
import Proofs.Compiler.Foundations.LinearAlgebra.RefreshBounds



/-!
# Terminal conditioning for signed state approximations

The two secret fibers are disjoint, so their conditional densities have a joint bound of `1 / pMin` times the reference density. Combining this bound with the factor `1/2` in statistical distance gives error `E / (2 * pMin)`. The generic estimate applies to finite reference distributions and signed tables; approximating tables need not be nonnegative.
-/

set_option autoImplicit false

open scoped BigOperators

namespace TableAnalysis

open Refresh MatrixRefresh

noncomputable section

variable {X H : Type*} [Fintype X] [Fintype H]

/-- The total L1 error of a history-indexed signed approximation. -/
/-
Mathematical definition (normal notation): For ν ∈ 𝒟(X); P, G ∈ H → X → ℝ, define

terminalError(ν, P, G) := ∑ₕ (𝔼_(x ← ν) [|P(h, x) - G(h, x)|]).
-/
def terminalError (ν : FiniteDistribution X) (P G : H → X → ℝ) : ℝ :=
  ∑ h, ν.expect (fun x => |P h x - G h x|)

/-- Total variation expression for two fixed-secret history distributions. -/
/-
Mathematical definition (normal notation): For μ₁, μ₀ ∈ 𝒟(X); P ∈ H → X → ℝ, define

terminalDistance(μ₁, μ₀, P) := 1 / 2 · ∑ₕ (|𝔼_(u ← μ₁) [P(h, u)] - 𝔼_(v ← μ₀) [P(h, v)]|).
-/
def terminalDistance (μ₁ μ₀ : FiniteDistribution X) (P : H → X → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ h, |μ₁.expect (P h) - μ₀.expect (P h)|

/-- The disjoint-fiber density estimate controls the sum of both errors. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ν, μ₁, μ₀ ∈ 𝒟(X); pMin ∈ ℝ; D ∈ X → ℝ, assume 0 < pMin; ∀ x, pMin · (μ₁(x) + μ₀(x)) ≤ ν(x). Then

|𝔼_(u ← μ₁) [D(u)]| + |𝔼_(v ← μ₀) [D(v)]| ≤ (pMin)⁻¹ · 𝔼_(x ← ν) [|D(x)|].
-/
theorem two_conditioning_errors_le (ν μ₁ μ₀ : FiniteDistribution X) (pMin : ℝ)
    (hpMin : 0 < pMin)
    (hdensity : ∀ x, pMin * (μ₁.weight x + μ₀.weight x) ≤ ν.weight x)
    (D : X → ℝ) :
    |μ₁.expect D| + |μ₀.expect D| ≤ pMin⁻¹ * ν.expect (fun x => |D x|) := by
  calc
    _ ≤ μ₁.expect (fun x => |D x|) + μ₀.expect (fun x => |D x|) :=
      add_le_add (abs_expect_le_expect_abs μ₁ D) (abs_expect_le_expect_abs μ₀ D)
    _ = ∑ x, (μ₁.weight x + μ₀.weight x) * |D x| := by
      simp only [FiniteDistribution.expect, ← Finset.sum_add_distrib, add_mul]
    _ ≤ ∑ x, (pMin⁻¹ * ν.weight x) * |D x| := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      have h := mul_le_mul_of_nonneg_left (hdensity x) (inv_nonneg.mpr hpMin.le)
      simpa only [← mul_assoc, inv_mul_cancel₀ hpMin.ne', one_mul] using h
    _ = pMin⁻¹ * ν.expect (fun x => |D x|) := by
      simp only [FiniteDistribution.expect, Finset.mul_sum, mul_assoc]

/-- The terminal comparison separates approximation error from the discrepancy of the signed approximations. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ν, μ₁, μ₀ ∈ 𝒟(X); pMin ∈ ℝ; P, G ∈ H → X → ℝ, assume 0 < pMin; ∀ x, pMin · (μ₁(x) + μ₀(x)) ≤ ν(x). Then

terminalDistance(μ₁, μ₀, P) ≤ terminalError(ν, P, G) / (2 · pMin) + 1 / 2 · ∑ₕ (|𝔼_(u ← μ₁) [G(h, u)] - 𝔼_(v ← μ₀) [G(h, v)]|).
-/
theorem terminal_conditioning_bound (ν μ₁ μ₀ : FiniteDistribution X) (pMin : ℝ)
    (hpMin : 0 < pMin)
    (hdensity : ∀ x, pMin * (μ₁.weight x + μ₀.weight x) ≤ ν.weight x)
    (P G : H → X → ℝ) :
    terminalDistance μ₁ μ₀ P ≤ terminalError ν P G / (2 * pMin) +
      (1 / 2 : ℝ) * ∑ h, |μ₁.expect (G h) - μ₀.expect (G h)| := by
  have hone (h : H) :
      |μ₁.expect (P h) - μ₀.expect (P h)| ≤
        pMin⁻¹ * ν.expect (fun x => |P h x - G h x|) +
          |μ₁.expect (G h) - μ₀.expect (G h)| := by
    have he := two_conditioning_errors_le ν μ₁ μ₀ pMin hpMin hdensity
      (fun x => P h x - G h x)
    rw [expect_sub, expect_sub] at he
    have hsplit : μ₁.expect (P h) - μ₀.expect (P h) =
        (μ₁.expect (P h) - μ₁.expect (G h)) -
          (μ₀.expect (P h) - μ₀.expect (G h)) +
          (μ₁.expect (G h) - μ₀.expect (G h)) := by ring
    rw [hsplit]
    exact (abs_add_le _ _).trans
      (add_le_add ((abs_sub _ _).trans he) (le_refl _))
  calc
    terminalDistance μ₁ μ₀ P ≤ (1 / 2 : ℝ) * ∑ h,
        (pMin⁻¹ * ν.expect (fun x => |P h x - G h x|) +
          |μ₁.expect (G h) - μ₀.expect (G h)|) := by
      unfold terminalDistance
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun h _ => hone h))
        (by norm_num)
    _ = terminalError ν P G / (2 * pMin) +
        (1 / 2 : ℝ) * ∑ h, |μ₁.expect (G h) - μ₀.expect (G h)| := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, terminalError]
      field_simp

section Factorization

variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype I]

/-- Static discrepancy applies term by term to a normalized rank-one decomposition. An SVD supplies `shareL2 = 1` for all retained vectors. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s, t ∈ F; c ∈ I → ℝ; a, b ∈ I → U(F, n) → ℝ; G ∈ State(F, n) → ℝ, assume 2 ≤ n; ∀ x, G(x) = ∑ᵢ (c(i) · (a(i, L(x)) · b(i, R(x)))); ∀ i, ‖ a(i)‖₂ = 1; ∀ i, ‖ b(i)‖₂ = 1. Then

|𝔼_(u ← μₛ) [G(u)] - 𝔼_(v ← μₜ) [G(v)]| ≤ zeta(F, n) · ∑ᵢ (|c(i)|).
-/
theorem decomposition_secret_discrepancy {n : ℕ} (hn : 2 ≤ n) (s t : F)
    (c : I → ℝ) (a b : I → U F n → ℝ) (G : State F n → ℝ)
    (hG : ∀ x, G x = ∑ i, c i * (a i (stateLeftShare x) * b i (stateRightShare x)))
    (ha : ∀ i, shareL2 (a i) = 1) (hb : ∀ i, shareL2 (b i) = 1) :
    |(mu F n hn s).expect G - (mu F n hn t).expect G| ≤
      zeta F n * ∑ i, |c i| := by
  have hs := expect_sum (mu F n hn s)
    (fun i x => c i * (a i (stateLeftShare x) * b i (stateRightShare x)))
  have ht := expect_sum (mu F n hn t)
    (fun i x => c i * (a i (stateLeftShare x) * b i (stateRightShare x)))
  have hfun : G = fun x => ∑ i, c i * (a i (stateLeftShare x) * b i (stateRightShare x)) := funext hG
  rw [hfun]
  rw [hs, ht]
  simp_rw [expect_smul]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |c i * ((mu F n hn s).expect (fun x => a i (stateLeftShare x) * b i (stateRightShare x)) -
        (mu F n hn t).expect (fun x => a i (stateLeftShare x) * b i (stateRightShare x)))| := by
      simpa only [mul_sub] using Finset.abs_sum_le_sum_abs
        (fun i => c i * ((mu F n hn s).expect (fun x => a i (stateLeftShare x) * b i (stateRightShare x)) -
          (mu F n hn t).expect (fun x => a i (stateLeftShare x) * b i (stateRightShare x)))) Finset.univ
    _ ≤ ∑ i, |c i| * zeta F n := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have h := innerProduct_discrepancy hn s t (a i) (b i)
      rw [ha i, hb i, mul_one, mul_one] at h
      exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = zeta F n * ∑ i, |c i| := by rw [← Finset.sum_mul, mul_comm]

/-- Distinct actual encoding fibers satisfy the joint density bound, including when one secret is zero. Their disjointness is essential here. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s, t ∈ F; x ∈ State(F, n), assume 2 ≤ n; s ≠ t. Then

minSecretProbability(F, n) · (μₛ(x) + μₜ(x)) ≤ independentStateDistribution(F, n)(x).
-/
theorem encoding_joint_density_bound {n : ℕ} (hn : 2 ≤ n) (s t : F) (hst : s ≠ t)
    (x : State F n) :
    minSecretProbability F n * ((mu F n hn s).weight x + (mu F n hn t).weight x) ≤
      (independentStateDistribution F n hn).weight x := by
  rw [mu_weight_density, mu_weight_density, ← add_mul, ← mul_assoc]
  have hjoint :
      (if secret x = s then densityWeight F n s else 0) +
        (if secret x = t then densityWeight F n t else 0) ≤ (minSecretProbability F n)⁻¹ := by
    split_ifs with hs ht
    · exact False.elim (hst (hs.symm.trans ht))
    · simpa only [add_zero] using densityWeight_le_inv_minSecretProbability hn s
    · simpa only [zero_add] using densityWeight_le_inv_minSecretProbability hn t
    · simpa only [zero_add] using inv_nonneg.mpr (minSecretProbability_pos (F := F) hn).le
  have hscaled := mul_le_mul_of_nonneg_left hjoint (minSecretProbability_pos (F := F) hn).le
  rw [mul_inv_cancel₀ (minSecretProbability_pos (F := F) hn).ne'] at hscaled
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hscaled
    ((independentStateDistribution F n hn).nonneg x)

/-- Terminal conditioning specialized to the manuscript's actual encoding distributions and its exact minimum fiber mass. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s, t ∈ F; P, G ∈ H → State(F, n) → ℝ, assume 2 ≤ n; s ≠ t. Then

terminalDistance(μₛ, μₜ, P) ≤ terminalError(independentStateDistribution(F, n), P, G) / (2 · minSecretProbability(F, n)) + 1 / 2 · ∑ₕ (|𝔼_(u ← μₛ) [G(h, u)] - 𝔼_(v ← μₜ) [G(h, v)]|).
-/
theorem actual_terminal_conditioning_bound {n : ℕ} (hn : 2 ≤ n) (s t : F)
    (hst : s ≠ t) (P G : H → State F n → ℝ) :
    terminalDistance (mu F n hn s) (mu F n hn t) P ≤
      terminalError (independentStateDistribution F n hn) P G / (2 * minSecretProbability F n) +
        (1 / 2 : ℝ) * ∑ h, |(mu F n hn s).expect (G h) -
          (mu F n hn t).expect (G h)| :=
  terminal_conditioning_bound _ _ _ _ (minSecretProbability_pos hn)
    (encoding_joint_density_bound hn s t hst) P G

end Factorization

end

end TableAnalysis
