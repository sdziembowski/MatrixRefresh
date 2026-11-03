import Proofs.Compiler.GateApproximation.MatrixPhase.AugmentedTensor
import Proofs.Compiler.LocalComparisons.Cutoff.LocalRates
import Proofs.Compiler.GateApproximation.MatrixPhase.InjectiveRefreshOperator



/-!
# Explicit local rates for augmented tensor refresh

The long dimension is `n*n+1`: the last coordinate implements the public multiplication/NAND offset. Injectivity gives the same old-feature count as for the unaugmented tensor. The density correction only decreases when the refresh dimension grows, so the local error retains the `2^(-n/4)` rate.
-/
set_option autoImplicit false

set_option maxHeartbeats 1500000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n m : ℕ}

/-- Density correction at any refresh dimension at least the share length. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume |F| = 2; 2 ≤ n; n ≤ m. Then

2 / (|F|ᵐ - 2) ≤ 4 · exp((-(log(2)) · n / 4)).
-/
theorem binary_feature_density_rate (hq : fieldCard F = 2) (hn : 2 ≤ n) (hnm : n ≤ m) :
    2 / ((vectorCard F m : ℝ)-2) ≤ 4 * Real.exp (-Real.log 2 * (n : ℝ) / 4) := by
  have hQ := vectorCard_real_ge_four (F := F) (hn.trans hnm)
  have hpow : (vectorCard F n : ℝ) ≤ (vectorCard F m : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (fieldCard_pos (F := F)) hnm
  have hN := vectorCard_real_ge_four (F := F) hn
  have hfirst : 2 / ((vectorCard F m : ℝ)-2) ≤ 4 / (vectorCard F n : ℝ) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).2
    linarith
  have hrpow : (vectorCard F n : ℝ)⁻¹ ≤ (vectorCard F n : ℝ) ^ (-(1/4 : ℝ)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have heq : (vectorCard F n : ℝ) ^ (-(1/4 : ℝ)) = Real.exp (-Real.log 2 * (n : ℝ) / 4) := by
    simp only [vectorCard, hq, Nat.cast_pow, Nat.cast_ofNat]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [heq] at hrpow
  exact hfirst.trans (by simpa only [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_left hrpow (by norm_num : (0 : ℝ) ≤ 4))

/-
Mathematical definition (normal notation): For F a set; n ∈ ℕ, assume F is finite. define

augmentedOperatorError(n) := (2 · √3 + 96) · (tensorShareCount(F, n))^(−(1 / 8)).
-/
def augmentedOperatorError (F : Type*) [Fintype F] (n : ℕ) : ℝ :=
  (2 * Real.sqrt 3 + 96) * tensorShareCount F n ^ (-(1/8 : ℝ))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

0 ≤ augmentedOperatorError(F, n).
-/
theorem augmentedOperatorError_nonneg (hn : 2 ≤ n) :
    0 ≤ augmentedOperatorError F n := by
  unfold augmentedOperatorError
  exact mul_nonneg (by positivity)
    (Real.rpow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (tensorShareCount_geometry (F := F) hn).1) _)

/-- Augmenting the tensor preserves the explicit matrix-phase local rate. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume |F| = 2; 2 ≤ n. Then

augmentedOperatorError(F, n) + 2 / (|F|^(n · n + 1) - 2) ≤ 208 · exp((-(log(2)) · n / 4)).
-/
theorem binary_augmented_local_rate (hq : fieldCard F = 2) (hn : 2 ≤ n) :
    augmentedOperatorError F n + 2 / ((vectorCard F (n*n+1) : ℝ)-2) ≤
      208 * Real.exp (-Real.log 2 * (n : ℝ) / 4) := by
  have hfeature := binary_tensor_feature_rate hq hn
  have hdensity := binary_feature_density_rate hq hn (show n ≤ n*n+1 by nlinarith)
  have hconst : 2*Real.sqrt 3+96 ≤ 102 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have h := mul_le_mul hconst hfeature (Real.rpow_nonneg
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) (tensorShareCount_geometry (F := F) hn).1) _)
    (by norm_num : (0 : ℝ) ≤ 102)
  unfold augmentedOperatorError
  linarith

/-- The abstract consistency condition is exactly the augmented product equation. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c ∈ F; x, y ∈ GateSide(F, n, (n · n + 1)), we have

refreshConsistent(Rectangular.augmentedShare(c), Rectangular.augmentedShare(1), x, y) ⇔ ((x)₂ · (y)₂) = (((x)₁)₁ · ((y)₁)₁) · (((x)₁)₂ · ((y)₁)₂) + c.
-/
theorem augmented_refreshConsistent (c : F)
    (x y : GateSide F n (n*n+1)) :
    refreshConsistent (Rectangular.augmentedShare c) (Rectangular.augmentedShare 1) x y ↔
      dot x.2.val y.2.val =
        dot x.1.1.val y.1.1.val * dot x.1.2.val y.1.2.val + c := by
  simp only [refreshConsistent, Rectangular.augmentedShare_dot]

/-- A table supported on correct multiplication/NAND ports meets the generic injective-feature support hypothesis. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c ∈ F; A ∈ ℝ^(GateSide(F, n, (n · n + 1)) × GateSide(F, n, (n · n + 1))), assume ∀ x, y, (((x)₂ · (y)₂) ≠ (((x)₁)₁ · ((y)₁)₁) · (((x)₁)₂ · ((y)₁)₂) + c) ⇒ A(x, y) = 0. Then

∀ x, y, ¬ (refreshConsistent(Rectangular.augmentedShare(c), Rectangular.augmentedShare(1), x, y)) → A(x, y) = 0.
-/
theorem augmented_product_support (c : F)
    (A : Matrix (GateSide F n (n*n+1)) (GateSide F n (n*n+1)) ℝ)
    (hsupport : ∀ x y, dot x.2.val y.2.val ≠
      dot x.1.1.val y.1.1.val * dot x.1.2.val y.1.2.val + c → A x y = 0) :
    ∀ x y, ¬refreshConsistent (Rectangular.augmentedShare c)
      (Rectangular.augmentedShare 1) x y → A x y = 0 := by
  intro x y hxy
  apply hsupport x y
  simpa only [augmented_refreshConsistent] using hxy

/-- Operator-norm bound under a random refresh for the actual augmented multiplication/NAND tensor, with every analytic hypothesis discharged. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c ∈ F; A ∈ ℝ^(GateSide(F, n, (n · n + 1)) × GateSide(F, n, (n · n + 1))), assume |F| = 2; 2 ≤ n; ∀ x, y, ¬ (refreshConsistent(Rectangular.augmentedShare(c), Rectangular.augmentedShare(1), x, y)) → A(x, y) = 0; ∀ x, y, |A(x, y)| ≤ 1. Then

𝔼_(M ∈ GL_(n · n + 1)(F)) [‖ refreshTable(Rectangular.augmentedShare(c), Rectangular.augmentedShare(1), A, M)‖ₒₚ] ≤ 2 · ‖ A‖ₒₚ + augmentedOperatorError(F, n).
-/
theorem augmented_operator_bound (hq : fieldCard F = 2) (hn : 2 ≤ n) (c : F)
    (A : Matrix (GateSide F n (n*n+1)) (GateSide F n (n*n+1)) ℝ)
    (hsupport : ∀ x y, ¬refreshConsistent (Rectangular.augmentedShare c)
      (Rectangular.augmentedShare 1) x y → A x y = 0)
    (hA : ∀ x y, |A x y| ≤ 1) :
    uavg (fun M : Refresh.«GL» F (n*n+1) =>
      largestSingularCoefficient (refreshTable (Rectangular.augmentedShare c)
        (Rectangular.augmentedShare 1) A M)) ≤
      2 * largestSingularCoefficient A + augmentedOperatorError F n := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  have h := feature_operator_bound hq (show 2 ≤ n*n+1 by nlinarith)
    (Rectangular.augmentedShare c) (Rectangular.augmentedShare 1)
    (Rectangular.augmentedShare_injective_binary hq c)
    (Rectangular.augmentedShare_injective_binary hq 1) A hsupport hA
  simpa only [augmentedOperatorError, tensorShareCount_card] using h

/-- The augmented operator and density correction have the same explicit exponential scale needed by the local separation argument. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c ∈ F; A ∈ ℝ^(GateSide(F, n, (n · n + 1)) × GateSide(F, n, (n · n + 1))), assume |F| = 2; 2 ≤ n; ∀ x, y, ¬ (refreshConsistent(Rectangular.augmentedShare(c), Rectangular.augmentedShare(1), x, y)) → A(x, y) = 0; ∀ x, y, |A(x, y)| ≤ 1. Then

𝔼_(M ∈ GL_(n · n + 1)(F)) [‖ refreshTable(Rectangular.augmentedShare(c), Rectangular.augmentedShare(1), A, M)‖ₒₚ] + 2 / (|F|^(n · n + 1) - 2) ≤ 2 · ‖ A‖ₒₚ + 208 · exp((-(log(2)) · n / 4)).
-/
theorem augmented_operator_bound_with_density (hq : fieldCard F = 2) (hn : 2 ≤ n) (c : F)
    (A : Matrix (GateSide F n (n*n+1)) (GateSide F n (n*n+1)) ℝ)
    (hsupport : ∀ x y, ¬refreshConsistent (Rectangular.augmentedShare c)
      (Rectangular.augmentedShare 1) x y → A x y = 0)
    (hA : ∀ x y, |A x y| ≤ 1) :
    uavg (fun M : Refresh.«GL» F (n*n+1) =>
      largestSingularCoefficient (refreshTable (Rectangular.augmentedShare c)
        (Rectangular.augmentedShare 1) A M)) + 2 / ((vectorCard F (n*n+1) : ℝ)-2) ≤
      2 * largestSingularCoefficient A + 208 * Real.exp (-Real.log 2 * (n : ℝ) / 4) := by
  have hop := augmented_operator_bound hq hn c A hsupport hA
  have hrate := binary_augmented_local_rate hq hn
  linarith

end

end CircuitCompiler.RefreshAnalysis
