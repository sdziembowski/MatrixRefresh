import Proofs.Compiler.GateApproximation.MatrixPhase.Operator



/-!
# Explicit exponential rates for the current tensor local estimate
-/
set_option autoImplicit false

set_option maxHeartbeats 1000000

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

-- Auxiliary lemma (cutoff-based comparison); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For N ∈ ℝ, assume 2 ≤ N. Then

((N - 1)²)^(−(1 / 8)) ≤ 2 · N^(−(1 / 4)) .
-/
theorem feature_rate_le {N : ℝ} (hN : 2 ≤ N) :
    ((N-1)^2) ^ (-(1/8 : ℝ)) ≤ 2 * N ^ (-(1/4 : ℝ)) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < N-1 := by linarith
  have heq : ((N-1)^2) ^ (-(1/8 : ℝ)) = (N-1) ^ (-(1/4 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN1.le]
    congr 1
    norm_num
  rw [heq]
  have hbase := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < N/2)
    (by linarith : N/2 ≤ N-1) (by norm_num : -(1/4 : ℝ) ≤ 0)
  have hsmall : (2 : ℝ) ^ (1/4 : ℝ) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1/4 : ℝ) ≤ 1)
  have heq' : (N/2) ^ (-(1/4 : ℝ)) = (2 : ℝ)^(1/4 : ℝ)*N^(-(1/4 : ℝ)) := by
    rw [Real.div_rpow hN0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [div_inv_eq_mul, mul_comm]
  rw [heq'] at hbase
  exact hbase.trans (mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hN0.le _))

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

-- Auxiliary lemma (cutoff-based comparison); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume |F| = 2; 2 ≤ n. Then

(tensorShareCount(F, n))^(−(1 / 8)) ≤ 2 · exp((-(log(2)) · n / 4)).
-/
theorem binary_tensor_feature_rate (hq : fieldCard F = 2) (hn : 2 ≤ n) :
    tensorShareCount F n ^ (-(1/8 : ℝ)) ≤
      2 * Real.exp (-Real.log 2 * (n : ℝ) / 4) := by
  have hN := vectorCard_real_ge_four (F := F) hn
  have h := feature_rate_le (by linarith : 2 ≤ (vectorCard F n : ℝ))
  change tensorShareCount F n ^ (-(1/8 : ℝ)) ≤ _ at h
  have heq : (vectorCard F n : ℝ) ^ (-(1/4 : ℝ)) = Real.exp (-Real.log 2 * (n : ℝ) / 4) := by
    simp only [vectorCard, hq, Nat.cast_pow, Nat.cast_ofNat]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  simpa only [heq] using h

-- Auxiliary lemma (cutoff-based comparison); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume |F| = 2; 2 ≤ n. Then

2 / (|F|^(n · n) - 2) ≤ 4 · exp((-(log(2)) · n / 4)).
-/
theorem binary_tensor_density_rate (hq : fieldCard F = 2) (hn : 2 ≤ n) :
    2 / ((vectorCard F (n*n) : ℝ)-2) ≤ 4 * Real.exp (-Real.log 2 * (n : ℝ) / 4) := by
  have hQ := vectorCard_real_ge_four (F := F) (show 2 ≤ n*n by nlinarith)
  have hpow : (vectorCard F n : ℝ) ≤ (vectorCard F (n*n) : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (fieldCard_pos (F := F)) (show n ≤ n*n by nlinarith)
  have hN := vectorCard_real_ge_four (F := F) hn
  have hfirst : 2 / ((vectorCard F (n*n) : ℝ)-2) ≤ 4 / (vectorCard F n : ℝ) := by
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
  exact hfirst.trans (by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hrpow (by norm_num : (0 : ℝ) ≤ 4))

/-- The supported-operator error and density-conversion correction together have the paper's `2^(-n/4)` scale, with an explicit absolute constant. -/
-- Auxiliary lemma (cutoff-based comparison); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume |F| = 2; 2 ≤ n. Then

(2 · √6 + 96) · (tensorShareCount(F, n))^(−(1 / 8)) + 2 / (|F|^(n · n) - 2) ≤ 208 · exp((-(log(2)) · n / 4)).
-/
theorem binary_tensor_local_rate (hq : fieldCard F = 2) (hn : 2 ≤ n) :
    (2*Real.sqrt 6+96)*tensorShareCount F n ^ (-(1/8 : ℝ)) +
      2 / ((vectorCard F (n*n) : ℝ)-2) ≤ 208 * Real.exp (-Real.log 2 * (n : ℝ) / 4) := by
  have hfeature := binary_tensor_feature_rate hq hn
  have hdensity := binary_tensor_density_rate hq hn
  have hconst : 2*Real.sqrt 6+96 ≤ 102 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6), Real.sqrt_nonneg 6]
  have h := mul_le_mul hconst hfeature (Real.rpow_nonneg
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) (tensorShareCount_geometry (F := F) hn).1) _)
    (by norm_num : (0 : ℝ) ≤ 102)
  linarith

end

end CircuitCompiler.RefreshAnalysis
