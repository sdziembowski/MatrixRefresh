import Proofs.Compiler.GateApproximation.Refreshing.EnergyCompression.Induction
import Proofs.Compiler.Foundations.LinearAlgebra.Mixing



/-!
# Parameters for weighted-factor compression

The input singular values are retained. Balancing the weighted Gram error and the elementary residual estimate uses θ=κ^(1/12), H=J=θ⁻¹, β=θ³.
-/

set_option autoImplicit false

namespace TableAnalysis.EnergyCompression

open MatrixRefresh Refresh TableAnalysis

noncomputable section

/-
Mathematical definition (normal notation): For K, pMin, κ, H, J, β, c, Γ, m ∈ ℝ, define

compressionRawError(K, pMin, κ, H, J, β, c, Γ, m) := 2 · c / (H · √pMin) + 2 · m / (pMin · J) + √K · Γ · (√κ · H · J / β + H² · β).
-/
def compressionRawError (K pMin κ H J β c Γ m : ℝ) : ℝ :=
  2 * c / (H * Real.sqrt pMin) + 2 * m / (pMin * J) +
    Real.sqrt K * Γ * (Real.sqrt κ * H * J / β + H ^ 2 * β)

/-
Mathematical definition (normal notation): For F a set; n ∈ ℕ, assume F is finite. define

θ(n) := (mixingCoefficient(F, n))^(1 / 12).
-/
def theta (F : Type*) [Fintype F] (n : ℕ) : ℝ :=
  mixingCoefficient F n ^ ((1 : ℝ) / 12)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

0 < θ(F, n).
-/
theorem theta_pos (hn : 2 ≤ n) : 0 < theta F n :=
  Real.rpow_pos_of_pos (mixingCoefficient_pos hn) _

-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

(θ(F, n))¹² = mixingCoefficient(F, n).
-/
theorem theta_power (hn : 2 ≤ n) : theta F n ^ (12 : ℕ) = mixingCoefficient F n := by
  unfold theta
  rw [← Real.rpow_natCast, ← Real.rpow_mul (mixingCoefficient_pos (F := F) hn).le]
  norm_num

-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

θ(F, n) ≤ 1.
-/
theorem theta_le_one (hn : 2 ≤ n) : theta F n ≤ 1 := by
  exact Real.rpow_le_one (mixingCoefficient_nonneg hn) (mixingCoefficient_le_one hn)
    (by norm_num)

omit [Field F] [Fintype F] [DecidableEq F] in
-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For θ ∈ ℝ, assume 0 < θ. Then

√(θ¹²) · (θ)⁻¹ · (θ)⁻¹ / θ³ = θ.
-/
theorem gram_parameter_identity (θ : ℝ) (hθ : 0 < θ) :
    Real.sqrt (θ ^ 12) * θ⁻¹ * θ⁻¹ / θ ^ 3 = θ := by
  have hp : θ ^ 12 = (θ ^ 6) ^ 2 := by ring
  rw [hp, Real.sqrt_sq (by positivity)]
  field_simp

omit [Field F] [Fintype F] [DecidableEq F] in
-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For θ ∈ ℝ, assume 0 < θ. Then

((θ)⁻¹)² · θ³ = θ.
-/
theorem residual_parameter_identity (θ : ℝ) (hθ : 0 < θ) :
    (θ⁻¹) ^ 2 * θ ^ 3 = θ := by
  field_simp

omit [Field F] [Fintype F] [DecidableEq F] in
-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For θ ∈ ℝ, assume 0 < θ; θ ≤ 1. Then

1 ≤ (θ)⁻¹ ∧ 0 < θ³ ∧ θ³ ≤ 1.
-/
theorem compression_parameters (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    1 ≤ θ⁻¹ ∧ 0 < θ ^ 3 ∧ θ ^ 3 ≤ 1 := by
  exact ⟨(one_le_inv₀ hθ).2 hθ1, by positivity, pow_le_one₀ hθ.le hθ1⟩

omit [Field F] [Fintype F] [DecidableEq F] in
-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K, pMin, θ, c, Γ, m ∈ ℝ, assume 0 < θ. Then

compressionRawError(K, pMin, (θ¹²), (θ)⁻¹, (θ)⁻¹, (θ³), c, Γ, m) = compressionError(K, pMin, θ, c, Γ, m).
-/
theorem compressionRawError_eq (K pMin θ c Γ m : ℝ) (hθ : 0 < θ) :
    compressionRawError K pMin (θ ^ 12) θ⁻¹ θ⁻¹ (θ ^ 3) c Γ m =
      compressionError K pMin θ c Γ m := by
  unfold compressionRawError compressionError
  rw [gram_parameter_identity θ hθ, residual_parameter_identity θ hθ]
  field_simp
  ring

end

end TableAnalysis.EnergyCompression
