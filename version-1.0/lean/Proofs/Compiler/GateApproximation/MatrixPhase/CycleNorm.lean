import Proofs.Compiler.Foundations.LinearAlgebra.GramBounds



/-!
# The signed four-cycle is bounded by operator norm times L2 energy
-/
set_option autoImplicit false

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); v ∈ I → ℝ, we have

𝔼ᵢ [(𝔼ⱼ [A(i, j) · v(j)])²] ≤ (‖ A‖ₒₚ)² · 𝔼ⱼ [(v(j))²].
-/
theorem normalized_matrix_action_sq (A : Matrix I I ℝ) (v : I → ℝ) :
    uavg (fun i => (uavg (fun j => A i j * v j)) ^ 2) ≤
      largestSingularCoefficient A ^ 2 * uavg (fun j => v j ^ 2) := by
  have h := mul_le_mul_of_nonneg_left (sum_sq_matrix_action_le A v)
    (by positivity : (0 : ℝ) ≤ (Fintype.card I : ℝ)⁻¹ ^ 3)
  unfold uavg largestSingularCoefficient
  simp_rw [mul_pow, ← Finset.mul_sum]
  convert h using 1 <;> ring

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); i ∈ I, we have

𝔼ⱼ [(rowProduct(A, i, j))²] ≤ (‖ A‖ₒₚ)² · 𝔼ⱼ [(A(i, j))²].
-/
theorem rowProduct_energy_le (A : Matrix I I ℝ) (i : I) :
    uavg (fun j => rowProduct A i j ^ 2) ≤ largestSingularCoefficient A ^ 2 * uavg (fun j => A i j ^ 2) := by
  simpa only [rowProduct, mul_comm] using normalized_matrix_action_sq A (A i)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I), we have

fourCycle(A) ≤ (‖ A‖ₒₚ)² · 𝔼ᵢ [𝔼ⱼ [(A(i, j))²]].
-/
theorem fourCycle_le_op_sq_energy (A : Matrix I I ℝ) :
    fourCycle A ≤ largestSingularCoefficient A ^ 2 * uavg (fun i => uavg (fun j => A i j ^ 2)) := by
  have h := uavg_mono (rowProduct_energy_le A)
  change fourCycle A ≤ _ at h
  simpa only [uavg, ← Finset.mul_sum, mul_assoc, mul_left_comm] using h

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I), we have

fourCycle(A) ≤ (‖ A‖ₒₚ)² · (‖ A‖₂)².
-/
theorem fourCycle_le_op_sq_l2_sq (A : Matrix I I ℝ) :
    fourCycle A ≤ largestSingularCoefficient A ^ 2 * tableL2Norm A ^ 2 := by
  rw [tableL2Norm_sq, signedL2Sq, uavg_prod]
  exact fourCycle_le_op_sq_energy A

end

end CircuitCompiler.RefreshAnalysis
