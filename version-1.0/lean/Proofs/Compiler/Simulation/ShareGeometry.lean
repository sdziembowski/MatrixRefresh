import Proofs.Compiler.Construction.Parameters
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.InitialDiscrepancy

/-!
# Binary share geometry for the finite bound (Section 5.4)

The nonzero share count is q = 2ⁿ−1, and the two-secret discrepancy is at most 4/√(q−1). These facts are used with the current paper's local full-retry comparison.
-/
noncomputable section
namespace CircuitCompiler.SimulationParameters
open Refresh MatrixRefresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- The discrepancy parameter is at most 4/√(q − 1), where q is the nonzero-share count. -/
theorem zeta_le_four_share_card (hq : fieldCard F = 2) (hn : 2 ≤ n) :
    zeta F n ≤ 4 / Real.sqrt ((Fintype.card (U F n):ℝ)-1) := by
  have hcard : (Fintype.card (U F n):ℝ) = (vectorCard F n:ℝ)-1 := by
    rw [nonzero_vector_card]
    change (shareCard F n:ℝ) = _
    exact shareCard_cast_real (F := F) (n := n)
  have hN := vectorCard_real_ge_four (F := F) hn
  rw [zeta, hq]
  norm_num only [Nat.cast_ofNat]
  apply div_le_div_of_nonneg_left (by norm_num)
    (Real.sqrt_pos.mpr (by rw [hcard]; linarith))
  exact Real.sqrt_le_sqrt (by rw [hcard]; linarith)

/-- Over the binary field, the number of nonzero n-dimensional shares is q = 2ⁿ − 1. -/
theorem share_card_binary (hq : fieldCard F = 2) :
    (Fintype.card (U F n):ℝ) = (2:ℝ)^n-1 := by
  rw [nonzero_vector_card]
  change (shareCard F n:ℝ) = _
  rw [shareCard_cast_real]
  simp [vectorCard,hq]

/-- The space of nonzero n-bit shares has at least three points when n ≥ 2. -/
theorem share_card_ge_three (hq : fieldCard F = 2) (hn : 2 ≤ n) :
    3 ≤ (Fintype.card (U F n) : ℝ) := by
  rw [nonzero_vector_card]
  have hN := vectorCard_real_ge_four (F := F) hn
  change 3 ≤ (shareCard F n : ℝ)
  rw [shareCard_cast_real]
  linarith

end CircuitCompiler.SimulationParameters
