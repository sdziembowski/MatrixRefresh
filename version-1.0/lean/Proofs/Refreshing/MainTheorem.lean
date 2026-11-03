import Proofs.Refreshing.Model
import Proofs.Refreshing.Theorem41

/-!
# Main theorem for Refreshing

The encoding-fiber witness and Theorem 4.1 prove the full stated bound.
-/

set_option autoImplicit false
noncomputable section

namespace Refreshing
theorem main_theorem :
    (∀ {n : ℕ} (hn : 2 ≤ n) (s : Bit), Nonempty (Encoding n s)) ∧
    (∃ C C' : ℝ, 1 ≤ C ∧ 1 ≤ C' ∧
      ∀ (n T leakage : ℕ) (hn : 2 ≤ n),
        C * (T : ℝ) * (((2 ^ (2 * leakage) : ℕ) : ℝ) ^ 3) *
            Real.rpow (((2 ^ n - 1 : ℕ) : ℝ)) (-(1 / 9 : ℝ)) ≤
          C' * (T : ℝ) *
            Real.rpow ((2 : ℕ) : ℝ) (((6 : ℕ) : ℝ) * (leakage : ℝ) - (n : ℝ) / 9) ∧
        (∀ A : Strategy n T leakage,
          statisticalDistance (transcriptDistribution hn A 0)
            (transcriptDistribution hn A 1) ≤
              C * (T : ℝ) * (((2 ^ (2 * leakage) : ℕ) : ℝ) ^ 3) *
                Real.rpow (((2 ^ n - 1 : ℕ) : ℝ)) (-(1 / 9 : ℝ)))) := by
  constructor
  · exact @encoding_nonempty
  · simpa only [firstBound, secondBound, q, K] using theorem_4_1
end Refreshing
