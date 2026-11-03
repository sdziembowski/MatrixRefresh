import Proofs.Refreshing.Model

/-!
# Basic properties of the refreshing model

These lemmas are used by the proofs but are not needed to construct the model. They retain the `Refreshing` namespace so their names remain unchanged.
-/

open scoped ENNReal

namespace Refreshing

/-- Every point of a nonempty finite uniform PMF has mass equal to the reciprocal carrier size. -/
@[simp] theorem uniformPMF_apply {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    uniformPMF α a = (Fintype.card α : ℝ≥0∞)⁻¹ := rfl

/-- Algebraic well-definedness of the refresh, independent of security. -/
theorem refresh_preserves_secret {n : ℕ} (x : State n) (M : RefreshMatrix n) :
    secret (refresh x M) = secret x := by
  simp only [secret, refresh, refreshLeft, refreshRight]
  rw [Matrix.dotProduct_mulVec]
  simp

end Refreshing
