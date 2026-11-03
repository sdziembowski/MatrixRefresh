import Proofs.Refreshing.PrescribedFourCycle
import Proofs.Refreshing.TwoSecret

/-!
# Averaging the four prescribed-matrix rank cases

The signed full-rank contribution is retained. Only the nonnegative mixed-rank terms are enlarged before applying the exact collision normalizations.
-/

noncomputable section
open scoped BigOperators Matrix

namespace RefreshingProof
open Refreshing

/-- The unrestricted refresh table’s mean four-cycle quantity is bounded by the proved rank envelope under its zero and consistency support conditions. -/
theorem unrestricted_fourCycle_le_rankEnvelope {n : ℕ} (hn : 2 ≤ n)
    (F : Local.Table (ExtendedSharePair n) (ExtendedSharePair n))
    (hz : ∀ x y, y.2 = 0 → F x y = 0)
    (hs : ∀ x y, x.1.val ⬝ᵥ y.1.val ≠ x.2 ⬝ᵥ y.2 → F x y = 0) :
    Local.average (fun A : BinaryMatrix n =>
      Local.fourCycle (unrestrictedRefreshTable F A)) ≤
        Local.fourRankEnvelope F (q n : ℝ) := by
  classical
  have hcard : (Fintype.card (ExtendedSharePair n) : ℝ) =
      (q n : ℝ) * (2 : ℝ) ^ n := by
    rw [Fintype.card_prod, Nat.cast_mul, card_share]
    congr 1
    simp [Refreshing.Vector, Bit, ZMod.card]
  have hQ : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hq : (q n : ℝ) ≠ 0 := by have := q_real_three_le hn; linarith
  rw [unrestricted_fourCycle_prescribed_expansion, ← Local.average_smul,
    average_cycle_indices]
  calc
    _ ≤ Local.average (fun x₁ : ExtendedSharePair n =>
        Local.average (fun x₂ : ExtendedSharePair n =>
        Local.average (fun y₁ : ExtendedSharePair n =>
        Local.average (fun y₂ : ExtendedSharePair n =>
          16 * (if x₁.1 ≠ x₂.1 ∧ y₁.2 ≠ y₂.2 then
            F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂ else 0) +
          (4 * (2 : ℝ) ^ n) * (if x₁ = x₂ then F x₁ y₁ ^ 2 * F x₁ y₂ ^ 2 else 0) +
          (4 * (2 : ℝ) ^ n) * (if y₁ = y₂ then F x₁ y₁ ^ 2 * F x₂ y₁ ^ 2 else 0) +
          (2 * ((2 : ℝ) ^ n) ^ 2) * (if x₁ = x₂ ∧ y₁ = y₂ then F x₁ y₁ ^ 4 else 0))))) := by
      apply uniform_average_mono
      intro x₁
      apply uniform_average_mono
      intro x₂
      apply uniform_average_mono
      intro y₁
      apply uniform_average_mono
      intro y₂
      simpa only [mul_assoc] using cyclePrescription_four_rank_le F hz hs x₁ x₂ y₁ y₂
    _ = Local.fourRankEnvelope F (q n : ℝ) := by
      simp only [Local.average_add, Local.average_smul]
      rw [average_full_row_collision, average_full_column_collision,
        average_full_corner_collision]
      unfold Local.fourRankEnvelope Local.cycleContribution
      rw [hcard]
      simp only [mul_inv_rev, div_eq_mul_inv, inv_pow]
      field_simp
      <;> ring

end RefreshingProof
