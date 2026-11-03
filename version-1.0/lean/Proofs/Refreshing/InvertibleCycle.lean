import Proofs.Refreshing.RefreshTable
import Proofs.Refreshing.GroupedZeroExtension
import Proofs.Refreshing.FourCycleBounds

/-!
# Invertible matrices inside the unrestricted four-cycle experiment

The extra new-column coordinate contributes exactly 1/Q twice in a complete cycle, canceling the four factors sqrt(Q). The comparison by invertibility is applied only to a nonnegative complete four-cycle.
-/

noncomputable section
open scoped BigOperators Matrix

namespace RefreshingProof.Local
open Refreshing

/-- Restrict a two-endpoint table to pairs of shares related by a fixed invertible refresh matrix. -/
def matrixPullback {n : ℕ}
    (F : Table (Share n × Share n) (Share n × Share n)) (M : RefreshMatrix n) :
    Table (Share n) (Share n) :=
  fun l r => F (l, refreshLeft l M) (r, refreshRight r M)

/-- For an invertible matrix M, M · v = r holds exactly when v = M⁻¹ · r. -/
theorem matrix_mulVec_eq_iff {n : ℕ} (M : RefreshMatrix n)
    (v r : Refreshing.Vector n) :
    (M : BinaryMatrix n) *ᵥ v = r ↔ v = (↑(M⁻¹) : BinaryMatrix n) *ᵥ r := by
  constructor
  · intro h
    have h' := congrArg (fun w => (↑(M⁻¹) : BinaryMatrix n) *ᵥ w) h
    simpa using h'
  · intro h
    rw [h]
    simp

/-- For invertible M, an unrestricted refresh-table entry vanishes off the actual refreshed right share and otherwise has its stated normalized pullback value. -/
theorem unrestrictedRefreshTable_invertible_entry {n : ℕ}
    (F : Table (Share n × Share n) (Share n × Share n)) (M : RefreshMatrix n)
    (l r : Share n) (v : Refreshing.Vector n) :
    unrestrictedRefreshTable (groupedZeroExtension F) (M : BinaryMatrix n) l (r, v) =
      if v = (refreshRight r M).val then
        Real.sqrt ((2 : ℝ) ^ n) * matrixPullback F M l r else 0 := by
  by_cases hv : v = (refreshRight r M).val
  · subst v
    have heq : (M : BinaryMatrix n) *ᵥ (refreshRight r M).val = r.val := by
      simp [refreshRight]
    simp only [unrestrictedRefreshTable, heq, ite_true, eq_self]
    have h := groupedZeroExtension_nonzero F l (refreshLeft l M) r (refreshRight r M)
    exact congrArg (fun t => Real.sqrt ((2 : ℝ) ^ n) * t) h
  · have heq : (M : BinaryMatrix n) *ᵥ v ≠ r.val :=
      fun h => hv ((matrix_mulVec_eq_iff M v r.val).mp h)
    simp only [unrestrictedRefreshTable, heq, ite_false, hv]

/-- For invertible M, the unrestricted refresh-table Gram entry equals the Gram entry of the actual matrix pullback. -/
theorem unrestrictedRefreshTable_invertible_gram {n : ℕ}
    (F : Table (Share n × Share n) (Share n × Share n)) (M : RefreshMatrix n)
    (l₁ l₂ : Share n) :
    average (fun rr : ExtendedSharePair n =>
      unrestrictedRefreshTable (groupedZeroExtension F) (M : BinaryMatrix n) l₁ rr *
        unrestrictedRefreshTable (groupedZeroExtension F) (M : BinaryMatrix n) l₂ rr) =
      average (fun r : Share n => matrixPullback F M l₁ r * matrixPullback F M l₂ r) := by
  rw [average_product]
  apply average_congr
  intro r
  have hp (v : Refreshing.Vector n) :
      unrestrictedRefreshTable (groupedZeroExtension F) (M : BinaryMatrix n) l₁ (r, v) *
        unrestrictedRefreshTable (groupedZeroExtension F) (M : BinaryMatrix n) l₂ (r, v) =
      if (refreshRight r M).val = v then
        (2 : ℝ) ^ n * (matrixPullback F M l₁ r * matrixPullback F M l₂ r) else 0 := by
    rw [unrestrictedRefreshTable_invertible_entry, unrestrictedRefreshTable_invertible_entry]
    by_cases hv : v = (refreshRight r M).val
    · simp only [hv, ite_true, eq_self]
      calc
        _ = (Real.sqrt ((2 : ℝ) ^ n) * Real.sqrt ((2 : ℝ) ^ n)) *
            (matrixPullback F M l₁ r * matrixPullback F M l₂ r) := by ring
        _ = _ := by rw [Real.mul_self_sqrt (by positivity)]
    · simp only [hv, ite_false, Ne.symm hv, zero_mul]
  simp_rw [hp]
  rw [average_eq_indicator]
  have hcard : (Fintype.card (Refreshing.Vector n) : ℝ) = (2 : ℝ) ^ n := by
    simp [Refreshing.Vector, ZMod.card]
  rw [hcard]
  have hQ : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

/-- Exact cancellation of the added coordinate and sqrt(Q) normalization. -/
theorem unrestrictedRefreshTable_invertible_cycle {n : ℕ}
    (F : Table (Share n × Share n) (Share n × Share n)) (M : RefreshMatrix n) :
    fourCycle (unrestrictedRefreshTable (groupedZeroExtension F) (M : BinaryMatrix n)) =
      fourCycle (matrixPullback F M) := by
  rw [fourCycle_gram, fourCycle_gram]
  simp only [unrestrictedRefreshTable_invertible_gram]

/-- A complete four-cycle is nonnegative, so the proved constant-density comparison with all binary matrices applies despite signed individual entries. -/
theorem average_refresh_cycle_le_unrestricted {n : ℕ}
    (F : Table (Share n × Share n) (Share n × Share n)) :
    average (fun M : RefreshMatrix n => fourCycle (matrixPullback F M)) ≤
      4 * average (fun A : BinaryMatrix n =>
        fourCycle (unrestrictedRefreshTable (groupedZeroExtension F) A)) := by
  have h := average_invertible_le_four n
    (fun A => fourCycle (unrestrictedRefreshTable (groupedZeroExtension F) A))
    (fun A => fourCycle_nonneg _)
  simp_rw [unrestrictedRefreshTable_invertible_cycle] at h
  exact h

end RefreshingProof.Local
