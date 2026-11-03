import Proofs.Refreshing.ZeroExtension
import Proofs.Refreshing.TwoSecret

/-!
# Extending the two new shares to unrestricted binary vectors
-/

noncomputable section
open scoped BigOperators Matrix

namespace RefreshingProof.Local
open Refreshing

/-- An old nonzero share paired with an unrestricted new binary vector. -/
abbrev RawGrouped (n : ℕ) := Share n × Refreshing.Vector n

/-- Extend a two-endpoint share table by zero whenever either new share vector is zero. -/
def groupedZeroExtension {n : ℕ}
    (F : Table (Share n × Share n) (Share n × Share n)) : Table (RawGrouped n) (RawGrouped n) :=
  extendTableZero (fun x : RawGrouped n => x.2 ≠ 0) (fun y : RawGrouped n => y.2 ≠ 0)
    (fun x y => F (nonzeroSecondEquiv (Share n) (Refreshing.Vector n) x)
      (nonzeroSecondEquiv (Share n) (Refreshing.Vector n) y))

/-- The density q(n)/2ⁿ of nonzero vectors among all new binary vectors. -/
def newShareDensity (n : ℕ) : ℝ := (q n : ℝ) / (2 : ℝ) ^ n

/-- The nonzero-new-share subset of the grouped carrier has density q(n)/2ⁿ. -/
theorem groupedNonzero_density {n : ℕ} (hn : 2 ≤ n) :
    ((Fintype.card {x : RawGrouped n // x.2 ≠ 0} : ℝ) / Fintype.card (RawGrouped n)) =
      newShareDensity n := by
  have hq : (q n : ℝ) ≠ 0 := by have h := q_real_three_le hn; linarith
  have hsub : Fintype.card {x : RawGrouped n // x.2 ≠ 0} = q n * q n := by
    rw [Fintype.card_congr (nonzeroSecondEquiv (Share n) (Refreshing.Vector n)),
      Fintype.card_prod]
    simp only [card_share]
  have hraw : Fintype.card (RawGrouped n) = q n * 2 ^ n := by
    simp [RawGrouped, Fintype.card_prod, Share, q, Refreshing.Vector, ZMod.card]
  simp only [hsub, hraw, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, newShareDensity]
  field_simp

/-- The nonzero-new-share density is nonnegative. -/
theorem newShareDensity_nonneg (n : ℕ) : 0 ≤ newShareDensity n := by
  unfold newShareDensity
  positivity

/-- The nonzero-new-share density is at most one. -/
theorem newShareDensity_le_one (n : ℕ) : newShareDensity n ≤ 1 := by
  have hq : (q n : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.sub_le (2 ^ n) 1)
  exact (div_le_one (by positivity)).mpr hq

/-- For n ≥ 2, the carrier of nonzero binary shares is nonempty. -/
theorem grouped_share_nonempty {n : ℕ} (hn : 2 ≤ n) : Nonempty (Share n) := by
  obtain ⟨x⟩ := encoding_nonempty hn (0 : Bit)
  exact ⟨x.val.1⟩

/-- Zero-extending both new-share coordinates multiplies the squared normalized L₂ norm by the square of their nonzero density. -/
theorem normSq_groupedZeroExtension {n : ℕ} (hn : 2 ≤ n)
    (F : Table (Share n × Share n) (Share n × Share n)) :
    normSq (groupedZeroExtension F) = newShareDensity n ^ 2 * normSq F := by
  let v : Share n := Classical.choice (grouped_share_nonempty hn)
  let : Nonempty (RawGrouped n) := ⟨(v, v.val)⟩
  let : Nonempty {x : RawGrouped n // x.2 ≠ 0} := ⟨⟨(v, v.val), v.property⟩⟩
  unfold groupedZeroExtension
  rw [normSq_extendTableZero]
  simp only [groupedNonzero_density hn]
  rw [normSq_reindex]
  ring

/-- Zero-extending both new-share coordinates multiplies the four-cycle quantity by the fourth power of their nonzero density. -/
theorem fourCycle_groupedZeroExtension {n : ℕ} (hn : 2 ≤ n)
    (F : Table (Share n × Share n) (Share n × Share n)) :
    fourCycle (groupedZeroExtension F) = newShareDensity n ^ 4 * fourCycle F := by
  let v : Share n := Classical.choice (grouped_share_nonempty hn)
  let : Nonempty (RawGrouped n) := ⟨(v, v.val)⟩
  let : Nonempty {x : RawGrouped n // x.2 ≠ 0} := ⟨⟨(v, v.val), v.property⟩⟩
  unfold groupedZeroExtension
  rw [fourCycle_extendTableZero]
  simp only [groupedNonzero_density hn]
  rw [fourCycle_reindex]
  ring

/-- The grouped zero extension agrees with the original table when both new shares are nonzero. -/
@[simp] theorem groupedZeroExtension_nonzero {n : ℕ}
    (F : Table (Share n × Share n) (Share n × Share n)) (l l' r r' : Share n) :
    groupedZeroExtension F (l, l'.val) (r, r'.val) = F (l, l') (r, r') := by
  simp [groupedZeroExtension, extendTableZero, nonzeroSecondEquiv, l'.property, r'.property]

/-- Extension by zero preserves a nonnegative uniform absolute entry bound. -/
theorem groupedZeroExtension_entry_bound {n : ℕ}
    (F : Table (Share n × Share n) (Share n × Share n)) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ x y, |F x y| ≤ B) : ∀ x y, |groupedZeroExtension F x y| ≤ B := by
  intro x y
  by_cases hx : x.2 ≠ 0 <;> by_cases hy : y.2 ≠ 0
  · simpa [groupedZeroExtension, extendTableZero, hx, hy, nonzeroSecondEquiv] using
      hF (x.1, ⟨x.2, hx⟩) (y.1, ⟨y.2, hy⟩)
  all_goals simpa [groupedZeroExtension, extendTableZero, hx, hy] using hB

/-- For a nonzero new left share, the extended row’s mean square is the original row mean square times the nonzero density. -/
theorem groupedZeroExtension_row_average {n : ℕ} (hn : 2 ≤ n)
    (F : Table (Share n × Share n) (Share n × Share n))
    (x : RawGrouped n) (hx : x.2 ≠ 0) :
    average (fun y => groupedZeroExtension F x y ^ 2) =
      newShareDensity n * average (fun y => F (x.1, ⟨x.2, hx⟩) y ^ 2) := by
  let v : Share n := Classical.choice (grouped_share_nonempty hn)
  let : Nonempty (RawGrouped n) := ⟨(v, v.val)⟩
  let : Nonempty {x : RawGrouped n // x.2 ≠ 0} := ⟨⟨(v, v.val), v.property⟩⟩
  have hp (y : RawGrouped n) : groupedZeroExtension F x y ^ 2 =
      extendZero (fun y : RawGrouped n => y.2 ≠ 0)
        (fun y => F (x.1, ⟨x.2, hx⟩)
          (nonzeroSecondEquiv (Share n) (Refreshing.Vector n) y) ^ 2) y := by
    by_cases hy : y.2 ≠ 0 <;>
      simp [groupedZeroExtension, extendTableZero, extendZero, nonzeroSecondEquiv, hx, hy]
  simp_rw [hp]
  rw [average_extendZero, groupedNonzero_density hn]
  exact congrArg (fun c => newShareDensity n * c)
    (average_equiv (nonzeroSecondEquiv (Share n) (Refreshing.Vector n))
      (fun y => F (x.1, ⟨x.2, hx⟩) y ^ 2))

/-- Extension by zero preserves every uniform row mean-square bound. -/
theorem groupedZeroExtension_row_bound {n : ℕ} (hn : 2 ≤ n)
    (F : Table (Share n × Share n) (Share n × Share n)) {R : ℝ}
    (hF : ∀ x, average (fun y => F x y ^ 2) ≤ R ^ 2) :
    ∀ x, average (fun y => groupedZeroExtension F x y ^ 2) ≤ R ^ 2 := by
  intro x
  by_cases hx : x.2 ≠ 0
  · rw [groupedZeroExtension_row_average hn F x hx]
    calc
      _ ≤ 1 * average (fun y => F (x.1, ⟨x.2, hx⟩) y ^ 2) :=
        mul_le_mul_of_nonneg_right (newShareDensity_le_one n)
          (average_nonneg (fun _ => sq_nonneg _))
      _ ≤ _ := by simpa only [one_mul] using hF (x.1, ⟨x.2, hx⟩)
  · simp [groupedZeroExtension, extendTableZero, hx, average]
    positivity

/-- Grouped zero extension commutes with transposing the table. -/
theorem groupedZeroExtension_transpose {n : ℕ}
    (F : Table (Share n × Share n) (Share n × Share n)) :
    groupedZeroExtension (fun y x => F x y) = fun y x => groupedZeroExtension F x y := by
  funext y x
  by_cases hx : x.2 ≠ 0 <;> by_cases hy : y.2 ≠ 0 <;>
    simp [groupedZeroExtension, extendTableZero, hx, hy]

/-- Extension by zero preserves every uniform column mean-square bound. -/
theorem groupedZeroExtension_column_bound {n : ℕ} (hn : 2 ≤ n)
    (F : Table (Share n × Share n) (Share n × Share n)) {R : ℝ}
    (hF : ∀ y, average (fun x => F x y ^ 2) ≤ R ^ 2) :
    ∀ y, average (fun x => groupedZeroExtension F x y ^ 2) ≤ R ^ 2 := by
  simpa only [groupedZeroExtension_transpose] using
    groupedZeroExtension_row_bound hn (fun y x => F x y) hF

/-- The grouped extension vanishes when the new left vector is zero. -/
@[simp] theorem groupedZeroExtension_left_zero {n : ℕ}
    (F : Table (Share n × Share n) (Share n × Share n)) (l : Share n) (rr : RawGrouped n) :
    groupedZeroExtension F (l, 0) rr = 0 := by
  simp [groupedZeroExtension, extendTableZero]

/-- The grouped extension vanishes when the new right vector is zero. -/
@[simp] theorem groupedZeroExtension_right_zero {n : ℕ}
    (F : Table (Share n × Share n) (Share n × Share n)) (ll : RawGrouped n) (r : Share n) :
    groupedZeroExtension F ll (r, 0) = 0 := by
  by_cases hl : ll.2 ≠ 0 <;> simp [groupedZeroExtension, extendTableZero, hl]

/-- Consistency support survives extension by zero to unrestricted new shares. -/
theorem groupedZeroExtension_supported {n : ℕ}
    (F : Table (Share n × Share n) (Share n × Share n))
    (hF : ∀ ll rr, ll.1.val ⬝ᵥ rr.1.val ≠ ll.2.val ⬝ᵥ rr.2.val → F ll rr = 0) :
    ∀ ll rr : RawGrouped n,
      ll.1.val ⬝ᵥ rr.1.val ≠ ll.2 ⬝ᵥ rr.2 → groupedZeroExtension F ll rr = 0 := by
  intro ll rr hne
  by_cases hl : ll.2 ≠ 0 <;> by_cases hr : rr.2 ≠ 0
  · simpa [groupedZeroExtension, extendTableZero, nonzeroSecondEquiv, hl, hr] using
      hF (ll.1, ⟨ll.2, hl⟩) (rr.1, ⟨rr.2, hr⟩) hne
  all_goals simp [groupedZeroExtension, extendTableZero, hl, hr]

end RefreshingProof.Local
