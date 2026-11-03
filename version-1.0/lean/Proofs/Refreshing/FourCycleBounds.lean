import Proofs.Refreshing.LocalSVD
import Proofs.Refreshing.GramVariance
import Mathlib.Tactic

/-!
# Analytic bounds for the four rank cases

These finite-table estimates preserve complete four-cycle positivity. They do not replace signed products by their absolute values before the collision terms have been separated.
-/

noncomputable section
open scoped BigOperators

namespace RefreshingProof.Local

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The four-cycle average restricted to the specified row-pair and column-pair relations. -/
def cycleContribution (F : Table X Y) (p : X → X → Prop) (q : Y → Y → Prop)
    [DecidableRel p] [DecidableRel q] : ℝ :=
  average (fun x₁ => average (fun x₂ => average (fun y₁ => average (fun y₂ =>
    if p x₁ x₂ ∧ q y₁ y₂ then
      F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂ else 0))))

/-- Any restriction depending only on the two rows leaves a nonnegative complete four-cycle in the two columns. -/
theorem row_cycleContribution_nonneg (F : Table X Y) (p : X → X → Prop)
    [DecidableRel p] : 0 ≤ cycleContribution F p (fun _ _ => True) := by
  unfold cycleContribution
  apply average_nonneg
  intro x₁
  apply average_nonneg
  intro x₂
  by_cases hp : p x₁ x₂
  · simp only [hp, and_self, ite_true]
    have heq : average (fun y₁ => average (fun y₂ =>
        F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂)) =
          (average (fun y => F x₁ y * F x₂ y)) ^ 2 := by
      rw [pow_two, average_mul_average]
      apply average_congr
      intro y₁
      apply average_congr
      intro y₂
      ring
    rw [heq]
    exact sq_nonneg _
  · simp [hp, average]

/-- Transposing a table exchanges the row and column restrictions in its four-cycle contribution. -/
theorem cycleContribution_transpose (F : Table X Y)
    (p : X → X → Prop) (q : Y → Y → Prop) [DecidableRel p] [DecidableRel q] :
    cycleContribution F p q = cycleContribution (fun y x => F x y) q p := by
  unfold cycleContribution
  rw [average_pair_comm]
  apply average_congr
  intro y₁
  apply average_congr
  intro y₂
  apply average_congr
  intro x₁
  apply average_congr
  intro x₂
  by_cases hp : p x₁ x₂ <;> by_cases hq : q y₁ y₂
  all_goals simp only [hp, hq, and_self, and_true, true_and, and_false, false_and,
    ite_true, ite_false] <;> ring

/-- A four-cycle contribution restricted only by the column-pair relation is nonnegative. -/
theorem column_cycleContribution_nonneg (F : Table X Y) (q : Y → Y → Prop)
    [DecidableRel q] : 0 ≤ cycleContribution F (fun _ _ => True) q := by
  rw [cycleContribution_transpose]
  exact row_cycleContribution_nonneg _ q

/-- Inclusion-exclusion with both single-collision contributions nonnegative. Only the intersection can increase the upper bound. -/
theorem restricted_fourCycle_le (F : Table X Y)
    (p : X → X → Prop) (q : Y → Y → Prop) [DecidableRel p] [DecidableRel q] :
    cycleContribution F (fun x₁ x₂ => ¬p x₁ x₂) (fun y₁ y₂ => ¬q y₁ y₂) ≤
      fourCycle F + cycleContribution F p q := by
  have heq : cycleContribution F (fun x₁ x₂ => ¬p x₁ x₂) (fun y₁ y₂ => ¬q y₁ y₂) =
      fourCycle F - cycleContribution F p (fun _ _ => True) -
        cycleContribution F (fun _ _ => True) q + cycleContribution F p q := by
    have hpoint (x₁ x₂ : X) (y₁ y₂ : Y) :
        (if ¬p x₁ x₂ ∧ ¬q y₁ y₂ then
          F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂ else 0) =
        F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂ -
        (if p x₁ x₂ ∧ True then F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂ else 0) -
        (if True ∧ q y₁ y₂ then F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂ else 0) +
        (if p x₁ x₂ ∧ q y₁ y₂ then F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂ else 0) := by
      by_cases hp : p x₁ x₂ <;> by_cases hq : q y₁ y₂
      all_goals simp only [hp, hq, not_true_eq_false, not_false_eq_true, and_self,
        and_true, true_and, and_false, false_and, ite_true, ite_false] <;> ring
    unfold cycleContribution fourCycle
    simp_rw [hpoint, average_add, average_sub]
  have hp := row_cycleContribution_nonneg F p
  have hq := column_cycleContribution_nonneg F q
  linarith

/-- Each mixed-rank term is controlled by a pointwise row energy bound and one averaged energy, without assuming the entries are nonnegative. -/
theorem row_second_moment_bound (F : Table X Y) {R : ℝ}
    (hrow : ∀ x, average (fun y => F x y ^ 2) ≤ R ^ 2) :
    average (fun x => (average (fun y => F x y ^ 2)) ^ 2) ≤ R ^ 2 * normSq F := by
  calc
    _ ≤ average (fun x => R ^ 2 * average (fun y => F x y ^ 2)) := by
      apply average_mono
      intro x
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hrow x)
        (average_nonneg (fun y => sq_nonneg (F x y)))
    _ = _ := by simp only [average_smul, normSq, pairing, pow_two]

/-- A uniform column mean-square bound R² bounds the mean squared column energy by R² times the full squared L₂ norm. -/
theorem column_second_moment_bound (F : Table X Y) {R : ℝ}
    (hcolumn : ∀ y, average (fun x => F x y ^ 2) ≤ R ^ 2) :
    average (fun y => (average (fun x => F x y ^ 2)) ^ 2) ≤ R ^ 2 * normSq F := by
  have h := row_second_moment_bound (fun y x => F x y) hcolumn
  have heq : normSq (fun y x => F x y) = normSq F := by
    unfold normSq pairing
    exact average_comm _
  rw [heq] at h
  exact h

/-- A uniform absolute entry bound B bounds the mean fourth power by B² times the squared L₂ norm. -/
theorem fourth_moment_bound (F : Table X Y) {B : ℝ} (hB : 0 ≤ B)
    (hentry : ∀ x y, |F x y| ≤ B) :
    average (fun x => average (fun y => F x y ^ 4)) ≤ B ^ 2 * normSq F := by
  calc
    _ ≤ average (fun x => average (fun y => B ^ 2 * F x y ^ 2)) := by
      apply average_mono
      intro x
      apply average_mono
      intro y
      have hs : F x y ^ 2 ≤ B ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hentry x y)
      have hp := mul_le_mul_of_nonneg_right hs (sq_nonneg (F x y))
      nlinarith
    _ = _ := by simp only [average_smul, normSq, pairing, pow_two]

/-- The collision-intersection estimate at the level of four entries. Only the middle two need the pointwise bound. -/
theorem four_entries_le_two_squares {a b c d B : ℝ} (hB : 0 ≤ B)
    (hb : |b| ≤ B) (hc : |c| ≤ B) :
    a * b * c * d ≤ (B ^ 2 / 2) * (a ^ 2 + d ^ 2) := by
  have hbc : |b * c| ≤ B ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hb hc (abs_nonneg _) hB
  have had : |a * d| ≤ (a ^ 2 + d ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|a| - |d|), sq_abs a, sq_abs d]
  calc
    _ ≤ |a * b * c * d| := le_abs_self _
    _ = |b * c| * |a * d| := by simp only [abs_mul]; ring
    _ ≤ B ^ 2 * ((a ^ 2 + d ^ 2) / 2) :=
      mul_le_mul hbc had (abs_nonneg _) (sq_nonneg _)
    _ = _ := by ring

/-- A function equal to c at one fixed point and zero elsewhere has uniform mean c divided by the carrier size. -/
theorem average_eq_indicator {A : Type*} [Fintype A] [DecidableEq A]
    (a : A) (c : ℝ) :
    average (fun a' => if a = a' then c else 0) = (Fintype.card A : ℝ)⁻¹ * c := by
  simp [average]

/-- Restricting the first coordinate of a uniform pair to one fixed value contributes the reciprocal size of its carrier. -/
theorem average_pair_first_eq {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty B] [DecidableEq A] (a : A) (c : ℝ) :
    average (fun x : A × B => if a = x.1 then c else 0) =
      (Fintype.card A : ℝ)⁻¹ * c := by
  rw [average_product]
  calc
    _ = average (fun a' : A => if a = a' then c else 0) :=
      average_congr (fun _ => RefreshingProof.average_const _)
    _ = _ := average_eq_indicator a c

/-- Restricting the second coordinate of a uniform pair to one fixed value contributes the reciprocal size of its carrier. -/
theorem average_pair_second_eq {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [DecidableEq B] (b : B) (c : ℝ) :
    average (fun x : A × B => if b = x.2 then c else 0) =
      (Fintype.card B : ℝ)⁻¹ * c := by
  rw [average_product]
  simp only [average_eq_indicator, RefreshingProof.average_const]

/-- After colliding one row coordinate and one column coordinate, a single corner retains its full product marginal, with the exact collision probability. -/
theorem collision_corner_average {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    [DecidableEq A] [DecidableEq D] (H : (A × B) → (C × D) → ℝ) :
    average (fun x₁ : A × B => average (fun x₂ : A × B =>
      average (fun y₁ : C × D => average (fun y₂ : C × D =>
        if x₁.1 = x₂.1 ∧ y₁.2 = y₂.2 then H x₁ y₁ else 0)))) =
      ((Fintype.card A : ℝ) * Fintype.card D)⁻¹ *
        average (fun x => average (H x)) := by
  calc
    _ = average (fun x₁ : A × B => average (fun y₁ : C × D =>
        average (fun x₂ : A × B => average (fun y₂ : C × D =>
          if x₁.1 = x₂.1 ∧ y₁.2 = y₂.2 then H x₁ y₁ else 0)))) := by
      apply average_congr
      intro x₁
      exact average_comm _
    _ = average (fun x₁ : A × B => average (fun y₁ : C × D =>
        (Fintype.card A : ℝ)⁻¹ * ((Fintype.card D : ℝ)⁻¹ * H x₁ y₁))) := by
      apply average_congr
      intro x₁
      apply average_congr
      intro y₁
      have hin (x₂ : A × B) :
          average (fun y₂ : C × D =>
            if x₁.1 = x₂.1 ∧ y₁.2 = y₂.2 then H x₁ y₁ else 0) =
            if x₁.1 = x₂.1 then (Fintype.card D : ℝ)⁻¹ * H x₁ y₁ else 0 := by
        by_cases hx : x₁.1 = x₂.1
        · simp only [hx, true_and, ite_true]
          exact average_pair_second_eq y₁.2 (H x₁ y₁)
        · simp [hx, average]
      simp_rw [hin]
      exact average_pair_first_eq x₁.1 _
    _ = _ := by simp only [average_smul, mul_inv]; ring

/-- The opposite corner of a row-and-column collision retains its product marginal with the exact reciprocal collision count. -/
theorem collision_reverse_corner_average {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    [DecidableEq A] [DecidableEq D] (H : (A × B) → (C × D) → ℝ) :
    average (fun x₁ : A × B => average (fun x₂ : A × B =>
      average (fun y₁ : C × D => average (fun y₂ : C × D =>
        if x₁.1 = x₂.1 ∧ y₁.2 = y₂.2 then H x₂ y₂ else 0)))) =
      ((Fintype.card A : ℝ) * Fintype.card D)⁻¹ *
        average (fun x => average (H x)) := by
  rw [average_comm]
  have heq : average (fun x₂ : A × B => average (fun x₁ : A × B =>
      average (fun y₁ : C × D => average (fun y₂ : C × D =>
        if x₁.1 = x₂.1 ∧ y₁.2 = y₂.2 then H x₂ y₂ else 0)))) =
      average (fun x₂ : A × B => average (fun x₁ : A × B =>
        average (fun y₂ : C × D => average (fun y₁ : C × D =>
          if x₂.1 = x₁.1 ∧ y₂.2 = y₁.2 then H x₂ y₂ else 0)))) := by
    apply average_congr
    intro x₂
    apply average_congr
    intro x₁
    rw [average_comm]
    apply average_congr
    intro y₂
    apply average_congr
    intro y₁
    simp only [eq_comm]
  rw [heq]
  exact collision_corner_average H

/-- The double-collision correction has the exact 1/(|A||D|) scaling used in the four-cycle refresh estimate. -/
theorem collision_intersection_bound {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    [DecidableEq A] [DecidableEq D] (F : Table (A × B) (C × D))
    {bound : ℝ} (hb : 0 ≤ bound) (hentry : ∀ x y, |F x y| ≤ bound) :
    cycleContribution F (fun x₁ x₂ => x₁.1 = x₂.1) (fun y₁ y₂ => y₁.2 = y₂.2) ≤
      bound ^ 2 / ((Fintype.card A : ℝ) * Fintype.card D) * normSq F := by
  have hpoint (x₁ x₂ : A × B) (y₁ y₂ : C × D) :
      (if x₁.1 = x₂.1 ∧ y₁.2 = y₂.2 then
        F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂ else 0) ≤
      (bound ^ 2 / 2) *
        ((if x₁.1 = x₂.1 ∧ y₁.2 = y₂.2 then F x₁ y₁ ^ 2 else 0) +
          (if x₁.1 = x₂.1 ∧ y₁.2 = y₂.2 then F x₂ y₂ ^ 2 else 0)) := by
    by_cases hc : x₁.1 = x₂.1 ∧ y₁.2 = y₂.2
    · simp only [hc, ite_true]
      exact four_entries_le_two_squares hb (hentry x₁ y₂) (hentry x₂ y₁)
    · simp only [hc, ite_false, zero_add, mul_zero, le_refl]
  unfold cycleContribution
  calc
    _ ≤ average (fun x₁ : A × B => average (fun x₂ : A × B =>
        average (fun y₁ : C × D => average (fun y₂ : C × D =>
          (bound ^ 2 / 2) *
            ((if x₁.1 = x₂.1 ∧ y₁.2 = y₂.2 then F x₁ y₁ ^ 2 else 0) +
              (if x₁.1 = x₂.1 ∧ y₁.2 = y₂.2 then F x₂ y₂ ^ 2 else 0)))))) := by
      apply average_mono
      intro x₁
      apply average_mono
      intro x₂
      apply average_mono
      intro y₁
      exact average_mono (hpoint x₁ x₂ y₁)
    _ = _ := by
      simp_rw [average_smul, average_add]
      rw [collision_corner_average, collision_reverse_corner_average]
      simp only [normSq, pairing, ← pow_two]
      ring

/-- The rank-case upper envelope after dropping only nonnegative restrictions in the two mixed-rank terms. -/
def fourRankEnvelope {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq D] (F : Table (A × B) (C × D)) (q : ℝ) : ℝ :=
  16 * cycleContribution F (fun x₁ x₂ => x₁.1 ≠ x₂.1) (fun y₁ y₂ => y₁.2 ≠ y₂.2) +
  (4 / q) * average (fun x => (average (fun y => F x y ^ 2)) ^ 2) +
  (4 / q) * average (fun y => (average (fun x => F x y ^ 2)) ^ 2) +
  (2 / q ^ 2) * average (fun x => average (fun y => F x y ^ 4))

/-- The complete analytic bound on the four rank cases, including the leading factor four from the invertibility-density comparison. -/
theorem fourRankEnvelope_bound {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    [DecidableEq A] [DecidableEq D] (F : Table (A × B) (C × D))
    (hcard : Fintype.card A ≤ Fintype.card D) {Binf R : ℝ} (hB : 0 ≤ Binf)
    (hentry : ∀ x y, |F x y| ≤ Binf)
    (hrow : ∀ x, average (fun y => F x y ^ 2) ≤ R ^ 2)
    (hcolumn : ∀ y, average (fun x => F x y ^ 2) ≤ R ^ 2) :
    4 * fourRankEnvelope F (Fintype.card A : ℝ) ≤
      64 * fourCycle F + (32 * R ^ 2 / (Fintype.card A : ℝ)) * normSq F +
        (72 * Binf ^ 2 / (Fintype.card A : ℝ) ^ 2) * normSq F := by
  let q : ℝ := Fintype.card A
  let Q : ℝ := Fintype.card D
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos
  have hQ : 0 < Q := by dsimp [Q]; exact_mod_cast Fintype.card_pos
  have hqQ : q ≤ Q := by dsimp [q, Q]; exact_mod_cast hcard
  have hn : 0 ≤ normSq F := average_nonneg (fun x => average_nonneg (fun y => mul_self_nonneg _))
  have hmain : cycleContribution F (fun x₁ x₂ => x₁.1 ≠ x₂.1)
      (fun y₁ y₂ => y₁.2 ≠ y₂.2) ≤ fourCycle F + Binf ^ 2 / (q * Q) * normSq F :=
    (restricted_fourCycle_le F (fun x₁ x₂ => x₁.1 = x₂.1) (fun y₁ y₂ => y₁.2 = y₂.2)).trans
      (add_le_add le_rfl (collision_intersection_bound F hB hentry))
  have hr := row_second_moment_bound F hrow
  have hc := column_second_moment_bound F hcolumn
  have hf := fourth_moment_bound F hB hentry
  have hm := mul_le_mul_of_nonneg_left hmain (by norm_num : (0 : ℝ) ≤ 16)
  have hrr := mul_le_mul_of_nonneg_left hr (show 0 ≤ 4 / q by positivity)
  have hcc := mul_le_mul_of_nonneg_left hc (show 0 ≤ 4 / q by positivity)
  have hff := mul_le_mul_of_nonneg_left hf (show 0 ≤ 2 / q ^ 2 by positivity)
  have hinv : 1 / (q * Q) ≤ 1 / q ^ 2 := by
    apply one_div_le_one_div_of_le (sq_pos_of_pos hq)
    nlinarith
  have hcoef : 64 / (q * Q) + 8 / q ^ 2 ≤ 72 / q ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 64)
    simp only [div_eq_mul_inv, one_mul] at hh ⊢
    linarith
  have hcorr := mul_le_mul_of_nonneg_right hcoef (mul_nonneg (sq_nonneg Binf) hn)
  change 4 * fourRankEnvelope F q ≤ _
  have hsum : fourRankEnvelope F q ≤
      16 * (fourCycle F + Binf ^ 2 / (q * Q) * normSq F) +
      (4 / q) * (R ^ 2 * normSq F) + (4 / q) * (R ^ 2 * normSq F) +
      (2 / q ^ 2) * (Binf ^ 2 * normSq F) :=
    add_le_add (add_le_add (add_le_add hm hrr) hcc) hff
  calc
    _ ≤ 4 * (16 * (fourCycle F + Binf ^ 2 / (q * Q) * normSq F) +
        (4 / q) * (R ^ 2 * normSq F) + (4 / q) * (R ^ 2 * normSq F) +
        (2 / q ^ 2) * (Binf ^ 2 * normSq F)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 64 * fourCycle F + (32 * R ^ 2 / q) * normSq F +
        (64 / (q * Q) + 8 / q ^ 2) * (Binf ^ 2 * normSq F) := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ 64 * fourCycle F + (32 * R ^ 2 / q) * normSq F +
        (72 / q ^ 2) * (Binf ^ 2 * normSq F) := add_le_add le_rfl hcorr
    _ = _ := by
      change _ = 64 * fourCycle F + (32 * R ^ 2 / q) * normSq F +
        (72 * Binf ^ 2 / q ^ 2) * normSq F
      simp only [div_eq_mul_inv]
      ring

end RefreshingProof.Local
