import Proofs.Refreshing.TwoSecret
import Proofs.Refreshing.LocalSVD

/-!
# The actual consistency-sign operator on pairs of nonzero shares

Binary orthogonality supplies the full tensor Walsh estimate. Zero extension then restricts it to the actual grouped share domains. All averages below are probability-normalized as in the manuscript.
-/

noncomputable section
open scoped BigOperators Matrix

namespace RefreshingProof
open Refreshing

/-- Extend a function on two nonzero shares by zero in either zero coordinate. -/
def extendNonzeroPair {n : ℕ} (f : State n → ℝ) (p : Binary.Vec n × Binary.Vec n) : ℝ :=
  extendNonzero (fun l => extendNonzero (fun r => f (l, r)) p.2) p.1

/-- Extending a two-share function by zero agrees with it on pairs of nonzero vectors. -/
@[simp] theorem extendNonzeroPair_coe {n : ℕ} (f : State n → ℝ) (p : State n) :
    extendNonzeroPair f (p.1.val, p.2.val) = f p := by
  classical
  simp [extendNonzeroPair, extendNonzero, p.1.property, p.2.property]

/-- Drop both excluded zero-coordinate sets exactly. -/
theorem sum_allPair_eq_nonzero {n : ℕ}
    (F : (Binary.Vec n × Binary.Vec n) → ℝ)
    (hL : ∀ y, F (0, y) = 0) (hR : ∀ x, F (x, 0) = 0) :
    (∑ p : Binary.Vec n × Binary.Vec n, F p) =
      ∑ p : State n, F (p.1.val, p.2.val) := by
  classical
  simp only [State, Fintype.sum_prod_type]
  rw [sum_all_eq_nonzero _ (by simp [hL])]
  apply Finset.sum_congr rfl
  intro l _
  rw [sum_all_eq_nonzero _ (hR l.val)]

/-- Zero extension from nonzero share pairs preserves the unnormalized sum of squares. -/
theorem sum_extendNonzeroPair_sq {n : ℕ} (f : State n → ℝ) :
    (∑ p : Binary.Vec n × Binary.Vec n, extendNonzeroPair f p ^ 2) =
      ∑ p : State n, f p ^ 2 := by
  classical
  rw [sum_allPair_eq_nonzero _ (by intro y; simp [extendNonzeroPair, extendNonzero])
    (by intro x; simp [extendNonzeroPair, extendNonzero])]
  simp only [extendNonzeroPair_coe]

/-- Raw tensor sign pairing on the actual grouped nonzero shares. -/
def nonzeroPairSignPairing {n : ℕ} (u v : State n → ℝ) : ℝ :=
  ∑ x : State n, ∑ y : State n,
    u x * Binary.pairSign (x.1.val, x.2.val) (y.1.val, y.2.val) * v y

/-- The full binary-pair Walsh pairing of zero extensions equals the corresponding nonzero-share sum. -/
theorem pairWalshPairing_extendNonzeroPair {n : ℕ} (u v : State n → ℝ) :
    Binary.pairWalshPairing (extendNonzeroPair u) (extendNonzeroPair v) =
      nonzeroPairSignPairing u v := by
  classical
  unfold Binary.pairWalshPairing nonzeroPairSignPairing
  rw [sum_allPair_eq_nonzero _
    (by intro y; simp [extendNonzeroPair, extendNonzero])
    (by intro x; simp [extendNonzeroPair, extendNonzero])]
  apply Finset.sum_congr rfl
  intro x _
  rw [sum_allPair_eq_nonzero _
    (by intro y; simp [extendNonzeroPair, extendNonzero])
    (by intro x; simp [extendNonzeroPair, extendNonzero])]
  simp only [extendNonzeroPair_coe]

/-- Counting-L₂ operator estimate on the actual grouped share domains. -/
theorem nonzeroPairSignPairing_abs_le {n : ℕ} (u v : State n → ℝ) :
    |nonzeroPairSignPairing u v| ≤
      (2 : ℝ) ^ n * Real.sqrt (∑ x : State n, u x ^ 2) *
        Real.sqrt (∑ y : State n, v y ^ 2) := by
  have h := Binary.pairWalshPairing_abs_le (extendNonzeroPair u) (extendNonzeroPair v)
  rw [pairWalshPairing_extendNonzeroPair, sum_extendNonzeroPair_sq,
    sum_extendNonzeroPair_sq] at h
  exact h

/-- The two endpoint inner products agree precisely on the consistency support. -/
def sharePairsConsistent {n : ℕ} (x y : State n) : Prop :=
  x.1.val ⬝ᵥ y.1.val = x.2.val ⬝ᵥ y.2.val

instance (n : ℕ) : DecidableRel (@sharePairsConsistent n) := fun x y =>
  inferInstanceAs (Decidable (x.1.val ⬝ᵥ y.1.val = x.2.val ⬝ᵥ y.2.val))

/-- The paper's actual centered consistency sign J. -/
def refreshConsistencySign {n : ℕ} : Local.Table (State n) (State n) :=
  Local.consistencySign sharePairsConsistent

/-- The refresh consistency sign is half the binary character of the difference of endpoint secrets. -/
theorem refreshConsistencySign_eq {n : ℕ} (x y : State n) :
    refreshConsistencySign x y =
      (1 / 2 : ℝ) * Binary.pairSign (x.1.val, x.2.val) (y.1.val, y.2.val) := by
  unfold Binary.pairSign
  rw [Binary.sign_add]
  rcases Binary.bit_cases (x.1.val ⬝ᵥ y.1.val) with h0 | h0 <;>
    rcases Binary.bit_cases (x.2.val ⬝ᵥ y.2.val) with h1 | h1
  all_goals norm_num [refreshConsistencySign, Local.consistencySign,
    sharePairsConsistent, h0, h1]

/-- The grouped share domain has exactly q² points. -/
theorem card_state_real (n : ℕ) :
    (Fintype.card (State n) : ℝ) = (q n : ℝ) ^ 2 := by
  simp only [Fintype.card_prod, card_share, Nat.cast_mul, pow_two]

/-- Conversion from counting L₂ to the probability normalization on share pairs. -/
theorem sqrt_average_state_sq {n : ℕ} (hn : 2 ≤ n) (u : State n → ℝ) :
    Real.sqrt (Local.average (fun x => u x ^ 2)) =
      (q n : ℝ)⁻¹ * Real.sqrt (∑ x : State n, u x ^ 2) := by
  have hQ : 0 ≤ (q n : ℝ) := le_trans (by norm_num) (q_real_three_le hn)
  unfold Local.average
  rw [card_state_real, Real.sqrt_mul (by positivity), Real.sqrt_inv,
    Real.sqrt_sq hQ]

/-- Nested uniform averages equal the squared reciprocal cardinal times a single double sum. -/
theorem double_average_eq {X : Type*} [Fintype X] (F : X → X → ℝ) :
    Local.average (fun x => Local.average (F x)) =
      ((Fintype.card X : ℝ)⁻¹) ^ 2 * ∑ x, ∑ y, F x y := by
  simp only [Local.average, ← Finset.mul_sum]
  ring

/-- Probability-normalized pairing against the actual consistency sign. -/
def consistencySignPairing {n : ℕ} (u v : State n → ℝ) : ℝ :=
  Local.average fun x => Local.average fun y => u x * refreshConsistencySign x y * v y

/-- The consistency-sign pairing on nonzero shares equals the stated normalized full-vector Walsh pairing. -/
theorem consistencySignPairing_raw {n : ℕ} (u v : State n → ℝ) :
    consistencySignPairing u v =
      ((Fintype.card (State n) : ℝ)⁻¹) ^ 2 *
        ((1 / 2 : ℝ) * nonzeroPairSignPairing u v) := by
  unfold consistencySignPairing
  rw [double_average_eq]
  congr 1
  unfold nonzeroPairSignPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [refreshConsistencySign_eq]
  ring

/-- Exact normalized consistency-sign coefficient 2^n/(2q²), obtained from actual binary character orthogonality and zero extension. -/
theorem consistency_sign_precise_bound {n : ℕ} (hn : 2 ≤ n) (u v : State n → ℝ) :
    |consistencySignPairing u v| ≤
      ((2 : ℝ) ^ n / (2 * (q n : ℝ) ^ 2)) *
        Real.sqrt (Local.average (fun x => u x ^ 2)) *
        Real.sqrt (Local.average (fun y => v y ^ 2)) := by
  have hQ0 : 0 < (q n : ℝ) := lt_of_lt_of_le (by norm_num) (q_real_three_le hn)
  rw [consistencySignPairing_raw, abs_mul,
    abs_of_nonneg (sq_nonneg _), abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    _ ≤ ((Fintype.card (State n) : ℝ)⁻¹) ^ 2 *
        ((1 / 2 : ℝ) * ((2 : ℝ) ^ n * Real.sqrt (∑ x : State n, u x ^ 2) *
          Real.sqrt (∑ y : State n, v y ^ 2))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (nonzeroPairSignPairing_abs_le u v) (by norm_num))
        (sq_nonneg _)
    _ = _ := by
      rw [sqrt_average_state_sq hn, sqrt_average_state_sq hn, card_state_real]
      field_simp

/-- The exact sign coefficient is at most 1/q in every theorem dimension. -/
theorem consistency_sign_coefficient_le {n : ℕ} (hn : 2 ≤ n) :
    (2 : ℝ) ^ n / (2 * (q n : ℝ) ^ 2) ≤ 1 / (q n : ℝ) := by
  have hQ := q_real_three_le hn
  have hQ0 : 0 < (q n : ℝ) := by linarith
  apply (div_le_div_iff₀ (by positivity) hQ0).2
  have hN : (2 : ℝ) ^ n = (q n : ℝ) + 1 := by rw [q_real_eq]; ring
  rw [hN]
  nlinarith [sq_nonneg ((q n : ℝ) - 1)]

/-- The paper's cancellation bound for arbitrary real left/right functions on the actual grouped nonzero-share domains. -/
theorem consistency_sign_bound {n : ℕ} (hn : 2 ≤ n) (u v : State n → ℝ) :
    |consistencySignPairing u v| ≤
      (1 / (q n : ℝ)) * Real.sqrt (Local.average (fun x => u x ^ 2)) *
        Real.sqrt (Local.average (fun y => v y ^ 2)) :=
  (consistency_sign_precise_bound hn u v).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (consistency_sign_coefficient_le hn) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _))

/-- Correlation of J times a real table with a left/right product test. -/
def weightedConsistencyCorrelation {n : ℕ} (P : Local.Table (State n) (State n))
    (u v : State n → ℝ) : ℝ :=
  Local.pairing (fun x y => refreshConsistencySign x y * P x y)
    (fun x y => u x * v y)

/-- A finite factor representation expands the weighted sign correlation. -/
theorem weightedConsistencyCorrelation_sum {n : ℕ} {ι : Type*}
    (I : Finset ι) (a b : ι → State n → ℝ) (u v : State n → ℝ) :
    weightedConsistencyCorrelation (fun x y => ∑ j ∈ I, a j x * b j y) u v =
      ∑ j ∈ I, consistencySignPairing (fun x => u x * a j x) (fun y => v y * b j y) := by
  unfold weightedConsistencyCorrelation Local.pairing
  calc
    _ = Local.average (fun x => Local.average fun y =>
        ∑ j ∈ I, (u x * a j x) * refreshConsistencySign x y * (v y * b j y)) := by
      apply Local.average_congr
      intro x
      apply Local.average_congr
      intro y
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by simp only [Local.average_sum, consistencySignPairing]

/-- Pointwise factor energy controls the average sum of weighted squares. -/
theorem weighted_factor_average_sum_le {n : ℕ} {ι : Type*}
    (I : Finset ι) (a : ι → State n → ℝ) (u : State n → ℝ)
    {beta : ℝ} (henergy : ∀ x, (∑ j ∈ I, a j x ^ 2) ≤ 1 / beta)
    (hu : Local.average (fun x => u x ^ 2) = 1) :
    (∑ j ∈ I, Local.average (fun x => (u x * a j x) ^ 2)) ≤ 1 / beta := by
  calc
    _ = Local.average (fun x => ∑ j ∈ I, (u x * a j x) ^ 2) :=
      (Local.average_sum I _).symm
    _ = Local.average (fun x => u x ^ 2 * ∑ j ∈ I, a j x ^ 2) := by
      apply Local.average_congr
      intro x
      simp only [mul_pow, Finset.mul_sum]
    _ ≤ Local.average (fun x => (1 / beta) * u x ^ 2) := by
      apply Local.average_mono
      intro x
      have h := mul_le_mul_of_nonneg_left (henergy x) (sq_nonneg (u x))
      simpa only [mul_comm] using h
    _ = (1 / beta) * Local.average (fun x => u x ^ 2) := Local.average_smul _ _
    _ = _ := by rw [hu, mul_one]

/-- Actual consistency-sign cancellation for any finite factor representation whose left and right energies are bounded by 1/beta. -/
theorem weighted_factor_consistency_bound {n : ℕ} (hn : 2 ≤ n)
    {ι : Type*} (I : Finset ι) (a b : ι → State n → ℝ) {beta : ℝ} (hbeta : 0 < beta)
    (ha : ∀ x, (∑ j ∈ I, a j x ^ 2) ≤ 1 / beta)
    (hb : ∀ y, (∑ j ∈ I, b j y ^ 2) ≤ 1 / beta)
    (u v : State n → ℝ)
    (hu : Local.average (fun x => u x ^ 2) = 1)
    (hv : Local.average (fun y => v y ^ 2) = 1) :
    |weightedConsistencyCorrelation (fun x y => ∑ j ∈ I, a j x * b j y) u v| ≤
      1 / ((q n : ℝ) * beta) := by
  let A := fun j => Local.average (fun x => (u x * a j x) ^ 2)
  let B := fun j => Local.average (fun y => (v y * b j y) ^ 2)
  have hA : ∀ j, 0 ≤ A j := fun j => Local.average_nonneg (fun _ => sq_nonneg _)
  have hB : ∀ j, 0 ≤ B j := fun j => Local.average_nonneg (fun _ => sq_nonneg _)
  have hsA : (∑ j ∈ I, A j) ≤ 1 / beta := weighted_factor_average_sum_le I a u ha hu
  have hsB : (∑ j ∈ I, B j) ≤ 1 / beta := weighted_factor_average_sum_le I b v hb hv
  have hcs : (∑ j ∈ I, Real.sqrt (A j) * Real.sqrt (B j)) ≤
      Real.sqrt (∑ j ∈ I, A j) * Real.sqrt (∑ j ∈ I, B j) :=
    Real.sum_sqrt_mul_sqrt_le I hA hB
  have hsum : (∑ j ∈ I, Real.sqrt (A j) * Real.sqrt (B j)) ≤ 1 / beta := by
    calc
      _ ≤ _ := hcs
      _ ≤ Real.sqrt (1 / beta) * Real.sqrt (1 / beta) :=
        mul_le_mul (Real.sqrt_le_sqrt hsA) (Real.sqrt_le_sqrt hsB)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by rw [← pow_two, Real.sq_sqrt (by positivity)]
  rw [weightedConsistencyCorrelation_sum]
  calc
    _ ≤ ∑ j ∈ I, |consistencySignPairing (fun x => u x * a j x) (fun y => v y * b j y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ I, (1 / (q n : ℝ)) * Real.sqrt (A j) * Real.sqrt (B j) := by
      apply Finset.sum_le_sum
      intro j _
      exact consistency_sign_bound hn _ _
    _ = (1 / (q n : ℝ)) * ∑ j ∈ I, Real.sqrt (A j) * Real.sqrt (B j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ (1 / (q n : ℝ)) * (1 / beta) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev, one_mul]; ring

/-- A pointwise bounded function has probability-normalized squared L₂ norm at most one on a nonempty finite set. -/
theorem bounded_average_square_le_one {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    Local.average (fun x => f x ^ 2) ≤ 1 := by
  have hc : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    _ ≤ Local.average (fun _ : X => (1 : ℝ)) := by
      apply Local.average_mono
      intro x
      have h := abs_le.mp (hf x)
      nlinarith
    _ = _ := by simp [Local.average, hc]

/-- The weighted sign bound for the actual strict spectral truncation of a bounded table. Its energy bounds are derived from the constructed SVD. -/
theorem spectralTruncation_weighted_sign_bound {n : ℕ} (hn : 2 ≤ n)
    (F : Local.Table (State n) (State n)) {beta : ℝ} (hbeta : 0 < beta)
    (hF : ∀ x y, |F x y| ≤ 1) (u v : State n → ℝ)
    (hu : Local.average (fun x => u x ^ 2) = 1)
    (hv : Local.average (fun y => v y ^ 2) = 1) :
    |weightedConsistencyCorrelation (Local.spectralTruncation F beta) u v| ≤
      1 / ((q n : ℝ) * beta) := by
  classical
  obtain ⟨e⟩ := encoding_nonempty hn (0 : Bit)
  letI : Nonempty (State n) := ⟨e.val⟩
  have hrow (x : State n) : Local.average (fun y => F x y ^ 2) ≤ 1 :=
    bounded_average_square_le_one _ (hF x)
  have hcol (y : State n) : Local.average (fun x => F x y ^ 2) ≤ 1 :=
    bounded_average_square_le_one _ (fun x => hF x y)
  have ha (x : State n) : (∑ j ∈ Local.retainedDirections F beta,
      Local.leftBalancedFactor F j x ^ 2) ≤ 1 / beta :=
    Local.leftFactorEnergy_le F hbeta x (hrow x)
  have hb (y : State n) : (∑ j ∈ Local.retainedDirections F beta,
      Local.rightBalancedFactor F j y ^ 2) ≤ 1 / beta :=
    Local.rightFactorEnergy_le F hbeta y (hcol y)
  have hexpand : Local.spectralTruncation F beta = fun x y =>
      ∑ j ∈ Local.retainedDirections F beta,
        Local.leftBalancedFactor F j x * Local.rightBalancedFactor F j y := by
    funext x y
    exact Local.spectralTruncation_balanced_expansion F beta x y
  rw [hexpand]
  exact weighted_factor_consistency_bound hn _ _ _ hbeta ha hb u v hu hv

end RefreshingProof
