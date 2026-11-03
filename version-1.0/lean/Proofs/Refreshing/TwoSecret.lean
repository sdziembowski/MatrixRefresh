import Proofs.Refreshing.ModelFacts
import Proofs.Refreshing.Discrepancy

/-!
# Two-secret discrepancy for the actual initial encoding distributions

Uniform fiber counts and the binary Walsh estimate are applied to the PMFs in the specification, rather than assuming a discrepancy property of those PMFs.
-/

noncomputable section
open scoped BigOperators Matrix ENNReal

namespace RefreshingProof
open Refreshing
open RefreshingProof.Binary (sign)

/-- There are exactly q(n) = 2ⁿ − 1 nonzero binary shares of dimension n. -/
@[simp] theorem card_share (n : ℕ) : Fintype.card (Share n) = q n := by
  simp [Share, Refreshing.Vector, q, Fintype.card_subtype_compl, ZMod.card]

/-- A nonzero row has character sum -1 over the nonzero columns. -/
theorem nonzero_character_sum {n : ℕ} (l : Share n) :
    ∑ r : Share n, sign (l.val ⬝ᵥ r.val) = -1 := by
  classical
  have he : (∑ r : Share n, sign (l.val ⬝ᵥ r.val)) =
      ∑ r ∈ (Finset.univ : Finset (Binary.Vec n)).erase 0, sign (l.val ⬝ᵥ r) := by
    symm
    exact Finset.sum_subtype _ (by simp) _
  rw [he]
  have hs := Finset.sum_erase_add (Finset.univ : Finset (Binary.Vec n))
    (fun r => sign (l.val ⬝ᵥ r)) (Finset.mem_univ 0)
  rw [Binary.character_sum_zero l.val l.property] at hs
  simp only [dotProduct_zero, Binary.sign_zero] at hs
  linarith

/-- The total consistency sign is exactly minus the nonzero-share count. -/
theorem state_character_sum (n : ℕ) :
    (∑ x : State n, sign (secret x)) = -(q n : ℝ) := by
  simp only [State, Fintype.sum_prod_type, secret, nonzero_character_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_share]
  ring

/-- Real cardinality of a secret fiber as a sum of its indicator. -/
theorem card_encoding_indicator (n : ℕ) (s : Bit) :
    (Fintype.card (Encoding n s) : ℝ) =
      ∑ x : State n, if secret x = s then (1 : ℝ) else 0 := by
  classical
  symm
  calc
    _ = ∑ x ∈ Finset.univ.filter (fun x : State n => secret x = s), (1 : ℝ) := by
      rw [Finset.sum_filter]
    _ = ∑ x : Encoding n s, (1 : ℝ) :=
      Finset.sum_subtype _ (by simp) _
    _ = _ := by simp

/-- Exact real counts of the two nonzero inner-product fibers. -/
theorem card_encoding_real (n : ℕ) :
    (Fintype.card (Encoding n 0) : ℝ) = (q n : ℝ) * ((q n : ℝ) - 1) / 2 ∧
    (Fintype.card (Encoding n 1) : ℝ) = (q n : ℝ) * ((q n : ℝ) + 1) / 2 := by
  classical
  have hsum : (Fintype.card (Encoding n 0) : ℝ) +
      (Fintype.card (Encoding n 1) : ℝ) = (q n : ℝ) ^ 2 := by
    rw [card_encoding_indicator, card_encoding_indicator, ← Finset.sum_add_distrib]
    calc
      _ = ∑ x : State n, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x _
        rcases Binary.bit_cases (secret x) with h | h <;> simp [h]
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
          Fintype.card_prod, Nat.cast_mul, card_share, pow_two]
  have hdiff : (Fintype.card (Encoding n 0) : ℝ) -
      (Fintype.card (Encoding n 1) : ℝ) = -(q n : ℝ) := by
    rw [card_encoding_indicator, card_encoding_indicator, ← Finset.sum_sub_distrib]
    calc
      _ = ∑ x : State n, sign (secret x) := by
        apply Finset.sum_congr rfl
        intro x _
        rcases Binary.bit_cases (secret x) with h | h <;> simp [h]
      _ = _ := state_character_sum n
  constructor <;> nlinarith [hsum, hdiff]

/-- Uniform sampling of a subtype has the expected explicit point masses. -/
theorem uniformSubtype_map_apply {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] [Nonempty {a // p a}] (x : α) :
    ((uniformPMF {a // p a}).map Subtype.val) x =
      if p x then (Fintype.card {a // p a} : ℝ≥0∞)⁻¹ else 0 := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  by_cases hx : p x
  · let e : {a // p a} := ⟨x, hx⟩
    rw [ite_eq_left hx]
    calc
      _ = if x = e.val then uniformPMF {a // p a} e else 0 := by
        apply Finset.sum_eq_single e
        · intro b _ hbe
          have hb : x ≠ b.val := by
            intro h
            apply hbe
            exact Subtype.ext h.symm
          simp [hb]
        · simp
      _ = _ := by simp [e]
  · rw [ite_eq_right hx]
    apply Finset.sum_eq_zero
    intro a _
    have ha : x ≠ a.val := by intro h; exact hx (h.symm ▸ a.property)
    simp [ha]

/-- The actual specification PMF is uniform on the corresponding secret fiber. -/
theorem initialDistribution_apply {n : ℕ} (hn : 2 ≤ n) (s : Bit) (x : State n) :
    initialDistribution hn s x =
      if secret x = s then (Fintype.card (Encoding n s) : ℝ≥0∞)⁻¹ else 0 := by
  letI := encoding_nonempty hn s
  exact uniformSubtype_map_apply (fun x : State n => secret x = s) x

/-- Mean of a rank-one table under the actual initial encoding PMF. -/
def initialPairMean {n : ℕ} (hn : 2 ≤ n) (s : Bit) (u v : Share n → ℝ) : ℝ :=
  ∑ x : State n, (initialDistribution hn s x).toReal * (u x.1 * v x.2)

/-- Unnormalized rank-one mass in one secret fiber. -/
def pairFiberSum {n : ℕ} (s : Bit) (u v : Share n → ℝ) : ℝ :=
  ∑ x : State n, if secret x = s then u x.1 * v x.2 else 0

/-- Passing to real masses gives the exact uniform fiber average. -/
theorem initialPairMean_eq {n : ℕ} (hn : 2 ≤ n) (s : Bit) (u v : Share n → ℝ) :
    initialPairMean hn s u v =
      (Fintype.card (Encoding n s) : ℝ)⁻¹ * pairFiberSum s u v := by
  classical
  unfold initialPairMean pairFiberSum
  simp only [initialDistribution_apply, apply_ite ENNReal.toReal,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_zero, ite_mul, zero_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

/-- Extending a real nonzero-share function by zero at the excluded vector. -/
def extendNonzero {n : ℕ} (f : Share n → ℝ) (x : Binary.Vec n) : ℝ := by
  classical
  exact if hx : x ≠ 0 then f ⟨x, hx⟩ else 0

/-- Dropping the zero vector from a sum is exact when its summand vanishes. -/
theorem sum_all_eq_nonzero {n : ℕ} (F : Binary.Vec n → ℝ) (hF : F 0 = 0) :
    (∑ x : Binary.Vec n, F x) = ∑ x : Share n, F x.val := by
  classical
  calc
    _ = (∑ x ∈ (Finset.univ : Finset (Binary.Vec n)).erase 0, F x) + F 0 :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ 0)).symm
    _ = ∑ x ∈ (Finset.univ : Finset (Binary.Vec n)).erase 0, F x := by rw [hF, add_zero]
    _ = _ := Finset.sum_subtype _ (by simp) _

/-- Extending a function by zero at the zero vector preserves its unnormalized sum of squares. -/
theorem sum_extendNonzero_sq {n : ℕ} (f : Share n → ℝ) :
    (∑ x : Binary.Vec n, extendNonzero f x ^ 2) = ∑ x : Share n, f x ^ 2 := by
  classical
  rw [sum_all_eq_nonzero _ (by simp [extendNonzero])]
  apply Finset.sum_congr rfl
  intro x _
  simp [extendNonzero, x.property]

/-- Raw sign pairing on nonzero left and right shares. -/
def nonzeroSignPairing {n : ℕ} (u v : Share n → ℝ) : ℝ :=
  ∑ l : Share n, ∑ r : Share n, u l * sign (l.val ⬝ᵥ r.val) * v r

/-- Zero extension identifies the actual nonzero sign pairing with a full Walsh pairing. -/
theorem walshPairing_extendNonzero {n : ℕ} (u v : Share n → ℝ) :
    Binary.walshPairing (extendNonzero u) (extendNonzero v) = nonzeroSignPairing u v := by
  classical
  unfold Binary.walshPairing nonzeroSignPairing
  rw [sum_all_eq_nonzero _ (by simp [extendNonzero])]
  apply Finset.sum_congr rfl
  intro l _
  rw [sum_all_eq_nonzero _ (by simp [extendNonzero])]
  apply Finset.sum_congr rfl
  intro r _
  simp [extendNonzero, l.property, r.property]

/-- Actual nonzero-share sign pairing, derived without a spectral hypothesis. -/
theorem nonzeroSignPairing_sq_le {n : ℕ} (u v : Share n → ℝ) :
    nonzeroSignPairing u v ^ 2 ≤
      (2 : ℝ) ^ n * (∑ l : Share n, u l ^ 2) * ∑ r : Share n, v r ^ 2 := by
  have h := Binary.walshPairing_sq_le (extendNonzero u) (extendNonzero v)
  rw [walshPairing_extendNonzero, sum_extendNonzero_sq, sum_extendNonzero_sq] at h
  exact h

/-- The two fiber sums partition the whole rank-one table. -/
theorem pairFiberSum_add {n : ℕ} (u v : Share n → ℝ) :
    pairFiberSum 0 u v + pairFiberSum 1 u v =
      (∑ l : Share n, u l) * ∑ r : Share n, v r := by
  unfold pairFiberSum
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ x : State n, u x.1 * v x.2 := by
      apply Finset.sum_congr rfl
      intro x _
      rcases Binary.bit_cases (secret x) with h | h <;> simp [h]
    _ = _ := by
      simp only [State, Fintype.sum_prod_type]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]

/-- The difference of the two fiber sums is the nonzero sign pairing. -/
theorem pairFiberSum_sub {n : ℕ} (u v : Share n → ℝ) :
    pairFiberSum 0 u v - pairFiberSum 1 u v = nonzeroSignPairing u v := by
  unfold pairFiberSum nonzeroSignPairing
  rw [← Finset.sum_sub_distrib]
  change (∑ x : State n, _) = _
  calc
    _ = ∑ x : State n, u x.1 * sign (secret x) * v x.2 := by
      apply Finset.sum_congr rfl
      intro x _
      rcases Binary.bit_cases (secret x) with h | h <;> simp [h]
    _ = _ := by simp only [State, Fintype.sum_prod_type, secret]

/-- Centering the right function removes the constant singular direction. -/
def centerShare {n : ℕ} (v : Share n → ℝ) (r : Share n) : ℝ :=
  v r - (q n : ℝ)⁻¹ * ∑ r : Share n, v r

/-- Centering the right function adds the stated product-of-means correction to its nonzero-share character pairing. -/
theorem nonzeroSignPairing_center {n : ℕ} (u v : Share n → ℝ) :
    nonzeroSignPairing u (centerShare v) = nonzeroSignPairing u v +
      (q n : ℝ)⁻¹ * (∑ l : Share n, u l) * ∑ r : Share n, v r := by
  unfold nonzeroSignPairing centerShare
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hrow (l : Share n) :
      (∑ r : Share n, u l * sign (l.val ⬝ᵥ r.val) *
        ((q n : ℝ)⁻¹ * ∑ r : Share n, v r)) =
      -((q n : ℝ)⁻¹ * ∑ r : Share n, v r) * u l := by
    calc
      _ = ((q n : ℝ)⁻¹ * ∑ r : Share n, v r) * u l *
          ∑ r : Share n, sign (l.val ⬝ᵥ r.val) := by
        conv_rhs => rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ = _ := by rw [nonzero_character_sum]; ring
  simp only [hrow, ← Finset.mul_sum]
  ring

/-- The real nonzero-share count agrees with 2^n - 1. -/
theorem q_real_eq (n : ℕ) : (q n : ℝ) = (2 : ℝ) ^ n - 1 := by
  have hp : 1 ≤ (2 : ℕ) ^ n := Nat.one_le_pow _ _ (by omega)
  simp only [q, Nat.cast_sub hp, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]

/-- At the theorem's dimensions the nonzero-share count is at least three. -/
theorem q_real_three_le {n : ℕ} (hn : 2 ≤ n) : 3 ≤ (q n : ℝ) := by
  have hp : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
  rw [q_real_eq]
  norm_num at hp
  linarith

/-- Removing the uniform mean contracts the squared nonzero-share L₂ norm. -/
theorem centerShare_sq_sum_le {n : ℕ} (hn : 2 ≤ n) (v : Share n → ℝ) :
    (∑ r : Share n, centerShare v r ^ 2) ≤ ∑ r : Share n, v r ^ 2 := by
  let Q : ℝ := q n
  let m : ℝ := Q⁻¹ * ∑ r : Share n, v r
  have hQ : 0 < Q := lt_of_lt_of_le (by norm_num) (q_real_three_le hn)
  have hm : Q * m = ∑ r : Share n, v r := by
    dsimp [m]
    field_simp
  have hm2 : m * (∑ r : Share n, v r) = Q * m ^ 2 := by
    rw [← hm]
    ring
  have hexpand : (∑ r : Share n, (v r - m) ^ 2) =
      (∑ r : Share n, v r ^ 2) - 2 * m * (∑ r : Share n, v r) + Q * m ^ 2 := by
    calc
      _ = ∑ r : Share n, (v r ^ 2 - (2 * m) * v r + m ^ 2) := by
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, card_share, Q]
  change (∑ r : Share n, (v r - m) ^ 2) ≤ _
  have hnonneg : 0 ≤ Q * m ^ 2 := mul_nonneg hQ.le (sq_nonneg m)
  nlinarith [hexpand, hm2, hnonneg]

/-- Exact cancellation of the constant character in the difference of the actual secret-conditioned PMF means. -/
theorem initialPairMean_difference {n : ℕ} (hn : 2 ≤ n) (u v : Share n → ℝ) :
    initialPairMean hn 0 u v - initialPairMean hn 1 u v =
      2 / (((q n : ℝ) + 1) * ((q n : ℝ) - 1)) *
        nonzeroSignPairing u (centerShare v) := by
  have hQ := q_real_three_le hn
  have hQ0 : (q n : ℝ) ≠ 0 := by linarith
  have hQm : (q n : ℝ) - 1 ≠ 0 := by linarith
  have hQp : (q n : ℝ) + 1 ≠ 0 := by linarith
  have hs := pairFiberSum_add u v
  have hd := pairFiberSum_sub u v
  have h0 : pairFiberSum 0 u v =
      ((∑ l : Share n, u l) * (∑ r : Share n, v r) + nonzeroSignPairing u v) / 2 :=
    by linarith
  have h1 : pairFiberSum 1 u v =
      ((∑ l : Share n, u l) * (∑ r : Share n, v r) - nonzeroSignPairing u v) / 2 :=
    by linarith
  rw [initialPairMean_eq, initialPairMean_eq, (card_encoding_real n).1,
    (card_encoding_real n).2, nonzeroSignPairing_center, h0, h1]
  field_simp [hQ0, hQm, hQp]
  ring

/-- Scalar comparison needed to obtain the paper's absolute constant 3. -/
theorem discrepancy_coefficient_le {Q : ℝ} (hQ : 3 ≤ Q) :
    (2 / ((Q + 1) * (Q - 1))) ^ 2 * (Q + 1) ≤
      9 / ((Q - 1) * Q ^ 2) := by
  have hQ0 : 0 < Q := by linarith
  have hm : 0 < Q - 1 := by linarith
  have hp : 0 < Q + 1 := by linarith
  have hQ0' := ne_of_gt hQ0
  have hm' := ne_of_gt hm
  have hp' := ne_of_gt hp
  have heq : (2 / ((Q + 1) * (Q - 1))) ^ 2 * (Q + 1) =
      4 / ((Q + 1) * (Q - 1) ^ 2) := by field_simp; ring
  rw [heq]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hscalar : 4 * Q ^ 2 ≤ 9 * ((Q + 1) * (Q - 1)) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hscalar hm.le
  nlinarith [hmul]

/-- Squared probability-normalized L₂ norm of a function on nonzero shares. -/
def shareL2Sq {n : ℕ} (u : Share n → ℝ) : ℝ :=
  (q n : ℝ)⁻¹ * ∑ l : Share n, u l ^ 2

/-- The actual two-secret discrepancy estimate, in the paper's probability normalization and with no assumed discrepancy property. -/
theorem two_secret_discrepancy {n : ℕ} (hn : 2 ≤ n) (u v : Share n → ℝ) :
    |initialPairMean hn 0 u v - initialPairMean hn 1 u v| ≤
      3 / Real.sqrt ((2 : ℝ) ^ n - 2) *
        Real.sqrt (shareL2Sq u) * Real.sqrt (shareL2Sq v) := by
  let Q : ℝ := q n
  have hQ : 3 ≤ Q := q_real_three_le hn
  have hQ0 : 0 < Q := by linarith
  have hQm : 0 < Q - 1 := by linarith
  have hQ0' := ne_of_gt hQ0
  have hQm' := ne_of_gt hQm
  have hu : 0 ≤ ∑ l : Share n, u l ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hv : 0 ≤ ∑ r : Share n, v r ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have huc : 0 ≤ shareL2Sq u := by unfold shareL2Sq; positivity
  have hvc : 0 ≤ shareL2Sq v := by unfold shareL2Sq; positivity
  have hwalsh : nonzeroSignPairing u (centerShare v) ^ 2 ≤
      (Q + 1) * (∑ l : Share n, u l ^ 2) * ∑ r : Share n, v r ^ 2 := by
    have hw := nonzeroSignPairing_sq_le u (centerShare v)
    have hc := centerShare_sq_sum_le hn v
    have hN : (2 : ℝ) ^ n = Q + 1 := by dsimp [Q]; rw [q_real_eq]; ring
    rw [hN] at hw
    exact hw.trans (mul_le_mul_of_nonneg_left hc (by positivity))
  have hcoef := discrepancy_coefficient_le hQ
  have hmain : (initialPairMean hn 0 u v - initialPairMean hn 1 u v) ^ 2 ≤
      (9 / (Q - 1)) * shareL2Sq u * shareL2Sq v := by
    rw [initialPairMean_difference, mul_pow]
    calc
      _ ≤ (2 / ((Q + 1) * (Q - 1))) ^ 2 *
          ((Q + 1) * (∑ l : Share n, u l ^ 2) * ∑ r : Share n, v r ^ 2) :=
        mul_le_mul_of_nonneg_left hwalsh (sq_nonneg _)
      _ ≤ (9 / ((Q - 1) * Q ^ 2)) *
          ((∑ l : Share n, u l ^ 2) * ∑ r : Share n, v r ^ 2) := by
        have h := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hu hv)
        nlinarith [h]
      _ = _ := by
        unfold shareL2Sq
        dsimp [Q] at *
        field_simp [hQ0', hQm']
  calc
    _ ≤ Real.sqrt ((9 / (Q - 1)) * shareL2Sq u * shareL2Sq v) := Real.abs_le_sqrt hmain
    _ = _ := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ (9 / (Q - 1)) * shareL2Sq u),
        Real.sqrt_mul (by positivity : 0 ≤ 9 / (Q - 1)),
        Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 9)]
      have hroot : Real.sqrt (9 : ℝ) = 3 := by norm_num
      rw [hroot]
      have hden : Q - 1 = (2 : ℝ) ^ n - 2 := by
        dsimp [Q]
        rw [q_real_eq]
        ring
      rw [hden]

/-- Actual initial-distribution expectation of an arbitrary real table. -/
def initialTableMean {n : ℕ} (hn : 2 ≤ n) (s : Bit) (F : State n → ℝ) : ℝ :=
  ∑ x : State n, (initialDistribution hn s x).toReal * F x

/-- Expectation commutes with a finite product representation. -/
theorem initialTableMean_sum_products {n : ℕ} (hn : 2 ≤ n) (s : Bit)
    {ι : Type*} [Fintype ι] (u v : ι → Share n → ℝ) :
    initialTableMean hn s (fun x => ∑ i, u i x.1 * v i x.2) =
      ∑ i, initialPairMean hn s (u i) (v i) := by
  unfold initialTableMean initialPairMean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The table discrepancy estimate for an arbitrary finite product representation. Its right-hand sum is the factor cost, so a normalized singular expansion gives the paper's nuclear-norm version. -/
theorem two_secret_product_sum_discrepancy {n : ℕ} (hn : 2 ≤ n)
    {ι : Type*} [Fintype ι] (u v : ι → Share n → ℝ) :
    |initialTableMean hn 0 (fun x => ∑ i, u i x.1 * v i x.2) -
        initialTableMean hn 1 (fun x => ∑ i, u i x.1 * v i x.2)| ≤
      3 / Real.sqrt ((2 : ℝ) ^ n - 2) *
        ∑ i, Real.sqrt (shareL2Sq (u i)) * Real.sqrt (shareL2Sq (v i)) := by
  rw [initialTableMean_sum_products, initialTableMean_sum_products, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |initialPairMean hn 0 (u i) (v i) - initialPairMean hn 1 (u i) (v i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 3 / Real.sqrt ((2 : ℝ) ^ n - 2) *
        Real.sqrt (shareL2Sq (u i)) * Real.sqrt (shareL2Sq (v i)) := by
      apply Finset.sum_le_sum
      intro i _
      exact two_secret_discrepancy hn (u i) (v i)
    _ = _ := by simp only [Finset.mul_sum, mul_assoc]

end RefreshingProof

