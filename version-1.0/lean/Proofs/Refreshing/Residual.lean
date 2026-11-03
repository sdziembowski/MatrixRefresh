import Proofs.Refreshing.LocalNuclear
import Proofs.Refreshing.ConsistencySign

/-!
# Estimates for the actual local refreshing residual

The residual is constructed from the actual conditional-answer table and its actual strict spectral truncation. No four-cycle refresh transfer or security bound is assumed in this file.
-/

noncomputable section
open scoped BigOperators Matrix

namespace RefreshingProof.Local
open Refreshing

/-- The paper's residual F−2ΠP for the actual refreshing answer table. -/
def actualResidual {n leakage : ℕ} (f : LeakageQuery n leakage) (z : Answer leakage)
    (beta : ℝ) : Table (State n) (State n) :=
  fun ll rr => groupedAnswerTable f z ll rr -
    2 * projection sharePairsConsistent (spectralTruncation (groupedAnswerTable f z) beta) ll rr

/-- The actual residual is zero on inconsistent endpoint tuples. -/
theorem actualResidual_supported {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) (ll rr : State n)
    (h : ¬ sharePairsConsistent ll rr) : actualResidual f z beta ll rr = 0 := by
  unfold actualResidual
  rw [groupedAnswerTable_supported f z ll rr h]
  simp [projection, h]

/-- Exact sign decomposition of the actual residual. -/
theorem actualResidual_decomposition {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) :
    actualResidual f z beta = fun ll rr =>
      (groupedAnswerTable f z ll rr - spectralTruncation (groupedAnswerTable f z) beta ll rr) -
        2 * refreshConsistencySign ll rr * spectralTruncation (groupedAnswerTable f z) beta ll rr := by
  funext ll rr
  unfold actualResidual
  rw [projection_sign]
  unfold refreshConsistencySign
  ring

/-- Exact residual identity, using actual truncation orthogonality. -/
theorem actualResidual_identity {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) :
    normSq (actualResidual f z beta) = pairing (groupedAnswerTable f z) (actualResidual f z beta) +
      4 * pairing (spectralTruncation (groupedAnswerTable f z) beta)
        (fun ll rr => refreshConsistencySign ll rr * spectralTruncation (groupedAnswerTable f z) beta ll rr) := by
  exact residual_identity sharePairsConsistent (groupedAnswerTable f z)
    (spectralTruncation (groupedAnswerTable f z) beta)
    (groupedAnswerTable_supported f z)
    (pairing_spectralTruncation_eq_normSq _ _)

/-- A coordinate consistency projection contracts every row's squared norm. -/
theorem projection_row_average_sq_le {X Y : Type*} [Fintype Y]
    (c : X → Y → Prop) [DecidableRel c] (P : Table X Y) (x : X) :
    average (fun y => projection c P x y ^ 2) ≤ average (fun y => P x y ^ 2) := by
  apply average_mono
  intro y
  by_cases h : c x y
  · simp [projection, h]
  · simp only [projection, h, ite_false, zero_pow (by norm_num : 2 ≠ 0)]
    exact sq_nonneg _

/-- Restricting a table to a consistency relation cannot increase any column’s mean square. -/
theorem projection_column_average_sq_le {X Y : Type*} [Fintype X]
    (c : X → Y → Prop) [DecidableRel c] (P : Table X Y) (y : Y) :
    average (fun x => projection c P x y ^ 2) ≤ average (fun x => P x y ^ 2) := by
  apply average_mono
  intro x
  by_cases h : c x y
  · simp [projection, h]
  · simp only [projection, h, ite_false, zero_pow (by norm_num : 2 ≠ 0)]
    exact sq_nonneg _

/-- Squared row norm of the actual residual is at most nine. -/
theorem actualResidual_row_average_sq_le_nine {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) (ll : State n) :
    average (fun rr => actualResidual f z beta ll rr ^ 2) ≤ 9 := by
  let : Nonempty (Share n) := share_nonempty_of_two_le hn
  let A := groupedAnswerTable f z
  let P := spectralTruncation A beta
  let Q := projection sharePairsConsistent P
  have hA : average (fun rr => A ll rr ^ 2) ≤ 1 := groupedAnswerTable_row_average_sq_le_one f z ll
  have hP : average (fun rr => P ll rr ^ 2) ≤ 1 := (spectralTruncation_row_average_sq_le A beta ll).trans hA
  have hQ : average (fun rr => Q ll rr ^ 2) ≤ 1 := (projection_row_average_sq_le _ P ll).trans hP
  have hp (rr : State n) : actualResidual f z beta ll rr ^ 2 ≤
      3 * A ll rr ^ 2 + 6 * Q ll rr ^ 2 := by
    change (A ll rr - 2 * Q ll rr) ^ 2 ≤ _
    nlinarith [sq_nonneg (A ll rr + Q ll rr)]
  have h := average_mono hp
  rw [average_add, average_smul, average_smul] at h
  linarith

/-- Squared column norm of the actual residual is also at most nine. -/
theorem actualResidual_column_average_sq_le_nine {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) (rr : State n) :
    average (fun ll => actualResidual f z beta ll rr ^ 2) ≤ 9 := by
  let : Nonempty (Share n) := share_nonempty_of_two_le hn
  let A := groupedAnswerTable f z
  let P := spectralTruncation A beta
  let Q := projection sharePairsConsistent P
  have hA : average (fun ll => A ll rr ^ 2) ≤ 1 := groupedAnswerTable_column_average_sq_le_one f z rr
  have hP : average (fun ll => P ll rr ^ 2) ≤ 1 := (spectralTruncation_column_average_sq_le A beta rr).trans hA
  have hQ : average (fun ll => Q ll rr ^ 2) ≤ 1 := (projection_column_average_sq_le _ P rr).trans hP
  have hp (ll : State n) : actualResidual f z beta ll rr ^ 2 ≤
      3 * A ll rr ^ 2 + 6 * Q ll rr ^ 2 := by
    change (A ll rr - 2 * Q ll rr) ^ 2 ≤ _
    nlinarith [sq_nonneg (A ll rr + Q ll rr)]
  have h := average_mono hp
  rw [average_add, average_smul, average_smul] at h
  linarith

/-- The actual residual max norm is at most 3/beta. -/
theorem actualResidual_entry_abs_le {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (ll rr : State n) :
    |actualResidual f z beta ll rr| ≤ 3 / beta := by
  let : Nonempty (Share n) := share_nonempty_of_two_le hn
  let A := groupedAnswerTable f z
  let P := spectralTruncation A beta
  let Q := projection sharePairsConsistent P
  have hP : |P ll rr| ≤ 1 / beta := spectralTruncation_entry_abs_le A hbeta ll rr
    (groupedAnswerTable_row_average_sq_le_one f z ll)
    (groupedAnswerTable_column_average_sq_le_one f z rr)
  have hQ : |Q ll rr| ≤ 1 / beta := by
    by_cases h : sharePairsConsistent ll rr
    · simpa only [Q, projection, h, ite_true] using hP
    · simp only [Q, projection, h, ite_false, abs_zero]
      positivity
  have hA := groupedAnswerTable_abs_le_one f z ll rr
  have hInv : 1 ≤ 1 / beta := (le_div_iff₀ hbeta).mpr (by simpa using hbeta1)
  change |A ll rr - 2 * Q ll rr| ≤ _
  calc
    _ ≤ |A ll rr| + |-(2 * Q ll rr)| := abs_add_le _ _
    _ = |A ll rr| + 2 * |Q ll rr| := by rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 1 + 2 * (1 / beta) := add_le_add hA (mul_le_mul_of_nonneg_left hQ (by norm_num))
    _ ≤ 3 * (1 / beta) := by linarith
    _ = _ := by ring

/-- Pairing form of the exact residual sign decomposition. -/
theorem actualResidual_product_pairing_decomposition {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) (u v : State n → ℝ) :
    pairing (actualResidual f z beta) (fun x y => u x * v y) =
      pairing (fun x y => groupedAnswerTable f z x y - spectralTruncation (groupedAnswerTable f z) beta x y)
        (fun x y => u x * v y) -
      2 * weightedConsistencyCorrelation (spectralTruncation (groupedAnswerTable f z) beta) u v := by
  rw [actualResidual_decomposition]
  unfold weightedConsistencyCorrelation pairing
  calc
    _ = average (fun x => average (fun y =>
        ((groupedAnswerTable f z x y - spectralTruncation (groupedAnswerTable f z) beta x y) * (u x * v y)) -
        2 * ((refreshConsistencySign x y * spectralTruncation (groupedAnswerTable f z) beta x y) * (u x * v y)))) := by
      apply average_congr
      intro x
      apply average_congr
      intro y
      ring
    _ = _ := by simp only [average_sub, average_smul]

/-- The actual residual has small correlation with every unit product test. -/
theorem actualResidual_unit_product_bound {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ} (hbeta : 0 < beta)
    (u v : State n → ℝ)
    (hu : average (fun x => u x ^ 2) = 1) (hv : average (fun y => v y ^ 2) = 1) :
    |pairing (actualResidual f z beta) (fun x y => u x * v y)| ≤ beta + 2 * (1 / ((q n : ℝ) * beta)) := by
  let : Nonempty (Share n) := share_nonempty_of_two_le hn
  have hd := discarded_pairing_abs_le (groupedAnswerTable f z) (le_of_lt hbeta) u v
  simp only [hu, hv, Real.sqrt_one, mul_one] at hd
  have hs := spectralTruncation_weighted_sign_bound hn (groupedAnswerTable f z) hbeta
    (groupedAnswerTable_abs_le_one f z) u v hu hv
  rw [actualResidual_product_pairing_decomposition]
  calc
    _ ≤ |pairing (fun x y => groupedAnswerTable f z x y - spectralTruncation (groupedAnswerTable f z) beta x y)
          (fun x y => u x * v y)| +
        |-(2 * weightedConsistencyCorrelation (spectralTruncation (groupedAnswerTable f z) beta) u v)| :=
      abs_add_le _ _
    _ = |pairing (fun x y => groupedAnswerTable f z x y - spectralTruncation (groupedAnswerTable f z) beta x y)
          (fun x y => u x * v y)| +
        2 * |weightedConsistencyCorrelation (spectralTruncation (groupedAnswerTable f z) beta) u v| := by
      rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ _ := add_le_add hd (mul_le_mul_of_nonneg_left hs (by norm_num))

/-- The threshold condition makes the consistency correction at most beta. -/
theorem inverse_q_beta_le_beta {n : ℕ} (hn : 2 ≤ n) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3) :
    1 / ((q n : ℝ) * beta) ≤ beta := by
  have hq : 0 < (q n : ℝ) := by have := q_real_three_le hn; linarith
  have hm := mul_le_mul_of_nonneg_left hbeta1 (mul_nonneg (le_of_lt hq) (sq_nonneg beta))
  have hh : 1 ≤ (q n : ℝ) * beta ^ 2 := by nlinarith
  apply (div_le_iff₀ (mul_pos hq hbeta)).mpr
  nlinarith

/-- The paper's actual residual product-test bound 3beta. -/
theorem actualResidual_unit_product_le_three_beta {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3)
    (u v : State n → ℝ)
    (hu : average (fun x => u x ^ 2) = 1) (hv : average (fun y => v y ^ 2) = 1) :
    |pairing (actualResidual f z beta) (fun x y => u x * v y)| ≤ 3 * beta := by
  have h := actualResidual_unit_product_bound hn f z hbeta u v hu hv
  have hc := inverse_q_beta_le_beta hn hbeta hbeta1 hthreshold
  linarith

/-- Exact unit tests suffice for the actual spectral fourth-moment bound. -/
theorem fourCycle_le_of_exact_unit_product_pairings {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty X] [Nonempty Y]
    (F : Table X Y) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ (u : X → ℝ) (v : Y → ℝ),
      average (fun x => u x ^ 2) = 1 → average (fun y => v y ^ 2) = 1 →
      |pairing F (fun x y => u x * v y)| ≤ M) :
    fourCycle F ≤ M ^ 2 * normSq F := by
  have hσ (j : Y) : normalizedSingularCoefficient F j ≤ M := by
    by_cases hj : 0 < rightEigenvalue F j
    · have hu : average (fun x => normalizedLeftFunction F j x ^ 2) = 1 := by
        simpa only [ite_true, ← pow_two] using
          normalizedLeftFunction_orthonormal F (⟨j, hj⟩ : PositiveDirection F) ⟨j, hj⟩
      have hv : average (fun y => normalizedRightFunction F j y ^ 2) = 1 := by
        simpa only [ite_true, ← pow_two] using normalizedRightFunction_orthonormal F j j
      have ht := h _ _ hu hv
      rw [pairing_singular_functions F j hj,
        abs_of_nonneg (normalizedSingularCoefficient_nonneg F j)] at ht
      exact ht
    · have hz : rightEigenvalue F j = 0 := le_antisymm (le_of_not_gt hj) (rightEigenvalue_nonneg F j)
      simpa only [normalizedSingularCoefficient, hz, Real.sqrt_zero, zero_div] using hM
  have ht := spectralPart_fourCycle_le F Finset.univ hM (fun j _ => hσ j)
  simpa only [spectralPart_univ] using ht

/-- The actual residual four-cycle estimate, without any assumed singular bound. -/
theorem actualResidual_fourCycle_le {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3) :
    fourCycle (actualResidual f z beta) ≤ 9 * beta ^ 2 * normSq (actualResidual f z beta) := by
  let : Nonempty (Share n) := share_nonempty_of_two_le hn
  have h := fourCycle_le_of_exact_unit_product_pairings (actualResidual f z beta)
    (by positivity : 0 ≤ 3 * beta)
    (actualResidual_unit_product_le_three_beta hn f z hbeta hbeta1 hthreshold)
  calc
    _ ≤ (3 * beta) ^ 2 * normSq (actualResidual f z beta) := h
    _ = _ := by ring

/-- Pairing commutes with finite sums in the first argument. -/
theorem pairing_sum_left {X Y ι : Type*} [Fintype X] [Fintype Y]
    (I : Finset ι) (F : ι → Table X Y) (G : Table X Y) :
    pairing (fun x y => ∑ j ∈ I, F j x y) G = ∑ j ∈ I, pairing (F j) G := by
  unfold pairing
  simp only [Finset.sum_mul, average_sum]

/-- The exact retained singular expansion expresses the cross term through actual unit sign correlations. -/
theorem actualTruncation_sign_cross_expansion {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) [Nonempty (Share n)] :
    pairing (spectralTruncation (groupedAnswerTable f z) beta)
      (fun x y => refreshConsistencySign x y * spectralTruncation (groupedAnswerTable f z) beta x y) =
      ∑ j ∈ retainedDirections (groupedAnswerTable f z) beta,
        normalizedSingularCoefficient (groupedAnswerTable f z) j *
          weightedConsistencyCorrelation (spectralTruncation (groupedAnswerTable f z) beta)
            (normalizedLeftFunction (groupedAnswerTable f z) j)
            (normalizedRightFunction (groupedAnswerTable f z) j) := by
  let A := groupedAnswerTable f z
  let P := spectralTruncation A beta
  have he : P = fun x y => ∑ j ∈ retainedDirections A beta,
      normalizedSingularCoefficient A j * normalizedLeftFunction A j x * normalizedRightFunction A j y := by
    funext x y
    exact spectralTruncation_normalized_expansion A beta x y
  change pairing P (fun x y => refreshConsistencySign x y * P x y) = _
  calc
    _ = pairing (fun x y => ∑ j ∈ retainedDirections A beta,
        normalizedSingularCoefficient A j * normalizedLeftFunction A j x * normalizedRightFunction A j y)
        (fun x y => refreshConsistencySign x y * P x y) :=
      congrArg (fun T => pairing T (fun x y => refreshConsistencySign x y * P x y)) he
    _ = _ := by
      rw [pairing_sum_left]
      apply Finset.sum_congr rfl
      intro j hj
      unfold weightedConsistencyCorrelation pairing
      rw [← average_smul]
      apply average_congr
      intro x
      rw [← average_smul]
      apply average_congr
      intro y
      ring

/-- The actual cross term is at most 2/(q beta), using the proved actual nuclear bound and actual consistency-sign cancellation. -/
theorem actualTruncation_sign_cross_abs_le {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3) :
    |pairing (spectralTruncation (groupedAnswerTable f z) beta)
      (fun x y => refreshConsistencySign x y * spectralTruncation (groupedAnswerTable f z) beta x y)| ≤
        2 / ((q n : ℝ) * beta) := by
  let : Nonempty (Share n) := share_nonempty_of_two_le hn
  let A := groupedAnswerTable f z
  let P := spectralTruncation A beta
  have htest (j : State n) (hj : j ∈ retainedDirections A beta) :
      |weightedConsistencyCorrelation P (normalizedLeftFunction A j) (normalizedRightFunction A j)| ≤
        1 / ((q n : ℝ) * beta) := by
    have hu : average (fun x => normalizedLeftFunction A j x ^ 2) = 1 := by
      have hh := normalizedLeftFunction_retained_inner A hbeta j j hj hj
      simpa only [ite_true, ← pow_two] using hh
    have hv : average (fun y => normalizedRightFunction A j y ^ 2) = 1 := by
      simpa only [ite_true, ← pow_two] using normalizedRightFunction_orthonormal A j j
    exact spectralTruncation_weighted_sign_bound hn A hbeta (groupedAnswerTable_abs_le_one f z) _ _ hu hv
  rw [actualTruncation_sign_cross_expansion]
  calc
    _ ≤ ∑ j ∈ retainedDirections A beta, |normalizedSingularCoefficient A j *
        weightedConsistencyCorrelation P (normalizedLeftFunction A j) (normalizedRightFunction A j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ retainedDirections A beta, normalizedSingularCoefficient A j * (1 / ((q n : ℝ) * beta)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (normalizedSingularCoefficient_nonneg A j)]
      exact mul_le_mul_of_nonneg_left (htest j hj) (normalizedSingularCoefficient_nonneg A j)
    _ = truncatedNuclearNorm A beta * (1 / ((q n : ℝ) * beta)) := (Finset.sum_mul _ _ _).symm
    _ ≤ 2 * (1 / ((q n : ℝ) * beta)) :=
      mul_le_mul_of_nonneg_right (actual_answer_nuclear_le_two hn f z hbeta hbeta1 hthreshold) (by positivity)
    _ = _ := by ring

end RefreshingProof.Local
