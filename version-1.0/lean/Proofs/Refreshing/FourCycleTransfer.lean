import Proofs.Refreshing.InvertibleCycle
import Proofs.Refreshing.RankEnvelope
import Proofs.Refreshing.ResidualBootstrap
import Proofs.Refreshing.LocalApproximation

/-!
# Transferring actual four-cycle bounds through a refresh

The analytic results first expose the exact rank-envelope estimate explicitly. The final results discharge it using the proved actual matrix-counting theorem. No counting, transfer, local approximation, or security conclusion is assumed in the unconditional public results.
-/

noncomputable section
open scoped BigOperators Matrix

namespace RefreshingProof.Local
open Refreshing

/-- The analytic four-cycle refresh bound, conditional only on the explicitly stated rank envelope of the actual zero-extended unrestricted experiment. -/
theorem fourCycle_refresh_transfer_of_rank_envelope {n : ℕ} (hn : 2 ≤ n)
    (F : Table (State n) (State n)) {B R : ℝ} (hB : 0 ≤ B)
    (hentry : ∀ x y, |F x y| ≤ B)
    (hrow : ∀ x, average (fun y => F x y ^ 2) ≤ R ^ 2)
    (hcolumn : ∀ y, average (fun x => F x y ^ 2) ≤ R ^ 2)
    (hRank : average (fun A : BinaryMatrix n =>
        fourCycle (unrestrictedRefreshTable (groupedZeroExtension F) A)) ≤
      fourRankEnvelope (groupedZeroExtension F) (q n : ℝ)) :
    average (fun M : RefreshMatrix n => fourCycle (matrixPullback F M)) ≤
      64 * fourCycle F + (32 * R ^ 2 / (q n : ℝ)) * normSq F +
        (72 * B ^ 2 / (q n : ℝ) ^ 2) * normSq F := by
  let : Nonempty (Share n) := share_nonempty_of_two_le hn
  have hcard : Fintype.card (Share n) ≤ Fintype.card (Refreshing.Vector n) :=
    Fintype.card_subtype_le (fun x : Refreshing.Vector n => x ≠ 0)
  have henv := fourRankEnvelope_bound (groupedZeroExtension F) hcard hB
    (groupedZeroExtension_entry_bound F hB hentry)
    (groupedZeroExtension_row_bound hn F hrow)
    (groupedZeroExtension_column_bound hn F hcolumn)
  have hN : 0 ≤ normSq F := average_nonneg fun x => average_nonneg fun y => mul_self_nonneg _
  have hC : 0 ≤ fourCycle F := fourCycle_nonneg F
  have hρ2 : newShareDensity n ^ 2 ≤ 1 := pow_le_one₀ (newShareDensity_nonneg n) (newShareDensity_le_one n)
  have hρ4 : newShareDensity n ^ 4 ≤ 1 := pow_le_one₀ (newShareDensity_nonneg n) (newShareDensity_le_one n)
  have hNbar : normSq (groupedZeroExtension F) ≤ normSq F := by
    rw [normSq_groupedZeroExtension hn]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hρ2 hN
  have hCbar : fourCycle (groupedZeroExtension F) ≤ fourCycle F := by
    rw [fourCycle_groupedZeroExtension hn]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hρ4 hC
  have hq : 0 < (q n : ℝ) := by have := q_real_three_le hn; linarith
  calc
    _ ≤ 4 * average (fun A : BinaryMatrix n =>
        fourCycle (unrestrictedRefreshTable (groupedZeroExtension F) A)) :=
      average_refresh_cycle_le_unrestricted F
    _ ≤ 4 * fourRankEnvelope (groupedZeroExtension F) (q n : ℝ) :=
      mul_le_mul_of_nonneg_left hRank (by norm_num)
    _ ≤ 64 * fourCycle (groupedZeroExtension F) +
        (32 * R ^ 2 / (q n : ℝ)) * normSq (groupedZeroExtension F) +
        (72 * B ^ 2 / (q n : ℝ) ^ 2) * normSq (groupedZeroExtension F) := by
      simpa only [card_share] using henv
    _ ≤ _ := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hCbar (by norm_num))
        (mul_le_mul_of_nonneg_left hNbar (by positivity)))
      (mul_le_mul_of_nonneg_left hNbar (by positivity))

/-- Numerical instantiation of the actual residual's four-cycle transfer. The explicit rank-envelope premise is the only remaining counting input. -/
theorem actualResidual_fourCycle_transfer_of_rank_envelope {n leakage : ℕ}
    (hn : 2 ≤ n) (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3)
    (hRank : average (fun A : BinaryMatrix n =>
        fourCycle (unrestrictedRefreshTable (groupedZeroExtension (actualResidual f z beta)) A)) ≤
      fourRankEnvelope (groupedZeroExtension (actualResidual f z beta)) (q n : ℝ)) :
    average (fun M : RefreshMatrix n => fourCycle (actualResidualPullback f z beta M)) ≤
      1512 * beta ^ 2 * normSq (actualResidual f z beta) := by
  let F := actualResidual f z beta
  have hrow (x : State n) : average (fun y => F x y ^ 2) ≤ (3 : ℝ) ^ 2 := by
    simpa only [show (3 : ℝ) ^ 2 = 9 by norm_num] using actualResidual_row_average_sq_le_nine hn f z beta x
  have hcolumn (y : State n) : average (fun x => F x y ^ 2) ≤ (3 : ℝ) ^ 2 := by
    simpa only [show (3 : ℝ) ^ 2 = 9 by norm_num] using actualResidual_column_average_sq_le_nine hn f z beta y
  have h := fourCycle_refresh_transfer_of_rank_envelope hn F (B := 3 / beta) (R := 3)
    (by positivity) (actualResidual_entry_abs_le hn f z hbeta hbeta1) hrow hcolumn hRank
  have hC := actualResidual_fourCycle_le hn f z hbeta hbeta1 hthreshold
  have hN : 0 ≤ normSq F := average_nonneg fun x => average_nonneg fun y => mul_self_nonneg _
  have hq : 0 < (q n : ℝ) := by have := q_real_three_le hn; linarith
  have hmono := mul_le_mul_of_nonneg_left hbeta1 (mul_nonneg (le_of_lt hq) (sq_nonneg beta))
  have hqbeta : 1 ≤ (q n : ℝ) * beta ^ 2 := by nlinarith
  have hqinv : 1 / (q n : ℝ) ≤ beta ^ 2 := (div_le_iff₀ hq).mpr (by nlinarith)
  have hinv := inverse_q_beta_le_beta hn hbeta hbeta1 hthreshold
  have hinvsq : (1 / ((q n : ℝ) * beta)) ^ 2 ≤ beta ^ 2 :=
    (sq_le_sq₀ (by positivity) (le_of_lt hbeta)).mpr hinv
  have hcoef₂ : 32 * (3 : ℝ) ^ 2 / (q n : ℝ) ≤ 288 * beta ^ 2 := by
    calc
      _ = 288 * (1 / (q n : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hqinv (by norm_num)
  have hcoef₃ : 72 * (3 / beta) ^ 2 / (q n : ℝ) ^ 2 ≤ 648 * beta ^ 2 := by
    calc
      _ = 648 * (1 / ((q n : ℝ) * beta)) ^ 2 := by
        field_simp [ne_of_gt hq, ne_of_gt hbeta]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hinvsq (by norm_num)
  calc
    _ ≤ 64 * fourCycle F + (32 * (3 : ℝ) ^ 2 / (q n : ℝ)) * normSq F +
        (72 * (3 / beta) ^ 2 / (q n : ℝ) ^ 2) * normSq F := h
    _ ≤ 64 * (9 * beta ^ 2 * normSq F) + (288 * beta ^ 2) * normSq F +
        (648 * beta ^ 2) * normSq F :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hC (by norm_num))
        (mul_le_mul_of_nonneg_right hcoef₂ hN))
        (mul_le_mul_of_nonneg_right hcoef₃ hN)
    _ = _ := by ring

/-- Explicit actual residual norm bound once the actual rank envelope is known. -/
theorem actualResidual_norm_le_of_rank_envelope {n leakage : ℕ}
    (hn : 2 ≤ n) (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3)
    (hRank : average (fun A : BinaryMatrix n =>
        fourCycle (unrestrictedRefreshTable (groupedZeroExtension (actualResidual f z beta)) A)) ≤
      fourRankEnvelope (groupedZeroExtension (actualResidual f z beta)) (q n : ℝ)) :
    Real.sqrt (normSq (actualResidual f z beta)) ≤ 324 * beta ^ (1 / 3 : ℝ) :=
  actualResidual_norm_le_of_fourCycle_transfer hn f z hbeta hbeta1 hthreshold
    (actualResidual_fourCycle_transfer_of_rank_envelope hn f z hbeta hbeta1 hthreshold hRank)

/-- Actual canonical conditional-answer error from the actual rank envelope. -/
theorem conditional_local_error_le_of_rank_envelope {n leakage : ℕ}
    (hn : 2 ≤ n) (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3)
    (hRank : average (fun A : BinaryMatrix n =>
        fourCycle (unrestrictedRefreshTable (groupedZeroExtension (actualResidual f z beta)) A)) ≤
      fourRankEnvelope (groupedZeroExtension (actualResidual f z beta)) (q n : ℝ)) (s : Bit) :
    Real.sqrt (average (fun x : Encoding n s => average (fun y : Encoding n s =>
      ((conditionalAnswer f x y z).toReal - localG f z beta (x.val.1, y.val.1) (x.val.2, y.val.2)) ^ 2))) ≤
      972 * beta ^ (1 / 3 : ℝ) :=
  conditional_local_error_le hn f z hbeta hbeta1 hthreshold
    (actualResidual_fourCycle_transfer_of_rank_envelope hn f z hbeta hbeta1 hthreshold hRank) s

/-- The actual zero extension satisfies the proved unrestricted rank envelope. -/
theorem groupedZeroExtension_rank_envelope {n : ℕ} (hn : 2 ≤ n)
    (F : Table (State n) (State n))
    (hF : ∀ ll rr, ll.1.val ⬝ᵥ rr.1.val ≠ ll.2.val ⬝ᵥ rr.2.val → F ll rr = 0) :
    average (fun A : BinaryMatrix n =>
      fourCycle (unrestrictedRefreshTable (groupedZeroExtension F) A)) ≤
        fourRankEnvelope (groupedZeroExtension F) (q n : ℝ) := by
  apply unrestricted_fourCycle_le_rankEnvelope hn (groupedZeroExtension F)
  · intro ll rr hz
    rcases rr with ⟨r, v⟩
    change v = 0 at hz
    subst v
    exact groupedZeroExtension_right_zero F ll r
  · exact groupedZeroExtension_supported F hF

/-- The unconditional actual refreshing four-cycle transfer from the paper. -/
theorem fourCycle_refresh_transfer {n : ℕ} (hn : 2 ≤ n)
    (F : Table (State n) (State n)) {B R : ℝ} (hB : 0 ≤ B)
    (hentry : ∀ x y, |F x y| ≤ B)
    (hrow : ∀ x, average (fun y => F x y ^ 2) ≤ R ^ 2)
    (hcolumn : ∀ y, average (fun x => F x y ^ 2) ≤ R ^ 2)
    (hF : ∀ ll rr, ll.1.val ⬝ᵥ rr.1.val ≠ ll.2.val ⬝ᵥ rr.2.val → F ll rr = 0) :
    average (fun M : RefreshMatrix n => fourCycle (matrixPullback F M)) ≤
      64 * fourCycle F + (32 * R ^ 2 / (q n : ℝ)) * normSq F +
        (72 * B ^ 2 / (q n : ℝ) ^ 2) * normSq F :=
  fourCycle_refresh_transfer_of_rank_envelope hn F hB hentry hrow hcolumn
    (groupedZeroExtension_rank_envelope hn F hF)

/-- The actual residual transfer bound, with every rank and counting input proved from the actual uniform matrix experiment. -/
theorem actualResidual_fourCycle_transfer {n leakage : ℕ}
    (hn : 2 ≤ n) (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3) :
    average (fun M : RefreshMatrix n => fourCycle (actualResidualPullback f z beta M)) ≤
      1512 * beta ^ 2 * normSq (actualResidual f z beta) :=
  actualResidual_fourCycle_transfer_of_rank_envelope hn f z hbeta hbeta1 hthreshold
    (groupedZeroExtension_rank_envelope hn (actualResidual f z beta)
      (fun ll rr hne => actualResidual_supported f z beta ll rr hne))

/-- Actual local residual approximation, with no transfer or counting premise. -/
theorem actualResidual_norm_le {n leakage : ℕ}
    (hn : 2 ≤ n) (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3) :
    Real.sqrt (normSq (actualResidual f z beta)) ≤ 324 * beta ^ (1 / 3 : ℝ) :=
  actualResidual_norm_le_of_fourCycle_transfer hn f z hbeta hbeta1 hthreshold
    (actualResidual_fourCycle_transfer hn f z hbeta hbeta1 hthreshold)

/-- The actual paper local approximation for the canonical conditional-answer PMFs, with no analytic or probabilistic estimates left as assumptions. -/
theorem actual_conditional_local_error_le {n leakage : ℕ}
    (hn : 2 ≤ n) (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3) (s : Bit) :
    Real.sqrt (average (fun x : Encoding n s => average (fun y : Encoding n s =>
      ((conditionalAnswer f x y z).toReal - localG f z beta (x.val.1, y.val.1) (x.val.2, y.val.2)) ^ 2))) ≤
      972 * beta ^ (1 / 3 : ℝ) :=
  conditional_local_error_le hn f z hbeta hbeta1 hthreshold
    (actualResidual_fourCycle_transfer hn f z hbeta hbeta1 hthreshold) s

/-- Squared form of the unconditional actual local approximation. -/
theorem actual_conditional_local_error_sq_le {n leakage : ℕ}
    (hn : 2 ≤ n) (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3) (s : Bit) :
    average (fun x : Encoding n s => average (fun y : Encoding n s =>
      ((conditionalAnswer f x y z).toReal - localG f z beta (x.val.1, y.val.1) (x.val.2, y.val.2)) ^ 2)) ≤
      (972 * beta ^ (1 / 3 : ℝ)) ^ 2 :=
  conditional_local_error_sq_le_explicit hn f z hbeta hbeta1 hthreshold
    (actualResidual_fourCycle_transfer hn f z hbeta hbeta1 hthreshold) s

end RefreshingProof.Local
