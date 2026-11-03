import Proofs.Refreshing.LocalSpectralBounds
import Proofs.Refreshing.Canonical
import Proofs.Refreshing.GramVariance
import Proofs.Refreshing.TwoSecret
import Proofs.Refreshing.RefreshFrames

/-!
# Actual refreshing answer table and its mask-pairing identity

The table is constructed from the operational matrix/answer observation PMF. Its normalization uses the actual size of the corresponding encoding fiber. The conditional table and its relation to the masks are derived, not assumed.
-/

noncomputable section
open scoped BigOperators Matrix ENNReal

namespace RefreshingProof.Local
open Refreshing

/-- Actual old-state observation: refresh by the real uniform matrix and observe the actual pair of local leakage answers. -/
def refreshObservation {n leakage : ℕ} (f : LeakageQuery n leakage) (x : State n) :
    PMF (State n × Answer leakage) :=
  (matrixDistribution n).map (fun M => (refresh x M, answer f x M))

/-- The actual conditional answer table extended to all state pairs. The fiber normalizer converts the joint state/answer point mass to conditional mass. -/
def answerKernel {n leakage : ℕ} (f : LeakageQuery n leakage) (z : Answer leakage)
    (x y : State n) : ℝ :=
  (Fintype.card (Encoding n (secret x)) : ℝ) * (refreshObservation f x (y, z)).toReal

/-- The paper's grouped-coordinate answer table. -/
def groupedAnswerTable {n leakage : ℕ} (f : LeakageQuery n leakage) (z : Answer leakage) :
    Table (Share n × Share n) (Share n × Share n) :=
  fun ll rr => answerKernel f z (ll.1, rr.1) (ll.2, rr.2)

/-- Actual fiber probability under independent uniform shares. -/
def secretFiberWeight (n : ℕ) (s : Bit) : ℝ :=
  (Fintype.card (Encoding n s) : ℝ) / (Fintype.card (State n) : ℝ)

/-- A finite injective PMF pushforward preserves masses at image points. -/
theorem pmf_map_injective_apply {α β : Type*} [Fintype α]
    (P : PMF α) (f : α → β) (hf : Function.Injective f) (a : α) :
    (P.map f) (f a) = P a := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    have hne : f a ≠ f b := fun h => hba (hf h).symm
    simp only [hne, ite_false]
  · exact fun hn => False.elim (hn (Finset.mem_univ a))

/-- Point mass of the exact experiment that first draws a state, then draws its answer from a conditional PMF while retaining the state. -/
theorem pmf_bind_pair_apply {α β : Type*} [Fintype α] [Fintype β]
    (P : PMF α) (K : α → PMF β) (a : α) (b : β) :
    (P.bind (fun a' => (K a').map (fun b' => (a', b')))) (a, b) = P a * K a b := by
  classical
  simp [PMF.bind_apply, PMF.map_apply, tsum_fintype, Prod.mk.injEq, ite_and]

/-- On every consistent pair, the constructed table is exactly the genuine conditional-answer PMF from the operational canonical experiment. -/
theorem answerKernel_eq_conditional {n leakage : ℕ} {s : Bit}
    (f : LeakageQuery n leakage) (z : Answer leakage) (x y : Encoding n s) :
    answerKernel f z x.val y.val = (conditionalAnswer f x y z).toReal := by
  classical
  let : Nonempty (Encoding n s) := ⟨x⟩
  let P : PMF (Encoding n s × Answer leakage) :=
    (matrixDistribution n).map (fun M => (refreshEncoding x M, answer f x.val M))
  let embed : Encoding n s × Answer leakage → State n × Answer leakage :=
    fun yz => (yz.1.val, yz.2)
  have hembed : Function.Injective embed := by
    intro a b h
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun p => p.1) h
    · exact congrArg (fun p => p.2) h
  have hmap : refreshObservation f x.val = P.map embed := by
    simp only [refreshObservation, P, PMF.map_comp, Function.comp_def, embed,
      refreshEncoding_val]
  have hpoint : refreshObservation f x.val (y.val, z) = P (y, z) := by
    rw [hmap]
    exact pmf_map_injective_apply P embed hembed (y, z)
  have hp : P (y, z) = uniformPMF (Encoding n s) y * conditionalAnswer f x y z := by
    dsimp [P]
    rw [round_joint_distribution]
    exact pmf_bind_pair_apply _ _ _ _
  unfold answerKernel
  rw [x.property, hpoint, hp, uniformPMF_apply, ENNReal.toReal_mul, ENNReal.toReal_inv]
  have hc : (Fintype.card (Encoding n s) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [ENNReal.toReal_natCast]
  field_simp [hc]

/-- An inconsistent state pair has zero mass in the actual observation. -/
theorem refreshObservation_inconsistent {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (x y : State n)
    (hxy : secret x ≠ secret y) : refreshObservation f x (y, z) = 0 := by
  classical
  have hne (M : RefreshMatrix n) : (y, z) ≠ (refresh x M, answer f x M) := by
    intro h
    have hs := congrArg (fun yz => secret yz.1) h
    rw [refresh_preserves_secret] at hs
    exact hxy hs.symm
  simp only [refreshObservation, PMF.map_apply, hne, ite_false, tsum_zero]

/-- Zero extension to inconsistent tuples is a derived property. -/
theorem answerKernel_inconsistent {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (x y : State n)
    (hxy : secret x ≠ secret y) : answerKernel f z x y = 0 := by
  rw [answerKernel, refreshObservation_inconsistent f z x y hxy, ENNReal.toReal_zero, mul_zero]

/-- Every entry of the completed conditional-answer kernel is nonnegative. -/
theorem answerKernel_nonneg {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (x y : State n) :
    0 ≤ answerKernel f z x y := by
  unfold answerKernel
  positivity

/-- The constructed table is a conditional probability on consistent pairs and zero elsewhere, so all its entries lie in [0,1]. -/
theorem answerKernel_le_one {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (x y : State n) :
    answerKernel f z x y ≤ 1 := by
  classical
  by_cases hxy : secret x = secret y
  · let x' : Encoding n (secret x) := ⟨x, rfl⟩
    let y' : Encoding n (secret x) := ⟨y, hxy.symm⟩
    rw [show x = x'.val from rfl, show y = y'.val from rfl, answerKernel_eq_conditional]
    simpa only [ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top ((conditionalAnswer f x' y').coe_le_one z)
  · rw [answerKernel_inconsistent f z x y hxy]
    norm_num

/-- Taking one answer slice of a finite joint PMF is ordinary expectation against its answer indicator. -/
theorem pmf_answer_slice {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : PMF (α × β)) (b : β) (W : α → ℝ) :
    (∑ a, (P (a, b)).toReal * W a) =
      ∑ ab, (P ab).toReal * (if ab.2 = b then W ab.1 else 0) := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  simp

/-- Exact expectation identity for the real operational observation distribution. -/
theorem refreshObservation_slice {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (x : State n) (W : State n → ℝ) :
    (∑ y, (refreshObservation f x (y, z)).toReal * W y) =
      average (fun M : RefreshMatrix n => if answer f x M = z then W (refresh x M) else 0) := by
  rw [pmf_answer_slice]
  rw [refreshObservation, pmf_expectation_map]
  exact uniformPMF_expectation (X := RefreshMatrix n) _

/-- Averaging the constructed kernel over all new shares gives the actual matrix experiment with precisely the encoding-fiber weight. -/
theorem answerKernel_average_new {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (x : State n) (W : State n → ℝ) :
    average (fun y => answerKernel f z x y * W y) =
      secretFiberWeight n (secret x) *
        average (fun M : RefreshMatrix n => if answer f x M = z then W (refresh x M) else 0) := by
  have heq (y : State n) : answerKernel f z x y * W y =
      (Fintype.card (Encoding n (secret x)) : ℝ) * ((refreshObservation f x (y, z)).toReal * W y) := by
    unfold answerKernel
    ring
  simp_rw [heq]
  rw [average_smul]
  calc
    _ = secretFiberWeight n (secret x) *
        (∑ y, (refreshObservation f x (y, z)).toReal * W y) := by
      unfold average secretFiberWeight
      ring
    _ = _ := by rw [refreshObservation_slice]

/-- The left and right answer masks are the actual indicators of the local leakage functions, not arbitrary test functions. -/
def leftAnswerMask {n leakage : ℕ} (f : LeakageQuery n leakage) (z : Answer leakage)
    (l : Share n) (M : RefreshMatrix n) : ℝ := if f.1 l M = z.1 then 1 else 0

/-- The right local answer mask equals one when the query returns the specified right answer and zero otherwise. -/
def rightAnswerMask {n leakage : ℕ} (f : LeakageQuery n leakage) (z : Answer leakage)
    (r : Share n) (M : RefreshMatrix n) : ℝ := if f.2 r M = z.2 then 1 else 0

/-- Current answer equality is exactly the product of the two local masks. -/
theorem answer_indicator_masks {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (x : State n) (M : RefreshMatrix n) (w : ℝ) :
    (if answer f x M = z then w else 0) =
      leftAnswerMask f z x.1 M * rightAnswerMask f z x.2 M * w := by
  classical
  rcases z with ⟨zl, zr⟩
  by_cases hL : f.1 x.1 M = zl <;> by_cases hR : f.2 x.2 M = zr <;>
    simp [answer, leftAnswerMask, rightAnswerMask, Prod.mk.injEq, hL, hR]

/-- Regroup the four independent shares into old and new states. -/
theorem groupedAnswerTable_pairing_states {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage)
    (W : Table (Share n × Share n) (Share n × Share n)) :
    pairing (groupedAnswerTable f z) W =
      average (fun x : State n => average (fun y : State n =>
        answerKernel f z x y * W (x.1, y.1) (x.2, y.2))) := by
  unfold pairing groupedAnswerTable
  simp only [average_product]
  apply average_congr
  intro l
  exact average_comm _

/-- The exact mask-pairing identity for the actual grouped refreshing answer table. This gives the paper's pairing formula directly from the refreshing experiment. -/
theorem groupedAnswerTable_mask_pairing {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage)
    (W : Table (Share n × Share n) (Share n × Share n)) :
    pairing (groupedAnswerTable f z) W =
      average (fun l : Share n => average (fun r : Share n =>
        average (fun M : RefreshMatrix n =>
          secretFiberWeight n (secret (l, r)) * leftAnswerMask f z l M * rightAnswerMask f z r M *
            W (l, refreshLeft l M) (r, refreshRight r M)))) := by
  rw [groupedAnswerTable_pairing_states]
  simp_rw [answerKernel_average_new]
  rw [average_product]
  apply average_congr
  intro l
  apply average_congr
  intro r
  rw [← average_smul]
  apply average_congr
  intro M
  rw [answer_indicator_masks]
  simp only [refresh]
  ring

/-- The relative weight of a secret fiber in the independent-share space is nonnegative. -/
theorem secretFiberWeight_nonneg (n : ℕ) (s : Bit) : 0 ≤ secretFiberWeight n s := by
  unfold secretFiberWeight
  positivity

/-- Every actual encoding fiber occupies at most the full independent-share space. -/
theorem secretFiberWeight_le_one (n : ℕ) (s : Bit) : secretFiberWeight n s ≤ 1 := by
  have hc : (Fintype.card (Encoding n s) : ℝ) ≤ (Fintype.card (State n) : ℝ) := by
    exact_mod_cast Fintype.card_subtype_le (fun x : State n => secret x = s)
  unfold secretFiberWeight
  by_cases hs : (Fintype.card (State n) : ℝ) = 0
  · rw [hs, div_zero]
    norm_num
  · have hp : 0 < (Fintype.card (State n) : ℝ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hs)
    apply (div_le_iff₀ hp).mpr
    simpa only [one_mul] using hc

/-- Explicit binary secret-fiber weights. -/
theorem secretFiberWeight_binary {n : ℕ} (hn : 2 ≤ n) :
    secretFiberWeight n 0 = ((q n : ℝ) - 1) / (2 * (q n : ℝ)) ∧
    secretFiberWeight n 1 = ((q n : ℝ) + 1) / (2 * (q n : ℝ)) := by
  have hq : (q n : ℝ) ≠ 0 := by have := q_real_three_le hn; linarith
  have hstate : (Fintype.card (State n) : ℝ) = (q n : ℝ) ^ 2 := by
    simp only [State, Fintype.card_prod, Nat.cast_mul, card_share, pow_two]
  unfold secretFiberWeight
  rw [hstate, (card_encoding_real n).1, (card_encoding_real n).2]
  constructor <;> field_simp [hq]

/-- The binary fiber weight differs from one half by exactly 1/(2q). -/
theorem secretFiberWeight_centered_abs {n : ℕ} (hn : 2 ≤ n) (s : Bit) :
    |secretFiberWeight n s - (1 / 2 : ℝ)| = 1 / (2 * (q n : ℝ)) := by
  have hq : 0 < (q n : ℝ) := by have := q_real_three_le hn; linarith
  rcases Binary.bit_cases s with hs | hs
  · subst s
    rw [(secretFiberWeight_binary hn).1]
    have he : ((q n : ℝ) - 1) / (2 * (q n : ℝ)) - 1 / 2 = -(1 / (2 * (q n : ℝ))) := by
      field_simp
      ring
    rw [he, abs_neg, abs_of_nonneg (by positivity)]
  · subst s
    rw [(secretFiberWeight_binary hn).2]
    have he : ((q n : ℝ) + 1) / (2 * (q n : ℝ)) - 1 / 2 = 1 / (2 * (q n : ℝ)) := by
      field_simp
      ring
    rw [he, abs_of_nonneg (by positivity)]

/-- Nonempty shares at the theorem's dimensions. -/
theorem share_nonempty_of_two_le {n : ℕ} (hn : 2 ≤ n) : Nonempty (Share n) := by
  let x : Encoding n 0 := Classical.choice (encoding_nonempty hn 0)
  exact ⟨x.val.1⟩

/-- Every entry of the grouped conditional-answer table is nonnegative. -/
theorem groupedAnswerTable_nonneg {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (ll rr : Share n × Share n) :
    0 ≤ groupedAnswerTable f z ll rr := answerKernel_nonneg _ _ _ _

/-- Every grouped conditional-answer probability is at most one. -/
theorem groupedAnswerTable_le_one {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (ll rr : Share n × Share n) :
    groupedAnswerTable f z ll rr ≤ 1 := answerKernel_le_one _ _ _ _

/-- Every grouped conditional-answer table entry has absolute value at most one. -/
theorem groupedAnswerTable_abs_le_one {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (ll rr : Share n × Share n) :
    |groupedAnswerTable f z ll rr| ≤ 1 := by
  rw [abs_of_nonneg (groupedAnswerTable_nonneg f z ll rr)]
  exact groupedAnswerTable_le_one f z ll rr

/-- The consistency predicate for the grouped old/new shares. -/
def refreshConsistency {n : ℕ} (ll rr : Share n × Share n) : Prop :=
  secret (ll.1, rr.1) = secret (ll.2, rr.2)

/-- The actual answer table has exactly the support convention of the paper. -/
theorem groupedAnswerTable_supported {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (ll rr : Share n × Share n)
    (h : ¬ refreshConsistency ll rr) : groupedAnswerTable f z ll rr = 0 :=
  answerKernel_inconsistent _ _ _ _ h

/-- Canonical conditional answer probabilities equal the actual grouped table at every pair of encodings of the same secret. -/
theorem groupedAnswerTable_eq_conditional {n leakage : ℕ} {s : Bit}
    (f : LeakageQuery n leakage) (z : Answer leakage) (x y : Encoding n s) :
    groupedAnswerTable f z (x.val.1, y.val.1) (x.val.2, y.val.2) =
      (conditionalAnswer f x y z).toReal := answerKernel_eq_conditional _ _ _ _

/-- The centered density estimate in the convention |2p_s−1|=1/q. -/
theorem secretFiberWeight_twice_centered_abs {n : ℕ} (hn : 2 ≤ n) (s : Bit) :
    |2 * secretFiberWeight n s - 1| = 1 / (q n : ℝ) := by
  have he : 2 * secretFiberWeight n s - 1 = 2 * (secretFiberWeight n s - (1 / 2 : ℝ)) := by ring
  rw [he, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), secretFiberWeight_centered_abs hn s]
  have hq : (q n : ℝ) ≠ 0 := by have := q_real_three_le hn; linarith
  field_simp [hq]

/-- The square of a left local answer mask is at most one. -/
@[simp] theorem leftAnswerMask_sq_le_one {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (l : Share n) (M : RefreshMatrix n) :
    leftAnswerMask f z l M ^ 2 ≤ 1 := by
  unfold leftAnswerMask
  split_ifs <;> norm_num

/-- The square of a right local answer mask is at most one. -/
@[simp] theorem rightAnswerMask_sq_le_one {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (r : Share n) (M : RefreshMatrix n) :
    rightAnswerMask f z r M ^ 2 ≤ 1 := by
  unfold rightAnswerMask
  split_ifs <;> norm_num

/-- Actual local Boolean masks have normalized L₂ norm at most one. -/
theorem leftAnswerMask_average_sq_le_one {n leakage : ℕ} [Nonempty (Share n)]
    (f : LeakageQuery n leakage) (z : Answer leakage) (M : RefreshMatrix n) :
    average (fun l => leftAnswerMask f z l M ^ 2) ≤ 1 := by
  have h := average_mono (fun l => leftAnswerMask_sq_le_one f z l M)
  simpa only [RefreshingProof.average_const] using h

/-- The uniform right-share mean of a fixed-matrix answer mask’s square is at most one. -/
theorem rightAnswerMask_average_sq_le_one {n leakage : ℕ} [Nonempty (Share n)]
    (f : LeakageQuery n leakage) (z : Answer leakage) (M : RefreshMatrix n) :
    average (fun r => rightAnswerMask f z r M ^ 2) ≤ 1 := by
  have h := average_mono (fun r => rightAnswerMask_sq_le_one f z r M)
  simpa only [RefreshingProof.average_const] using h

section RetainedFrames
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

/-- Strictly retained positive-threshold directions have positive eigenvalue. -/
theorem retained_eigenvalue_pos (F : Table X Y) {beta : ℝ} (hbeta : 0 < beta)
    (j : Y) (hj : j ∈ retainedDirections F beta) : 0 < rightEigenvalue F j := by
  have hp : 0 < normalizedSingularCoefficient F j :=
    lt_trans hbeta (Finset.mem_filter.mp hj).2
  by_contra hn
  have hz : rightEigenvalue F j = 0 := le_antisymm (le_of_not_gt hn) (rightEigenvalue_nonneg F j)
  simp only [normalizedSingularCoefficient, hz, Real.sqrt_zero, zero_div, lt_self_iff_false] at hp

/-- Actual retained left singular functions are jointly orthonormal. -/
theorem normalizedLeftFunction_retained_inner [Nonempty X]
    (F : Table X Y) {beta : ℝ} (hbeta : 0 < beta) (i j : Y)
    (hi : i ∈ retainedDirections F beta) (hj : j ∈ retainedDirections F beta) :
    average (fun x => normalizedLeftFunction F i x * normalizedLeftFunction F j x) =
      if i = j then 1 else 0 := by
  simpa only [Subtype.mk.injEq] using normalizedLeftFunction_orthonormal F
    (⟨i, retained_eigenvalue_pos F hbeta i hi⟩ : PositiveDirection F)
    ⟨j, retained_eigenvalue_pos F hbeta j hj⟩

/-- Unit-function frame energy, rather than the balanced-factor energy. -/
def leftUnitFrameEnergy (F : Table X Y) (beta : ℝ) (x : X) : ℝ :=
  ∑ j ∈ retainedDirections F beta, normalizedLeftFunction F j x ^ 2

/-- The pointwise sum of squared normalized right singular functions retained at threshold β. -/
def rightUnitFrameEnergy (F : Table X Y) (beta : ℝ) (y : Y) : ℝ :=
  ∑ j ∈ retainedDirections F beta, normalizedRightFunction F j y ^ 2

/-- Actual pointwise left-frame energy bound from the row contraction. -/
theorem leftUnitFrameEnergy_le [Nonempty X] [Nonempty Y]
    (F : Table X Y) {beta : ℝ} (hbeta : 0 < beta) (x : X)
    (hrow : average (fun y => F x y ^ 2) ≤ 1) :
    leftUnitFrameEnergy F beta x ≤ 1 / beta ^ 2 := by
  apply retained_unweighted_energy _ _ _ hbeta
  · intro j hj
    exact le_of_lt ((Finset.mem_filter.mp hj).2)
  · rw [normalized_retained_row_sq]
    exact (spectralTruncation_row_average_sq_le F beta x).trans hrow

/-- Actual pointwise right-frame energy bound from the column contraction. -/
theorem rightUnitFrameEnergy_le [Nonempty X] [Nonempty Y]
    (F : Table X Y) {beta : ℝ} (hbeta : 0 < beta) (y : Y)
    (hcolumn : average (fun x => F x y ^ 2) ≤ 1) :
    rightUnitFrameEnergy F beta y ≤ 1 / beta ^ 2 := by
  apply retained_unweighted_energy _ _ _ hbeta
  · intro j hj
    exact le_of_lt ((Finset.mem_filter.mp hj).2)
  · rw [normalized_retained_column_sq]
    exact (spectralTruncation_column_average_sq_le F beta y).trans hcolumn

/-- The mean actual left-frame energy is exactly the number of retained directions. -/
theorem leftUnitFrameEnergy_average [Nonempty X]
    (F : Table X Y) {beta : ℝ} (hbeta : 0 < beta) :
    average (leftUnitFrameEnergy F beta) = (retainedDirections F beta).card := by
  unfold leftUnitFrameEnergy
  rw [average_sum]
  calc
    _ = ∑ j ∈ retainedDirections F beta, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hu := normalizedLeftFunction_retained_inner F hbeta j j hj hj
      simpa only [ite_true, ← pow_two] using hu
    _ = _ := by simp

/-- The right-frame mean energy has the same exact value. -/
theorem rightUnitFrameEnergy_average [Nonempty Y] (F : Table X Y) (beta : ℝ) :
    average (rightUnitFrameEnergy F beta) = (retainedDirections F beta).card := by
  unfold rightUnitFrameEnergy
  rw [average_sum]
  calc
    _ = ∑ j ∈ retainedDirections F beta, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hu := normalizedRightFunction_orthonormal F j j
      simpa only [ite_true, ← pow_two] using hu
    _ = _ := by simp

/-- Left-frame second moment needed by the actual Gram-variance estimate. -/
theorem leftUnitFrameEnergy_secondMoment [Nonempty X] [Nonempty Y]
    (F : Table X Y) {beta : ℝ} (hbeta : 0 < beta)
    (hrow : ∀ x, average (fun y => F x y ^ 2) ≤ 1) :
    average (fun x => leftUnitFrameEnergy F beta x ^ 2) ≤
      (retainedDirections F beta).card / beta ^ 2 := by
  have hp (x : X) : leftUnitFrameEnergy F beta x ^ 2 ≤
      (1 / beta ^ 2) * leftUnitFrameEnergy F beta x := by
    have he := leftUnitFrameEnergy_le F hbeta x (hrow x)
    have hn : 0 ≤ leftUnitFrameEnergy F beta x := Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith
  have h := average_mono hp
  rw [average_smul, leftUnitFrameEnergy_average F hbeta] at h
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using h

/-- Right-frame second moment, using actual column contraction. -/
theorem rightUnitFrameEnergy_secondMoment [Nonempty X] [Nonempty Y]
    (F : Table X Y) {beta : ℝ} (hbeta : 0 < beta)
    (hcolumn : ∀ y, average (fun x => F x y ^ 2) ≤ 1) :
    average (fun y => rightUnitFrameEnergy F beta y ^ 2) ≤
      (retainedDirections F beta).card / beta ^ 2 := by
  have hp (y : Y) : rightUnitFrameEnergy F beta y ^ 2 ≤
      (1 / beta ^ 2) * rightUnitFrameEnergy F beta y := by
    have he := rightUnitFrameEnergy_le F hbeta y (hcolumn y)
    have hn : 0 ≤ rightUnitFrameEnergy F beta y := Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith
  have h := average_mono hp
  rw [average_smul, rightUnitFrameEnergy_average] at h
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using h

/-- Retaining coefficients strictly above beta bounds the retained count by nuclear norm divided by beta. -/
theorem retained_count_mul_threshold_le (F : Table X Y) (beta : ℝ) :
    ((retainedDirections F beta).card : ℝ) * beta ≤ truncatedNuclearNorm F beta := by
  unfold truncatedNuclearNorm
  calc
    _ = ∑ j ∈ retainedDirections F beta, beta := by simp
    _ ≤ _ := Finset.sum_le_sum fun j hj => le_of_lt ((Finset.mem_filter.mp hj).2)


/-- The unit singular witness for the retained family. -/
def unitSpectralWitness (F : Table X Y) (beta : ℝ) : Table X Y :=
  fun x y => ∑ j ∈ retainedDirections F beta,
    normalizedLeftFunction F j x * normalizedRightFunction F j y

omit [DecidableEq Y] in
/-- Pairing commutes with finite sums in its second table argument. -/
theorem pairing_sum_right {ι : Type*} (I : Finset ι) (F : Table X Y) (G : ι → Table X Y) :
    pairing F (fun x y => ∑ j ∈ I, G j x y) = ∑ j ∈ I, pairing F (G j) := by
  unfold pairing
  simp only [Finset.mul_sum, average_sum]

/-- Actual singular duality: the retained unit witness extracts exactly the actual truncated nuclear norm. -/
theorem pairing_unitSpectralWitness_eq_nuclear [Nonempty X] [Nonempty Y]
    (F : Table X Y) {beta : ℝ} (hbeta : 0 < beta) :
    pairing F (unitSpectralWitness F beta) = truncatedNuclearNorm F beta := by
  unfold unitSpectralWitness truncatedNuclearNorm
  rw [pairing_sum_right]
  exact Finset.sum_congr rfl fun j hj =>
    pairing_singular_functions F j (retained_eigenvalue_pos F hbeta j hj)

/-- Cauchy--Schwarz controls the unit witness using its actual unit-frame energies. -/
theorem unitSpectralWitness_entry_sq_le (F : Table X Y) (beta : ℝ) (x : X) (y : Y) :
    unitSpectralWitness F beta x y ^ 2 ≤ leftUnitFrameEnergy F beta x * rightUnitFrameEnergy F beta y :=
  Finset.sum_mul_sq_le_sq_mul_sq (retainedDirections F beta)
    (fun j => normalizedLeftFunction F j x) (fun j => normalizedRightFunction F j y)

/-- The actual unit singular witness has max norm at most beta^-2. -/
theorem unitSpectralWitness_entry_abs_le [Nonempty X] [Nonempty Y]
    (F : Table X Y) {beta : ℝ} (hbeta : 0 < beta) (x : X) (y : Y)
    (hrow : average (fun z => F x z ^ 2) ≤ 1)
    (hcolumn : average (fun z => F z y ^ 2) ≤ 1) :
    |unitSpectralWitness F beta x y| ≤ 1 / beta ^ 2 := by
  have hL := leftUnitFrameEnergy_le F hbeta x hrow
  have hR := rightUnitFrameEnergy_le F hbeta y hcolumn
  have hR0 : 0 ≤ rightUnitFrameEnergy F beta y := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB0 : 0 ≤ 1 / beta ^ 2 := by positivity
  have hm := mul_le_mul hL hR hR0 hB0
  have hs := (unitSpectralWitness_entry_sq_le F beta x y).trans hm
  apply (sq_le_sq₀ (abs_nonneg _) hB0).mp
  rw [sq_abs]
  simpa only [pow_two] using hs

end RetainedFrames

/-- Independent means can move the matrix coin before the two share coins. -/
theorem average_third_first {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) :
    average (fun a => average (fun b => average (fun c => f a b c))) =
      average (fun c => average (fun a => average (fun b => f a b c))) := by
  calc
    _ = average (fun a => average (fun c => average (fun b => f a b c))) := by
      apply average_congr
      intro a
      exact average_comm _
    _ = _ := average_comm _

/-- The actual retained witness coefficients for the left local mask. -/
def leftWitnessCoefficient {n leakage : ℕ} (f : LeakageQuery n leakage) (z : Answer leakage)
    (M : RefreshMatrix n) (j : Share n × Share n) : ℝ :=
  average (fun l => leftAnswerMask f z l M *
    normalizedLeftFunction (groupedAnswerTable f z) j (l, refreshLeft l M))

/-- The correlation of the right answer mask with one retained right singular function along a fixed refresh matrix. -/
def rightWitnessCoefficient {n leakage : ℕ} (f : LeakageQuery n leakage) (z : Answer leakage)
    (M : RefreshMatrix n) (j : Share n × Share n) : ℝ :=
  average (fun r => rightAnswerMask f z r M *
    normalizedRightFunction (groupedAnswerTable f z) j (r, refreshRight r M))

/-- The fixed-matrix local mask pairing with the actual retained unit witness is the Euclidean dot product of the two actual mask coefficient vectors. -/
theorem mask_unitWitness_pairing_at_matrix {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) (M : RefreshMatrix n) :
    average (fun l => average (fun r => leftAnswerMask f z l M * rightAnswerMask f z r M *
      unitSpectralWitness (groupedAnswerTable f z) beta (l, refreshLeft l M) (r, refreshRight r M))) =
      ∑ j ∈ retainedDirections (groupedAnswerTable f z) beta,
        leftWitnessCoefficient f z M j * rightWitnessCoefficient f z M j := by
  unfold unitSpectralWitness
  simp only [Finset.mul_sum, average_sum]
  apply Finset.sum_congr rfl
  intro j hj
  unfold leftWitnessCoefficient rightWitnessCoefficient
  rw [average_mul_average]
  apply average_congr
  intro l
  apply average_congr
  intro r
  ring

/-- Exact actual nuclear-witness identity before the fiber weights are replaced by one half in the paper's bootstrap. -/
theorem actual_nuclear_witness_mask_identity {n leakage : ℕ} [Nonempty (Share n)]
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ} (hbeta : 0 < beta) :
    truncatedNuclearNorm (groupedAnswerTable f z) beta =
      average (fun l : Share n => average (fun r : Share n =>
        average (fun M : RefreshMatrix n =>
          secretFiberWeight n (secret (l, r)) * leftAnswerMask f z l M * rightAnswerMask f z r M *
            unitSpectralWitness (groupedAnswerTable f z) beta (l, refreshLeft l M) (r, refreshRight r M)))) := by
  rw [← pairing_unitSpectralWitness_eq_nuclear (groupedAnswerTable f z) hbeta]
  exact groupedAnswerTable_mask_pairing _ _ _

/-- A bounded function on a nonempty finite probability space has squared norm≤1. -/
theorem average_sq_le_one {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (hf : ∀ a, |f a| ≤ 1) : average (fun a => f a ^ 2) ≤ 1 := by
  have h := average_mono (fun a => (sq_le_sq₀ (abs_nonneg (f a)) (by norm_num : (0 : ℝ) ≤ 1)).mpr (hf a))
  simpa only [sq_abs, one_pow, RefreshingProof.average_const] using h

/-- Actual kernel rows satisfy the input norm bound used by the spectral energy estimates. -/
theorem groupedAnswerTable_row_average_sq_le_one {n leakage : ℕ} [Nonempty (Share n)]
    (f : LeakageQuery n leakage) (z : Answer leakage) (ll : Share n × Share n) :
    average (fun rr => groupedAnswerTable f z ll rr ^ 2) ≤ 1 :=
  average_sq_le_one _ (groupedAnswerTable_abs_le_one f z ll)

/-- Every column of the grouped answer table has uniform mean squared magnitude at most one. -/
theorem groupedAnswerTable_column_average_sq_le_one {n leakage : ℕ} [Nonempty (Share n)]
    (f : LeakageQuery n leakage) (z : Answer leakage) (rr : Share n × Share n) :
    average (fun ll => groupedAnswerTable f z ll rr ^ 2) ≤ 1 :=
  average_sq_le_one _ (fun ll => groupedAnswerTable_abs_le_one f z ll rr)

/-- The actual retained index type, including the possible empty family. -/
abbrev ActualRetainedDirection {n leakage : ℕ} (f : LeakageQuery n leakage)
    (z : Answer leakage) (beta : ℝ) :=
  {j : Share n × Share n // j ∈ retainedDirections (groupedAnswerTable f z) beta}

/-- The retained normalized left singular functions, indexed by actual retained directions and split into old and new shares. -/
def actualLeftUnitFrame {n leakage : ℕ} (f : LeakageQuery n leakage) (z : Answer leakage)
    (beta : ℝ) (j : ActualRetainedDirection f z beta) (l l' : Share n) : ℝ :=
  normalizedLeftFunction (groupedAnswerTable f z) j.val (l, l')

/-- The retained normalized right singular functions, indexed by actual retained directions and split into old and new shares. -/
def actualRightUnitFrame {n leakage : ℕ} (f : LeakageQuery n leakage) (z : Answer leakage)
    (beta : ℝ) (j : ActualRetainedDirection f z beta) (r r' : Share n) : ℝ :=
  normalizedRightFunction (groupedAnswerTable f z) j.val (r, r')

/-- Summing over the retained-direction subtype equals summing over its defining finite set. -/
theorem sum_actualRetainedDirection {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) (a : Share n × Share n → ℝ) :
    (∑ j : ActualRetainedDirection f z beta, a j.val) =
      ∑ j ∈ retainedDirections (groupedAnswerTable f z) beta, a j :=
  (Finset.sum_subtype _ (fun _ => Iff.rfl) _).symm

/-- For β > 0, the actual retained left singular functions are orthonormal under the uniform two-share average. -/
theorem actualLeftUnitFrame_orthonormal {n leakage : ℕ} [Nonempty (Share n)]
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ} (hbeta : 0 < beta)
    (i j : ActualRetainedDirection f z beta) :
    average (fun l => average (fun l' => actualLeftUnitFrame f z beta i l l' *
      actualLeftUnitFrame f z beta j l l')) = if i = j then 1 else 0 := by
  have h := normalizedLeftFunction_retained_inner (groupedAnswerTable f z) hbeta
    i.val j.val i.property j.property
  rw [average_product] at h
  simpa only [actualLeftUnitFrame, Subtype.val_inj] using h

/-- The actual retained right singular functions are orthonormal under the uniform two-share average. -/
theorem actualRightUnitFrame_orthonormal {n leakage : ℕ} [Nonempty (Share n)]
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ)
    (i j : ActualRetainedDirection f z beta) :
    average (fun r => average (fun r' => actualRightUnitFrame f z beta i r r' *
      actualRightUnitFrame f z beta j r r')) = if i = j then 1 else 0 := by
  have h := normalizedRightFunction_orthonormal (groupedAnswerTable f z) i.val j.val
  rw [average_product] at h
  simpa only [actualRightUnitFrame, Subtype.val_inj] using h

/-- The pointwise energy of the retained left unit frame is at most 1/β². -/
theorem actualLeftUnitFrame_energy_le {n leakage : ℕ} [Nonempty (Share n)]
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ} (hbeta : 0 < beta)
    (l l' : Share n) :
    (∑ j : ActualRetainedDirection f z beta, actualLeftUnitFrame f z beta j l l' ^ 2) ≤ 1 / beta ^ 2 := by
  change (∑ j : ActualRetainedDirection f z beta,
    normalizedLeftFunction (groupedAnswerTable f z) j.val (l, l') ^ 2) ≤ _
  rw [sum_actualRetainedDirection f z beta (fun j => normalizedLeftFunction (groupedAnswerTable f z) j (l, l') ^ 2)]
  exact leftUnitFrameEnergy_le _ hbeta _ (groupedAnswerTable_row_average_sq_le_one f z _)

/-- The pointwise energy of the retained right unit frame is at most 1/β². -/
theorem actualRightUnitFrame_energy_le {n leakage : ℕ} [Nonempty (Share n)]
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ} (hbeta : 0 < beta)
    (r r' : Share n) :
    (∑ j : ActualRetainedDirection f z beta, actualRightUnitFrame f z beta j r r' ^ 2) ≤ 1 / beta ^ 2 := by
  change (∑ j : ActualRetainedDirection f z beta,
    normalizedRightFunction (groupedAnswerTable f z) j.val (r, r') ^ 2) ≤ _
  rw [sum_actualRetainedDirection f z beta (fun j => normalizedRightFunction (groupedAnswerTable f z) j (r, r') ^ 2)]
  exact rightUnitFrameEnergy_le _ hbeta _ (groupedAnswerTable_column_average_sq_le_one f z _)

/-- Inversion is a bijection of the actual uniform matrix coin space. -/
def inverseRefreshMatrixEquiv (n : ℕ) : RefreshMatrix n ≃ RefreshMatrix n where
  toFun := Inv.inv
  invFun := Inv.inv
  left_inv := inv_inv
  right_inv := inv_inv

/-- The exact Frobenius Gram bound for the actual retained family. -/
def actualGramBound {n leakage : ℕ} (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) : ℝ :=
  ((retainedDirections (groupedAnswerTable f z) beta).card : ℝ) / (((q n : ℝ) - 1) * beta ^ 2)

set_option maxHeartbeats 1000000 in
/-- The mean squared Gram deviation of the left frame along uniform refresh matrices satisfies the actual Gram bound. -/
theorem actualLeftGram_deviation_sq_le {n leakage : ℕ} [Nonempty (Share n)]
    (hn : 2 ≤ n) (f : LeakageQuery n leakage) (z : Answer leakage)
    {beta : ℝ} (hbeta : 0 < beta) :
    average (fun M : RefreshMatrix n => frameDeviation
      (fun (j : ActualRetainedDirection f z beta) (l : Share n) =>
        actualLeftUnitFrame f z beta j l (refreshLeft l M)) ^ 2) ≤ actualGramBound f z beta := by
  have hcard : 2 ≤ Fintype.card (Share n) := by
    have hr : (2 : ℝ) ≤ (Fintype.card (Share n) : ℝ) := by
      rw [card_share]
      have := q_real_three_le hn
      linarith
    exact_mod_cast hr
  have h := matrix_frame_deviation_sq_le_of_energy (I := Fin n) (J := ActualRetainedDirection f z beta) hcard (actualLeftUnitFrame f z beta)
    transposeMatrixUnitEquiv (actualLeftUnitFrame_orthonormal f z hbeta)
    (actualLeftUnitFrame_energy_le f z hbeta)
  have haction (M : RefreshMatrix n) (l : Share n) :
      matrixUnitNonzeroApply (transposeMatrixUnitEquiv M) l = refreshLeft l M := by
    apply Subtype.ext
    exact transposeMatrixUnitEquiv_action M l
  change average (fun M : RefreshMatrix n => frameDeviation
    (fun (j : ActualRetainedDirection f z beta) (l : Share n) => actualLeftUnitFrame f z beta j l
      (matrixUnitNonzeroApply (transposeMatrixUnitEquiv M) l)) ^ 2) ≤
        (1 / beta ^ 2) * (Fintype.card (ActualRetainedDirection f z beta) : ℝ) /
          ((Fintype.card (Share n) : ℝ) - 1) at h
  simp_rw [haction] at h
  simpa only [actualGramBound, Fintype.card_coe, card_share,
    one_div, div_eq_mul_inv, mul_inv, mul_assoc, mul_left_comm, mul_comm, mul_one] using h

/-- The mean squared Gram deviation of the right frame along uniform refresh matrices satisfies the actual Gram bound. -/
theorem actualRightGram_deviation_sq_le {n leakage : ℕ} [Nonempty (Share n)]
    (hn : 2 ≤ n) (f : LeakageQuery n leakage) (z : Answer leakage)
    {beta : ℝ} (hbeta : 0 < beta) :
    average (fun M : RefreshMatrix n => frameDeviation
      (fun (j : ActualRetainedDirection f z beta) (r : Share n) =>
        actualRightUnitFrame f z beta j r (refreshRight r M)) ^ 2) ≤ actualGramBound f z beta := by
  have hcard : 2 ≤ Fintype.card (Share n) := by
    have hr : (2 : ℝ) ≤ (Fintype.card (Share n) : ℝ) := by
      rw [card_share]
      have := q_real_three_le hn
      linarith
    exact_mod_cast hr
  have h := matrix_frame_deviation_sq_le_of_energy (I := Fin n) (J := ActualRetainedDirection f z beta) hcard (actualRightUnitFrame f z beta)
    (inverseRefreshMatrixEquiv n) (actualRightUnitFrame_orthonormal f z beta)
    (actualRightUnitFrame_energy_le f z hbeta)
  have haction (M : RefreshMatrix n) (r : Share n) :
      matrixUnitNonzeroApply (inverseRefreshMatrixEquiv n M) r = refreshRight r M := by
    apply Subtype.ext
    rfl
  change average (fun M : RefreshMatrix n => frameDeviation
    (fun (j : ActualRetainedDirection f z beta) (r : Share n) => actualRightUnitFrame f z beta j r
      (matrixUnitNonzeroApply (inverseRefreshMatrixEquiv n M) r)) ^ 2) ≤
        (1 / beta ^ 2) * (Fintype.card (ActualRetainedDirection f z beta) : ℝ) /
          ((Fintype.card (Share n) : ℝ) - 1) at h
  simp_rw [haction] at h
  simpa only [actualGramBound, Fintype.card_coe, card_share,
    one_div, div_eq_mul_inv, mul_inv, mul_assoc, mul_left_comm, mul_comm, mul_one] using h

/-- The two actual mask coefficient frames have bounded averaged pairing even though they use the same matrix coin. -/
theorem actual_mask_unitWitness_pairing_le {n leakage : ℕ} [Nonempty (Share n)]
    (hn : 2 ≤ n) (f : LeakageQuery n leakage) (z : Answer leakage)
    {beta : ℝ} (hbeta : 0 < beta) :
    average (fun l => average (fun r => average (fun M : RefreshMatrix n =>
      leftAnswerMask f z l M * rightAnswerMask f z r M *
        unitSpectralWitness (groupedAnswerTable f z) beta (l, refreshLeft l M) (r, refreshRight r M)))) ≤
      1 + Real.sqrt (actualGramBound f z beta) := by
  have h := average_mask_pairing_le
    (fun (M : RefreshMatrix n) (j : ActualRetainedDirection f z beta) (l : Share n) =>
      actualLeftUnitFrame f z beta j l (refreshLeft l M))
    (fun (M : RefreshMatrix n) (j : ActualRetainedDirection f z beta) (r : Share n) =>
      actualRightUnitFrame f z beta j r (refreshRight r M))
    (fun M l => leftAnswerMask f z l M) (fun M r => rightAnswerMask f z r M)
    (leftAnswerMask_average_sq_le_one f z) (rightAnswerMask_average_sq_le_one f z)
    (actualLeftGram_deviation_sq_le hn f z hbeta) (actualRightGram_deviation_sq_le hn f z hbeta)
  change average (fun M : RefreshMatrix n => ∑ j : ActualRetainedDirection f z beta,
    leftWitnessCoefficient f z M j.val * rightWitnessCoefficient f z M j.val) ≤ _ at h
  have hsum (M : RefreshMatrix n) :
      (∑ j : ActualRetainedDirection f z beta,
        leftWitnessCoefficient f z M j.val * rightWitnessCoefficient f z M j.val) =
        ∑ j ∈ retainedDirections (groupedAnswerTable f z) beta,
          leftWitnessCoefficient f z M j * rightWitnessCoefficient f z M j :=
    sum_actualRetainedDirection f z beta (fun j => leftWitnessCoefficient f z M j * rightWitnessCoefficient f z M j)
  simp_rw [hsum] at h
  rw [average_third_first]
  simp_rw [mask_unitWitness_pairing_at_matrix f z beta]
  exact h

/-- Replacing the actual binary fiber weight by one half costs at most the max norm of the test table divided by q, after doubling the pairing. -/
theorem groupedAnswerTable_weight_replacement {n leakage : ℕ} [Nonempty (Share n)]
    (hn : 2 ≤ n) (f : LeakageQuery n leakage) (z : Answer leakage)
    (W : Table (Share n × Share n) (Share n × Share n)) {B : ℝ} (hB : 0 ≤ B)
    (hW : ∀ ll rr, |W ll rr| ≤ B) :
    2 * pairing (groupedAnswerTable f z) W ≤
      average (fun l => average (fun r => average (fun M : RefreshMatrix n =>
        leftAnswerMask f z l M * rightAnswerMask f z r M *
          W (l, refreshLeft l M) (r, refreshRight r M)))) + B / (q n : ℝ) := by
  let m : Share n → Share n → RefreshMatrix n → ℝ := fun l r M =>
    leftAnswerMask f z l M * rightAnswerMask f z r M * W (l, refreshLeft l M) (r, refreshRight r M)
  have hq : 0 < (q n : ℝ) := by have := q_real_three_le hn; linarith
  have hpoint (l r : Share n) (M : RefreshMatrix n) :
      (2 * secretFiberWeight n (secret (l, r)) - 1) * m l r M ≤ B / (q n : ℝ) := by
    by_cases hL : f.1 l M = z.1
    · by_cases hR : f.2 r M = z.2
      · simp only [m, leftAnswerMask, rightAnswerMask, hL, hR, ite_true, one_mul]
        calc
          _ ≤ |(2 * secretFiberWeight n (secret (l, r)) - 1) *
              W (l, refreshLeft l M) (r, refreshRight r M)| := le_abs_self _
          _ = (1 / (q n : ℝ)) * |W (l, refreshLeft l M) (r, refreshRight r M)| := by
            rw [abs_mul, secretFiberWeight_twice_centered_abs hn]
          _ ≤ (1 / (q n : ℝ)) * B := mul_le_mul_of_nonneg_left (hW _ _) (by positivity)
          _ = _ := by ring
      · simp only [m, leftAnswerMask, rightAnswerMask, hL, hR, ite_true, ite_false, mul_zero, zero_mul]
        positivity
    · simp only [m, leftAnswerMask, hL, ite_false, zero_mul, mul_zero]
      positivity
  have hav := average_mono (fun l => average_mono (fun r => average_mono (fun M => hpoint l r M)))
  simp only [RefreshingProof.average_const] at hav
  have hp : pairing (groupedAnswerTable f z) W = average (fun l => average (fun r =>
      average (fun M : RefreshMatrix n => secretFiberWeight n (secret (l, r)) * m l r M))) := by
    rw [groupedAnswerTable_mask_pairing]
    apply average_congr
    intro l
    apply average_congr
    intro r
    apply average_congr
    intro M
    dsimp [m]
    ring
  simp only [average_smul] at hp
  have hlinear : average (fun l => average (fun r => average (fun M : RefreshMatrix n =>
      (2 * secretFiberWeight n (secret (l, r)) - 1) * m l r M))) =
      2 * pairing (groupedAnswerTable f z) W -
        average (fun l => average (fun r => average (fun M : RefreshMatrix n => m l r M))) := by
    have heq (l r : Share n) (M : RefreshMatrix n) :
        (2 * secretFiberWeight n (secret (l, r)) - 1) * m l r M =
          2 * (secretFiberWeight n (secret (l, r)) * m l r M) - m l r M := by ring
    simp_rw [heq, average_sub, average_smul]
    rw [← hp]
  rw [hlinear] at hav
  change 2 * pairing (groupedAnswerTable f z) W ≤
    average (fun l => average (fun r => average (fun M : RefreshMatrix n => m l r M))) + B / (q n : ℝ)
  linarith

/-- The actual finite-dimensional nuclear bootstrap before the threshold inequalities are simplified. -/
theorem actual_nuclear_prebootstrap {n leakage : ℕ} [Nonempty (Share n)]
    (hn : 2 ≤ n) (f : LeakageQuery n leakage) (z : Answer leakage)
    {beta : ℝ} (hbeta : 0 < beta) :
    2 * truncatedNuclearNorm (groupedAnswerTable f z) beta ≤
      1 + Real.sqrt (actualGramBound f z beta) + (1 / beta ^ 2) / (q n : ℝ) := by
  have hw (ll rr : Share n × Share n) :
      |unitSpectralWitness (groupedAnswerTable f z) beta ll rr| ≤ 1 / beta ^ 2 :=
    unitSpectralWitness_entry_abs_le _ hbeta ll rr
      (groupedAnswerTable_row_average_sq_le_one f z ll)
      (groupedAnswerTable_column_average_sq_le_one f z rr)
  have h := groupedAnswerTable_weight_replacement hn f z
    (unitSpectralWitness (groupedAnswerTable f z) beta) (by positivity) hw
  rw [pairing_unitSpectralWitness_eq_nuclear _ hbeta] at h
  have hc := actual_mask_unitWitness_pairing_le hn f z hbeta
  linarith

/-- The retained count and the threshold condition control the actual Gram bound by twice the actual nuclear norm. -/
theorem actualGramBound_le_two_nuclear {n leakage : ℕ}
    (hn : 2 ≤ n) (f : LeakageQuery n leakage) (z : Answer leakage)
    {beta : ℝ} (hbeta : 0 < beta) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3) :
    actualGramBound f z beta ≤ 2 * truncatedNuclearNorm (groupedAnswerTable f z) beta := by
  let L := truncatedNuclearNorm (groupedAnswerTable f z) beta
  let N : ℝ := (retainedDirections (groupedAnswerTable f z) beta).card
  let D : ℝ := ((q n : ℝ) - 1) * beta ^ 2
  have hq := q_real_three_le hn
  have hD : 0 < D := mul_pos (by linarith) (sq_pos_of_pos hbeta)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hc : N * beta ≤ L := retained_count_mul_threshold_le _ _
  have hf : 1 ≤ 2 * ((q n : ℝ) - 1) * beta ^ 3 := by
    have hp := mul_nonneg (by linarith : 0 ≤ (q n : ℝ) - 2) (le_of_lt (pow_pos hbeta 3))
    nlinarith
  have hscaled : N ≤ (2 * L) * D := by
    calc
      N = N * 1 := by ring
      _ ≤ N * (2 * ((q n : ℝ) - 1) * beta ^ 3) := mul_le_mul_of_nonneg_left hf hN
      _ = (N * beta) * (2 * D) := by dsimp [D]; ring
      _ ≤ L * (2 * D) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (2 * L) * D := by ring
  exact (div_le_iff₀ hD).mpr hscaled

/-- The spectral truncation of the actual refreshing answer table has nuclear norm at most two throughout the paper's threshold range. -/
theorem actual_answer_nuclear_le_two {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage)
    {beta : ℝ} (hbeta : 0 < beta) (hbeta1 : beta ≤ 1)
    (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3) :
    truncatedNuclearNorm (groupedAnswerTable f z) beta ≤ 2 := by
  let : Nonempty (Share n) := share_nonempty_of_two_le hn
  have hq : 0 < (q n : ℝ) := by have := q_real_three_le hn; linarith
  have hL : 0 ≤ truncatedNuclearNorm (groupedAnswerTable f z) beta :=
    Finset.sum_nonneg (fun j _ => normalizedSingularCoefficient_nonneg _ j)
  have hG := actualGramBound_le_two_nuclear hn f z hbeta hthreshold
  have herr : (1 / beta ^ 2) / (q n : ℝ) ≤ 1 := by
    have hp := mul_le_mul_of_nonneg_left hbeta1 (mul_nonneg (le_of_lt hq) (sq_nonneg beta))
    have hh : 1 ≤ beta ^ 2 * (q n : ℝ) := by nlinarith
    rw [div_div]
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hbeta) hq)).mpr
    simpa only [one_mul] using hh
  apply nuclear_bootstrap hL
  calc
    _ ≤ 1 + Real.sqrt (actualGramBound f z beta) + (1 / beta ^ 2) / (q n : ℝ) :=
      actual_nuclear_prebootstrap hn f z hbeta
    _ ≤ 1 + Real.sqrt (2 * truncatedNuclearNorm (groupedAnswerTable f z) beta) + 1 :=
      add_le_add (add_le_add le_rfl (Real.sqrt_le_sqrt hG)) herr
    _ = _ := by ring

end RefreshingProof.Local
