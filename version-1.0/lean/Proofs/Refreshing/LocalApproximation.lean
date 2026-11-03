import Proofs.Refreshing.ResidualBootstrap

/-!
# Lifting the actual local approximation to fixed-secret encoding distributions

The density bound is proved from actual encoding counts. The matrix-refresh marginals are proved from actual freshness and uniform single-vector images.
-/

noncomputable section
open scoped BigOperators Matrix ENNReal

namespace RefreshingProof.Local
open Refreshing

/-- Each binary secret fiber has probability at least one third under independent uniform nonzero shares. -/
theorem secretFiberWeight_one_third_le {n : ℕ} (hn : 2 ≤ n) (s : Bit) :
    (1 / 3 : ℝ) ≤ secretFiberWeight n s := by
  have hq := q_real_three_le hn
  have hq0 : 0 < (q n : ℝ) := by linarith
  rcases Binary.bit_cases s with hs | hs
  · subst s
    rw [(secretFiberWeight_binary hn).1]
    apply (le_div_iff₀ (by positivity : 0 < 2 * (q n : ℝ))).mpr
    linarith
  · subst s
    rw [(secretFiberWeight_binary hn).2]
    apply (le_div_iff₀ (by positivity : 0 < 2 * (q n : ℝ))).mpr
    linarith

/-- Actual pointwise density of μ_s relative to the independent-share distribution is at most three. -/
theorem initialDistribution_real_le_three_uniform {n : ℕ} (hn : 2 ≤ n) (s : Bit) (x : State n) :
    (initialDistribution hn s x).toReal ≤ 3 * (Fintype.card (State n) : ℝ)⁻¹ := by
  classical
  let : Nonempty (Share n) := share_nonempty_of_two_le hn
  let : Nonempty (Encoding n s) := encoding_nonempty hn s
  have hstate : 0 < (Fintype.card (State n) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hfiber : 0 < (Fintype.card (Encoding n s) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hp := secretFiberWeight_one_third_le hn s
  unfold secretFiberWeight at hp
  have hcard : (Fintype.card (State n) : ℝ) ≤ 3 * (Fintype.card (Encoding n s) : ℝ) := by
    have h := (le_div_iff₀ hstate).mp hp
    linarith
  rw [initialDistribution_apply]
  by_cases hx : secret x = s
  · rw [ite_eq_left hx, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    have hr : (1 : ℝ) / (Fintype.card (Encoding n s) : ℝ) ≤
        3 / (Fintype.card (State n) : ℝ) :=
      (div_le_div_iff₀ hfiber hstate).mpr (by simpa only [one_mul] using hcard)
    simpa only [one_div, div_eq_mul_inv, one_mul] using hr
  · rw [ite_eq_right hx, ENNReal.toReal_zero]
    positivity

/-- Actual initial-distribution expectation is at most three times the uniform expectation for every nonnegative table. -/
theorem initialTableMean_le_three_average {n : ℕ} (hn : 2 ≤ n) (s : Bit)
    (H : State n → ℝ) (hH : ∀ x, 0 ≤ H x) :
    initialTableMean hn s H ≤ 3 * average H := by
  unfold initialTableMean
  calc
    _ ≤ ∑ x : State n, (3 * (Fintype.card (State n) : ℝ)⁻¹) * H x :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right
        (initialDistribution_real_le_three_uniform hn s x) (hH x)
    _ = _ := by unfold average; rw [← Finset.mul_sum]; ring

/-- Two independent actual initial-state samples with possibly different secrets. -/
def initialProductMean {n : ℕ} (hn : 2 ≤ n) (s t : Bit) (H : State n → State n → ℝ) : ℝ :=
  initialTableMean hn s (fun x => initialTableMean hn t (H x))

/-- Pointwise inequalities are preserved by the initial secret-fiber expectation. -/
theorem initialTableMean_mono {n : ℕ} (hn : 2 ≤ n) (s : Bit)
    {H K : State n → ℝ} (h : ∀ x, H x ≤ K x) :
    initialTableMean hn s H ≤ initialTableMean hn s K :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) ENNReal.toReal_nonneg

/-- A real scalar factors out of the initial secret-fiber expectation. -/
theorem initialTableMean_smul {n : ℕ} (hn : 2 ≤ n) (s : Bit) (c : ℝ) (H : State n → ℝ) :
    initialTableMean hn s (fun x => c * H x) = c * initialTableMean hn s H := by
  unfold initialTableMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- Product density at most nine, proved from the two actual pointwise density bounds. -/
theorem initialProductMean_le_nine_average {n : ℕ} (hn : 2 ≤ n) (s t : Bit)
    (H : State n → State n → ℝ) (hH : ∀ x y, 0 ≤ H x y) :
    initialProductMean hn s t H ≤ 9 * average (fun x => average (H x)) := by
  unfold initialProductMean
  calc
    _ ≤ initialTableMean hn s (fun x => 3 * average (H x)) :=
      initialTableMean_mono hn s fun x => initialTableMean_le_three_average hn t (H x) (hH x)
    _ = 3 * initialTableMean hn s (fun x => average (H x)) := initialTableMean_smul _ _ _ _
    _ ≤ 3 * (3 * average (fun x => average (H x))) :=
      mul_le_mul_of_nonneg_left
        (initialTableMean_le_three_average hn s _ (fun x => average_nonneg (hH x))) (by norm_num)
    _ = _ := by ring

/-- Grouping four independent shares as two states is a permutation of the same four uniform coordinates. -/
theorem grouped_average_states {n : ℕ} (H : Table (State n) (State n)) :
    average (fun x : State n => average (fun y : State n => H (x.1, y.1) (x.2, y.2))) =
      average (fun ll : State n => average (fun rr : State n => H ll rr)) := by
  simp only [average_product]
  apply average_congr
  intro l
  exact average_comm _

/-- The actual fixed-secret product distribution has squared-table density at most nine relative to the grouped uniform reference measure. -/
theorem initialProductMean_grouped_sq_le {n : ℕ} (hn : 2 ≤ n) (s t : Bit)
    (H : Table (State n) (State n)) :
    initialProductMean hn s t (fun x y => H (x.1, y.1) (x.2, y.2) ^ 2) ≤ 9 * normSq H := by
  have h := initialProductMean_le_nine_average hn s t
    (fun x y => H (x.1, y.1) (x.2, y.2) ^ 2) (fun _ _ => sq_nonneg _)
  rw [grouped_average_states (fun ll rr => H ll rr ^ 2)] at h
  simpa only [normSq, pairing, pow_two] using h

/-- A uniform actual matrix refresh sends every fixed nonzero left share to a uniform nonzero left share, via transposition of the matrix coins. -/
theorem refreshLeft_distribution {n : ℕ} [Nonempty (Share n)] (l : Share n) :
    (matrixDistribution n).map (refreshLeft l) = uniformPMF (Share n) := by
  have he : refreshLeft l = fun M => matrixUnitNonzeroApply (transposeMatrixUnitEquiv M) l := by
    funext M
    apply Subtype.ext
    exact (transposeMatrixUnitEquiv_action M l).symm
  rw [he]
  calc
    _ = ((uniformPMF (RefreshMatrix n)).map transposeMatrixUnitEquiv).map
        (fun M => matrixUnitNonzeroApply M l) := (PMF.map_comp _ _ _).symm
    _ = _ := by rw [uniformPMF_map_equiv, uniform_matrixUnit_nonzero]

/-- The actual right refresh marginal is uniform, using uniform inverse coins. -/
theorem refreshRight_distribution {n : ℕ} [Nonempty (Share n)] (r : Share n) :
    (matrixDistribution n).map (refreshRight r) = uniformPMF (Share n) :=
  uniform_inverse_matrixUnit_nonzero r

/-- Actual μ_s has exactly uniform left-share marginal for every secret. -/
theorem initialDistribution_left_marginal {n : ℕ} [Nonempty (Share n)] (hn : 2 ≤ n) (s : Bit) :
    (initialDistribution hn s).map Prod.fst = uniformPMF (Share n) := by
  let : Nonempty (Share n) := share_nonempty_of_two_le hn
  obtain ⟨x⟩ := encoding_nonempty hn s
  have h := refresh_distribution_eq_initial hn x.val
  rw [x.property] at h
  have hm := congrArg (fun p : PMF (State n) => p.map Prod.fst) h
  have he : (initialDistribution hn s).map Prod.fst =
      (matrixDistribution n).map (refreshLeft x.val.1) := by
    simpa only [PMF.map_comp, Function.comp_def, refresh] using hm.symm
  rw [he, refreshLeft_distribution]

/-- Actual μ_s has exactly uniform right-share marginal as well. -/
theorem initialDistribution_right_marginal {n : ℕ} [Nonempty (Share n)] (hn : 2 ≤ n) (s : Bit) :
    (initialDistribution hn s).map Prod.snd = uniformPMF (Share n) := by
  let : Nonempty (Share n) := share_nonempty_of_two_le hn
  obtain ⟨x⟩ := encoding_nonempty hn s
  have h := refresh_distribution_eq_initial hn x.val
  rw [x.property] at h
  have hm := congrArg (fun p : PMF (State n) => p.map Prod.snd) h
  have he : (initialDistribution hn s).map Prod.snd =
      (matrixDistribution n).map (refreshRight x.val.2) := by
    simpa only [PMF.map_comp, Function.comp_def, refresh] using hm.symm
  rw [he, refreshRight_distribution]

/-- Uniform left marginal, in the real expectation convention used by the hybrids. -/
theorem initialTableMean_left_share {n : ℕ} (hn : 2 ≤ n) (s : Bit) (H : Share n → ℝ) :
    initialTableMean hn s (fun x => H x.1) = average H := by
  let : Nonempty (Share n) := share_nonempty_of_two_le hn
  rw [initialTableMean, ← pmf_expectation_map (initialDistribution hn s) Prod.fst H,
    initialDistribution_left_marginal hn s, uniformPMF_expectation]

/-- The right-share marginal of the initial secret-fiber distribution is the uniform nonzero-share distribution. -/
theorem initialTableMean_right_share {n : ℕ} (hn : 2 ≤ n) (s : Bit) (H : Share n → ℝ) :
    initialTableMean hn s (fun x => H x.2) = average H := by
  let : Nonempty (Share n) := share_nonempty_of_two_le hn
  rw [initialTableMean, ← pmf_expectation_map (initialDistribution hn s) Prod.snd H,
    initialDistribution_right_marginal hn s, uniformPMF_expectation]

/-- The actual initial PMF mean equals the uniform mean on its actual encoding fiber. -/
theorem initialTableMean_encoding_average {n : ℕ} (hn : 2 ≤ n) (s : Bit) (H : State n → ℝ) :
    initialTableMean hn s H = average (fun x : Encoding n s => H x.val) := by
  let : Nonempty (Encoding n s) := encoding_nonempty hn s
  have he : initialDistribution hn s = (uniformPMF (Encoding n s)).map Subtype.val := rfl
  unfold initialTableMean
  rw [he, pmf_expectation_map, uniformPMF_expectation]

/-- Product of the actual initial PMFs equals independent uniform sampling from the actual two encoding fibers. -/
theorem initialProductMean_encoding_average {n : ℕ} (hn : 2 ≤ n) (s t : Bit)
    (H : State n → State n → ℝ) :
    initialProductMean hn s t H =
      average (fun x : Encoding n s => average (fun y : Encoding n t => H x.val y.val)) := by
  unfold initialProductMean
  rw [initialTableMean_encoding_average]
  apply average_congr
  intro x
  exact initialTableMean_encoding_average hn t (H x.val)

/-- The paper's actual signed local approximation G=2P. -/
def localG {n leakage : ℕ} (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) :
    Table (State n) (State n) := fun ll rr => 2 * spectralTruncation (groupedAnswerTable f z) beta ll rr

/-- On same-secret states, the actual residual is exactly conditional answer probability minus the actual signed approximation. -/
theorem actualResidual_on_encoding_pair {n leakage : ℕ} {s : Bit}
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) (x y : Encoding n s) :
    actualResidual f z beta (x.val.1, y.val.1) (x.val.2, y.val.2) =
      (conditionalAnswer f x y z).toReal - localG f z beta (x.val.1, y.val.1) (x.val.2, y.val.2) := by
  have hc : sharePairsConsistent (x.val.1, y.val.1) (x.val.2, y.val.2) := by
    change secret x.val = secret y.val
    rw [x.property, y.property]
  unfold actualResidual
  rw [projection, ite_eq_left hc, groupedAnswerTable_eq_conditional f z x y]
  rfl

/-- Exact conditional-answer L₂ error under two independent encodings of the same secret, controlled by the actual reference residual norm. -/
theorem conditional_local_error_sq_le {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) (s : Bit) :
    average (fun x : Encoding n s => average (fun y : Encoding n s =>
      ((conditionalAnswer f x y z).toReal - localG f z beta (x.val.1, y.val.1) (x.val.2, y.val.2)) ^ 2)) ≤
      9 * normSq (actualResidual f z beta) := by
  have h := initialProductMean_grouped_sq_le hn s s (actualResidual f z beta)
  rw [initialProductMean_encoding_average] at h
  simpa only [actualResidual_on_encoding_pair] using h

/-- Root form of the actual conditional local error density lift. -/
theorem conditional_local_error_norm_le {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) (s : Bit) :
    Real.sqrt (average (fun x : Encoding n s => average (fun y : Encoding n s =>
      ((conditionalAnswer f x y z).toReal - localG f z beta (x.val.1, y.val.1) (x.val.2, y.val.2)) ^ 2))) ≤
      3 * Real.sqrt (normSq (actualResidual f z beta)) := by
  calc
    _ ≤ Real.sqrt (9 * normSq (actualResidual f z beta)) :=
      Real.sqrt_le_sqrt (conditional_local_error_sq_le hn f z beta s)
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)]; norm_num

/-- Actual reference L₂ norm of G is at most two. -/
theorem localG_normSq_le_four {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) : normSq (localG f z beta) ≤ 4 := by
  let : Nonempty (Share n) := share_nonempty_of_two_le hn
  let A := groupedAnswerTable f z
  let P := spectralTruncation A beta
  have hA : normSq A ≤ 1 := by
    have h := average_mono (groupedAnswerTable_row_average_sq_le_one f z)
    simpa only [normSq, pairing, ← pow_two, RefreshingProof.average_const] using h
  have hP : normSq P ≤ 1 := (spectralTruncation_normSq_le A beta).trans hA
  have he : normSq (localG f z beta) = 4 * normSq P := by
    unfold normSq pairing localG
    rw [← average_smul]
    apply average_congr
    intro ll
    rw [← average_smul]
    apply average_congr
    intro rr
    dsimp [P, A]
    ring
  rw [he]
  linarith

/-- Actual G has squared norm at most36 under every pair of endpoint labels. -/
theorem localG_encoding_sq_le_thirtySix {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) (s t : Bit) :
    average (fun x : Encoding n s => average (fun y : Encoding n t =>
      localG f z beta (x.val.1, y.val.1) (x.val.2, y.val.2) ^ 2)) ≤ 36 := by
  have h := initialProductMean_grouped_sq_le hn s t (localG f z beta)
  rw [initialProductMean_encoding_average] at h
  have hg := localG_normSq_le_four hn f z beta
  linarith

/-- The paper's actual G L₂ bound of six, for both valid and cheating endpoint labels. -/
theorem localG_encoding_norm_le_six {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) (s t : Bit) :
    Real.sqrt (average (fun x : Encoding n s => average (fun y : Encoding n t =>
      localG f z beta (x.val.1, y.val.1) (x.val.2, y.val.2) ^ 2))) ≤ 6 := by
  calc
    _ ≤ Real.sqrt 36 := Real.sqrt_le_sqrt (localG_encoding_sq_le_thirtySix hn f z beta s t)
    _ = _ := by norm_num

/-- Number of factors in a concrete Fin-indexed product representation of G. -/
def localFactorCount {n leakage : ℕ} (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) : ℕ :=
  Fintype.card (ActualRetainedDirection f z beta)

/-- Index the actually retained singular directions by the finite range of their cardinality. -/
def localFactorIndex {n leakage : ℕ} (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) :
    Fin (localFactorCount f z beta) → ActualRetainedDirection f z beta :=
  (Fintype.equivFin (ActualRetainedDirection f z beta)).symm

/-- Fin-indexed left factors, each depending only on its own two endpoint shares. -/
def localLeftFactor {n leakage : ℕ} (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ)
    (i : Fin (localFactorCount f z beta)) (l l' : Share n) : ℝ :=
  Real.sqrt 2 * leftBalancedFactor (groupedAnswerTable f z) (localFactorIndex f z beta i).val (l, l')

/-- The finite-indexed right balanced singular factor, scaled by √2 and evaluated on its own old and new shares. -/
def localRightFactor {n leakage : ℕ} (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ)
    (i : Fin (localFactorCount f z beta)) (r r' : Share n) : ℝ :=
  Real.sqrt 2 * rightBalancedFactor (groupedAnswerTable f z) (localFactorIndex f z beta i).val (r, r')

/-- Summing over finite factor indices equals summing over the retained singular directions. -/
theorem sum_localFactorIndex {n leakage : ℕ} (f : LeakageQuery n leakage) (z : Answer leakage)
    (beta : ℝ) (a : State n → ℝ) :
    (∑ i : Fin (localFactorCount f z beta), a (localFactorIndex f z beta i).val) =
      ∑ j ∈ retainedDirections (groupedAnswerTable f z) beta, a j := by
  calc
    _ = ∑ j : ActualRetainedDirection f z beta, a j.val :=
      (Fintype.equivFin (ActualRetainedDirection f z beta)).symm.sum_comp _
    _ = _ := sum_actualRetainedDirection _ _ _ _

/-- G has the concrete finite-factor form used in the continual hybrid argument. -/
theorem localG_finite_factor_expansion {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) (x y : State n) :
    localG f z beta (x.1, y.1) (x.2, y.2) =
      ∑ i : Fin (localFactorCount f z beta),
        localLeftFactor f z beta i x.1 y.1 * localRightFactor f z beta i x.2 y.2 := by
  let : Nonempty (Share n) := share_nonempty_of_two_le hn
  have he (j : State n) : (Real.sqrt 2 * leftBalancedFactor (groupedAnswerTable f z) j (x.1, y.1)) *
      (Real.sqrt 2 * rightBalancedFactor (groupedAnswerTable f z) j (x.2, y.2)) =
      2 * (leftBalancedFactor (groupedAnswerTable f z) j (x.1, y.1) *
        rightBalancedFactor (groupedAnswerTable f z) j (x.2, y.2)) := by
    calc
      _ = (Real.sqrt 2) ^ 2 * (leftBalancedFactor (groupedAnswerTable f z) j (x.1, y.1) *
        rightBalancedFactor (groupedAnswerTable f z) j (x.2, y.2)) := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  unfold localLeftFactor localRightFactor
  simp_rw [he]
  rw [← Finset.mul_sum]
  rw [sum_localFactorIndex f z beta (fun j => leftBalancedFactor (groupedAnswerTable f z) j (x.1, y.1) *
    rightBalancedFactor (groupedAnswerTable f z) j (x.2, y.2))]
  rw [← spectralTruncation_balanced_expansion]
  rfl

/-- The concrete left-factor energy is twice the actual balanced truncation energy. -/
theorem localLeftFactor_energy_eq {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) (ll : State n) :
    (∑ i : Fin (localFactorCount f z beta), localLeftFactor f z beta i ll.1 ll.2 ^ 2) =
      2 * leftFactorEnergy (groupedAnswerTable f z) beta ll := by
  unfold localLeftFactor
  simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Finset.mul_sum]
  rw [sum_localFactorIndex f z beta (fun j => leftBalancedFactor (groupedAnswerTable f z) j (ll.1, ll.2) ^ 2)]
  rfl

/-- The squared finite right-factor energy equals twice the retained right balanced-factor energy. -/
theorem localRightFactor_energy_eq {n leakage : ℕ}
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) (rr : State n) :
    (∑ i : Fin (localFactorCount f z beta), localRightFactor f z beta i rr.1 rr.2 ^ 2) =
      2 * rightFactorEnergy (groupedAnswerTable f z) beta rr := by
  unfold localRightFactor
  simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Finset.mul_sum]
  rw [sum_localFactorIndex f z beta (fun j => rightBalancedFactor (groupedAnswerTable f z) j (rr.1, rr.2) ^ 2)]
  rfl

/-- Pointwise concrete left-factor energy bound used when one state label changes. -/
theorem localLeftFactor_point_energy_le {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ} (hbeta : 0 < beta) (ll : State n) :
    (∑ i : Fin (localFactorCount f z beta), localLeftFactor f z beta i ll.1 ll.2 ^ 2) ≤ 2 / beta := by
  let : Nonempty (Share n) := share_nonempty_of_two_le hn
  rw [localLeftFactor_energy_eq]
  have h := leftFactorEnergy_le (groupedAnswerTable f z) hbeta ll
    (groupedAnswerTable_row_average_sq_le_one f z ll)
  calc
    _ ≤ 2 * (1 / beta) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

/-- For β > 0, the actual right local factor energy at every endpoint pair is at most 2/β. -/
theorem localRightFactor_point_energy_le {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ} (hbeta : 0 < beta) (rr : State n) :
    (∑ i : Fin (localFactorCount f z beta), localRightFactor f z beta i rr.1 rr.2 ^ 2) ≤ 2 / beta := by
  let : Nonempty (Share n) := share_nonempty_of_two_le hn
  rw [localRightFactor_energy_eq]
  have h := rightFactorEnergy_le (groupedAnswerTable f z) hbeta rr
    (groupedAnswerTable_column_average_sq_le_one f z rr)
  calc
    _ ≤ 2 * (1 / beta) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

/-- Mean concrete left-factor energy is at most four, using the actual nuclear proof. -/
theorem localLeftFactor_mean_energy_le {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3) :
    average (fun ll : State n => ∑ i : Fin (localFactorCount f z beta), localLeftFactor f z beta i ll.1 ll.2 ^ 2) ≤ 4 := by
  let : Nonempty (Share n) := share_nonempty_of_two_le hn
  simp_rw [localLeftFactor_energy_eq]
  rw [average_smul, leftFactorEnergy_average]
  have h := actual_answer_nuclear_le_two hn f z hbeta hbeta1 hthreshold
  linarith

/-- At an admissible threshold, the actual right local factor family has uniform mean energy at most four. -/
theorem localRightFactor_mean_energy_le {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3) :
    average (fun rr : State n => ∑ i : Fin (localFactorCount f z beta), localRightFactor f z beta i rr.1 rr.2 ^ 2) ≤ 4 := by
  let : Nonempty (Share n) := share_nonempty_of_two_le hn
  simp_rw [localRightFactor_energy_eq]
  rw [average_smul, rightFactorEnergy_average]
  have h := actual_answer_nuclear_le_two hn f z hbeta hbeta1 hthreshold
  linarith

/-- Explicit actual conditional-answer approximation error after an actual four-cycle transfer estimate has been supplied. -/
theorem conditional_local_error_le {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3)
    (htransfer : average (fun M : RefreshMatrix n => fourCycle (actualResidualPullback f z beta M)) ≤
      1512 * beta ^ 2 * normSq (actualResidual f z beta)) (s : Bit) :
    Real.sqrt (average (fun x : Encoding n s => average (fun y : Encoding n s =>
      ((conditionalAnswer f x y z).toReal - localG f z beta (x.val.1, y.val.1) (x.val.2, y.val.2)) ^ 2))) ≤
      972 * beta ^ (1 / 3 : ℝ) := by
  calc
    _ ≤ 3 * Real.sqrt (normSq (actualResidual f z beta)) := conditional_local_error_norm_le hn f z beta s
    _ ≤ 3 * (324 * beta ^ (1 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left (actualResidual_norm_le_of_fourCycle_transfer hn f z hbeta hbeta1 hthreshold htransfer)
        (by norm_num)
    _ = _ := by ring

/-- Squared-error version of the explicit actual local bound, convenient for the finite Cauchy--Schwarz window estimates. -/
theorem conditional_local_error_sq_le_explicit {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3)
    (htransfer : average (fun M : RefreshMatrix n => fourCycle (actualResidualPullback f z beta M)) ≤
      1512 * beta ^ 2 * normSq (actualResidual f z beta)) (s : Bit) :
    average (fun x : Encoding n s => average (fun y : Encoding n s =>
      ((conditionalAnswer f x y z).toReal - localG f z beta (x.val.1, y.val.1) (x.val.2, y.val.2)) ^ 2)) ≤
      (972 * beta ^ (1 / 3 : ℝ)) ^ 2 := by
  have h := conditional_local_error_le hn f z hbeta hbeta1 hthreshold htransfer s
  have h0 : 0 ≤ average (fun x : Encoding n s => average (fun y : Encoding n s =>
      ((conditionalAnswer f x y z).toReal - localG f z beta (x.val.1, y.val.1) (x.val.2, y.val.2)) ^ 2)) :=
    average_nonneg fun _ => average_nonneg fun _ => sq_nonneg _
  have he : 0 ≤ 972 * beta ^ (1 / 3 : ℝ) := by positivity
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) he).mpr h
  rwa [Real.sq_sqrt h0] at hs

end RefreshingProof.Local
