import Proofs.Compiler.Foundations.MatrixRefreshing.Probability.FiniteDistribution
import Proofs.Compiler.Construction.Parameters



/-!
# Bounded rejection sampling

The distribution of a capped rejection loop is computed exactly, including its fallback. The resulting distance bound is then propagated through an adaptive sequence of sampling calls. This is the sampling-error argument used for the strict-time simulator; bounds for the individual matrix and encoding samplers must still be instantiated separately.
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler.Sampling

open Refresh


variable {α β : Type*} [Fintype α] [Fintype β]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; fallback ∈ 𝒟(α); a ∈ α, we have

trial(P, accept, fallback)(a) = ({ P(a) if accept(a),; 0 otherwise }) + (1 - acceptance(P, accept)) · fallback(a).
-/
theorem trial_weight (P : FiniteDistribution α) (accept : α → Bool)
    (fallback : FiniteDistribution α) (a : α) :
    (trial P accept fallback).weight a =
      (if accept a then P.weight a else 0) +
        (1 - acceptance P accept) * fallback.weight a := by
  classical
  have hpoint (b : α) :
      P.weight b * (if accept b then FiniteDistribution.pure b else fallback).weight a =
        (if b = a then if accept a then P.weight a else 0 else 0) +
          (P.weight b - (if accept b then P.weight b else 0)) * fallback.weight a := by
    by_cases hba : b = a
    · subst b
      cases accept a <;> simp [FiniteDistribution.pure]
    · cases accept b <;> simp [FiniteDistribution.pure, hba, Ne.symm hba]
  simp only [trial, FiniteDistribution.bind, hpoint, Finset.sum_add_distrib,
    ← Finset.sum_mul, Finset.sum_sub_distrib, P.total]
  simp [acceptance]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; fallback ∈ 𝒟(α); attempts ∈ ℕ; a ∈ α, assume 0 < acceptance(P, accept). Then

capped(P, accept, fallback, attempts)(a) = (1 - (1 - acceptance(P, accept))^attempts) · accepted(P, accept)(a) + (1 - acceptance(P, accept))^attempts · fallback(a).
-/
theorem capped_weight (P : FiniteDistribution α) (accept : α → Bool)
    (fallback : FiniteDistribution α) (hp : 0 < acceptance P accept) (attempts : ℕ) (a : α) :
    (capped P accept fallback attempts).weight a =
      (1 - (1 - acceptance P accept) ^ attempts) * (accepted P accept hp).weight a +
        (1 - acceptance P accept) ^ attempts * fallback.weight a := by
  induction attempts with
  | zero => simp [capped]
  | succ attempts ih =>
    rw [capped, trial_weight, ih, pow_succ]
    have hacc : (if accept a then P.weight a else 0) =
        acceptance P accept * (accepted P accept hp).weight a := by
      dsimp [accepted]
      field_simp
    rw [hacc]
    ring

/-- The exact error is the rejected-all-trials probability times the fallback error. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; fallback ∈ 𝒟(α); attempts ∈ ℕ, assume 0 < acceptance(P, accept). Then

δ(capped(P, accept, fallback, attempts), accepted(P, accept)) = (1 - acceptance(P, accept))^attempts · δ(fallback, accepted(P, accept)).
-/
theorem capped_distance (P : FiniteDistribution α) (accept : α → Bool)
    (fallback : FiniteDistribution α) (hp : 0 < acceptance P accept) (attempts : ℕ) :
    statisticalDistance (capped P accept fallback attempts) (accepted P accept hp) =
      (1 - acceptance P accept) ^ attempts *
        statisticalDistance fallback (accepted P accept hp) := by
  have hnonneg : 0 ≤ (1 - acceptance P accept) ^ attempts :=
    pow_nonneg (sub_nonneg.mpr (acceptance_le_one P accept)) _
  unfold statisticalDistance variationNorm
  simp_rw [capped_weight P accept fallback hp attempts]
  have hpoint (a : α) :
      (1 - (1 - acceptance P accept) ^ attempts) * (accepted P accept hp).weight a +
        (1 - acceptance P accept) ^ attempts * fallback.weight a -
          (accepted P accept hp).weight a =
      (1 - acceptance P accept) ^ attempts *
        (fallback.weight a - (accepted P accept hp).weight a) := by ring
  simp_rw [hpoint, abs_mul, abs_of_nonneg hnonneg]
  rw [← Finset.mul_sum]
  ring

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; fallback ∈ 𝒟(α); attempts ∈ ℕ, assume 0 < acceptance(P, accept). Then

δ(capped(P, accept, fallback, attempts), accepted(P, accept)) ≤ (1 - acceptance(P, accept))^attempts.
-/
theorem capped_distance_le (P : FiniteDistribution α) (accept : α → Bool)
    (fallback : FiniteDistribution α) (hp : 0 < acceptance P accept) (attempts : ℕ) :
    statisticalDistance (capped P accept fallback attempts) (accepted P accept hp) ≤
      (1 - acceptance P accept) ^ attempts := by
  rw [capped_distance]
  exact mul_le_of_le_one_right
    (pow_nonneg (sub_nonneg.mpr (acceptance_le_one P accept)) _)
    (statisticalDistance_le_one _ _)

/-- A constant acceptance lower bound yields a uniform geometric tail. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; fallback ∈ 𝒟(α); c ∈ ℝ; attempts ∈ ℕ, assume 0 < c; c ≤ acceptance(P, accept). Then

δ(capped(P, accept, fallback, attempts), accepted(P, accept, hc.trans_le)) ≤ (1 - c)^attempts.
-/
theorem capped_distance_le_of_acceptance (P : FiniteDistribution α) (accept : α → Bool)
    (fallback : FiniteDistribution α) {c : ℝ} (hc : 0 < c)
    (haccept : c ≤ acceptance P accept) (attempts : ℕ) :
    statisticalDistance (capped P accept fallback attempts)
      (accepted P accept (hc.trans_le haccept)) ≤ (1 - c) ^ attempts := by
  apply (capped_distance_le _ _ _ _ _).trans
  exact pow_le_pow_left₀ (sub_nonneg.mpr (acceptance_le_one P accept))
    (sub_le_sub_left haccept 1) _

universe u

/-- The ordinary executable capped loop, with one deterministic fallback value. -/
/- Mathematical definition (normal notation): Given an explicit finite proposal tape, return the first value passing the acceptance test, or the specified fallback value if none passes. -/
def sample (accept : α → Bool) (fallback : α) :
    (attempts : ℕ) → Tape α attempts → α
  | 0, _ => fallback
  | n + 1, tape => if accept tape.1 then tape.1 else sample accept fallback n tape.2

/-- Number of tested proposals; candidate generation is accounted for separately. -/
/- Mathematical definition (normal notation): Count the proposals inspected up to and including the first accepted one, or all n proposals if none is accepted. The empty tape contributes zero. -/
def attemptsUsed (accept : α → Bool) : (n : ℕ) → Tape α n → ℕ
  | 0, _ => 0
  | n + 1, tape => if accept tape.1 then 1 else 1 + attemptsUsed accept n tape.2

omit [Fintype α] in
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For accept ∈ α → Bool; n ∈ ℕ; tape ∈ Tape(α, n), we have

attemptsUsed(accept, n, tape) ≤ n.
-/
theorem attemptsUsed_le (accept : α → Bool) (n : ℕ) (tape : Tape α n) :
    attemptsUsed accept n tape ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [attemptsUsed]
    split_ifs
    · omega
    · have := ih tape.2
      omega

/-- Independent proposals give a distribution on the explicit finite random tape. -/
/- Mathematical definition (normal notation): Give the length-n proposal tape its independent product distribution P^(⊗ n). -/
noncomputable def tapeDistribution (P : FiniteDistribution α) : (n : ℕ) → FiniteDistribution (Tape α n)
  | 0 => FiniteDistribution.pure PUnit.unit
  | n + 1 => P.prod (tapeDistribution P n)

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); Q ∈ 𝒟(β); γ a set; f ∈ α × β → γ, assume γ is finite. Then

(f_*(P ⊗ Q)) = bind(P, ((a ↦ (((b ↦ f((a, b))))_*Q)))).
-/
theorem prod_map (P : FiniteDistribution α) (Q : FiniteDistribution β) {γ : Type*} [Fintype γ]
    (f : α × β → γ) :
    (P.prod Q).map f = P.bind (fun a => Q.map (fun b => f (a, b))) := by
  classical
  ext c
  simp only [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.prod, FiniteDistribution.joint,
    Fintype.sum_prod_type, Finset.mul_sum]
  congr 1
  funext a
  congr 1
  funext b
  ring

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); b ∈ β, we have

(((x₁ ↦ b))_*P) = FiniteDistribution.pure(b).
-/
theorem map_const (P : FiniteDistribution α) (b : β) :
    P.map (fun _ => b) = FiniteDistribution.pure b := by
  ext c
  simp [FiniteDistribution.map, FiniteDistribution.bind, ← Finset.sum_mul, P.total]

/-- The executable tape program has exactly the analyzed capped distribution. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; fallback ∈ α; n ∈ ℕ, we have

(sample(accept, fallback, n)_*tapeDistribution(P, n)) = capped(P, accept, FiniteDistribution.pure(fallback), n).
-/
theorem sample_distribution (P : FiniteDistribution α) (accept : α → Bool) (fallback : α) (n : ℕ) :
    (tapeDistribution P n).map (sample accept fallback n) =
      capped P accept (FiniteDistribution.pure fallback) n := by
  induction n with
  | zero =>
    change (FiniteDistribution.pure (PUnit.unit : Tape α 0)).map (fun _ => fallback) = _
    exact map_const _ _
  | succ n ih =>
    change (P.prod (tapeDistribution P n)).map
      (fun tape : α × Tape α n => if accept tape.1 then tape.1 else sample accept fallback n tape.2) =
      trial P accept (capped P accept (FiniteDistribution.pure fallback) n)
    erw [prod_map P (tapeDistribution P n)]
    unfold trial
    congr 1
    funext a
    cases h : accept a
    · simpa [sample, h] using ih
    · simp [sample, h, map_const]

/-- Error of the executable bounded sampler, after any deterministic observation. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; fallback ∈ α; n ∈ ℕ; observe ∈ α → β, assume 0 < acceptance(P, accept). Then

δ((((tape ↦ observe(sample(accept, fallback, n, tape))))_*tapeDistribution(P, n)), (observe_*accepted(P, accept))) ≤ (1 - acceptance(P, accept))ⁿ.
-/
theorem sample_distance_le (P : FiniteDistribution α) (accept : α → Bool) (fallback : α)
    (hp : 0 < acceptance P accept) (n : ℕ) (observe : α → β) :
    statisticalDistance
      ((tapeDistribution P n).map (fun tape => observe (sample accept fallback n tape)))
      ((accepted P accept hp).map observe) ≤ (1 - acceptance P accept) ^ n := by
  rw [show (fun tape => observe (sample accept fallback n tape)) =
      observe ∘ sample accept fallback n from rfl, ← FiniteDistribution.map_map, sample_distribution]
  exact (statisticalDistance_map_le _ _ _).trans (capped_distance_le _ _ _ hp n)

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; n ∈ ℕ, we have

𝔼_(tape ← tapeDistribution(P, (n + 1))) [attemptsUsed(accept, (n + 1), tape)] = 1 + (1 - acceptance(P, accept)) · 𝔼_(tape ← tapeDistribution(P, n)) [attemptsUsed(accept, n, tape)].
-/
theorem expected_attempts_succ (P : FiniteDistribution α) (accept : α → Bool) (n : ℕ) :
    (tapeDistribution P (n + 1)).expect (fun tape => (attemptsUsed accept (n + 1) tape : ℝ)) =
      1 + (1 - acceptance P accept) *
        (tapeDistribution P n).expect (fun tape => (attemptsUsed accept n tape : ℝ)) := by
  change (P.prod (tapeDistribution P n)).expect _ = _
  erw [MatrixRefresh.expect_prod]
  have hpoint (a : α) :
      (tapeDistribution P n).expect (fun tape => (attemptsUsed accept (n + 1) (a, tape) : ℝ)) =
        1 + (if accept a then 0 else 1) *
          (tapeDistribution P n).expect (fun tape => (attemptsUsed accept n tape : ℝ)) := by
    cases ha : accept a <;>
      simp [attemptsUsed, ha, MatrixRefresh.expect_add]
  simp_rw [hpoint]
  rw [MatrixRefresh.expect_add]
  simp only [FiniteDistribution.expect_const]
  congr 1
  unfold FiniteDistribution.expect
  have hfactor (a : α) :
      P.weight a * ((if accept a then 0 else 1) *
        ∑ tape, (tapeDistribution P n).weight tape * (attemptsUsed accept n tape : ℝ)) =
      (P.weight a - (if accept a then P.weight a else 0)) *
        (∑ tape, (tapeDistribution P n).weight tape * (attemptsUsed accept n tape : ℝ)) := by
    cases accept a <;> simp
  simp_rw [hfactor]
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, P.total]
  rfl

/-- The expected number of tested candidates never exceeds reciprocal acceptance. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; n ∈ ℕ, assume 0 < acceptance(P, accept). Then

𝔼_(tape ← tapeDistribution(P, n)) [attemptsUsed(accept, n, tape)] ≤ (acceptance(P, accept))⁻¹.
-/
theorem expected_attempts_le (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (n : ℕ) :
    (tapeDistribution P n).expect (fun tape => (attemptsUsed accept n tape : ℝ)) ≤
      (acceptance P accept)⁻¹ := by
  induction n with
  | zero => simp [tapeDistribution, attemptsUsed, FiniteDistribution.expect, hp.le]
  | succ n ih =>
    rw [expected_attempts_succ]
    calc
      _ ≤ 1 + (1 - acceptance P accept) * (acceptance P accept)⁻¹ :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (acceptance_le_one P accept)))
      _ = _ := by field_simp; ring

/-- Four trials at acceptance at least one quarter lose at most one bit of error. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, we have

(3 / 4)^(4 · n) ≤ (1 / 2)ⁿ.
-/
theorem quarter_tail_block (n : ℕ) :
    (3 / 4 : ℝ) ^ (4 * n) ≤ (1 / 2 : ℝ) ^ n := by
  rw [pow_mul]
  exact pow_le_pow_left₀ (by positivity) (by norm_num) n

/-- An explicit logarithmic cap suffices for the union bound on all calls. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For calls, σ ∈ ℕ, we have

calls · (3 / 4)^(4 · (σ + Nat.clog(2, calls))) ≤ (1 / 2)^σ.
-/
theorem quarter_tail_union (calls σ : ℕ) :
    (calls : ℝ) * (3 / 4 : ℝ) ^ (4 * (σ + Nat.clog 2 calls)) ≤
      (1 / 2 : ℝ) ^ σ := by
  have hcalls : (calls : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 calls := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) calls
  calc
    _ ≤ (2 : ℝ) ^ Nat.clog 2 calls * (1 / 2 : ℝ) ^ (σ + Nat.clog 2 calls) :=
      mul_le_mul hcalls (quarter_tail_block _) (by positivity) (by positivity)
    _ = (1 / 2 : ℝ) ^ σ := by
      rw [pow_add]
      have h : (2 : ℝ) ^ Nat.clog 2 calls * (1 / 2 : ℝ) ^ Nat.clog 2 calls = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        _ = (1 / 2 : ℝ) ^ σ *
            ((2 : ℝ) ^ Nat.clog 2 calls * (1 / 2 : ℝ) ^ Nat.clog 2 calls) := by ring
        _ = _ := by rw [h, mul_one]

/-- A block with expected acceptance at least one halves the failure probability. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c ∈ ℝ; block ∈ ℕ, assume 0 ≤ c; c ≤ 1; 1 ≤ block · c. Then

(1 - c)^block ≤ 1 / 2.
-/
theorem geometric_tail_block {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (block : ℕ) (hblock : 1 ≤ (block : ℝ) * c) :
    (1 - c) ^ block ≤ (1 / 2 : ℝ) := by
  have hlarge : (2 : ℝ) ≤ (1 + c) ^ block := by
    exact (by linarith : (2 : ℝ) ≤ 1 + (block : ℝ) * c).trans
      (one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ c) block)
  have hprod : (1 - c) ^ block * (1 + c) ^ block ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (mul_nonneg (by linarith) (by linarith)) (by nlinarith)
  have hn : 0 ≤ (1 - c) ^ block := pow_nonneg (by linarith) _
  nlinarith [mul_le_mul_of_nonneg_left hlarge hn]

/-- A constant acceptance lower bound gives an explicit logarithmic cap for any adaptive number of sampling calls. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c ∈ ℝ; block ∈ ℕ; calls, σ ∈ ℕ, assume 0 ≤ c; c ≤ 1; 1 ≤ block · c. Then

calls · (1 - c)^(block · (σ + Nat.clog(2, calls))) ≤ (1 / 2)^σ.
-/
theorem geometric_tail_union {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (block : ℕ) (hblock : 1 ≤ (block : ℝ) * c) (calls σ : ℕ) :
    (calls : ℝ) * (1 - c) ^ (block * (σ + Nat.clog 2 calls)) ≤ (1 / 2 : ℝ) ^ σ := by
  have hcalls : (calls : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 calls := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) calls
  have hp : (1 - c) ^ (block * (σ + Nat.clog 2 calls)) ≤
      (1 / 2 : ℝ) ^ (σ + Nat.clog 2 calls) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg (by linarith) _)
      (geometric_tail_block hc hc1 block hblock) _
  calc
    _ ≤ (2 : ℝ) ^ Nat.clog 2 calls * (1 / 2 : ℝ) ^ (σ + Nat.clog 2 calls) :=
      mul_le_mul hcalls hp (pow_nonneg (by linarith) _) (by positivity)
    _ = (1 / 2 : ℝ) ^ σ := by
      rw [pow_add]
      have h : (2 : ℝ) ^ Nat.clog 2 calls * (1 / 2 : ℝ) ^ Nat.clog 2 calls = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        _ = (1 / 2 : ℝ) ^ σ *
            ((2 : ℝ) ^ Nat.clog 2 calls * (1 / 2 : ℝ) ^ Nat.clog 2 calls) := by ring
        _ = _ := by rw [h, mul_one]

/-- Replacing conditional distributions costs their uniform distance bound. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P, Q ∈ 𝒟(α); f, g ∈ α → 𝒟(β); ε ∈ ℝ, assume ∀ a, δ(f(a), g(a)) ≤ ε. Then

δ(bind(P, f), bind(Q, g)) ≤ δ(P, Q) + ε.
-/
theorem bind_distance_le (P Q : FiniteDistribution α) (f g : α → FiniteDistribution β)
    {ε : ℝ} (h : ∀ a, statisticalDistance (f a) (g a) ≤ ε) :
    statisticalDistance (P.bind f) (Q.bind g) ≤ statisticalDistance P Q + ε := by
  have hmap (R : FiniteDistribution α) (k : α → FiniteDistribution β) :
      (R.joint k).map Prod.snd = R.bind k := by
    classical
    ext b
    simp [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.joint, FiniteDistribution.pure,
      Fintype.sum_prod_type]
  have hsame : statisticalDistance (Q.bind f) (Q.bind g) ≤ ε := by
    rw [← hmap Q f, ← hmap Q g]
    exact (statisticalDistance_map_le _ _ _).trans
      ((statisticalDistance_joint_mixture Q f g).le.trans (Q.expect_le_const h))
  exact (statisticalDistance_triangle _ (Q.bind f) _).trans
    (add_le_add (statisticalDistance_bind_le P Q f) hsame)

/-- An adaptive state transition can include all earlier samples and answers. -/
/- Mathematical definition (normal notation): Starting from the initial state distribution, successively sample each next state from the time-indexed transition applied to the current state. The state may contain all previous samples and answers. -/
noncomputable def execute (initial : FiniteDistribution α) (step : ℕ → α → FiniteDistribution α) :
    ℕ → FiniteDistribution α
  | 0 => initial
  | n + 1 => (execute initial step n).bind (step n)

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For initial ∈ 𝒟(α); step, approximate ∈ ℕ → α → 𝒟(α); ε ∈ ℕ → ℝ; calls ∈ ℕ, assume ∀ i, a, δ(step(i, a), approximate(i, a)) ≤ ε(i). Then

δ(execute(initial, step, calls), execute(initial, approximate, calls)) ≤ ∑_(i ∈ {0,…,calls−1}) (ε(i)).
-/
theorem execute_distance_le (initial : FiniteDistribution α) (step approximate : ℕ → α → FiniteDistribution α)
    (ε : ℕ → ℝ) (h : ∀ i a, statisticalDistance (step i a) (approximate i a) ≤ ε i)
    (calls : ℕ) :
    statisticalDistance (execute initial step calls) (execute initial approximate calls) ≤
      ∑ i ∈ Finset.range calls, ε i := by
  induction calls with
  | zero => simp [execute]
  | succ calls ih =>
    simpa only [execute, Finset.sum_range_succ] using
      (bind_distance_le (execute initial step calls) (execute initial approximate calls)
        (step calls) (approximate calls) (h calls)).trans (add_le_add ih le_rfl)

/-- Adaptive capped samplers accumulate at most `calls` geometric tails. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For initial ∈ 𝒟(α); proposal ∈ ℕ → α → 𝒟(α); accept ∈ ℕ → α → α → Bool; fallback ∈ ℕ → α → 𝒟(α); c ∈ ℝ; attempts, calls ∈ ℕ, assume 0 < c; ∀ i, a, c ≤ acceptance(proposal(i, a), accept(i, a)). Then

δ(execute(initial, ((i, a ↦ capped(proposal(i, a), accept(i, a), fallback(i, a), attempts))), calls), execute(initial, ((i, a ↦ accepted(proposal(i, a), accept(i, a), hc.trans_le))), calls)) ≤ calls · (1 - c)^attempts.
-/
theorem execute_capped_distance_le (initial : FiniteDistribution α)
    (proposal : ℕ → α → FiniteDistribution α) (accept : ℕ → α → α → Bool)
    (fallback : ℕ → α → FiniteDistribution α) {c : ℝ} (hc : 0 < c)
    (haccept : ∀ i a, c ≤ acceptance (proposal i a) (accept i a)) (attempts calls : ℕ) :
    statisticalDistance
      (execute initial (fun i a =>
        capped (proposal i a) (accept i a) (fallback i a) attempts) calls)
      (execute initial (fun i a =>
        accepted (proposal i a) (accept i a) (hc.trans_le (haccept i a))) calls) ≤
      calls * (1 - c) ^ attempts := by
  have h := execute_distance_le initial
    (fun i a => capped (proposal i a) (accept i a) (fallback i a) attempts)
    (fun i a => accepted (proposal i a) (accept i a) (hc.trans_le (haccept i a)))
    (fun _ => (1 - c) ^ attempts)
    (fun i a => capped_distance_le_of_acceptance _ _ _ hc (haccept i a) attempts) calls
  simpa using h

end CircuitCompiler.Sampling
