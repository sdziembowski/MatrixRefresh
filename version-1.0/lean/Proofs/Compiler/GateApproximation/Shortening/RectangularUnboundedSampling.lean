import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Proofs.Compiler.GateApproximation.MatrixPhase.RejectionSampling
import Proofs.Compiler.Construction.Parameters



/-!
# Unbounded rejection sampling with the complete stopped tape

The carrier includes every rejected proposal and the final accepted proposal. Its mass is exactly the product of the proposal masses, with no retry cap. Consequently an observation may depend on the entire (almost surely finite) private retry tape, not just on the returned proposal.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ENNReal

namespace CircuitCompiler.Sampling.Unbounded

open Refresh

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The probability of stopping after exactly `k` failures is geometric. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool, assume 0 < acceptance(P, accept). Then

((Sigma)₁_*distribution(P, accept)) = ProbabilityTheory.geometricPMF.
-/
theorem count_distribution (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) :
    (distribution P accept hp).map Sigma.fst =
      ProbabilityTheory.geometricPMF hp (acceptance_le_one P accept) := by
  classical
  apply PMF.ext
  intro k
  rw [PMF.map_apply, ENNReal.tsum_sigma']
  simp_rw [distribution_apply]
  simp_rw [tsum_fintype]
  calc
    _ = ∑' j, if j = k then ENNReal.ofReal
        (ProbabilityTheory.geometricPMFReal (acceptance P accept) j) else 0 := by
      apply tsum_congr
      intro j
      by_cases hj : j = k
      · subst j
        simp only [ite_true]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => traceWeight_nonneg P accept _),
          traceWeight_sum]
      · simp [hj, Ne.symm hj]
    _ = _ := by rw [tsum_ite_eq]; rfl

/-- The total probability on finite terminated executions is one. No cap or fallback is used in this statement. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool, assume 0 < acceptance(P, accept). Then

(∑_(t ∈ StoppedTape(α)) (ENNReal.ofReal(traceWeight(P, accept, t)))) = 1.
-/
theorem terminates_almost_surely (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) :
    (∑' t : StoppedTape α, ENNReal.ofReal (traceWeight P accept t)) = 1 :=
  (distribution P accept hp).tsum_coe

/-- Forgetting all rejected proposals gives exactly the accepted proposal distribution. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool, assume 0 < acceptance(P, accept). Then

(((t ↦ ((t)₂)₂))_*distribution(P, accept)) = toPMF(accepted(P, accept)).
-/
theorem last_distribution (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) :
    (distribution P accept hp).map (fun t => t.2.2) = toPMF (accepted P accept hp) := by
  classical
  apply PMF.ext
  intro a
  rw [PMF.map_apply, ENNReal.tsum_sigma']
  have h (k : ℕ) :
      (∑' t : Tape α k × α,
        if a = t.2 then distribution P accept hp ⟨k, t⟩ else 0) =
      ProbabilityTheory.geometricPMF hp (acceptance_le_one P accept) k *
        toPMF (accepted P accept hp) a := by
    rw [tsum_fintype, Fintype.sum_prod_type]
    simp only [distribution_apply, traceWeight]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun t _ => mul_nonneg (prefixWeight_nonneg P accept _ _) (by
        split_ifs; exact P.nonneg a; rfl)), ← Finset.sum_mul, prefixWeight_sum]
    change ENNReal.ofReal (_ * _) = ENNReal.ofReal (_ ^ k * _) * ENNReal.ofReal (_ / _)
    rw [← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (sub_nonneg.mpr (acceptance_le_one P accept)) k) hp.le)]
    congr 1
    field_simp
  simp_rw [h]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Any returned-value observation has exactly the accepted-distribution distribution. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; f ∈ α → β, assume 0 < acceptance(P, accept). Then

observe(P, accept, ((t ↦ f(((t)₂)₂)))) = (f_*accepted(P, accept)).
-/
theorem observe_last (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (f : α → β) :
    observe P accept hp (fun t => f t.2.2) = (accepted P accept hp).map f := by
  have h := congrArg (fun Q : PMF α => toFinite (Q.map f)) (last_distribution P accept hp)
  simpa only [observe, PMF.map_comp, Function.comp_def, ← toPMF_map, toFinite_toPMF] using h

/-- A failed prefix has no accepted proposal. -/
/- Mathematical definition (normal notation): A finite tape satisfies this predicate exactly when every entry fails the acceptance test. The empty tape satisfies it vacuously. -/
def AllRejected (accept : α → Bool) : (k : ℕ) → Tape α k → Prop
  | 0, _ => True
  | k + 1, t => accept t.1 = false ∧ AllRejected accept k t.2

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; k ∈ ℕ; t ∈ Tape(α, k), assume prefixWeight(P, accept, k, t) ≠ 0. Then

AllRejected(accept, k, t).
-/
theorem prefixWeight_valid (P : FiniteDistribution α) (accept : α → Bool)
    (k : ℕ) (t : Tape α k) (h : prefixWeight P accept k t ≠ 0) :
    AllRejected accept k t := by
  induction k with
  | zero => trivial
  | succ k ih =>
    constructor
    · cases ha : accept t.1 with
      | false => rfl
      | true => exact False.elim (h (by simp [prefixWeight, ha]))
    · apply ih t.2
      intro hz
      exact h (by simp [prefixWeight, hz])

/-- On a rejected prefix, the stopped-tape mass equals the usual finite iid proposal-tape mass. This identifies the countable model with the actual loop. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; k ∈ ℕ; t ∈ Tape(α, k), assume AllRejected(accept, k, t). Then

prefixWeight(P, accept, k, t) = tapeDistribution(P, k)(t).
-/
theorem prefixWeight_eq_tapeDistribution (P : FiniteDistribution α) (accept : α → Bool)
    (k : ℕ) (t : Tape α k) (h : AllRejected accept k t) :
    prefixWeight P accept k t = (tapeDistribution P k).weight t := by
  induction k with
  | zero => simp [prefixWeight, tapeDistribution, FiniteDistribution.pure, Tape]
  | succ k ih =>
    change (if accept t.1 then 0 else P.weight t.1) * prefixWeight P accept k t.2 =
      P.weight t.1 * (tapeDistribution P k).weight t.2
    simp only [h.1, Bool.false_eq_true, if_false, ih t.2 h.2]

/-- Every valid complete trace has exactly the independent proposal weight. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; t ∈ StoppedTape(α), assume AllRejected(accept, (t)₁, ((t)₂)₁); accept(((t)₂)₂) = true. Then

traceWeight(P, accept, t) = tapeDistribution(P, (t)₁)(((t)₂)₁) · P(((t)₂)₂).
-/
theorem traceWeight_eq_iid (P : FiniteDistribution α) (accept : α → Bool)
    (t : StoppedTape α) (hprefix : AllRejected accept t.1 t.2.1)
    (hlast : accept t.2.2 = true) :
    traceWeight P accept t = (tapeDistribution P t.1).weight t.2.1 * P.weight t.2.2 := by
  simp only [traceWeight, prefixWeight_eq_tapeDistribution P accept _ _ hprefix, hlast, ite_true]

/-- Positive-mass executions consist of failures followed by one success. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; t ∈ StoppedTape(α), assume 0 < acceptance(P, accept); t ∈ support(distribution(P, accept)). Then

AllRejected(accept, (t)₁, ((t)₂)₁) ∧ accept(((t)₂)₂) = true.
-/
theorem support_valid (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (t : StoppedTape α)
    (ht : t ∈ (distribution P accept hp).support) :
    AllRejected accept t.1 t.2.1 ∧ accept t.2.2 = true := by
  have hw : traceWeight P accept t ≠ 0 := by
    intro h
    have := (distribution P accept hp).mem_support_iff t |>.mp ht
    exact this (by simp [distribution_apply, h])
  constructor
  · apply prefixWeight_valid P accept
    intro h
    exact hw (by simp [traceWeight, h])
  · cases ha : accept t.2.2 with
    | true => rfl
    | false => exact False.elim (hw (by simp [traceWeight, ha]))

/-- Expected number of attempts, computed from the proved geometric count distribution. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool, assume 0 < acceptance(P, accept). Then

HasSum(((k ∈ ℕ ↦ (k + 1) · toReal(map(distribution(P, accept))((Sigma)₁, k)))), (1 / acceptance(P, accept))).
-/
theorem expected_attempts (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) :
    HasSum (fun k : ℕ => ((k : ℝ) + 1) *
      (((distribution P accept hp).map Sigma.fst) k).toReal) (1 / acceptance P accept) := by
  have hr0 := sub_nonneg.mpr (acceptance_le_one P accept)
  have hr1 : 1 - acceptance P accept < 1 := by linarith
  have hnorm : ‖1 - acceptance P accept‖ < 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hsum := ((hasSum_coe_mul_geometric_of_norm_lt_one hnorm).add
    (hasSum_geometric_of_lt_one hr0 hr1)).mul_right (acceptance P accept)
  rw [count_distribution]
  convert hsum using 1
  · ext k
    change ((k : ℝ) + 1) * (ENNReal.ofReal ((1 - acceptance P accept) ^ k * acceptance P accept)).toReal = _
    rw [ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg hr0 k) hp.le)]
    ring
  · simp only [sub_sub_cancel]
    field_simp [ne_of_gt hp]
    ring

/-- First-attempt success leaves no hidden failed prefix. -/
/-
Mathematical definition (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; f ∈ StoppedTape(α) → β, assume 0 < acceptance(P, accept). define

firstView(P, accept, f) := (((a ↦ f((0, (PUnit.unit, a)))))_*accepted(P, accept)).
-/
def firstView (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (f : StoppedTape α → β) : FiniteDistribution β :=
  (accepted P accept hp).map (fun a => f ⟨0, (PUnit.unit, a)⟩)

/-- The joint observation of the success flag and the complete stopped tape. The flag is used for analysis, without exposing it in the physical protocol. -/
/-
Mathematical definition (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; f ∈ StoppedTape(α) → β, assume 0 < acceptance(P, accept). define

flaggedView(P, accept, f) := observe(P, accept, ((t ↦ (decide(((t)₁ = 0)), f(t))))).
-/
def flaggedView (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (f : StoppedTape α → β) : FiniteDistribution (Bool × β) :=
  observe P accept hp (fun t => (decide (t.1 = 0), f t))

/-- The first-success slice has mass `p` times its conditional observation distribution. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; f ∈ StoppedTape(α) → β; b ∈ β, assume 0 < acceptance(P, accept). Then

flaggedView(P, accept, f)((true, b)) = acceptance(P, accept) · firstView(P, accept, f)(b).
-/
theorem flaggedView_true_weight (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (f : StoppedTape α → β) (b : β) :
    (flaggedView P accept hp f).weight (true, b) =
      acceptance P accept * (firstView P accept hp f).weight b := by
  classical
  unfold flaggedView observe toFinite
  dsimp only
  rw [PMF.map_apply, ENNReal.tsum_sigma']
  rw [tsum_eq_single 0 (fun k hk => by simp [hk]), tsum_fintype, Fintype.sum_prod_type]
  simp only [Tape, Fintype.sum_unique, Bool.decide_true, Prod.mk.injEq, true_and,
    distribution_apply, traceWeight, prefixWeight, one_mul]
  have h (a : α) : (if b = f ⟨0, (PUnit.unit, a)⟩ then
      ENNReal.ofReal (if accept a then P.weight a else 0) else 0) =
      ENNReal.ofReal ((if accept a then P.weight a else 0) *
        (FiniteDistribution.pure (f ⟨0, (PUnit.unit, a)⟩)).weight b) := by
    by_cases ha : b = f ⟨0, (PUnit.unit, a)⟩ <;> simp [ha, FiniteDistribution.pure]
  simp_rw [h]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => mul_nonneg (by
    split_ifs; exact P.nonneg a; rfl) ((FiniteDistribution.pure _).nonneg _)), ENNReal.toReal_ofReal (by
      apply Finset.sum_nonneg; intro a _; apply mul_nonneg
      · split_ifs; exact P.nonneg a; rfl
      · exact (FiniteDistribution.pure _).nonneg _)]
  change _ = acceptance P accept * ∑ a,
    ((if accept a then P.weight a else 0) / acceptance P accept) *
      (FiniteDistribution.pure (f ⟨0, (PUnit.unit, a)⟩)).weight b
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  field_simp

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ PMF(α), we have

toPMF(toFinite(P)) = P.
-/
@[simp] theorem toPMF_toFinite (P : PMF α) : toPMF (toFinite P) = P := by
  apply PMF.ext
  intro a
  exact ENNReal.ofReal_toReal (P.apply_ne_top a)

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ PMF(α); f ∈ α → β, we have

toFinite((f_*P)) = (f_*toFinite(P)).
-/
theorem toFinite_map (P : PMF α) (f : α → β) :
    toFinite (P.map f) = (toFinite P).map f := by
  rw [← toFinite_toPMF ((toFinite P).map f), toPMF_map, toPMF_toFinite]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For γ a set; P ∈ 𝒟(α); accept ∈ α → Bool; f ∈ StoppedTape(α) → β; g ∈ β → γ, assume γ is finite; 0 < acceptance(P, accept). Then

(g_*observe(P, accept, f)) = observe(P, accept, ((t ↦ g(f(t))))).
-/
theorem observe_map {γ : Type*} [Fintype γ]
    (P : FiniteDistribution α) (accept : α → Bool) (hp : 0 < acceptance P accept)
    (f : StoppedTape α → β) (g : β → γ) :
    (observe P accept hp f).map g = observe P accept hp (fun t => g (f t)) := by
  unfold observe
  rw [← toFinite_map, PMF.map_comp]
  rfl

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; f ∈ StoppedTape(α) → β, assume 0 < acceptance(P, accept). Then

((Prod)₂_*flaggedView(P, accept, f)) = observe(P, accept, f).
-/
theorem flaggedView_map (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (f : StoppedTape α → β) :
    (flaggedView P accept hp f).map Prod.snd = observe P accept hp f := by
  exact observe_map P accept hp _ Prod.snd

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; f ∈ StoppedTape(α) → β, assume 0 < acceptance(P, accept). Then

acceptance(flaggedView(P, accept, f), (Prod)₁) = acceptance(P, accept).
-/
theorem flaggedView_acceptance (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (f : StoppedTape α → β) :
    acceptance (flaggedView P accept hp f) Prod.fst = acceptance P accept := by
  simp only [acceptance, Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true,
    if_false, if_true, Finset.sum_const_zero, add_zero]
  simp_rw [flaggedView_true_weight, ← Finset.mul_sum, (firstView P accept hp f).total, mul_one]
  rfl

/-- Conditioning the analysis flag on first-attempt success gives the distribution of observing the accepted proposal, with the complete tape correctly specialized to an empty failed prefix. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; f ∈ StoppedTape(α) → β, assume 0 < acceptance(P, accept); 0 < acceptance(flaggedView(P, accept, f), (Prod)₁). Then

((Prod)₂_*accepted(flaggedView(P, accept, f), (Prod)₁)) = firstView(P, accept, f).
-/
theorem flaggedView_accepted_map (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (f : StoppedTape α → β)
    (hflag : 0 < acceptance (flaggedView P accept hp f) Prod.fst) :
    (accepted (flaggedView P accept hp f) Prod.fst hflag).map Prod.snd =
      firstView P accept hp f := by
  classical
  ext b
  simp only [FiniteDistribution.map, FiniteDistribution.bind, accepted, Fintype.sum_prod_type,
    Fintype.sum_bool, Bool.false_eq_true, if_false, if_true, zero_div,
    zero_mul, Finset.sum_const_zero, add_zero]
  rw [flaggedView_acceptance]
  simp_rw [flaggedView_true_weight]
  simp only [FiniteDistribution.pure]
  simp_rw [mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  field_simp

end

end CircuitCompiler.Sampling.Unbounded
