import Proofs.Compiler.GateApproximation.Shortening.RectangularUnbounded
import Proofs.Compiler.Construction.Parameters



/-!
# Stochastic observations of complete rectangular retry tapes

A finite answer can depend on additional, input-dependent private randomness. This module averages that randomness to obtain the answer distribution conditioned on the complete outer tape. The answer distribution may depend on every value in that tape.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

open scoped BigOperators ENNReal

namespace CircuitCompiler.Sampling.Unbounded

open Refresh

noncomputable section

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For v ∈ α, we have

toPMF(FiniteDistribution.pure(v)) = PMF.pure(v).
-/
@[simp] theorem toPMF_pure (v : α) : toPMF (FiniteDistribution.pure v) = PMF.pure v := by
  apply PMF.ext
  intro w
  by_cases h : w=v <;> simp [toPMF_apply,FiniteDistribution.pure,PMF.pure_apply,h]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For v ∈ α, we have

toFinite(PMF.pure(v)) = FiniteDistribution.pure(v).
-/
@[simp] theorem toFinite_pure (v : α) : toFinite (PMF.pure v) = FiniteDistribution.pure v := by
  rw [← toPMF_pure,toFinite_toPMF]

/-- Converting a finite PMF mixture to real weights preserves its mixture. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ PMF(α); Q ∈ α → PMF(β), we have

toFinite(bind(P, Q)) = bind(toFinite(P), ((a ↦ toFinite(Q(a))))).
-/
theorem toFinite_bind (P : PMF α) (Q : α → PMF β) :
    toFinite (P.bind Q) = (toFinite P).bind (fun a => toFinite (Q a)) := by
  rw [← toFinite_toPMF ((toFinite P).bind (fun a => toFinite (Q a))),toPMF_bind]
  simp only [toPMF_toFinite]

/-- A deterministic observation is a special case of the stochastic interface. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; f ∈ StoppedTape(α) → β, assume 0 < acceptance(P, accept). Then

observeDistribution(P, accept, ((t ↦ FiniteDistribution.pure(f(t))))) = observe(P, accept, f).
-/
theorem observeDistribution_pure (P : FiniteDistribution α) (accept : α → Bool) (hp : 0 < acceptance P accept)
    (f : StoppedTape α → β) :
    observeDistribution P accept hp (fun t => FiniteDistribution.pure (f t)) = observe P accept hp f := by
  unfold observeDistribution observe
  congr 1
  apply PMF.ext
  intro b
  simp only [PMF.bind_apply,PMF.map_apply]
  apply tsum_congr
  intro t
  by_cases h : b = f t <;> simp [toPMF_apply,FiniteDistribution.pure,h]

/-- Postprocessing the answer commutes with averaging the private randomness. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; f ∈ StoppedTape(α) → 𝒟(β); g ∈ β → γ, assume 0 < acceptance(P, accept). Then

(g_*observeDistribution(P, accept, f)) = observeDistribution(P, accept, ((t ↦ (g_*f(t))))).
-/
theorem observeDistribution_map (P : FiniteDistribution α) (accept : α → Bool) (hp : 0 < acceptance P accept)
    (f : StoppedTape α → FiniteDistribution β) (g : β → γ) :
    (observeDistribution P accept hp f).map g = observeDistribution P accept hp (fun t => (f t).map g) := by
  unfold observeDistribution
  rw [← toFinite_map,PMF.map_bind]
  simp only [toPMF_map]

/-- A returned-proposal-only stochastic observation uses exactly its accepted proposal distribution, regardless of the number of discarded attempts. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; f ∈ α → 𝒟(β), assume 0 < acceptance(P, accept). Then

observeDistribution(P, accept, ((t ↦ f(((t)₂)₂)))) = bind(accepted(P, accept), f).
-/
theorem observeDistribution_last (P : FiniteDistribution α) (accept : α → Bool) (hp : 0 < acceptance P accept)
    (f : α → FiniteDistribution β) :
    observeDistribution P accept hp (fun t => f t.2.2) = (accepted P accept hp).bind f := by
  unfold observeDistribution
  have h := PMF.bind_map (distribution P accept hp) (fun t => t.2.2) (fun a => toPMF (f a))
  dsimp only [Function.comp_def] at h
  rw [← h,last_distribution,← toPMF_bind,toFinite_toPMF]

/-- The conditional answer when the first outer proposal succeeds. -/
/-
Mathematical definition (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; f ∈ StoppedTape(α) → 𝒟(β), assume 0 < acceptance(P, accept). define

firstAcceptedAnswerDistribution(P, accept, f) := bind(accepted(P, accept), ((a ↦ f((0, (PUnit.unit, a)))))).
-/
def firstAcceptedAnswerDistribution (P : FiniteDistribution α) (accept : α → Bool) (hp : 0 < acceptance P accept)
    (f : StoppedTape α → FiniteDistribution β) : FiniteDistribution β :=
  (accepted P accept hp).bind (fun a => f ⟨0,(PUnit.unit,a)⟩)

/-- Analysis flag retained jointly with a stochastic answer. -/
/-
Mathematical definition (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; f ∈ StoppedTape(α) → 𝒟(β), assume 0 < acceptance(P, accept). define

flaggedAnswerDistribution(P, accept, f) := observeDistribution(P, accept, ((t ↦ (((b ↦ (decide(((t)₁ = 0)), b)))_*f(t))))).
-/
def flaggedAnswerDistribution (P : FiniteDistribution α) (accept : α → Bool) (hp : 0 < acceptance P accept)
    (f : StoppedTape α → FiniteDistribution β) : FiniteDistribution (Bool × β) :=
  observeDistribution P accept hp (fun t => (f t).map (fun b => (decide (t.1 = 0),b)))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(β); b ∈ β; v ∈ Bool, we have

(((b ↦ (v, b)))_*P)((true, b)) = { P(b) if v,; 0 otherwise }.
-/
private theorem tag_true_weight (P : FiniteDistribution β) (b : β) (v : Bool) :
    (P.map (fun b => (v,b))).weight (true,b) = if v then P.weight b else 0 := by
  classical
  cases v <;> simp [FiniteDistribution.map,FiniteDistribution.bind,FiniteDistribution.pure,ite_and]

/-- The flag-true mass is its probability times the exact first-success distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; f ∈ StoppedTape(α) → 𝒟(β); b ∈ β, assume 0 < acceptance(P, accept). Then

flaggedAnswerDistribution(P, accept, f)((true, b)) = acceptance(P, accept) · firstAcceptedAnswerDistribution(P, accept, f)(b).
-/
theorem flaggedAnswerDistribution_true_weight (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (f : StoppedTape α → FiniteDistribution β) (b : β) :
    (flaggedAnswerDistribution P accept hp f).weight (true,b) =
      acceptance P accept * (firstAcceptedAnswerDistribution P accept hp f).weight b := by
  classical
  unfold flaggedAnswerDistribution observeDistribution toFinite
  dsimp only
  rw [PMF.bind_apply,ENNReal.tsum_sigma']
  simp only [toPMF_apply,tag_true_weight]
  rw [tsum_eq_single 0 (fun k hk => by simp [hk]),tsum_fintype,Fintype.sum_prod_type]
  simp only [Tape,Fintype.sum_unique,Bool.decide_true,ite_true,distribution_apply,
    traceWeight,prefixWeight,one_mul]
  have hm (a : α) :
      ENNReal.ofReal (if accept a then P.weight a else 0) *
        ENNReal.ofReal ((f ⟨0,(PUnit.unit,a)⟩).weight b) =
      ENNReal.ofReal ((if accept a then P.weight a else 0) *
        (f ⟨0,(PUnit.unit,a)⟩).weight b) := by
    apply (ENNReal.ofReal_mul _).symm
    split_ifs; exact P.nonneg a; rfl
  simp_rw [hm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => mul_nonneg (by
    split_ifs; exact P.nonneg a; rfl) ((f _).nonneg b)),ENNReal.toReal_ofReal (by
      apply Finset.sum_nonneg; intro a _; apply mul_nonneg
      · split_ifs; exact P.nonneg a; rfl
      · exact (f _).nonneg b)]
  change _ = acceptance P accept * ∑ a,
    ((if accept a then P.weight a else 0) / acceptance P accept) * (f ⟨0,(PUnit.unit,a)⟩).weight b
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  field_simp

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; f ∈ StoppedTape(α) → 𝒟(β), assume 0 < acceptance(P, accept). Then

((Prod)₂_*flaggedAnswerDistribution(P, accept, f)) = observeDistribution(P, accept, f).
-/
theorem flaggedAnswerDistribution_map (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (f : StoppedTape α → FiniteDistribution β) :
    (flaggedAnswerDistribution P accept hp f).map Prod.snd = observeDistribution P accept hp f := by
  rw [flaggedAnswerDistribution,observeDistribution_map]
  simp only [FiniteDistribution.map_map,Function.comp_def]
  have hid (Q : FiniteDistribution β) : Q.map (fun x => x) = Q := by
    classical
    ext b
    simp [FiniteDistribution.map,FiniteDistribution.bind,FiniteDistribution.pure]
  simp only [hid]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; f ∈ StoppedTape(α) → 𝒟(β), assume 0 < acceptance(P, accept). Then

acceptance(flaggedAnswerDistribution(P, accept, f), (Prod)₁) = acceptance(P, accept).
-/
theorem flaggedAnswerDistribution_acceptance (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (f : StoppedTape α → FiniteDistribution β) :
    acceptance (flaggedAnswerDistribution P accept hp f) Prod.fst = acceptance P accept := by
  simp only [acceptance,Fintype.sum_prod_type,Fintype.sum_bool,Bool.false_eq_true,
    if_false,if_true,Finset.sum_const_zero,add_zero]
  simp_rw [flaggedAnswerDistribution_true_weight,← Finset.mul_sum,(firstAcceptedAnswerDistribution P accept hp f).total,mul_one]
  rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; f ∈ StoppedTape(α) → 𝒟(β), assume 0 < acceptance(P, accept); 0 < acceptance(flaggedAnswerDistribution(P, accept, f), (Prod)₁). Then

((Prod)₂_*accepted(flaggedAnswerDistribution(P, accept, f), (Prod)₁)) = firstAcceptedAnswerDistribution(P, accept, f).
-/
theorem flaggedAnswerDistribution_accepted_map (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (f : StoppedTape α → FiniteDistribution β)
    (hflag : 0 < acceptance (flaggedAnswerDistribution P accept hp f) Prod.fst) :
    (accepted (flaggedAnswerDistribution P accept hp f) Prod.fst hflag).map Prod.snd = firstAcceptedAnswerDistribution P accept hp f := by
  classical
  ext b
  simp only [FiniteDistribution.map,FiniteDistribution.bind,accepted,Fintype.sum_prod_type,
    Fintype.sum_bool,Bool.false_eq_true,if_false,if_true,zero_div,
    zero_mul,Finset.sum_const_zero,add_zero]
  rw [flaggedAnswerDistribution_acceptance]
  simp_rw [flaggedAnswerDistribution_true_weight]
  simp only [FiniteDistribution.pure]
  simp_rw [mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  field_simp

/-- Arbitrary conditional answer distributions from private-tape observations cost only the actual outer rejection probability when replaced by their first-success restriction. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; f ∈ StoppedTape(α) → 𝒟(β), assume 0 < acceptance(P, accept). Then

δ(observeDistribution(P, accept, f), firstAcceptedAnswerDistribution(P, accept, f)) ≤ 1 - acceptance(P, accept).
-/
theorem observeDistribution_distance (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (f : StoppedTape α → FiniteDistribution β) :
    statisticalDistance (observeDistribution P accept hp f) (firstAcceptedAnswerDistribution P accept hp f) ≤
      1-acceptance P accept := by
  have hflag : 0 < acceptance (flaggedAnswerDistribution P accept hp f) Prod.fst := by
    rwa [flaggedAnswerDistribution_acceptance]
  have h := statisticalDistance_map_le (flaggedAnswerDistribution P accept hp f)
    (accepted (flaggedAnswerDistribution P accept hp f) Prod.fst hflag) Prod.snd
  rw [flaggedAnswerDistribution_map,flaggedAnswerDistribution_accepted_map,Rectangular.accepted_distance,
    flaggedAnswerDistribution_acceptance] at h
  exact h

end

end CircuitCompiler.Sampling.Unbounded

namespace CircuitCompiler.Rectangular

open Refresh Sampling

noncomputable section

variable {F Z : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype Z]

/-- Stochastic tape observations have the same first-success coupling error. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; u, v ∈ U(F, (n + t)); f ∈ FullTape(n = n, u) → 𝒟(Z), assume |F| = 2; 2 ≤ n. Then

δ(fullTapeAnswerDistribution(u, v, f), bind(accepted(attemptDistribution(u), ((p ↦ decide((rightOutput(v, p) ≠ 0))))), ((p ↦ f((0, (PUnit.unit, p))))))) ≤ 2 / 2ⁿ .
-/
theorem binary_fullTapeAnswerDistribution_distance {n t : ℕ}
    (hq : fieldCard F = 2) (hn : 2 ≤ n) (u v : U F (n+t))
    (f : FullTape (n := n) u → FiniteDistribution Z) :
    statisticalDistance (fullTapeAnswerDistribution hn u v f)
      ((accepted (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0))
        (attempt_acceptance_pos hn u v)).bind (fun p => f ⟨0,(PUnit.unit,p)⟩)) ≤
      2/(2:ℝ)^n := by
  have h := Unbounded.observeDistribution_distance (attemptDistribution hn u)
    (fun p => decide (rightOutput v p ≠ 0)) (attempt_acceptance_pos hn u v) f
  rw [attempt_acceptance_complement] at h
  simp only [sub_sub_cancel] at h
  exact h.trans (binary_attempt_rejection_le hq hn u v)

end

end CircuitCompiler.Rectangular
