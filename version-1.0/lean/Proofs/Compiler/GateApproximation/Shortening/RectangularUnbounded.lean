import Proofs.Compiler.GateApproximation.Shortening.RectangularRetries
import Proofs.Compiler.GateApproximation.Shortening.RectangularUnboundedSampling
import Proofs.Compiler.Construction.Parameters



/-!
# Complete, unbounded rectangular retry executions

The distribution retains every rejected rectangular proposal and the successful last proposal. Observers can inspect all local randomness and messages in this complete finite tape. No bound on the number of retries is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace CircuitCompiler.Sampling.Unbounded

open Refresh

noncomputable section

/-- Full-tape observations differ from their first-success-conditioned distribution by at most the probability that the first attempt fails. The observation may retain both the returned value and leakage of the entire private retry tape. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α,β a set; P ∈ 𝒟(α); accept ∈ α → Bool; f ∈ StoppedTape(α) → β, assume α is finite; β is finite; 0 < acceptance(P, accept). Then

δ(observe(P, accept, f), firstView(P, accept, f)) ≤ 1 - acceptance(P, accept).
-/
theorem observation_distance {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteDistribution α) (accept : α → Bool) (hp : 0 < acceptance P accept)
    (f : StoppedTape α → β) :
    statisticalDistance (observe P accept hp f) (firstView P accept hp f) ≤
      1 - acceptance P accept := by
  have hflag : 0 < acceptance (flaggedView P accept hp f) Prod.fst := by
    rwa [flaggedView_acceptance]
  have h := statisticalDistance_map_le (flaggedView P accept hp f)
    (accepted (flaggedView P accept hp f) Prod.fst hflag) Prod.snd
  rw [flaggedView_map, flaggedView_accepted_map, Rectangular.accepted_distance,
    flaggedView_acceptance] at h
  exact h

end

end CircuitCompiler.Sampling.Unbounded

namespace CircuitCompiler.Rectangular

open Refresh Sampling

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The unbounded physical retry distribution for every fixed long pair. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; u, v ∈ U(F, (n + t)), assume 2 ≤ n. define

fullTapeDistribution(u, v) := Unbounded.distribution(attemptDistribution(u), ((p ↦ decide((rightOutput(v, p) ≠ 0))))).
-/
def fullTapeDistribution {n t : ℕ} (hn : 2 ≤ n) (u v : U F (n+t)) :
    PMF (FullTape (n := n) u) :=
  Unbounded.distribution (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0))
    (attempt_acceptance_pos hn u v)

/-- An arbitrary finite-valued observation of the full private retry phase. -/
/-
Mathematical definition (normal notation): For Z a set; n, t ∈ ℕ; u, v ∈ U(F, (n + t)); f ∈ FullTape(n = n, u) → Z, assume Z is finite; 2 ≤ n. define

fullTapeObserve(u, v, f) := Unbounded.observe(attemptDistribution(u), ((p ↦ decide((rightOutput(v, p) ≠ 0)))), f).
-/
def fullTapeObserve {Z : Type*} [Fintype Z] {n t : ℕ}
    (hn : 2 ≤ n) (u v : U F (n+t)) (f : FullTape (n := n) u → Z) : FiniteDistribution Z :=
  Unbounded.observe (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0))
    (attempt_acceptance_pos hn u v) f

/-- The physical rectangular loop terminates with probability one. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; u, v ∈ U(F, (n + t)), assume 2 ≤ n. Then

(∑_(tape ∈ FullTape(n = n, u)) (ENNReal.ofReal(Unbounded.traceWeight(attemptDistribution(u), ((p ↦ decide((rightOutput(v, p) ≠ 0)))), tape)))) = 1.
-/
theorem fullTape_terminates {n t : ℕ} (hn : 2 ≤ n) (u v : U F (n+t)) :
    (∑' tape : FullTape (n := n) u,
      ENNReal.ofReal (Unbounded.traceWeight (attemptDistribution hn u)
        (fun p => decide (rightOutput v p ≠ 0)) tape)) = 1 :=
  Unbounded.terminates_almost_surely _ _ (attempt_acceptance_pos hn u v)

/-- The number of physical attempts has a finite expectation, bounded by two. This is the expectation of the genuine unbounded count marginal. -/

/- Mathematical statement (normal notation): For every fixed nonzero long input pair and n ≥ 2, let N ≥ 1 be the total number of shortening attempts, including the successful one. Then 𝔼[N] ≤ 2. -/
theorem fullTape_expected_attempts_le_two {n t : ℕ}
    (hn : 2 ≤ n) (u v : U F (n+t)) :
    (∑' k : ℕ, ((k : ℝ) + 1) *
      (((fullTapeDistribution hn u v).map Sigma.fst) k).toReal) ≤ 2 := by
  unfold fullTapeDistribution
  rw [(Unbounded.expected_attempts _ _ (attempt_acceptance_pos hn u v)).tsum_eq]
  exact (div_le_iff₀ (attempt_acceptance_pos hn u v)).mpr (by
    nlinarith [attempt_acceptance_ge_half hn u v])

/-- Every positive-mass physical tape ends with a successful proposal. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; u, v ∈ U(F, (n + t)); tape ∈ FullTape(n = n, u), assume 2 ≤ n; tape ∈ support(fullTapeDistribution(u, v)). Then

rightOutput(v, ((tape)₂)₂) ≠ 0.
-/
theorem fullTape_last_success {n t : ℕ} (hn : 2 ≤ n) (u v : U F (n+t))
    (tape : FullTape (n := n) u) (h : tape ∈ (fullTapeDistribution hn u v).support) :
    rightOutput v tape.2.2 ≠ 0 := by
  have hv := (Unbounded.support_valid _ _ (attempt_acceptance_pos hn u v) tape h).2
  exact of_decide_eq_true hv

/-- For each fixed input pair the final encoding is exactly uniform, even though the full retry tape is retained for the leakage observation. -/

/- Mathematical statement (normal notation): For every fixed nonzero long pair (u,v), n ≥ 2, the actual retry sampler's returned encoding has exactly distribution μ_(u · v). This statement includes the unbounded sequence of rejected attempts and the first accepted attempt; the fallback does not change the returned distribution. -/
theorem fullTape_returned_uniform {n t : ℕ} (hn : 2 ≤ n) (u v : U F (n+t))
    (fallback : Fiber F n (dot u.val v.val)) :
    letI := fiber_nonempty F n hn (dot u.val v.val)
    fullTapeObserve hn u v (fun tape => outputOr fallback tape.2.2) =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (dot u.val v.val))) := by
  letI := fiber_nonempty F n hn (dot u.val v.val)
  rw [fullTapeObserve, Unbounded.observe_last]
  exact accepted_returned_uniform hn u v fallback

/-- Exact full-tape comparison to the first-success distribution. There is no unspecified continuation: `f` observes the actual countable physical retry distribution. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Z a set; n, t ∈ ℕ; u, v ∈ U(F, (n + t)); f ∈ FullTape(n = n, u) → Z, assume Z is finite; 2 ≤ n. Then

δ(fullTapeObserve(u, v, f), (((p ↦ f((0, (PUnit.unit, p)))))_*accepted(attemptDistribution(u), ((p ↦ decide((rightOutput(v, p) ≠ 0))))))) ≤ acceptance(attemptDistribution(u), ((p ↦ decide((rightOutput(v, p) = 0))))).
-/
theorem fullTape_observation_distance {Z : Type*} [Fintype Z] {n t : ℕ}
    (hn : 2 ≤ n) (u v : U F (n+t)) (f : FullTape (n := n) u → Z) :
    statisticalDistance (fullTapeObserve hn u v f)
      ((accepted (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0))
        (attempt_acceptance_pos hn u v)).map (fun p => f ⟨0, (PUnit.unit, p)⟩)) ≤
      acceptance (attemptDistribution hn u) (fun p => decide (rightOutput v p = 0)) := by
  have h := Unbounded.observation_distance (attemptDistribution hn u)
    (fun p => decide (rightOutput v p ≠ 0)) (attempt_acceptance_pos hn u v) f
  rw [attempt_acceptance_complement] at h
  simpa only [fullTapeObserve, sub_sub_cancel, Unbounded.firstView] using h

/-- Binary fields give the paper's `2/N` retry error for arbitrary full-tape observations, including joint observations of output and leakage. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Z a set; n, t ∈ ℕ; u, v ∈ U(F, (n + t)); f ∈ FullTape(n = n, u) → Z, assume Z is finite; |F| = 2; 2 ≤ n. Then

δ(fullTapeObserve(u, v, f), (((p ↦ f((0, (PUnit.unit, p)))))_*accepted(attemptDistribution(u), ((p ↦ decide((rightOutput(v, p) ≠ 0))))))) ≤ 2 / 2ⁿ.
-/
theorem binary_fullTape_observation_distance {Z : Type*} [Fintype Z] {n t : ℕ}
    (hq : fieldCard F = 2) (hn : 2 ≤ n) (u v : U F (n+t))
    (f : FullTape (n := n) u → Z) :
    statisticalDistance (fullTapeObserve hn u v f)
      ((accepted (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0))
        (attempt_acceptance_pos hn u v)).map (fun p => f ⟨0, (PUnit.unit, p)⟩)) ≤
      2 / (2 : ℝ)^n :=
  (fullTape_observation_distance hn u v f).trans (binary_attempt_rejection_le hq hn u v)

end

end CircuitCompiler.Rectangular
