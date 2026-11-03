import Proofs.Compiler.GateApproximation.Shortening.RectangularCounts



/-!
# Retrying rectangular shortening

Explicit finite random tapes realize capped retries. Their output converges geometrically to the exact fresh-encoding distribution, and the expected number of tested attempts is bounded by two uniformly in the cap.
-/
set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace CircuitCompiler.Rectangular

open Refresh MatrixRefresh

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Only a capped implementation needs a fallback encoding. The accepted and limiting distributions below do not depend on this choice. -/
/- Mathematical definition (normal notation): Extend the output map to all attempts: return (A,H · v) when H · v ≠ 0, and otherwise return a supplied fixed encoding of u · v. This total map is used to describe distributions; accepted executions never use the fallback branch. -/
def outputOr {n m : ℕ} {u v : U F m}
    (fallback : Fiber F n (dot u.val v.val)) (p : Attempt (n := n) u) :
    Fiber F n (dot u.val v.val) :=
  if h : rightOutput v p ≠ 0 then output ⟨p,h⟩ else fallback

/-- Rejection conditioning followed by the output map is exactly fresh. -/

/- Mathematical statement (normal notation): For every fixed nonzero (u,v), n ≥ 2, condition the sequential attempt sampler on H · v ≠ 0. Its returned pair is exactly uniform on the short fiber {(L',R'):L',R' ≠ 0, L' · R' = u · v}. The arbitrary fallback value has no effect after conditioning on success. -/
theorem accepted_returned_uniform {n t : ℕ} (hn : 2 ≤ n) (u v : U F (n+t))
    (fallback : Fiber F n (dot u.val v.val)) :
    letI := fiber_nonempty F n hn (dot u.val v.val)
    (Sampling.accepted (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0))
      (attempt_acceptance_pos hn u v)).map (outputOr fallback) =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (dot u.val v.val))) := by
  classical
  letI := success_nonempty hn u v
  letI := fiber_nonempty F n hn (dot u.val v.val)
  rw [accepted_attemptDistribution, FiniteDistribution.map_map]
  have he : (fun p : Success (n := n) u v => outputOr fallback p.val) = output := by
    funext p
    simp [outputOr,p.property]
  simp only [Function.comp_def, he]
  exact output_uniform hn u v

/-- Every finite cap has the same uniform expected-work bound. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; u, v ∈ U(F, (n + t)); cap ∈ ℕ, assume 2 ≤ n. Then

𝔼_(tape ← Sampling.tapeDistribution(attemptDistribution(u), cap)) [Sampling.attemptsUsed(((p ↦ decide((rightOutput(v, p) ≠ 0)))), cap, tape)] ≤ 2.
-/
theorem expected_attempts_le_two {n t : ℕ} (hn : 2 ≤ n) (u v : U F (n+t)) (cap : ℕ) :
    (Sampling.tapeDistribution (attemptDistribution hn u) cap).expect
      (fun tape => (Sampling.attemptsUsed
        (fun p => decide (rightOutput v p ≠ 0)) cap tape : ℝ)) ≤ 2 := by
  apply (Sampling.expected_attempts_le (attemptDistribution hn u)
    (fun p => decide (rightOutput v p ≠ 0)) (attempt_acceptance_pos hn u v) cap).trans
  have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1/2)
    (attempt_acceptance_ge_half hn u v)
  simpa [one_div] using h

/-- A cap of `cap` attempts changes the fresh-encoding distribution by at most `2^-cap`. This follows from the actual independent-proposal rejection loop. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For any fixed long pair (u,v), n ≥ 2, and any chosen fallbacks, run at most B shortening attempts. Its returned short encoding distribution P_B obeys

δ(P_B,μ_(u · v)ⁿ) ≤ 2^(−B).

The bound charges the event that all B attempts reject.
-/
theorem capped_output_distance {n t : ℕ} (hn : 2 ≤ n) (u v : U F (n+t))
    (fallbackAttempt : Attempt (n := n) u)
    (fallbackOutput : Fiber F n (dot u.val v.val)) (cap : ℕ) :
    letI := fiber_nonempty F n hn (dot u.val v.val)
    statisticalDistance
      (((Sampling.tapeDistribution (attemptDistribution hn u) cap).map
        (Sampling.sample (fun p => decide (rightOutput v p ≠ 0)) fallbackAttempt cap)).map
          (outputOr fallbackOutput))
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (dot u.val v.val))) ≤ (1/2 : ℝ)^cap := by
  classical
  letI := fiber_nonempty F n hn (dot u.val v.val)
  rw [← accepted_returned_uniform hn u v fallbackOutput]
  apply (statisticalDistance_map_le _ _ (outputOr fallbackOutput)).trans
  rw [Sampling.sample_distribution]
  have h := Sampling.capped_distance_le_of_acceptance (attemptDistribution hn u)
    (fun p => decide (rightOutput v p ≠ 0)) (FiniteDistribution.pure fallbackAttempt)
    (by norm_num : (0:ℝ) < 1/2) (attempt_acceptance_ge_half hn u v) cap
  norm_num only [show (1:ℝ)-1/2=1/2 by norm_num] at h
  exact h

/-- The capped executable sampler tends to the exact fresh distribution. In particular its limiting output distribution does not depend on either fallback. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): For fixed long shares and n ≥ 2, the statistical distance between the capped shortening output and the uniform short encoding of the same secret tends to zero as the attempt cap tends to infinity. -/
theorem capped_output_converges {n t : ℕ} (hn : 2 ≤ n) (u v : U F (n+t))
    (fallbackAttempt : Attempt (n := n) u)
    (fallbackOutput : Fiber F n (dot u.val v.val)) :
    letI := fiber_nonempty F n hn (dot u.val v.val)
    Filter.Tendsto (fun cap => statisticalDistance
      (((Sampling.tapeDistribution (attemptDistribution hn u) cap).map
        (Sampling.sample (fun p => decide (rightOutput v p ≠ 0)) fallbackAttempt cap)).map
          (outputOr fallbackOutput))
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (dot u.val v.val)))) Filter.atTop (nhds 0) := by
  classical
  letI := fiber_nonempty F n hn (dot u.val v.val)
  apply squeeze_zero (fun cap => statisticalDistance_nonneg _ _)
    (fun cap => capped_output_distance hn u v fallbackAttempt fallbackOutput cap)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Conditioning on an event of probability `p` changes a distribution by exactly `1-p`. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A a set; P ∈ 𝒟(A); accept ∈ A → Bool, assume A is finite; 0 < Sampling.acceptance(P, accept). Then

δ(P, Sampling.accepted(P, accept)) = 1 - Sampling.acceptance(P, accept).
-/
theorem accepted_distance {A : Type*} [Fintype A] (P : FiniteDistribution A) (accept : A → Bool)
    (hp : 0 < Sampling.acceptance P accept) :
    statisticalDistance P (Sampling.accepted P accept hp) = 1-Sampling.acceptance P accept := by
  classical
  let p := Sampling.acceptance P accept
  have hple : p ≤ 1 := Sampling.acceptance_le_one P accept
  have hpos : 0 < p := hp
  have hpoint (a : A) : |P.weight a - (Sampling.accepted P accept hp).weight a| =
      if accept a then (1-p) / p * P.weight a else P.weight a := by
    by_cases h : accept a = true
    · simp only [Sampling.accepted,h,ite_true]
      have he : P.weight a - P.weight a / p = -((1-p)/p * P.weight a) := by field_simp; ring
      rw [he,abs_neg,abs_of_nonneg (mul_nonneg (div_nonneg (by linarith) hpos.le) (P.nonneg a))]
    · simp [Sampling.accepted,h,P.nonneg a,abs_of_nonneg]
  have hsum : (∑ a, if accept a then (1-p)/p * P.weight a else P.weight a) =
      ((1-p)/p)*p+(1-p) := by
    have hi (a : A) : (if accept a then (1-p)/p * P.weight a else P.weight a) =
        ((1-p)/p)*(if accept a then P.weight a else 0) +
          (P.weight a-(if accept a then P.weight a else 0)) := by
      cases h : accept a <;> simp [h]
    simp_rw [hi]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,Finset.sum_sub_distrib,P.total]
    rfl
  simp only [statisticalDistance,variationNorm,hpoint,hsum]
  field_simp
  ring

/-- Every continuation after rejection is harmless up to its probability. It may expose arbitrary information about all subsequent retry tapes. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Z a set; n, t ∈ ℕ; u, v ∈ U(F, (n + t)); first, continuation ∈ Attempt(n = n, u) → 𝒟(Z), assume Z is finite; 2 ≤ n. Then

δ(bind(attemptDistribution(u), ((p ↦ { first(p) if rightOutput(v, p) ≠ 0,; continuation(p) otherwise }))), bind(Sampling.accepted(attemptDistribution(u), ((p ↦ decide((rightOutput(v, p) ≠ 0))))), first)) ≤ Sampling.acceptance(attemptDistribution(u), ((p ↦ decide((rightOutput(v, p) = 0))))).
-/
theorem retry_view_distance_le {Z : Type*} [Fintype Z] {n t : ℕ}
    (hn : 2 ≤ n) (u v : U F (n+t))
    (first continuation : Attempt (n := n) u → FiniteDistribution Z) :
    statisticalDistance
      ((attemptDistribution hn u).bind (fun p => if rightOutput v p ≠ 0 then first p else continuation p))
      ((Sampling.accepted (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0))
        (attempt_acceptance_pos hn u v)).bind first) ≤
      Sampling.acceptance (attemptDistribution hn u) (fun p => decide (rightOutput v p = 0)) := by
  classical
  let P := attemptDistribution hn u
  let accept := fun p : Attempt (n := n) u => decide (rightOutput v p ≠ 0)
  let Q := Sampling.accepted P accept (attempt_acceptance_pos hn u v)
  let κ := fun p : Attempt (n := n) u => if rightOutput v p ≠ 0 then first p else continuation p
  have hbind : Q.bind κ = Q.bind first := by
    ext z
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : rightOutput v p ≠ 0
    · simp [κ,h]
    · simp [Q,Sampling.accepted,accept,h]
  have h := statisticalDistance_bind_le P Q κ
  rw [hbind,accepted_distance] at h
  rw [attempt_acceptance_complement] at h
  simpa [P,Q,κ,accept] using h

/-- Binary retry error: statistical distance at most `2/N`, hence summed conditional probability error at most `4/N` when marginals agree. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Z a set; n, t ∈ ℕ; u, v ∈ U(F, (n + t)); first, continuation ∈ Attempt(n = n, u) → 𝒟(Z), assume Z is finite; |F| = 2; 2 ≤ n. Then

δ(bind(attemptDistribution(u), ((p ↦ { first(p) if rightOutput(v, p) ≠ 0,; continuation(p) otherwise }))), bind(Sampling.accepted(attemptDistribution(u), ((p ↦ decide((rightOutput(v, p) ≠ 0))))), first)) ≤ 2 / 2ⁿ.
-/
theorem binary_retry_view_distance_le {Z : Type*} [Fintype Z] {n t : ℕ}
    (hq : fieldCard F = 2) (hn : 2 ≤ n) (u v : U F (n+t))
    (first continuation : Attempt (n := n) u → FiniteDistribution Z) :
    statisticalDistance
      ((attemptDistribution hn u).bind (fun p => if rightOutput v p ≠ 0 then first p else continuation p))
      ((Sampling.accepted (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0))
        (attempt_acceptance_pos hn u v)).bind first) ≤ 2/(2:ℝ)^n :=
  (retry_view_distance_le hn u v first continuation).trans (binary_attempt_rejection_le hq hn u v)

end

end CircuitCompiler.Rectangular
