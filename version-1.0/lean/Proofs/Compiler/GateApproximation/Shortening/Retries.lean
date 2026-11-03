import Proofs.Compiler.GateApproximation.Shortening.RectangularUnbounded
import Proofs.Compiler.Foundations.MatrixRefreshing.Protocol.Endpoints



/-!
# Pointwise conditional retry error for rectangular shortening

The common fresh-output marginal prevents conditioning on the returned encoding from magnifying the retry error. Observations may inspect the complete stopped tape, including every rejected proposal.
-/

set_option autoImplicit false

set_option maxHeartbeats 1200000

open scoped BigOperators

namespace CircuitCompiler.ShorteningTransport

open Refresh MatrixRefresh Sampling Rectangular

noncomputable section

/-- If two joint distributions have the same first marginal, and one contains at least a `p` fraction of the other at every atom, conditioning on any positive-mass first-coordinate value changes every answer probability by at most `1-p`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Y,Z a set; P, Q ∈ 𝒟((Y × Z)); μ ∈ 𝒟(Y); p ∈ ℝ; y ∈ Y; z ∈ Z, assume Y is finite; Z is finite; 0 ≤ p; p ≤ 1; ((Prod)₁_*P) = μ; ((Prod)₁_*Q) = μ; ∀ y, z, p · Q((y, z)) ≤ P((y, z)); 0 < μ(y). Then

|P((y, z)) / μ(y) - Q((y, z)) / μ(y)| ≤ 1 - p.
-/
theorem conditional_difference_le_of_domination
    {Y Z : Type*} [Fintype Y] [Fintype Z]
    (P Q : FiniteDistribution (Y × Z)) (μ : FiniteDistribution Y) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hP : P.map Prod.fst = μ) (hQ : Q.map Prod.fst = μ)
    (hdom : ∀ y z, p * Q.weight (y,z) ≤ P.weight (y,z))
    (y : Y) (z : Z) (hy : 0 < μ.weight y) :
    |P.weight (y,z) / μ.weight y - Q.weight (y,z) / μ.weight y| ≤ 1-p := by
  classical
  have hQle : Q.weight (y,z) ≤ μ.weight y := by
    simpa [hQ] using joint_weight_le_fst Q y z
  have hres : P.weight (y,z) - p * Q.weight (y,z) ≤ (1-p) * μ.weight y := by
    calc
      P.weight (y,z) - p * Q.weight (y,z) ≤
          ∑ w, (P.weight (y,w) - p * Q.weight (y,w)) :=
        Finset.single_le_sum (fun w _ => sub_nonneg.mpr (hdom y w)) (Finset.mem_univ z)
      _ = (1-p) * μ.weight y := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← map_fst_weight P y, ← map_fst_weight Q y, hP, hQ]
        ring
  rw [← sub_div, abs_div, abs_of_pos hy]
  apply (div_le_iff₀ hy).2
  apply abs_le.mpr
  constructor
  · nlinarith [hdom y z, mul_le_mul_of_nonneg_left hQle (sub_nonneg.mpr hp1)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (Q.nonneg (y,z))]

/-- The full stopped-tape distribution contains its first-success slice with exactly the acceptance probability as coefficient. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A,Z a set; P ∈ 𝒟(A); accept ∈ A → Bool; f ∈ Unbounded.StoppedTape(A) → Z; z ∈ Z, assume A is finite; Z is finite; 0 < acceptance(P, accept). Then

acceptance(P, accept) · Unbounded.firstView(P, accept, f)(z) ≤ Unbounded.observe(P, accept, f)(z).
-/
theorem firstView_domination {A Z : Type*} [Fintype A] [Fintype Z]
    (P : FiniteDistribution A) (accept : A → Bool) (hp : 0 < acceptance P accept)
    (f : Unbounded.StoppedTape A → Z) (z : Z) :
    acceptance P accept * (Unbounded.firstView P accept hp f).weight z ≤
      (Unbounded.observe P accept hp f).weight z := by
  rw [← Unbounded.flaggedView_true_weight]
  rw [← Unbounded.flaggedView_map P accept hp f, map_snd_weight]
  exact Finset.single_le_sum
    (fun b _ => (Unbounded.flaggedView P accept hp f).nonneg (b,z))
    (Finset.mem_univ true)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Conditioning on the returned short encoding does not increase the first-attempt retry error, for an arbitrary finite observation of all attempts. This is a pointwise statement about each answer, not just joint statistical distance. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Fix a long pair (u,v), with n ≥ 2, a short encoding o of its secret s, and an answer z. Let P_(∞) be the joint output/answer distribution from the full rejection loop and P₁ the distribution from the first attempt conditioned on acceptance. The leakage observation is an arbitrary deterministic finite function of the tape. Writing μₛ for the uniform short encoding distribution,

|P_(∞)(o,z)/μₛ(o)-P₁(o,z)/μₛ(o)| ≤ Pr[one attempt rejects].
-/
theorem fullTape_conditional_answer_difference {Z : Type*} [Fintype Z]
    {n t : ℕ} (hn : 2 ≤ n) (u v : U F (n+t))
    (fallback : Fiber F n (dot u.val v.val))
    (leak : FullTape (n := n) u → Z)
    (out : Fiber F n (dot u.val v.val)) (z : Z) :
    letI := fiber_nonempty F n hn (dot u.val v.val)
    let f := fun tape : FullTape (n := n) u => (outputOr fallback tape.2.2, leak tape)
    let μ := (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (dot u.val v.val)))
    |(fullTapeObserve hn u v f).weight (out,z) / μ.weight out -
      (Unbounded.firstView (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0))
        (attempt_acceptance_pos hn u v) f).weight (out,z) / μ.weight out| ≤
      acceptance (attemptDistribution hn u) (fun p => decide (rightOutput v p = 0)) := by
  classical
  letI := fiber_nonempty F n hn (dot u.val v.val)
  let f := fun tape : FullTape (n := n) u => (outputOr fallback tape.2.2, leak tape)
  let μ := (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (dot u.val v.val)))
  let P := fullTapeObserve hn u v f
  let Q := Unbounded.firstView (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0))
    (attempt_acceptance_pos hn u v) f
  have hP : P.map Prod.fst = μ := by
    change (Unbounded.observe _ _ _ f).map Prod.fst = μ
    rw [Unbounded.observe_map]
    exact fullTape_returned_uniform hn u v fallback
  have hQ : Q.map Prod.fst = μ := by
    change ((accepted _ _ _).map _).map Prod.fst = μ
    rw [FiniteDistribution.map_map]
    exact accepted_returned_uniform hn u v fallback
  have hμ : 0 < μ.weight out := by
    change 0 < (Fintype.card (Fiber F n (dot u.val v.val)) : ℝ)⁻¹
    positivity
  have h := conditional_difference_le_of_domination P Q μ
    (acceptance (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0)))
    (attempt_acceptance_pos hn u v).le (acceptance_le_one _ _) hP hQ
    (fun y z => firstView_domination _ _ _ f (y,z)) out z hμ
  rw [attempt_acceptance_complement] at h
  simpa only [sub_sub_cancel] using h

/-- Binary-field conditional retry error, uniform in the fixed long inputs, the returned encoding, and the answer. This is stronger than the manuscript's `4 / 2^n` allowance. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Fix a long pair (u,v), with n ≥ 2, a short encoding o of its secret s, and an answer z. Let P_(∞) be the joint output/answer distribution from the full rejection loop and P₁ the distribution from the first attempt conditioned on acceptance. The leakage observation is an arbitrary deterministic finite function of the tape. Writing μₛ for the uniform short encoding distribution,

|P_(∞)(o,z)/μₛ(o)-P₁(o,z)/μₛ(o)| ≤ 2/2ⁿ. This specialization assumes the binary field.
-/
theorem binary_fullTape_conditional_answer_difference {Z : Type*} [Fintype Z]
    {n t : ℕ} (hq : fieldCard F = 2) (hn : 2 ≤ n) (u v : U F (n+t))
    (fallback : Fiber F n (dot u.val v.val))
    (leak : FullTape (n := n) u → Z)
    (out : Fiber F n (dot u.val v.val)) (z : Z) :
    letI := fiber_nonempty F n hn (dot u.val v.val)
    let f := fun tape : FullTape (n := n) u => (outputOr fallback tape.2.2, leak tape)
    let μ := (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (dot u.val v.val)))
    |(fullTapeObserve hn u v f).weight (out,z) / μ.weight out -
      (Unbounded.firstView (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0))
        (attempt_acceptance_pos hn u v) f).weight (out,z) / μ.weight out| ≤
      2 / (2 : ℝ)^n := by
  exact (fullTape_conditional_answer_difference hn u v fallback leak out z).trans
    (binary_attempt_rejection_le hq hn u v)

end

end CircuitCompiler.ShorteningTransport
