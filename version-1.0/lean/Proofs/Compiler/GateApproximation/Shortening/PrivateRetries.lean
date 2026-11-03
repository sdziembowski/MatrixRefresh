import Proofs.Compiler.GateApproximation.Shortening.RectangularMarkedObservation
import Proofs.Compiler.GateApproximation.Shortening.Retries



/-!
# Conditional retry control with additional private randomness
-/
set_option autoImplicit false

set_option maxHeartbeats 1400000

open scoped BigOperators

namespace CircuitCompiler.ShorteningTransport

open Refresh MatrixRefresh Sampling Rectangular

noncomputable section

/-- Averaging fixed-input conditional errors incurs no answer-count factor. The denominator is the common output marginal of every component. -/
-- Auxiliary lemma (shortening); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For I,Y,Z a set; P ∈ 𝒟(I); A, B ∈ I → 𝒟((Y × Z)); μ ∈ 𝒟(Y); ε ∈ ℝ; y ∈ Y; z ∈ Z, assume I is finite; Y is finite; Z is finite; ∀ i, |A(i)((y, z)) / μ(y) - B(i)((y, z)) / μ(y)| ≤ ε. Then

|bind(P, A)((y, z)) / μ(y) - bind(P, B)((y, z)) / μ(y)| ≤ ε.
-/
theorem bind_conditional_difference_le
    {I Y Z : Type*} [Fintype I] [Fintype Y] [Fintype Z]
    (P : FiniteDistribution I) (A B : I → FiniteDistribution (Y × Z)) (μ : FiniteDistribution Y)
    (ε : ℝ) (y : Y) (z : Z)
    (h : ∀ i, |(A i).weight (y,z) / μ.weight y -
      (B i).weight (y,z) / μ.weight y| ≤ ε) :
    |(P.bind A).weight (y,z) / μ.weight y -
      (P.bind B).weight (y,z) / μ.weight y| ≤ ε := by
  have he : (P.bind A).weight (y,z) / μ.weight y -
      (P.bind B).weight (y,z) / μ.weight y =
      P.expect (fun i => (A i).weight (y,z) / μ.weight y -
        (B i).weight (y,z) / μ.weight y) := by
    simp only [FiniteDistribution.bind, FiniteDistribution.expect, Finset.sum_div,
      mul_sub, mul_div_assoc, Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ P.expect (fun i => |(A i).weight (y,z) / μ.weight y -
        (B i).weight (y,z) / μ.weight y|) := by
      unfold FiniteDistribution.expect
      calc
        _ ≤ ∑ i, |P.weight i * ((A i).weight (y,z) / μ.weight y -
          (B i).weight (y,z) / μ.weight y)| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul, abs_of_nonneg (P.nonneg _)]
    _ ≤ ε := P.expect_le_const h

/-- Stochastic leakage of all rejected proposals still contains the exact first-success slice, including its additional private randomness. -/
-- Auxiliary lemma (shortening); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A,Z a set; P ∈ 𝒟(A); accept ∈ A → Bool; f ∈ Unbounded.StoppedTape(A) → 𝒟(Z); z ∈ Z, assume A is finite; Z is finite; 0 < acceptance(P, accept). Then

acceptance(P, accept) · Unbounded.firstAcceptedAnswerDistribution(P, accept, f)(z) ≤ Unbounded.observeDistribution(P, accept, f)(z).
-/
theorem firstAcceptedAnswerDistribution_domination {A Z : Type*} [Fintype A] [Fintype Z]
    (P : FiniteDistribution A) (accept : A → Bool) (hp : 0 < acceptance P accept)
    (f : Unbounded.StoppedTape A → FiniteDistribution Z) (z : Z) :
    acceptance P accept * (Unbounded.firstAcceptedAnswerDistribution P accept hp f).weight z ≤
      (Unbounded.observeDistribution P accept hp f).weight z := by
  rw [← Unbounded.flaggedAnswerDistribution_true_weight]
  rw [← Unbounded.flaggedAnswerDistribution_map P accept hp f, map_snd_weight]
  exact Finset.single_le_sum
    (fun b _ => (Unbounded.flaggedAnswerDistribution P accept hp f).nonneg (b,z))
    (Finset.mem_univ true)

-- Auxiliary lemma (shortening); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Y,Z a set; P ∈ 𝒟(Z); y ∈ Y, assume Y is finite; Z is finite. Then

((Prod)₁_*(((z ↦ (y, z)))_*P)) = FiniteDistribution.pure(y).
-/
private theorem tag_fst {Y Z : Type*} [Fintype Y] [Fintype Z]
    (P : FiniteDistribution Z) (y : Y) :
    (P.map (fun z => (y,z))).map Prod.fst = FiniteDistribution.pure y := by
  classical
  rw [FiniteDistribution.map_map]
  ext x
  simp only [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.pure, Function.comp_def]
  by_cases h : y = x
  · simp [h, P.total]
  · simp [h, Ne.symm h]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Conditional per-answer retry bound for any stochastic observation of the full tape. Via `marked_observe_eq_distribution`, this includes all raw private marks in the actual rectangular sampler. -/
-- Auxiliary lemma (shortening); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Fix a long pair (u,v), with n ≥ 2, a short encoding o of its secret s, and an answer z. Let P_(∞) be the joint output/answer distribution from the full rejection loop and P₁ the distribution from the first attempt conditioned on acceptance. The leakage observation may itself be randomized. Writing μₛ for the uniform short encoding distribution,

|P_(∞)(o,z)/μₛ(o)-P₁(o,z)/μₛ(o)| ≤ Pr[one attempt rejects].
-/
theorem fullTapeConditionalAnswer_conditional_answer_difference {Z : Type*} [Fintype Z]
    {n t : ℕ} (hn : 2 ≤ n) (u v : U F (n+t))
    (fallback : Fiber F n (dot u.val v.val))
    (leak : FullTape (n := n) u → FiniteDistribution Z)
    (out : Fiber F n (dot u.val v.val)) (z : Z) :
    letI := fiber_nonempty F n hn (dot u.val v.val)
    let f := fun tape : FullTape (n := n) u =>
      (leak tape).map (fun z => (outputOr fallback tape.2.2,z))
    let μ := (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (dot u.val v.val)))
    |(fullTapeAnswerDistribution hn u v f).weight (out,z) / μ.weight out -
      (Unbounded.firstAcceptedAnswerDistribution (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0))
        (attempt_acceptance_pos hn u v) f).weight (out,z) / μ.weight out| ≤
      acceptance (attemptDistribution hn u) (fun p => decide (rightOutput v p = 0)) := by
  classical
  letI := fiber_nonempty F n hn (dot u.val v.val)
  let f := fun tape : FullTape (n := n) u =>
    (leak tape).map (fun z => (outputOr fallback tape.2.2,z))
  let μ := (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (dot u.val v.val)))
  let P := fullTapeAnswerDistribution hn u v f
  let Q := Unbounded.firstAcceptedAnswerDistribution (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0))
    (attempt_acceptance_pos hn u v) f
  have hf (tape : FullTape (n := n) u) :
      (f tape).map Prod.fst = FiniteDistribution.pure (outputOr fallback tape.2.2) :=
    tag_fst _ _
  have hP : P.map Prod.fst = μ := by
    change (Unbounded.observeDistribution _ _ _ f).map Prod.fst = μ
    rw [Unbounded.observeDistribution_map]
    simp_rw [hf]
    rw [Unbounded.observeDistribution_pure]
    exact fullTape_returned_uniform hn u v fallback
  have hQ : Q.map Prod.fst = μ := by
    change ((accepted _ _ _).bind _).map Prod.fst = μ
    rw [FiniteDistribution.map_bind]
    simp_rw [hf]
    exact accepted_returned_uniform hn u v fallback
  have hμ : 0 < μ.weight out := by
    change 0 < (Fintype.card (Fiber F n (dot u.val v.val)) : ℝ)⁻¹
    positivity
  have h := conditional_difference_le_of_domination P Q μ
    (acceptance (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0)))
    (attempt_acceptance_pos hn u v).le (acceptance_le_one _ _) hP hQ
    (fun y z => firstAcceptedAnswerDistribution_domination _ _ _ f (y,z)) out z hμ
  rw [attempt_acceptance_complement] at h
  simpa only [sub_sub_cancel] using h

/-- Binary conditional retry bound with arbitrary private-tape randomness. -/

/-
Mathematical statement (normal notation): Fix a binary long input pair (u,v), a short output encoding o of the same secret, and a leakage answer z. Assume n ≥ 2, and allow any finite observation of the complete shortening retry tape. Let P_retry be its joint output/answer distribution and P_accepted the first-attempt distribution conditioned on acceptance. With μₛ the uniform short encoding distribution,

|(P_retry(o,z))/(μₛ(o))- (P_accepted(o,z))/(μₛ(o))| ≤ 2/2ⁿ.

The bound is pointwise in both o and z.
-/
theorem binary_fullTapeConditionalAnswer_conditional_answer_difference {Z : Type*} [Fintype Z]
    {n t : ℕ} (hq : fieldCard F = 2) (hn : 2 ≤ n) (u v : U F (n+t))
    (fallback : Fiber F n (dot u.val v.val))
    (leak : FullTape (n := n) u → FiniteDistribution Z)
    (out : Fiber F n (dot u.val v.val)) (z : Z) :
    letI := fiber_nonempty F n hn (dot u.val v.val)
    let f := fun tape : FullTape (n := n) u =>
      (leak tape).map (fun z => (outputOr fallback tape.2.2,z))
    let μ := (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (dot u.val v.val)))
    |(fullTapeAnswerDistribution hn u v f).weight (out,z) / μ.weight out -
      (Unbounded.firstAcceptedAnswerDistribution (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0))
        (attempt_acceptance_pos hn u v) f).weight (out,z) / μ.weight out| ≤
      2 / (2 : ℝ)^n :=
  (fullTapeConditionalAnswer_conditional_answer_difference hn u v fallback leak out z).trans
    (binary_attempt_rejection_le hq hn u v)

end

end CircuitCompiler.ShorteningTransport
