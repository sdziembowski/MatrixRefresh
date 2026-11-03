import Proofs.Compiler.GateApproximation.Shortening.RectangularForward
import Proofs.Compiler.GateApproximation.Shortening.RectangularL1
import Proofs.Compiler.GateApproximation.Shortening.RectangularRetries
import Proofs.Compiler.GateApproximation.Shortening.ShorteningAnswerProbabilities
import Proofs.Compiler.Construction.Parameters



/-!
# The physical rectangular sampler and its conditional reverse distribution

The successful forward choices are those of the actual sampler: a uniform short row, followed by a uniform full-rank completion, conditioned on a nonzero right output.  Their reverse disintegration samples a uniform short encoding, a uniform full-rank matrix, and a uniform vector in its kernel.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace CircuitCompiler.Rectangular

open Refresh MatrixRefresh Shortening

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Changing coordinates on the long input preserves every accepted choice. -/
/- Mathematical definition (normal notation): For an invertible long matrix M, send a successful choice (A,H) for (u,v) to (A,H · M) for (u · M,M⁻¹ · v). This is a bijection, with inverse using M⁻¹, and leaves the short output (A,H · v) unchanged. -/
def successRefreshEquiv {n m : ℕ} (u v : U F m) (M : Refresh.«GL» F m) :
    Success (n := n) u v ≃ Success (n := n) (rowRefresh u M) (columnRefresh v M) where
  toFun p := ⟨⟨(p.val.val.1,⟨p.val.val.2.val * M.val,
    fullRowRank_right p.val.val.2 M⟩), by
      change Matrix.vecMul p.val.val.1.val (p.val.val.2.val * M.val) = _
      rw [← Matrix.vecMul_vecMul,p.val.property]
      rfl⟩, by
        simpa [rightOutput,columnRefresh,Matrix.mulVec_mulVec,Matrix.mul_assoc]
          using p.property⟩
  invFun p := ⟨⟨(p.val.val.1,⟨p.val.val.2.val * (M⁻¹).val,
    fullRowRank_right p.val.val.2 M⁻¹⟩), by
      rw [← Matrix.vecMul_vecMul,p.val.property]
      simp [rowRefresh,Matrix.vecMul_vecMul]⟩, by
        change (p.val.val.2.val * (M⁻¹).val).mulVec v.val ≠ 0
        simpa [rightOutput,columnRefresh,Matrix.mulVec_mulVec] using p.property⟩
  left_inv p := by
    apply Subtype.ext; apply Subtype.ext; apply Prod.ext
    · rfl
    · apply Subtype.ext; simp [Matrix.mul_assoc]
  right_inv p := by
    apply Subtype.ext; apply Subtype.ext; apply Prod.ext
    · rfl
    · apply Subtype.ext; simp [Matrix.mul_assoc]

/-- Acceptance does not reweight long encodings within a fixed secret fiber. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; s ∈ F; x, y ∈ Fiber(F, m, s), we have

|Success(n = n, x.val.L, x.val.R)| = |Success(n = n, y.val.L, y.val.R)|.
-/
theorem success_card_independent_input {n m : ℕ} {s : F} (x y : Fiber F m s) :
    Fintype.card (Success (n := n) x.val.L x.val.R) =
      Fintype.card (Success (n := n) y.val.L y.val.R) := by
  obtain ⟨M,hM⟩ := refresh_transitive x.val y.val (x.property.trans y.property.symm)
  have hL : rowRefresh x.val.L M = y.val.L := congrArg State.L hM
  have hR : columnRefresh x.val.R M = y.val.R := congrArg State.R hM
  simpa only [hL,hR] using Fintype.card_congr (successRefreshEquiv (n := n) x.val.L x.val.R M)

/-- Sampling an accepted attempt separately for each long encoding is uniform on the complete reverse record space. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): For n ≥ 2, sample a uniform long encoding of s, then uniformly sample a successful shortening attempt for that encoding. Rewriting the result as a reverse record gives the uniform distribution on all reverse records of secret s. -/
theorem accepted_forward_reverse_distribution {n t : ℕ} (hn : 2 ≤ n) (s : F)
    [Nonempty (Fiber F n s)] [Nonempty (Fiber F (n+t) s)]
    [Nonempty (FullRank F n (n+t))] :
    letI : ∀ x : Fiber F (n+t) s, Nonempty (Success (n := n) x.val.L x.val.R) :=
      fun x => success_nonempty hn x.val.L x.val.R
    (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) s)).bind (fun x =>
      (FiniteDistribution.uniform : FiniteDistribution (Success (n := n) x.val.L x.val.R)).map
        (fun p => successfulJointEquiv s ⟨x,p⟩)) =
      (FiniteDistribution.uniform : FiniteDistribution (Backward F n (n+t) s)) := by
  classical
  letI : ∀ x : Fiber F (n+t) s, Nonempty (Success (n := n) x.val.L x.val.R) :=
    fun x => success_nonempty hn x.val.L x.val.R
  let x₀ : Fiber F (n+t) s := Classical.choice inferInstance
  letI : Nonempty (SuccessfulJoint F n (n+t) s) := ⟨⟨x₀,Classical.choice inferInstance⟩⟩
  have h := uniform_sigma_bind (J := fun x : Fiber F (n+t) s =>
    Success (n := n) x.val.L x.val.R) x₀ (fun x => success_card_independent_input x x₀)
  have h' := congrArg (fun P => P.map (successfulJointEquiv (F := F) (n := n) (m := n+t) s)) h
  simpa only [FiniteDistribution.map_bind,FiniteDistribution.map_map,Function.comp_def,uniform_equiv] using h'

/-- Full reverse disintegration, including all communicated and private values. -/

/- Mathematical statement (normal notation): Fix the secret s. Independently sample a short pair (A,R') ∼ μₛ and a uniform full-row-rank n × (n+t) matrix H, then sample a uniform vector from ker H. Combining these data through the reverse-record construction gives exactly the uniform distribution on reverse records. The stated nonemptiness assumptions ensure these uniform distributions exist. -/
theorem reverse_record_distribution {n t : ℕ} (s : F) [Nonempty (Fiber F n s)]
    [Nonempty (FullRank F n (n+t))] :
    (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s)).bind (fun p =>
      (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).bind (fun H =>
        (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).map (reverseRecord p H))) =
      (FiniteDistribution.uniform : FiniteDistribution (Backward F n (n+t) s)) := by
  classical
  let p₀ := Classical.choice (inferInstance : Nonempty (Fiber F n s))
  let H₀ := Classical.choice (inferInstance : Nonempty (FullRank F n (n+t)))
  let J := fun p : Fiber F n s => (H : FullRank F n (n+t)) × Preimage H p.val.R
  letI : ∀ p, Nonempty (J p) := fun p => ⟨⟨H₀,Classical.choice inferInstance⟩⟩
  letI : Nonempty ((p : Fiber F n s) × J p) := ⟨⟨p₀,Classical.choice inferInstance⟩⟩
  have hout := uniform_sigma_bind (J := J) p₀
    (fun p => by simp [J,Fintype.card_sigma,preimage_card])
  have hin (p : Fiber F n s) := uniform_sigma_bind
    (J := fun H : FullRank F n (n+t) => Preimage H p.val.R) H₀
      (fun H => by simp [preimage_card])
  rw [← uniform_equiv (backwardSigmaEquiv (F := F) (n := n) (m := n+t) s).symm,
    ← hout, FiniteDistribution.map_bind]
  simp only [FiniteDistribution.map_map]
  simp_rw [← hin,FiniteDistribution.map_bind,FiniteDistribution.map_map]
  congr 1
  funext p
  congr 1
  funext H
  rw [← uniform_equiv (preimageEquivKernel H p.val.R).symm,FiniteDistribution.map_map]
  rfl

/-- Observing the actual proposal distribution conditioned on first-attempt success is exactly observing a uniform successful choice. No new sampler is postulated. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): For fixed long shares (u,v) and n ≥ 2, condition one shortening attempt on producing a nonzero right output. Any subsequent randomized observation has exactly the same distribution as when the attempt is sampled uniformly from all successful attempts for (u,v). -/
theorem accepted_sample_observation {Z : Type*} [Fintype Z] {n t : ℕ}
    (hn : 2 ≤ n) (u v : U F (n+t)) (observe : Attempt (n := n) u → FiniteDistribution Z) :
    letI := success_nonempty hn u v
    (Sampling.accepted (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0))
      (attempt_acceptance_pos hn u v)).bind observe =
      (FiniteDistribution.uniform : FiniteDistribution (Success (n := n) u v)).bind (fun p => observe p.val) := by
  letI := success_nonempty hn u v
  rw [accepted_attemptDistribution]
  simp [FiniteDistribution.map,FiniteDistribution.bind_assoc]

/-- Forward successful execution, retaining both the returned encoding and an arbitrary finite observation of all values in the successful attempt. -/
/- Mathematical definition (normal notation): Sample a uniform long encoding of s, then a uniform successful shortening attempt for that encoding. Return its short encoding together with an arbitrary finite observation sampled from the successful record. This defines the joint output-and-observation distribution of successful forward execution. -/
def acceptedObservation {Z : Type*} [Fintype Z] {n t : ℕ}
    (hn : 2 ≤ n) (s : F) [Nonempty (Fiber F (n+t) s)]
    (observe : Backward F n (n+t) s → FiniteDistribution Z) : FiniteDistribution (Fiber F n s × Z) := by
  letI : ∀ x : Fiber F (n+t) s, Nonempty (Success (n := n) x.val.L x.val.R) :=
    fun x => success_nonempty hn x.val.L x.val.R
  exact (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) s)).bind fun x =>
    (FiniteDistribution.uniform : FiniteDistribution (Success (n := n) x.val.L x.val.R)).bind fun a =>
      let p := successfulJointEquiv s ⟨x,a⟩
      (observe p).map (fun z => (p.val.1,z))

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X,Z a set; P ∈ 𝒟(X); K ∈ X → 𝒟(Z), assume X is finite; Z is finite. Then

P.joint(K) = bind(P, ((x ↦ (((z ↦ (x, z)))_*K(x))))).
-/
private theorem joint_eq_bind_map {X Z : Type*} [Fintype X] [Fintype Z]
    (P : FiniteDistribution X) (K : X → FiniteDistribution Z) :
    P.joint K = P.bind (fun x => (K x).map (fun z => (x,z))) := by
  classical
  ext ⟨x,z⟩
  simp [FiniteDistribution.joint,FiniteDistribution.map,FiniteDistribution.bind,FiniteDistribution.pure,ite_and,mul_ite]

/-- The actual accepted forward observation has the reverse conditional distribution, including the output, rather than merely matching its output marginal. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Z a set; n, t ∈ ℕ; s ∈ F; observe ∈ Backward(F, n, (n + t), s) → 𝒟(Z), assume Z is finite; 2 ≤ n; Fiber(F, n, s) ≠ ∅; Fiber(F, (n + t), s) ≠ ∅; FullRank(F, n, (n + t)) ≠ ∅. Then

acceptedObservation(s, observe) = joint(𝒰_(Fiber(F, n, s)))(recordAnswerDistribution(observe)) .
-/
theorem accepted_observation_disintegration {Z : Type*} [Fintype Z] {n t : ℕ}
    (hn : 2 ≤ n) (s : F) [Nonempty (Fiber F n s)] [Nonempty (Fiber F (n+t) s)]
    [Nonempty (FullRank F n (n+t))]
    (observe : Backward F n (n+t) s → FiniteDistribution Z) :
    acceptedObservation hn s observe =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s)).joint (recordAnswerDistribution observe) := by
  classical
  letI : ∀ x : Fiber F (n+t) s, Nonempty (Success (n := n) x.val.L x.val.R) :=
    fun x => success_nonempty hn x.val.L x.val.R
  let obs := fun p : Backward F n (n+t) s => (observe p).map (fun z => (p.val.1,z))
  have hf := congrArg (fun P : FiniteDistribution (Backward F n (n+t) s) => P.bind obs)
    (accepted_forward_reverse_distribution hn s)
  simp only [FiniteDistribution.map,FiniteDistribution.bind_assoc,FiniteDistribution.pure_bind] at hf
  change acceptedObservation hn s observe = _ at hf
  rw [hf,← reverse_record_distribution s]
  rw [joint_eq_bind_map]
  simp only [FiniteDistribution.bind_assoc,FiniteDistribution.map,FiniteDistribution.pure_bind,recordAnswerDistribution]
  rfl

/-- A finite first-attempt observation, with an arbitrary unused value on rejected attempts. Its successful branch is the complete physical record. -/
/-
Mathematical definition (normal notation): For Z a set; n, m ∈ ℕ; s ∈ F; observe ∈ Backward(F, n, m, s) → 𝒟(Z); fallback ∈ 𝒟((Fiber(F, n, s) × Z)); x ∈ Fiber(F, m, s); a ∈ Attempt(n = n, x.val.L), assume Z is finite. define

firstAttemptView(observe, fallback, x, a) := { Let p := successfulJointEquiv(s, (x, (a, h))); (((z ↦ ((p)₁, z)))_*observe(p)) if rightOutput(x.val.R, a) ≠ 0,; fallback otherwise }.
-/
def firstAttemptView {Z : Type*} [Fintype Z] {n m : ℕ} {s : F}
    (observe : Backward F n m s → FiniteDistribution Z)
    (fallback : FiniteDistribution (Fiber F n s × Z))
    (x : Fiber F m s) (a : Attempt (n := n) x.val.L) : FiniteDistribution (Fiber F n s × Z) :=
  if h : rightOutput x.val.R a ≠ 0 then
    let p := successfulJointEquiv s ⟨x,⟨a,h⟩⟩
    (observe p).map (fun z => (p.val.1,z))
  else fallback

/-- A uniform-success description is exactly the actual first-attempt sampler conditioned on acceptance; the fallback is irrelevant. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Z a set; n, t ∈ ℕ; s ∈ F; observe ∈ Backward(F, n, (n + t), s) → 𝒟(Z); fallback ∈ 𝒟((Fiber(F, n, s) × Z)), assume Z is finite; 2 ≤ n; Fiber(F, (n + t), s) ≠ ∅. Then

acceptedObservation(s, observe) = bind(𝒰_(Fiber(F, (n + t), s)), ((x ↦ bind(Sampling.accepted(attemptDistribution(x.val.L), ((a ↦ decide((rightOutput(x.val.R, a) ≠ 0))))), firstAttemptView(observe, fallback, x))))).
-/
theorem acceptedObservation_eq_accepted_attempts {Z : Type*} [Fintype Z] {n t : ℕ}
    (hn : 2 ≤ n) (s : F) [Nonempty (Fiber F (n+t) s)]
    (observe : Backward F n (n+t) s → FiniteDistribution Z)
    (fallback : FiniteDistribution (Fiber F n s × Z)) :
    acceptedObservation hn s observe =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) s)).bind (fun x =>
        (Sampling.accepted (attemptDistribution hn x.val.L)
          (fun a => decide (rightOutput x.val.R a ≠ 0))
          (attempt_acceptance_pos hn x.val.L x.val.R)).bind
          (firstAttemptView observe fallback x)) := by
  classical
  letI : ∀ x : Fiber F (n+t) s, Nonempty (Success (n := n) x.val.L x.val.R) :=
    fun x => success_nonempty hn x.val.L x.val.R
  unfold acceptedObservation
  congr 1
  funext x
  rw [accepted_sample_observation]
  congr 1
  funext a
  simp [firstAttemptView,a.property]

/-- Even arbitrary observations after rejection change the accepted physical joint distribution by at most the actual first-attempt rejection probability. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Z a set; n, t ∈ ℕ; s ∈ F; observe ∈ Backward(F, n, (n + t), s) → 𝒟(Z); fallback ∈ 𝒟((Fiber(F, n, s) × Z)); continuation ∈ ∏_(x ∈ Fiber(F, (n + t), s)) Attempt(n = n, x.val.L) → 𝒟((Fiber(F, n, s) × Z)), assume Z is finite; |F| = 2; 2 ≤ n; Fiber(F, (n + t), s) ≠ ∅. Then

δ(bind(𝒰_(Fiber(F, (n + t), s)), ((x ↦ bind(attemptDistribution(x.val.L), ((a ↦ { firstAttemptView(observe, fallback, x, a) if rightOutput(x.val.R, a) ≠ 0,; continuation(x, a) otherwise })))))), acceptedObservation(s, observe)) ≤ 2 / 2ⁿ.
-/
theorem binary_retry_observation_distance {Z : Type*} [Fintype Z] {n t : ℕ}
    (hq : fieldCard F = 2) (hn : 2 ≤ n) (s : F) [Nonempty (Fiber F (n+t) s)]
    (observe : Backward F n (n+t) s → FiniteDistribution Z)
    (fallback : FiniteDistribution (Fiber F n s × Z))
    (continuation : (x : Fiber F (n+t) s) → Attempt (n := n) x.val.L →
      FiniteDistribution (Fiber F n s × Z)) :
    statisticalDistance
      ((FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) s)).bind (fun x =>
        (attemptDistribution hn x.val.L).bind (fun a =>
          if rightOutput x.val.R a ≠ 0 then firstAttemptView observe fallback x a
          else continuation x a)))
      (acceptedObservation hn s observe) ≤ 2/(2:ℝ)^n := by
  rw [acceptedObservation_eq_accepted_attempts hn s observe fallback]
  have h := Sampling.bind_distance_le
    (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) s)) FiniteDistribution.uniform _ _
    (fun x => binary_retry_view_distance_le hq hn x.val.L x.val.R
      (firstAttemptView observe fallback x) (continuation x))
  simpa only [statisticalDistance_self,zero_add] using h

end

end CircuitCompiler.Rectangular
