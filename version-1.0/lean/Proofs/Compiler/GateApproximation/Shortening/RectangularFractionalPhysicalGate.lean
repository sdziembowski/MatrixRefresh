import Proofs.Compiler.GateApproximation.Shortening.RectangularFractionalAnswerProbabilities
import Proofs.Compiler.GateApproximation.Shortening.RectangularPhysicalGate
import Proofs.Compiler.GateApproximation.Shortening.RectangularPhysicalStochastic
import Proofs.Compiler.Construction.Parameters



/-!
# Rectangular gates with arbitrary conditional private-tape distributions

Shortening answers are stochastic finite observations of the complete outer retry tape. Their first-success restriction is a fractional local answer distribution, so input-dependent conditional sampler tapes are retained by the interface.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

open scoped BigOperators

namespace CircuitCompiler.Rectangular.Fractional

open Refresh MatrixRefresh Shortening RefreshAnalysis TableAnalysis

noncomputable section

variable {F O A B : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [DecidableEq O] [Nonempty O] [Fintype A] [Fintype B]

variable {n t : ℕ}

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X,Y,Z a set; P ∈ 𝒟(X); Q ∈ X → 𝒟(Y); R ∈ X → Y → 𝒟(Z), assume X is finite; Y is finite; Z is finite. Then

bind(P.joint(Q), ((xy ↦ R((xy)₁, (xy)₂)))) = bind(P, ((x ↦ bind(Q(x), R(x))))).
-/
private theorem bind_joint {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (P : FiniteDistribution X) (Q : X → FiniteDistribution Y) (R : X → Y → FiniteDistribution Z) :
    (P.joint Q).bind (fun xy => R xy.1 xy.2) = P.bind (fun x => (Q x).bind (R x)) := by
  ext z
  simp only [FiniteDistribution.bind,FiniteDistribution.joint,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

/-- Reordering the matrix phase is an exact equality, not a security hybrid. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ O → U(F, (n + t)); p ∈ TableRectanglePartition(O, GL_(n + t)(F), A); o ∈ O × O; fallback ∈ Fiber(F, n, gateSecret(a, b, o)); leak ∈ ∏_(x ∈ Fiber(F, (n + t), gateSecret(a, b, o))) A → FullTape(n = n, x.val.L) → 𝒟(B), assume 2 ≤ n; Fiber(F, (n + t), gateSecret(a, b, o)) ≠ ∅. Then

fullGateExecution(a, b, p, o, fallback, leak) = bind(𝒰_(Fiber(F, (n + t), gateSecret(a, b, o))), ((x ↦ bind(longAnswer(a, b, p, o, x), shorteningExecution(fallback, leak, x))))).
-/
theorem fullGateExecution_eq_long (hn : 2 ≤ n) (a b : O → U F (n+t))
    (p : TableRectanglePartition O (Refresh.«GL» F (n+t)) A) (o : O × O)
    [Nonempty (Fiber F (n+t) (gateSecret a b o))]
    (fallback : Fiber F n (gateSecret a b o))
    (leak : (x : Fiber F (n+t) (gateSecret a b o)) → A → FullTape (n := n) x.val.L → FiniteDistribution B) :
    fullGateExecution hn a b p o fallback leak =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) (gateSecret a b o))).bind (fun x =>
        (longAnswer a b p o x).bind (shorteningExecution hn fallback leak x)) := by
  have h := congrArg (fun P : FiniteDistribution (Fiber F (n+t) (gateSecret a b o) × A) =>
    P.bind (fun xa => shorteningExecution hn fallback leak xa.1 xa.2))
    (matrix_phase_fiber_canonical a b p o)
  rw [bind_joint] at h
  simpa only [FiniteDistribution.map,FiniteDistribution.bind_assoc,FiniteDistribution.pure_bind,fullGateExecution] using h

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X,Y,Z a set; P ∈ 𝒟(X); Q ∈ 𝒟(Y); R ∈ X → Y → 𝒟(Z), assume X is finite; Y is finite; Z is finite. Then

bind(P, ((x ↦ bind(Q, R(x))))) = bind(Q, ((y ↦ bind(P, ((x ↦ R(x, y))))))).
-/
private theorem bind_comm {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (P : FiniteDistribution X) (Q : FiniteDistribution Y) (R : X → Y → FiniteDistribution Z) :
    P.bind (fun x => Q.bind (R x)) = Q.bind (fun y => P.bind (fun x => R x y)) := by
  ext z
  simp only [FiniteDistribution.bind,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The comparison shortening distribution conditions the first actual attempt on success. No truncation or independence of the two parties' views is used. -/
/-
Mathematical definition (normal notation): For s ∈ F; fallback ∈ Fiber(F, n, s); leak ∈ ∏_(x ∈ Fiber(F, (n + t), s)) A → FullTape(n = n, x.val.L) → 𝒟(B); x ∈ Fiber(F, (n + t), s); α ∈ A, assume 2 ≤ n. define

firstShorteningExecution(fallback, leak, x, α) := bind(Sampling.accepted(attemptDistribution(x.val.L), ((z ↦ decide((rightOutput(x.val.R, z) ≠ 0))))), ((z ↦ (((β ↦ (returnedOutput(fallback, x, z), (α, β))))_*leak(x, α, (0, (PUnit.unit, z))))))).
-/
def firstShorteningExecution {s : F} (hn : 2 ≤ n) (fallback : Fiber F n s)
    (leak : (x : Fiber F (n+t) s) → A → FullTape (n := n) x.val.L → FiniteDistribution B)
    (x : Fiber F (n+t) s) (α : A) : FiniteDistribution (Fiber F n s × (A × B)) :=
  (Sampling.accepted (attemptDistribution hn x.val.L)
    (fun z => decide (rightOutput x.val.R z ≠ 0))
    (attempt_acceptance_pos hn x.val.L x.val.R)).bind (fun z =>
      (leak x α ⟨0,(PUnit.unit,z)⟩).map (fun β => (returnedOutput fallback x z,(α,β))))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F; fallback ∈ Fiber(F, n, s); leak ∈ ∏_(x ∈ Fiber(F, (n + t), s)) A → FullTape(n = n, x.val.L) → 𝒟(B); x ∈ Fiber(F, (n + t), s); α ∈ A, assume |F| = 2; 2 ≤ n. Then

δ(shorteningExecution(fallback, leak, x, α), firstShorteningExecution(fallback, leak, x, α)) ≤ 2 / 2ⁿ.
-/
theorem shorteningExecution_first_distance {s : F}
    (hq : fieldCard F = 2) (hn : 2 ≤ n) (fallback : Fiber F n s)
    (leak : (x : Fiber F (n+t) s) → A → FullTape (n := n) x.val.L → FiniteDistribution B)
    (x : Fiber F (n+t) s) (α : A) :
    statisticalDistance (shorteningExecution hn fallback leak x α)
      (firstShorteningExecution hn fallback leak x α) ≤ 2/(2:ℝ)^n :=
  binary_fullTapeAnswerDistribution_distance hq hn x.val.L x.val.R _

/-- Summing over the matrix answer and the accepted rectangular choice gives exactly the same record observation used by the transport theorem. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): Fix old data and a long encoding x, with n ≥ 2. Suppose the first successful-attempt leakage agrees with its specified rectangle answer. Sampling the matrix-phase answer and then a shortening attempt conditioned on success yields the same joint short-output/answer distribution as sampling a uniform successful attempt first, rewriting it as a reverse record, and applying its rectangle leakage distribution. -/
theorem first_shortening_record_distribution {s : F} (hn : 2 ≤ n)
    (fallback : Fiber F n s)
    (K : O × O → Fiber F (n+t) s → FiniteDistribution A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (O × U F n) ((O × U F n) × Kernel H)) (o : O × O)
    (leak : (x : Fiber F (n+t) s) → A → FullTape (n := n) x.val.L → FiniteDistribution B)
    (hleak : ∀ x α (z : Success (n := n) x.val.L x.val.R),
      leak x α ⟨0,(PUnit.unit,z.val)⟩ =
        rectangleRecordAnswer r o (successfulJointEquiv s ⟨x,z⟩) α)
    (x : Fiber F (n+t) s) :
    letI := success_nonempty hn x.val.L x.val.R
    (K o x).bind (firstShorteningExecution hn fallback leak x) =
      (FiniteDistribution.uniform : FiniteDistribution (Success (n := n) x.val.L x.val.R)).bind (fun z =>
        let v := successfulJointEquiv s ⟨x,z⟩
        (rectangleRecordLeak K r o v).map (fun a => (v.val.1,a))) := by
  classical
  letI := success_nonempty hn x.val.L x.val.R
  unfold firstShorteningExecution
  simp_rw [accepted_sample_observation]
  rw [bind_comm]
  congr 1
  funext z
  simp only [returnedOutput,hleak]
  rw [dif_pos z.property]
  unfold rectangleRecordLeak
  rw [backwardSource_successfulJoint]
  change _ = ((K o x).joint _).bind _
  rw [bind_joint (K o x) _ (fun α β =>
    FiniteDistribution.pure ((successfulJointEquiv s ⟨x,z⟩).val.1,(α,β)))]
  rfl

variable [Nonempty (FullRank F n (n+t))]

/-- The entire real gate is close to its accepted canonical distribution. The sole error is first-attempt rejection; all subsequent retry leakage is allowed. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ O → U(F, (n + t)); p ∈ TableRectanglePartition(O, GL_(n + t)(F), A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(B, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); o ∈ O × O; fallback ∈ Fiber(F, n, gateSecret(a, b, o)); leak ∈ ∏_(x ∈ Fiber(F, (n + t), gateSecret(a, b, o))) A → FullTape(n = n, x.val.L) → 𝒟(B), assume |F| = 2; 2 ≤ n; ∀ x, α, (, z, :, Success, (, n, :=, n,), x.val.L, x.val.R,), leak(x, α, (0, (PUnit.unit, z))) = rectangleRecordAnswer(r, o, successfulJointEquiv(gateSecret(a, b, o), (x, z)), α). Then

δ(fullGateExecution(a, b, p, o, fallback, leak), fullGateCanonical(a, b, p, r, o)) ≤ 2 / 2ⁿ.
-/
theorem fullGate_canonical_distance (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (a b : O → U F (n+t))
    (p : TableRectanglePartition O (Refresh.«GL» F (n+t)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (O × U F n) ((O × U F n) × Kernel H)) (o : O × O)
    (fallback : Fiber F n (gateSecret a b o))
    (leak : (x : Fiber F (n+t) (gateSecret a b o)) → A → FullTape (n := n) x.val.L → FiniteDistribution B)
    (hleak : ∀ x α (z : Success (n := n) x.val.L x.val.R),
      leak x α ⟨0,(PUnit.unit,z.val)⟩ =
        rectangleRecordAnswer r o (successfulJointEquiv (gateSecret a b o) ⟨x,z⟩) α) :
    statisticalDistance (fullGateExecution hn a b p o fallback leak)
      (fullGateCanonical hn a b p r o) ≤ 2/(2:ℝ)^n := by
  let s := gateSecret a b o
  letI := fiber_nonempty F n hn s
  letI := fiber_nonempty F (n+t) (by omega) s
  letI : Nonempty (U F n) := ⟨fallback.val.L⟩
  letI : Nonempty (U F (n+t)) := ⟨a o.1⟩
  let K := longAnswer (s := s) a b p
  have hc :
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) s)).bind (fun x =>
        (K o x).bind (firstShorteningExecution hn fallback leak x)) =
      fullGateCanonical hn a b p r o := by
    calc
      _ = acceptedObservation hn s (rectangleRecordLeak K r o) := by
        unfold acceptedObservation
        congr 1
        funext x
        exact first_shortening_record_distribution hn fallback K r o leak hleak x
      _ = _ := accepted_observation_disintegration hn s _
  rw [fullGateExecution_eq_long,← hc]
  have h := Sampling.bind_distance_le
    (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) s)) FiniteDistribution.uniform _ _ (fun x => by
      have hi := Sampling.bind_distance_le (K o x) (K o x)
        (shorteningExecution hn fallback leak x) (firstShorteningExecution hn fallback leak x)
        (fun α => shorteningExecution_first_distance hq hn fallback leak x α)
      simpa only [statisticalDistance_self,zero_add] using hi)
  simpa only [statisticalDistance_self,zero_add] using h

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ O → U(F, (n + t)); p ∈ TableRectanglePartition(O, GL_(n + t)(F), A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(B, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); o ∈ O × O; u ∈ Fiber(F, n, gateSecret(a, b, o)), assume 2 ≤ n. Then

ambientGateAnswerDistribution(a, b, p, r, o, u) = shortenedAnswerDistribution(longAnswer(a, b, p), r, o, u).
-/
@[simp] theorem ambientGateAnswerDistribution_fiber (hn : 2 ≤ n) (a b : O → U F (n+t))
    (p : TableRectanglePartition O (Refresh.«GL» F (n+t)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (O × U F n) ((O × U F n) × Kernel H)) (o : O × O)
    (u : Fiber F n (gateSecret a b o)) :
    ambientGateAnswerDistribution hn a b p r o u.val = shortenedAnswerDistribution (longAnswer a b p) r o u := by
  simp [ambientGateAnswerDistribution,u.property]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X,Y,Z a set; P ∈ 𝒟(X); f ∈ X → Y; K ∈ Y → 𝒟(Z), assume X is finite; Y is finite; Z is finite. Then

(((xz ↦ (f((xz)₁), (xz)₂)))_*P.joint(((x ↦ K(f(x)))))) = joint((f_*P))(K).
-/
private theorem map_joint_first {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (P : FiniteDistribution X) (f : X → Y) (K : Y → FiniteDistribution Z) :
    (P.joint (fun x => K (f x))).map (fun xz => (f xz.1,xz.2)) = (P.map f).joint K := by
  classical
  ext ⟨y,z⟩
  simp only [FiniteDistribution.map,FiniteDistribution.bind,FiniteDistribution.joint,FiniteDistribution.pure,
    Fintype.sum_prod_type,Prod.mk.injEq,ite_and,mul_ite,mul_one,mul_zero,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : f x = y
  · simp [h,eq_comm]
  · simp [h,Ne.symm h]

/-- Canonical distribution on the common state space used by a circuit runner. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ O → U(F, (n + t)); p ∈ TableRectanglePartition(O, GL_(n + t)(F), A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(B, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); o ∈ O × O, assume 2 ≤ n. Then

(((z ↦ ((z)₁, (z)₂)))_*fullGateCanonical(a, b, p, r, o)) = joint(μ_(gateSecret(a, b, o)))(ambientGateAnswerDistribution(a, b, p, r, o)) .
-/
theorem fullGateCanonical_ambient (hn : 2 ≤ n) (a b : O → U F (n+t))
    (p : TableRectanglePartition O (Refresh.«GL» F (n+t)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (O × U F n) ((O × U F n) × Kernel H)) (o : O × O) :
    (fullGateCanonical hn a b p r o).map (fun z => (z.1.val,z.2)) =
      (mu F n hn (gateSecret a b o)).joint (ambientGateAnswerDistribution hn a b p r o) := by
  letI := fiber_nonempty F n hn (gateSecret a b o)
  have h := map_joint_first (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (gateSecret a b o)))
    Subtype.val (ambientGateAnswerDistribution hn a b p r o)
  simpa only [fullGateCanonical, mu, ambientGateAnswerDistribution_fiber] using h

/-- The actual matrix-plus-rectangular gate discharges the physical runner's local transition coupling, with the paper's `2/N` error. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ O → U(F, (n + t)); p ∈ TableRectanglePartition(O, GL_(n + t)(F), A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(B, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); o ∈ O × O; fallback ∈ Fiber(F, n, gateSecret(a, b, o)); leak ∈ ∏_(x ∈ Fiber(F, (n + t), gateSecret(a, b, o))) A → FullTape(n = n, x.val.L) → 𝒟(B), assume |F| = 2; 2 ≤ n; ∀ x, α, (, z, :, Success, (, n, :=, n,), x.val.L, x.val.R,), leak(x, α, (0, (PUnit.unit, z))) = rectangleRecordAnswer(r, o, successfulJointEquiv(gateSecret(a, b, o), (x, z)), α). Then

δ((((z ↦ ((z)₁, (z)₂)))_*fullGateExecution(a, b, p, o, fallback, leak)), joint(μ_(gateSecret(a, b, o)))(ambientGateAnswerDistribution(a, b, p, r, o))) ≤ 2 / 2ⁿ.
-/
theorem fullGate_ambient_distance (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (a b : O → U F (n+t))
    (p : TableRectanglePartition O (Refresh.«GL» F (n+t)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (O × U F n) ((O × U F n) × Kernel H)) (o : O × O)
    (fallback : Fiber F n (gateSecret a b o))
    (leak : (x : Fiber F (n+t) (gateSecret a b o)) → A → FullTape (n := n) x.val.L → FiniteDistribution B)
    (hleak : ∀ x α (z : Success (n := n) x.val.L x.val.R),
      leak x α ⟨0,(PUnit.unit,z.val)⟩ =
        rectangleRecordAnswer r o (successfulJointEquiv (gateSecret a b o) ⟨x,z⟩) α) :
    statisticalDistance
      ((fullGateExecution hn a b p o fallback leak).map (fun z => (z.1.val,z.2)))
      ((mu F n hn (gateSecret a b o)).joint (ambientGateAnswerDistribution hn a b p r o)) ≤
      2/(2:ℝ)^n := by
  rw [← fullGateCanonical_ambient]
  exact (statisticalDistance_map_le _ _ _).trans
    (fullGate_canonical_distance hq hn a b p r o fallback leak hleak)

end

end CircuitCompiler.Rectangular.Fractional
