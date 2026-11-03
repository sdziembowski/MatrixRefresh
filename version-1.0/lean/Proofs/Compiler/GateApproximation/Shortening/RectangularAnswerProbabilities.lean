import Proofs.Compiler.GateApproximation.Shortening.RectangularConditionalDistribution
import Proofs.Compiler.Construction.Parameters



/-!
# The successful physical answer distribution is the rectangular transport

Matrix-phase answers may be arbitrary stochastic observations of the old and long encodings. After fixing the communicated rectangular matrix, shortening answers form a rectangle partition. The physical conditional answer distribution is exactly the previously analysed linear operator on the same common tables.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace CircuitCompiler.Rectangular

open Refresh MatrixRefresh TableAnalysis Shortening

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

variable {O A B : Type*} [Fintype O] [DecidableEq O] [Nonempty O]
  [Fintype A] [Fintype B]

variable {n t : ℕ} [Nonempty (U F n)] [Nonempty (U F (n+t))]
  [Nonempty (FullRank F n (n+t))]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F; p ∈ Fiber(F, n, s); H ∈ FullRank(F, n, (n + t)); k ∈ Kernel(H), we have

recordNoise(reverseRecord(p, H, k)) = k.
-/
@[simp] theorem recordNoise_reverseRecord {s : F} (p : Fiber F n s)
    (H : FullRank F n (n+t)) (k : Kernel H) :
    recordNoise (reverseRecord p H k) = k := by
  exact (preimageEquivKernel H p.val.R).apply_symm_apply k

/-- The deterministic shortening leakage, using only each party's available values once the communicated matrix has been fixed. -/
/-
Mathematical definition (normal notation): For s ∈ F; r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) RectanglePartition(B, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); o ∈ O × O; p ∈ Backward(F, n, (n + t), s); a ∈ A, define

rectangleRecordAnswer(r, o, p, a) := leaf(r(a, ((p)₂)₁))(((o)₁, p.val.1.val.L), (((o)₂, p.val.1.val.R), recordNoise(p))).
-/
def rectangleRecordAnswer {s : F}
    (r : A → (H : FullRank F n (n+t)) → RectanglePartition B
      (O × U F n) ((O × U F n) × Kernel H))
    (o : O × O) (p : Backward F n (n+t) s) (a : A) : B :=
  (r a p.val.2.1).leaf (o.1,p.val.1.val.L)
    ((o.2,p.val.1.val.R),recordNoise p)

/-- Retain both the matrix-phase answer and the shortening-phase answer. -/
/-
Mathematical definition (normal notation): For s ∈ F; K ∈ O × O → Fiber(F, (n + t), s) → 𝒟(A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) RectanglePartition(B, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); o ∈ O × O; p ∈ Backward(F, n, (n + t), s), define

rectangleRecordLeak(K, r, o, p) := joint(K(o, backwardSource(p)))(((a ↦ FiniteDistribution.pure(rectangleRecordAnswer(r, o, p, a))))).
-/
def rectangleRecordLeak {s : F}
    (K : O × O → Fiber F (n+t) s → FiniteDistribution A)
    (r : A → (H : FullRank F n (n+t)) → RectanglePartition B
      (O × U F n) ((O × U F n) × Kernel H))
    (o : O × O) (p : Backward F n (n+t) s) : FiniteDistribution (A × B) :=
  (K o (backwardSource p)).joint (fun a => FiniteDistribution.pure (rectangleRecordAnswer r o p a))

/-- The conditional complete answer after a first-attempt successful shortening. -/
/-
Mathematical definition (normal notation): For s ∈ F; K ∈ O × O → Fiber(F, (n + t), s) → 𝒟(A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) RectanglePartition(B, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); o ∈ O × O; p ∈ Fiber(F, n, s), define

shortenedAnswerDistribution(K, r, o, p) := recordAnswerDistribution(rectangleRecordLeak(K, r, o), p).
-/
def shortenedAnswerDistribution {s : F}
    (K : O × O → Fiber F (n+t) s → FiniteDistribution A)
    (r : A → (H : FullRank F n (n+t)) → RectanglePartition B
      (O × U F n) ((O × U F n) × Kernel H))
    (o : O × O) (p : Fiber F n s) : FiniteDistribution (A × B) :=
  recordAnswerDistribution (rectangleRecordLeak K r o) p

/-- The reverse formula is the exact joint distribution of the actual accepted sampler, including the output encoding and both leakage answers. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F; K ∈ O × O → Fiber(F, (n + t), s) → 𝒟(A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) RectanglePartition(B, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); o ∈ O × O, assume 2 ≤ n; Fiber(F, n, s) ≠ ∅; Fiber(F, (n + t), s) ≠ ∅. Then

acceptedObservation(s, rectangleRecordLeak(K, r, o)) = joint(𝒰_(Fiber(F, n, s)))(shortenedAnswerDistribution(K, r, o)).
-/
theorem physical_accepted_joint {s : F} (hn : 2 ≤ n)
    [Nonempty (Fiber F n s)] [Nonempty (Fiber F (n+t) s)]
    (K : O × O → Fiber F (n+t) s → FiniteDistribution A)
    (r : A → (H : FullRank F n (n+t)) → RectanglePartition B
      (O × U F n) ((O × U F n) × Kernel H)) (o : O × O) :
    acceptedObservation hn s (rectangleRecordLeak K r o) =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s)).joint (shortenedAnswerDistribution K r o) :=
  accepted_observation_disintegration hn s _

/-- The physical conditional answer weights are the very same linear transport used for the nuclear and summed absolute-error estimates. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F; K ∈ O × O → Fiber(F, (n + t), s) → 𝒟(A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) RectanglePartition(B, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); k ∈ A → ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))); o ∈ O × O; p ∈ Fiber(F, n, s); a ∈ A; b ∈ B, assume ∀ a, p, K(o, p)(a) = k(a, ((o)₁, p.val.L), ((o)₂, p.val.R)). Then

shortenedAnswerDistribution(K, r, o, p)((a, b)) = transport(r(a), k(a), b, ((o)₁, p.val.L), ((o)₂, p.val.R)).
-/
theorem shortenedAnswerDistribution_weight {s : F}
    (K : O × O → Fiber F (n+t) s → FiniteDistribution A)
    (r : A → (H : FullRank F n (n+t)) → RectanglePartition B
      (O × U F n) ((O × U F n) × Kernel H))
    (k : A → Matrix (O × U F (n+t)) (O × U F (n+t)) ℝ)
    (o : O × O)
    (hk : ∀ a p, (K o p).weight a = k a (o.1,p.val.L) (o.2,p.val.R))
    (p : Fiber F n s) (a : A) (b : B) :
    (shortenedAnswerDistribution K r o p).weight (a,b) =
      transport (r a) (k a) b (o.1,p.val.L) (o.2,p.val.R) := by
  classical
  change (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
    (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect (fun h =>
      (rectangleRecordLeak K r o (reverseRecord p H h)).weight (a,b))) = _
  unfold transport
  apply congrArg (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect
  funext H
  apply congrArg (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect
  funext h
  simp only [rectangleRecordLeak,FiniteDistribution.joint,FiniteDistribution.pure,hk,rectangleRecordAnswer,
    recordNoise_reverseRecord]
  change k a (o.1,leftShare H p.val.L) (o.2,rightLift H p.val.R h) *
      (if b = (r a H).leaf (o.1,p.val.L) ((o.2,p.val.R),h) then 1 else 0) = _
  rw [eq_comm (a := b),RectanglePartition.leaf_eq_iff]
  split_ifs <;> simp

/-- One common family of transported approximations controls the physical accepted conditional distributions in both norms, for every chosen secret fiber. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F; K ∈ O × O → Fiber(F, (n + t), s) → 𝒟(A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) RectanglePartition(B, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); k, G ∈ A → ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))); old ∈ 𝒟((O × O)), assume Fiber(F, n, s) ≠ ∅; Fiber(F, (n + t), s) ≠ ∅; ∀ o, (old(o) ≠ 0) ⇒ ∀ a, p, K(o, p)(a) = k(a, ((o)₁, p.val.L), ((o)₂, p.val.R)). Then

(∑ₐ (∑_b (‖ transport(r(a), G(a), b)‖_*))) ≤ √(|B|) · (∑ₐ (‖ G(a)‖_*)) ∧ 𝔼_(op ← (old ⊗ 𝒰_(Fiber(F, n, s)))) [∑ₐ (∑_b (|shortenedAnswerDistribution(K, r, (op)₁, (op)₂)((a, b)) - transport(r(a), G(a), b, (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R))|))] ≤ ∑ₐ (𝔼_(op ← (old ⊗ 𝒰_(Fiber(F, (n + t), s)))) [|k(a, (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R)) - G(a, (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R))|]).
-/
theorem physical_accepted_approximation {s : F}
    [Nonempty (Fiber F n s)] [Nonempty (Fiber F (n+t) s)]
    (K : O × O → Fiber F (n+t) s → FiniteDistribution A)
    (r : A → (H : FullRank F n (n+t)) → RectanglePartition B
      (O × U F n) ((O × U F n) × Kernel H))
    (k G : A → Matrix (O × U F (n+t)) (O × U F (n+t)) ℝ)
    (old : FiniteDistribution (O × O))
    (hk : ∀ o, old.weight o ≠ 0 → ∀ a p,
      (K o p).weight a = k a (o.1,p.val.L) (o.2,p.val.R)) :
    (∑ a, ∑ b, tableNuclearNorm (transport (r a) (G a) b)) ≤
      Real.sqrt (Fintype.card B) * (∑ a, tableNuclearNorm (G a)) ∧
    (old.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s))).expect (fun op =>
      ∑ a, ∑ b, |(shortenedAnswerDistribution K r op.1 op.2).weight (a,b) -
        transport (r a) (G a) b (op.1.1,op.2.val.L) (op.1.2,op.2.val.R)|) ≤
    ∑ a, (old.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) s))).expect (fun op =>
      |k a (op.1.1,op.2.val.L) (op.1.2,op.2.val.R) -
        G a (op.1.1,op.2.val.L) (op.1.2,op.2.val.R)|) := by
  have h := transport_approximation r k G old s
  constructor
  · exact h.1
  · have he :
        (old.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s))).expect (fun op =>
          ∑ a, ∑ b, |(shortenedAnswerDistribution K r op.1 op.2).weight (a,b) -
            transport (r a) (G a) b (op.1.1,op.2.val.L) (op.1.2,op.2.val.R)|) =
        (old.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s))).expect (fun op =>
          ∑ a, ∑ b, |transport (r a) (k a) b (op.1.1,op.2.val.L) (op.1.2,op.2.val.R) -
            transport (r a) (G a) b (op.1.1,op.2.val.L) (op.1.2,op.2.val.R)|) := by
      simp only [expect_prod]
      apply Finset.sum_congr rfl
      intro o _
      by_cases ho : old.weight o = 0
      · simp only [ho,zero_mul]
      · congr 1
        apply congrArg (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s)).expect
        funext p
        simp_rw [shortenedAnswerDistribution_weight K r k o (hk o ho)]
    rw [he,expect_sum]
    exact h.2

end

end CircuitCompiler.Rectangular
