import Proofs.Compiler.GateApproximation.Shortening.ShorteningCoupling
import Proofs.Compiler.GateApproximation.Shortening.ShorteningErrorExtension
import Proofs.Compiler.GateApproximation.Shortening.NuclearTransport



/-!
# Exact shortening distributions and their transported approximations
-/
set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.Shortening

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {F Z : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype Z]

/-- The canonical conditional answer is exactly the uniform average over the two freely chosen tails of the inverse shortening transformation. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; answer ∈ Auxiliary(F, (n + t), z) → 𝒟(Z); u ∈ Fiber(F, n, (c + ε · z)); β ∈ Z, assume ε ≠ 0; Accepted(F, n, t, c, ε, z) ≠ ∅; Fiber(F, n, (c + ε · z)) ≠ ∅. Then

acceptedAnswerDistribution(c, ε, z, answer, u)(β) = 𝔼_(tails ← 𝒰_(V(F, t) × V(F, t))) [answer(acceptedEmbedding(c, ε, z, reconstruct(c, ε, z, u, (tails)₁, (tails)₂)))(β)].
-/
theorem acceptedAnswerDistribution_weight_tails {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    [Nonempty (Accepted F n t c ε z)] [Nonempty (Fiber F n (c + ε * z))]
    (answer : Auxiliary F (n + t) z → FiniteDistribution Z)
    (u : Fiber F n (c + ε * z)) (β : Z) :
    (acceptedAnswerDistribution c ε z answer u).weight β =
      (FiniteDistribution.uniform : FiniteDistribution (V F t × V F t)).expect (fun tails =>
        (answer (acceptedEmbedding c ε z (reconstruct c ε z hε u tails.1 tails.2))).weight β) := by
  have hd : (Fintype.card (Fiber F n (c + ε * z)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hweight (a : Accepted F n t c ε z) := conditional_weight_identity
    (FiniteDistribution.uniform : FiniteDistribution (Accepted F n t c ε z)) (output c ε z) u a
  rw [accepted_output_uniform c ε z hε] at hweight
  have hscaled : (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (c + ε * z))).weight u *
      (acceptedAnswerDistribution c ε z answer u).weight β =
      (FiniteDistribution.uniform : FiniteDistribution (Accepted F n t c ε z)).expect
        (fun a => if output c ε z a = u then (answer (acceptedEmbedding c ε z a)).weight β else 0) := by
    simp only [acceptedAnswerDistribution, FiniteDistribution.bind, Finset.mul_sum, ← mul_assoc, hweight,
      FiniteDistribution.expect]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  rw [accepted_expect c ε z hε] at hscaled
  simp only [output_reconstruct] at hscaled
  have htail (v : Fiber F n (c + ε * z)) :
      (FiniteDistribution.uniform : FiniteDistribution (V F t × V F t)).expect
        (fun tails => if v = u then
          (answer (acceptedEmbedding c ε z (reconstruct c ε z hε v tails.1 tails.2))).weight β else 0) =
      if v = u then (FiniteDistribution.uniform : FiniteDistribution (V F t × V F t)).expect
        (fun tails => (answer (acceptedEmbedding c ε z (reconstruct c ε z hε u tails.1 tails.2))).weight β)
      else 0 := by
    by_cases h : v = u <;> simp [h, FiniteDistribution.expect]
  simp_rw [htail] at hscaled
  simp only [FiniteDistribution.expect, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, FiniteDistribution.uniform] at hscaled
  exact mul_left_cancel₀ (inv_ne_zero hd) hscaled

section RectangleLeaf

variable {B X Y : Type*} [Fintype B]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ RectanglePartition(B, X, Y); x ∈ X; y ∈ Y, we have

∃ β, ∀ γ, (r.left(γ, x) ∧ r.right(γ, y)) = true ⇔ γ = β.
-/
theorem RectanglePartition.exists_leaf (r : RectanglePartition B X Y) (x : X) (y : Y) :
    ∃ β, ∀ γ, (r.left γ x && r.right γ y) = true ↔ γ = β := by
  classical
  let S := Finset.univ.filter (fun β => r.left β x && r.right β y)
  have hcard : S.card = 1 := by
    have h := r.partition x y
    have he : (S.card : ℝ) = ∑ β, if r.left β x && r.right β y then (1 : ℝ) else 0 := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      rfl
    exact_mod_cast he.trans h
  obtain ⟨β, hβ⟩ := Finset.card_eq_one.mp hcard
  refine ⟨β, fun γ => ?_⟩
  have hmem : γ ∈ S ↔ γ = β := by rw [hβ]; simp
  simpa [S] using hmem

/-- The unique deterministic answer selected by a complete rectangle partition. -/
/-
Mathematical definition (normal notation): For r ∈ RectanglePartition(B, X, Y); x ∈ X; y ∈ Y, define

RectanglePartition.leaf(r, x, y) := Classical.choose(r.exists_leaf(x, y)).
-/
def RectanglePartition.leaf (r : RectanglePartition B X Y) (x : X) (y : Y) : B :=
  Classical.choose (r.exists_leaf x y)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ RectanglePartition(B, X, Y); x ∈ X; y ∈ Y; β ∈ B, we have

r.leaf(x, y) = β ⇔ (r.left(β, x) ∧ r.right(β, y)) = true.
-/
theorem RectanglePartition.leaf_eq_iff (r : RectanglePartition B X Y) (x : X) (y : Y) (β : B) :
    r.leaf x y = β ↔ (r.left β x && r.right β y) = true := by
  exact eq_comm.trans ((Classical.choose_spec (r.exists_leaf x y)) β).symm

end RectangleLeaf

variable {O A B : Type*} [Fintype O] [DecidableEq O] [Nonempty O]
  [Fintype A] [Fintype B] [DecidableEq B]

/-
Mathematical definition (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; r ∈ A → V(F, t) → Pivot(F, n) → RectanglePartition(B, (O × U(F, n)), ((O × U(F, n)) × V(F, t))); α ∈ A; o ∈ O × O; p ∈ Accepted(F, n, t, c, ε, z), define

acceptedRectangleAnswer(c, ε, z, r, α, o, p) := leaf(r(α, p.val.B, pivotMessage(p.val.A)))(((o)₁, p.val.A), (((o)₂, val.R(output(c, ε, z, p))), p.val.D)).
-/
def acceptedRectangleAnswer {n t : ℕ} (c ε z : F)
    (r : A → V F t → Pivot F n → RectanglePartition B (O × U F n) ((O × U F n) × V F t))
    (α : A) (o : O × O) (p : Accepted F n t c ε z) : B :=
  (r α p.val.B (pivotMessage p.val.A)).leaf (o.1, p.val.A)
    ((o.2, (output c ε z p).val.R), p.val.D)

/-- Execute the deterministic shortening leakage. The arbitrary answer on rejected inputs never enters the canonical accepted distribution. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; r ∈ A → V(F, t) → Pivot(F, n) → RectanglePartition(B, (O × U(F, n)), ((O × U(F, n)) × V(F, t))); β₀ ∈ B; o ∈ O × O; p ∈ Auxiliary(F, (n + t), z); α ∈ A, define

rectangleLeak(c, ε, z, r, β₀, o, p, α) := { { FiniteDistribution.pure(acceptedRectangleAnswer(c, ε, z, r, α, o, (splitData(p, hA), hR))) if outputRight(c, ε, splitData(p, hA)) ≠ 0,; FiniteDistribution.pure(β₀) otherwise } if head(p) ≠ 0,; FiniteDistribution.pure(β₀) otherwise } .
-/
def rectangleLeak {n t : ℕ} (c ε z : F)
    (r : A → V F t → Pivot F n → RectanglePartition B (O × U F n) ((O × U F n) × V F t))
    (β₀ : B) (o : O × O) (p : Auxiliary F (n + t) z) (α : A) : FiniteDistribution B :=
  if hA : head p ≠ 0 then
    if hR : outputRight c ε (splitData p hA) ≠ 0 then
      FiniteDistribution.pure (acceptedRectangleAnswer c ε z r α o
        ⟨splitData p hA, splitData_secret p hA, hR⟩)
    else FiniteDistribution.pure β₀
  else FiniteDistribution.pure β₀

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; r ∈ A → V(F, t) → Pivot(F, n) → RectanglePartition(B, (O × U(F, n)), ((O × U(F, n)) × V(F, t))); β₀ ∈ B; o ∈ O × O; p ∈ Accepted(F, n, t, c, ε, z); α ∈ A, we have

rectangleLeak(c, ε, z, r, β₀, o, acceptedEmbedding(c, ε, z, p), α) = FiniteDistribution.pure(acceptedRectangleAnswer(c, ε, z, r, α, o, p)).
-/
@[simp] theorem rectangleLeak_accepted {n t : ℕ} (c ε z : F)
    (r : A → V F t → Pivot F n → RectanglePartition B (O × U F n) ((O × U F n) × V F t))
    (β₀ : B) (o : O × O) (p : Accepted F n t c ε z) (α : A) :
    rectangleLeak c ε z r β₀ o (acceptedEmbedding c ε z p) α =
      FiniteDistribution.pure (acceptedRectangleAnswer c ε z r α o p) := by
  have hA : head (acceptedEmbedding c ε z p) ≠ 0 := by
    rw [head_acceptedEmbedding]; exact p.val.A.property
  have hs := splitData_acceptedEmbedding c ε z p hA
  have hR : outputRight c ε (splitData (acceptedEmbedding c ε z p) hA) ≠ 0 := by
    rw [hs]; exact p.property.2
  unfold rectangleLeak
  rw [dif_pos hA, dif_pos hR]
  congr 2
  exact Subtype.ext hs

/-- Evaluate a common long table on auxiliary coordinates, with zero extension at the virtual zero right share. -/
/-
Mathematical definition (normal notation): For m ∈ ℕ; z ∈ F; G ∈ ℝ^((O × U(F, m)) × (O × U(F, m))); o ∈ O × O; p ∈ Auxiliary(F, m, z), define

auxiliaryTable(z, G, o, p) := zeroExtend(((v ↦ G(((o)₁, (p)₁), ((o)₂, v)))), (p)₂).
-/
def auxiliaryTable {m : ℕ} (z : F)
    (G : Matrix (O × U F m) (O × U F m) ℝ)
    (o : O × O) (p : Auxiliary F m z) : ℝ :=
  zeroExtend (fun v => G (o.1, p.1) (o.2, v)) p.2.val

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; r ∈ A → V(F, t) → Pivot(F, n) → RectanglePartition(B, (O × U(F, n)), ((O × U(F, n)) × V(F, t))); G ∈ A → ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))); α ∈ A; β ∈ B; o ∈ O × O; u ∈ Fiber(F, n, (c + ε · z)), assume ε ≠ 0. Then

transportMatrix(c, ε, r(α), G(α), β, ((o)₁, u.val.L), ((o)₂, u.val.R)) = errorTransport(c, ε, z, ((α ↦ auxiliaryTable(z, G(α)))), acceptedRectangleAnswer(c, ε, z, r), α, β, o, u).
-/
theorem transportMatrix_eq_errorTransport {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    (r : A → V F t → Pivot F n → RectanglePartition B (O × U F n) ((O × U F n) × V F t))
    (G : A → Matrix (O × U F (n + t)) (O × U F (n + t)) ℝ)
    (α : A) (β : B) (o : O × O) (u : Fiber F n (c + ε * z)) :
    transportMatrix c ε (r α) (G α) β (o.1, u.val.L) (o.2, u.val.R) =
      errorTransport c ε z hε (fun α => auxiliaryTable z (G α))
        (acceptedRectangleAnswer c ε z r) α β o u := by
  unfold transportMatrix errorTransport
  rw [uniform_prod, expect_prod]
  apply congrArg (FiniteDistribution.expect (FiniteDistribution.uniform : FiniteDistribution (V F t)))
  funext Btail
  apply congrArg (FiniteDistribution.expect (FiniteDistribution.uniform : FiniteDistribution (V F t)))
  funext Dtail
  simp only [transportValue, acceptedRectangleAnswer, output_reconstruct,
    RectanglePartition.leaf_eq_iff]
  rfl

/-- The complete canonical answer for an arbitrary matrix-phase answer distribution and the actual deterministic shortening rectangles. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; K ∈ O × O → Auxiliary(F, (n + t), z) → 𝒟(A); r ∈ A → V(F, t) → Pivot(F, n) → RectanglePartition(B, (O × U(F, n)), ((O × U(F, n)) × V(F, t))); β₀ ∈ B; o ∈ O × O; u ∈ Fiber(F, n, (c + ε · z)), assume Accepted(F, n, t, c, ε, z) ≠ ∅. define

shortenedAnswerDistribution(c, ε, z, K, r, β₀, o, u) := acceptedAnswerDistribution(c, ε, z, ((p ↦ joint(K(o, p))(rectangleLeak(c, ε, z, r, β₀, o, p)))), u).
-/
def shortenedAnswerDistribution {n t : ℕ} (c ε z : F)
    [Nonempty (Accepted F n t c ε z)]
    (K : O × O → Auxiliary F (n + t) z → FiniteDistribution A)
    (r : A → V F t → Pivot F n → RectanglePartition B (O × U F n) ((O × U F n) × V F t))
    (β₀ : B) (o : O × O) (u : Fiber F n (c + ε * z)) : FiniteDistribution (A × B) :=
  acceptedAnswerDistribution c ε z (fun p => (K o p).joint (rectangleLeak c ε z r β₀ o p)) u

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; K ∈ O × O → Auxiliary(F, (n + t), z) → 𝒟(A); r ∈ A → V(F, t) → Pivot(F, n) → RectanglePartition(B, (O × U(F, n)), ((O × U(F, n)) × V(F, t))); β₀ ∈ B; o ∈ O × O; u ∈ Fiber(F, n, (c + ε · z)); α ∈ A; β ∈ B, assume ε ≠ 0; Accepted(F, n, t, c, ε, z) ≠ ∅; Fiber(F, n, (c + ε · z)) ≠ ∅. Then

shortenedAnswerDistribution(c, ε, z, K, r, β₀, o, u)((α, β)) = errorTransport(c, ε, z, ((α, o, p ↦ K(o, p)(α))), acceptedRectangleAnswer(c, ε, z, r), α, β, o, u) .
-/
theorem shortenedAnswerDistribution_weight {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    [Nonempty (Accepted F n t c ε z)] [Nonempty (Fiber F n (c + ε * z))]
    (K : O × O → Auxiliary F (n + t) z → FiniteDistribution A)
    (r : A → V F t → Pivot F n → RectanglePartition B (O × U F n) ((O × U F n) × V F t))
    (β₀ : B) (o : O × O) (u : Fiber F n (c + ε * z)) (α : A) (β : B) :
    (shortenedAnswerDistribution c ε z K r β₀ o u).weight (α, β) =
      errorTransport c ε z hε (fun α o p => (K o p).weight α)
        (acceptedRectangleAnswer c ε z r) α β o u := by
  rw [shortenedAnswerDistribution, acceptedAnswerDistribution_weight_tails c ε z hε]
  unfold errorTransport
  apply congrArg (FiniteDistribution.expect (FiniteDistribution.uniform : FiniteDistribution (V F t × V F t)))
  funext tails
  simp only [FiniteDistribution.joint, rectangleLeak_accepted, FiniteDistribution.pure, mul_ite, mul_one, mul_zero]
  congr 1
  exact propext eq_comm

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; e, f ∈ A → O × O → Auxiliary(F, (n + t), z) → ℝ; answer ∈ A → O × O → Accepted(F, n, t, c, ε, z) → B; α ∈ A; β ∈ B; o ∈ O × O; u ∈ Fiber(F, n, (c + ε · z)), assume ε ≠ 0. Then

errorTransport(c, ε, z, ((α, o, p ↦ e(α, o, p) - f(α, o, p))), answer, α, β, o, u) = errorTransport(c, ε, z, e, answer, α, β, o, u) - errorTransport(c, ε, z, f, answer, α, β, o, u).
-/
theorem errorTransport_sub {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    (e f : A → O × O → Auxiliary F (n + t) z → ℝ)
    (answer : A → O × O → Accepted F n t c ε z → B)
    (α : A) (β : B) (o : O × O) (u : Fiber F n (c + ε * z)) :
    errorTransport c ε z hε (fun α o p => e α o p - f α o p) answer α β o u =
      errorTransport c ε z hε e answer α β o u - errorTransport c ε z hε f answer α β o u := by
  unfold errorTransport
  rw [← expect_sub]
  apply congrArg (FiniteDistribution.expect (FiniteDistribution.uniform : FiniteDistribution (V F t × V F t)))
  funext tails
  dsimp only
  split_ifs <;> simp

/-- Exact error identity linking the canonical conditional distribution to the same linear table transport used by the nuclear-norm theorem. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; K ∈ O × O → Auxiliary(F, (n + t), z) → 𝒟(A); r ∈ A → V(F, t) → Pivot(F, n) → RectanglePartition(B, (O × U(F, n)), ((O × U(F, n)) × V(F, t))); G ∈ A → ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))); β₀ ∈ B; o ∈ O × O; u ∈ Fiber(F, n, (c + ε · z)); α ∈ A; β ∈ B, assume ε ≠ 0; Accepted(F, n, t, c, ε, z) ≠ ∅; Fiber(F, n, (c + ε · z)) ≠ ∅. Then

shortenedAnswerDistribution(c, ε, z, K, r, β₀, o, u)((α, β)) - transportMatrix(c, ε, r(α), G(α), β, ((o)₁, u.val.L), ((o)₂, u.val.R)) = errorTransport(c, ε, z, ((α, o, p ↦ K(o, p)(α) - auxiliaryTable(z, G(α), o, p))), acceptedRectangleAnswer(c, ε, z, r), α, β, o, u).
-/
theorem shortenedAnswerDistribution_sub_transport {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    [Nonempty (Accepted F n t c ε z)] [Nonempty (Fiber F n (c + ε * z))]
    (K : O × O → Auxiliary F (n + t) z → FiniteDistribution A)
    (r : A → V F t → Pivot F n → RectanglePartition B (O × U F n) ((O × U F n) × V F t))
    (G : A → Matrix (O × U F (n + t)) (O × U F (n + t)) ℝ)
    (β₀ : B) (o : O × O) (u : Fiber F n (c + ε * z)) (α : A) (β : B) :
    (shortenedAnswerDistribution c ε z K r β₀ o u).weight (α, β) -
        transportMatrix c ε (r α) (G α) β (o.1, u.val.L) (o.2, u.val.R) =
      errorTransport c ε z hε
        (fun α o p => (K o p).weight α - auxiliaryTable z (G α) o p)
        (acceptedRectangleAnswer c ε z r) α β o u := by
  rw [shortenedAnswerDistribution_weight c ε z hε, transportMatrix_eq_errorTransport c ε z hε,
    errorTransport_sub]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; z ∈ F; G ∈ ℝ^((O × U(F, m)) × (O × U(F, m))); o ∈ O × O; p ∈ Fiber(F, m, z), we have

auxiliaryTable(z, G, o, actualEmbedding(z, p)) = G(((o)₁, p.val.L), ((o)₂, p.val.R)).
-/
@[simp] theorem auxiliaryTable_actual {m : ℕ} (z : F)
    (G : Matrix (O × U F m) (O × U F m) ℝ)
    (o : O × O) (p : Fiber F m z) :
    auxiliaryTable z G o (actualEmbedding z p) = G (o.1, p.val.L) (o.2, p.val.R) := by
  change zeroExtend (fun v => G (o.1, p.val.L) (o.2, v)) p.val.R.val = _
  simp [zeroExtend, p.val.R.property]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(A), we have

(∑_α ((P(α))²)) ≤ 1.
-/
theorem probability_square_sum_le_one (P : FiniteDistribution A) : (∑ α, P.weight α ^ 2) ≤ 1 := by
  rw [← P.total]
  apply Finset.sum_le_sum
  intro α _
  have hle : P.weight α ≤ 1 := by
    rw [← P.total]
    exact Finset.single_le_sum (fun β _ => P.nonneg β) (Finset.mem_univ α)
  nlinarith [P.nonneg α]

/-- Actual canonical distribution approximation after shortening, including the virtual-zero cost. No boundedness assumption on the genuine matrix error is needed, and summing the squared errors adds no shortening-leaf factor. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; Pold ∈ 𝒟((O × O)); K ∈ O × O → Auxiliary(F, (n + t), z) → 𝒟(A); r ∈ A → V(F, t) → Pivot(F, n) → RectanglePartition(B, (O × U(F, n)), ((O × U(F, n)) × V(F, t))); G ∈ A → ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))); β₀ ∈ B; η ∈ ℝ, assume 2 ≤ n + t; ε ≠ 0; Accepted(F, n, t, c, ε, z) ≠ ∅; Fiber(F, n, (c + ε · z)) ≠ ∅; Fiber(F, (n + t), z) ≠ ∅; Auxiliary(F, (n + t), z) ≠ ∅; 𝔼_(op ← (Pold ⊗ 𝒰_(Fiber(F, (n + t), z)))) [∑_α ((K((op)₁, actualEmbedding(z, (op)₂))(α) - G(α, (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R)))²)] ≤ η². Then

𝔼_(op ← (Pold ⊗ 𝒰_(Fiber(F, n, (c + ε · z))))) [∑_α (∑ᵦ ((shortenedAnswerDistribution(c, ε, z, K, r, β₀, (op)₁, (op)₂)((α, β)) - transportMatrix(c, ε, r(α), G(α), β, (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R)))²))] ≤ (acceptanceMass(n = n, t = t, c, ε, z))⁻¹ · (η² + 1 / (|F|)^(n + t − 1)).
-/
theorem shortenedAnswerDistribution_error_L2 {n t : ℕ} (hm : 2 ≤ n + t) (c ε z : F) (hε : ε ≠ 0)
    [Nonempty (Accepted F n t c ε z)] [Nonempty (Fiber F n (c + ε * z))]
    [Nonempty (Fiber F (n + t) z)] [Nonempty (Auxiliary F (n + t) z)]
    (Pold : FiniteDistribution (O × O))
    (K : O × O → Auxiliary F (n + t) z → FiniteDistribution A)
    (r : A → V F t → Pivot F n → RectanglePartition B (O × U F n) ((O × U F n) × V F t))
    (G : A → Matrix (O × U F (n + t)) (O × U F (n + t)) ℝ)
    (β₀ : B) (η : ℝ)
    (hη : (Pold.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n + t) z))).expect
      (fun op => ∑ α, ((K op.1 (actualEmbedding z op.2)).weight α -
        G α (op.1.1, op.2.val.L) (op.1.2, op.2.val.R)) ^ 2) ≤ η ^ 2) :
    (Pold.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (c + ε * z)))).expect
      (fun op => ∑ α, ∑ β, ((shortenedAnswerDistribution c ε z K r β₀ op.1 op.2).weight (α, β) -
        transportMatrix c ε (r α) (G α) β (op.1.1, op.2.val.L) (op.1.2, op.2.val.R)) ^ 2) ≤
      (acceptanceMass (n := n) (t := t) c ε z)⁻¹ *
        (η ^ 2 + 1 / (fieldCard F : ℝ) ^ (n + t - 1)) := by
  simp_rw [shortenedAnswerDistribution_sub_transport c ε z hε]
  refine (errorTransport_L2 c ε z hε Pold
    (fun α o p => (K o p).weight α - auxiliaryTable z (G α) o p)
    (acceptedRectangleAnswer c ε z r)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by unfold acceptanceMass; positivity))
  have hx := auxiliary_error_extension hm z Pold
    (fun α o p => (K o p).weight α - auxiliaryTable z (G α) o p)
    (fun o p hp => by
      simpa only [auxiliaryTable, zeroExtend, hp, ne_eq, not_true_eq_false, dite_false,
        sub_zero] using probability_square_sum_le_one (K o p))
  simp only [auxiliaryTable_actual] at hx
  exact hx.trans (add_le_add hη (le_refl _))

end

end CircuitCompiler.Shortening
