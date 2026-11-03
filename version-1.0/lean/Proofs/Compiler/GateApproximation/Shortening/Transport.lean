import Proofs.Compiler.GateApproximation.Shortening.RectangularFractionalTransport



/-!
# Per-answer squared-error contraction for rectangular shortening

The probability operator below is the actual accepted backward shortening operator. Its L2 bound is proved from its sampling distribution, without an answer-count loss or an assumed analytic transport property.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace CircuitCompiler.ShorteningTransport

open Refresh MatrixRefresh TableAnalysis Shortening Rectangular

noncomputable section

/-- Jensen's inequality for an arbitrary finite probability distribution. -/
-- Auxiliary lemma (shortening); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Ω a set; P ∈ 𝒟(Ω); f ∈ Ω → ℝ, assume Ω is finite. Then

(𝔼_(u ← P) [f(u)])² ≤ 𝔼_(x ← P) [(f(x))²].
-/
theorem expect_sq_le {Ω : Type*} [Fintype Ω] (P : FiniteDistribution Ω) (f : Ω → ℝ) :
    P.expect f ^ 2 ≤ P.expect (fun x => f x ^ 2) := by
  simpa only [mul_one, one_pow, FiniteDistribution.expect_const] using
    expect_mul_sq_le P f (fun _ => 1)

/-- A mask in [0,1] cannot increase the second moment of a masked mean. -/
-- Auxiliary lemma (shortening); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Ω a set; P ∈ 𝒟(Ω); f, mask ∈ Ω → ℝ, assume Ω is finite; ∀ x, 0 ≤ mask(x); ∀ x, mask(x) ≤ 1. Then

(𝔼_(x ← P) [f(x) · mask(x)])² ≤ 𝔼_(x ← P) [(f(x))²].
-/
theorem masked_expect_sq_le {Ω : Type*} [Fintype Ω] (P : FiniteDistribution Ω)
    (f mask : Ω → ℝ) (h0 : ∀ x, 0 ≤ mask x) (h1 : ∀ x, mask x ≤ 1) :
    P.expect (fun x => f x * mask x) ^ 2 ≤ P.expect (fun x => f x ^ 2) := by
  apply (expect_sq_le P _).trans
  apply P.expect_mono
  intro x
  have hm : mask x ^ 2 ≤ 1 := by nlinarith [h0 x, h1 x]
  simpa only [mul_pow, mul_one] using mul_le_mul_of_nonneg_left hm (sq_nonneg (f x))

variable {F O Z : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [DecidableEq O] [Nonempty O] [Fintype Z]

variable {n t : ℕ} [Nonempty (U F n)] [Nonempty (U F (n+t))]
  [Nonempty (FullRank F n (n+t))]

/-- Per answer, the two stages of backward averaging contract the error square. -/
-- Auxiliary lemma (shortening); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); E ∈ (O × U(F, (n + t))) → (O × U(F, (n + t))) → ℝ; z ∈ Z; x, y ∈ O × U(F, n), we have

(Fractional.transport(r, E, z, x, y))² ≤ 𝔼_(H ← 𝒰_(FullRank(F, n, (n + t)))) [𝔼_(k ← 𝒰_(Kernel(H))) [(E(((x)₁, leftShare(H, (x)₂)), ((y)₁, rightLift(H, (y)₂, k))))²]].
-/
theorem transport_square_pointwise
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (E : (O × U F (n+t)) → (O × U F (n+t)) → ℝ)
    (z : Z) (x y : O × U F n) :
    Fractional.transport r E z x y ^ 2 ≤
      (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
        (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect (fun k =>
          E (x.1,leftShare H x.2) (y.1,rightLift H y.2 k) ^ 2)) := by
  unfold Fractional.transport
  apply (expect_sq_le _ _).trans
  apply FiniteDistribution.expect_mono
  intro H
  apply masked_expect_sq_le
  · intro k
    exact mul_nonneg ((r H).left_nonneg z x) ((r H).right_nonneg z (y,k))
  · intro k
    exact (mul_le_mul ((r H).left_le_one z x) ((r H).right_le_one z (y,k))
      ((r H).right_nonneg z (y,k)) (by norm_num)).trans_eq (by norm_num)

/-- Exact uniform backward marginals give L2 contraction on every secret fiber and on every (possibly correlated) distribution of retained old data. -/
-- Auxiliary lemma (shortening); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); E ∈ (O × U(F, (n + t))) → (O × U(F, (n + t))) → ℝ; z ∈ Z; old ∈ 𝒟((O × O)); s ∈ F, assume Fiber(F, n, s) ≠ ∅; Fiber(F, (n + t), s) ≠ ∅. Then

𝔼_(op ← (old ⊗ 𝒰_(Fiber(F, n, s)))) [(Fractional.transport(r, E, z, (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R)))²] ≤ 𝔼_(op ← (old ⊗ 𝒰_(Fiber(F, (n + t), s)))) [(E((((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R)))²].
-/
theorem transport_L2_sq
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (E : (O × U F (n+t)) → (O × U F (n+t)) → ℝ)
    (z : Z) (old : FiniteDistribution (O × O)) (s : F) [Nonempty (Fiber F n s)]
    [Nonempty (Fiber F (n+t) s)] :
    (old.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s))).expect (fun op =>
      Fractional.transport r E z (op.1.1,op.2.val.L) (op.1.2,op.2.val.R) ^ 2) ≤
    (old.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) s))).expect (fun op =>
      E (op.1.1,op.2.val.L) (op.1.2,op.2.val.R) ^ 2) := by
  simp only [expect_prod]
  apply old.expect_mono
  intro o
  calc
    _ ≤ (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s)).expect (fun p =>
        (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
          (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect (fun k =>
            E (o.1,leftShare H p.val.L) (o.2,rightLift H p.val.R k) ^ 2))) := by
      apply FiniteDistribution.expect_mono
      intro p
      exact transport_square_pointwise r E z (o.1,p.val.L) (o.2,p.val.R)
    _ = _ := backward_expect_kernel s (fun p => E (o.1,p.val.L) (o.2,p.val.R) ^ 2)

/-- RMS form of the per-answer contraction. -/
-- Auxiliary lemma (shortening); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); E ∈ (O × U(F, (n + t))) → (O × U(F, (n + t))) → ℝ; z ∈ Z; old ∈ 𝒟((O × O)); s ∈ F, assume Fiber(F, n, s) ≠ ∅; Fiber(F, (n + t), s) ≠ ∅. Then

‖ ((op ↦ Fractional.transport(r, E, z, (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R))))‖_(2,(old ⊗ 𝒰_(Fiber(F, n, s)))) ≤ ‖ ((op ↦ E((((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R))))‖_(2,(old ⊗ 𝒰_(Fiber(F, (n + t), s)))).
-/
theorem transport_L2
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (E : (O × U F (n+t)) → (O × U F (n+t)) → ℝ)
    (z : Z) (old : FiniteDistribution (O × O)) (s : F) [Nonempty (Fiber F n s)]
    [Nonempty (Fiber F (n+t) s)] :
    rms (old.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s))) (fun op =>
      Fractional.transport r E z (op.1.1,op.2.val.L) (op.1.2,op.2.val.R)) ≤
    rms (old.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) s))) (fun op =>
      E (op.1.1,op.2.val.L) (op.1.2,op.2.val.R)) :=
  Real.sqrt_le_sqrt (transport_L2_sq r E z old s)

/-- Applying the same operator to an answer probability and its approximation preserves their per-answer L2 error, with no factor from the answer alphabet. -/

/-
Mathematical statement (normal notation): Let 𝒯_z be the shortening transport for one answer z, with arbitrary fractional left/right leakage masks. For any real tables A,G, any distribution ρ of the old operand data, and any secret s,

‖𝒯_z(A)-𝒯_z(G)‖_(2, ρ ⊗ μₛⁿ) ≤ ‖A-G‖_(2, ρ ⊗ μₛⁿ⁺ᵗ).

Both encoding fibers are assumed nonempty. Thus the same transport contracts the approximation error in L₂.
-/
theorem transport_approximation_L2
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (prob G : (O × U F (n+t)) → (O × U F (n+t)) → ℝ)
    (z : Z) (old : FiniteDistribution (O × O)) (s : F) [Nonempty (Fiber F n s)]
    [Nonempty (Fiber F (n+t) s)] :
    rms (old.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s))) (fun op =>
      Fractional.transport r prob z (op.1.1,op.2.val.L) (op.1.2,op.2.val.R) -
        Fractional.transport r G z (op.1.1,op.2.val.L) (op.1.2,op.2.val.R)) ≤
    rms (old.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) s))) (fun op =>
      prob (op.1.1,op.2.val.L) (op.1.2,op.2.val.R) -
        G (op.1.1,op.2.val.L) (op.1.2,op.2.val.R)) := by
  have he : Fractional.transport r (prob - G) =
      Fractional.transport r prob - Fractional.transport r G :=
    (Fractional.transportLinear r).map_sub _ _
  have h := transport_L2 r (prob-G) z old s
  simpa only [he, Pi.sub_apply, Matrix.sub_apply] using h

end

end CircuitCompiler.ShorteningTransport
