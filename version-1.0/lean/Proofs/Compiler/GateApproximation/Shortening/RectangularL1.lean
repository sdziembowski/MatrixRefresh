import Proofs.Compiler.GateApproximation.Shortening.RectangularJoint
import Proofs.Compiler.GateApproximation.Shortening.RectangularNuclear



/-!
# Summed mean-error contraction for the rectangular table operator
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace CircuitCompiler.Rectangular

open Refresh MatrixRefresh TableAnalysis Shortening

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

variable {O Z : Type*} [Fintype O] [DecidableEq O] [Nonempty O] [Fintype Z]

variable {n t : ℕ} [Nonempty (U F n)] [Nonempty (U F (n+t))]
  [Nonempty (FullRank F n (n+t))]

/-- Summing over an exhaustive rectangle partition loses no answer factor. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ∏_(H ∈ FullRank(F, n, (n + t))) RectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); E ∈ ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))); x, y ∈ O × U(F, n), we have

(∑_z (|transport(r, E, z, x, y)|)) ≤ 𝔼_(H ← 𝒰_(FullRank(F, n, (n + t)))) [𝔼_(k ← 𝒰_(Kernel(H))) [|E(((x)₁, leftShare(H, (x)₂)), ((y)₁, rightLift(H, (y)₂, k)))|]].
-/
theorem transport_abs_sum
    (r : (H : FullRank F n (n+t)) → RectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (E : Matrix (O × U F (n+t)) (O × U F (n+t)) ℝ)
    (x y : O × U F n) :
    (∑ z, |transport r E z x y|) ≤
      (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
        (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect (fun k =>
          |E (x.1,leftShare H x.2) (y.1,rightLift H y.2 k)|)) := by
  unfold transport
  calc
    _ ≤ ∑ z, (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
        (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect (fun k =>
          |if (r H).left z x && (r H).right z (y,k) then
            E (x.1,leftShare H x.2) (y.1,rightLift H y.2 k) else 0|)) := by
      apply Finset.sum_le_sum
      intro z _
      apply (abs_expect_le_expect_abs _ _).trans
      exact FiniteDistribution.expect_mono _ (fun H => abs_expect_le_expect_abs _ _)
    _ = _ := by
      rw [← expect_sum]
      apply congrArg (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect
      funext H
      rw [← expect_sum]
      apply congrArg (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect
      funext k
      have hi (z : Z) :
          |if (r H).left z x && (r H).right z (y,k) then
            E (x.1,leftShare H x.2) (y.1,rightLift H y.2 k) else 0| =
          |E (x.1,leftShare H x.2) (y.1,rightLift H y.2 k)| *
            (if (r H).left z x && (r H).right z (y,k) then 1 else 0) := by
        split_ifs <;> simp
      simp_rw [hi]
      rw [← Finset.mul_sum,(r H).partition,mul_one]

/-- Arbitrary correlations among the old operands are retained in `old`. The short and long output encodings have their exact uniform fiber distributions. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ∏_(H ∈ FullRank(F, n, (n + t))) RectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); E ∈ ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))); old ∈ 𝒟((O × O)); s ∈ F, assume Fiber(F, n, s) ≠ ∅; Fiber(F, (n + t), s) ≠ ∅. Then

𝔼_(op ← (old ⊗ 𝒰_(Fiber(F, n, s)))) [∑_z (|transport(r, E, z, (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R))|)] ≤ 𝔼_(op ← (old ⊗ 𝒰_(Fiber(F, (n + t), s)))) [|E((((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R))|].
-/
theorem transport_L1
    (r : (H : FullRank F n (n+t)) → RectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (E : Matrix (O × U F (n+t)) (O × U F (n+t)) ℝ)
    (old : FiniteDistribution (O × O)) (s : F) [Nonempty (Fiber F n s)]
    [Nonempty (Fiber F (n+t) s)] :
    (old.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s))).expect (fun op =>
      ∑ z, |transport r E z (op.1.1,op.2.val.L) (op.1.2,op.2.val.R)|) ≤
    (old.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) s))).expect (fun op =>
      |E (op.1.1,op.2.val.L) (op.1.2,op.2.val.R)|) := by
  simp only [expect_prod]
  apply old.expect_mono
  intro o
  calc
    _ ≤ (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s)).expect (fun p =>
        (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
          (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect (fun k =>
            |E (o.1,leftShare H p.val.L) (o.2,rightLift H p.val.R k)|))) :=
      by
        apply FiniteDistribution.expect_mono
        intro p
        exact transport_abs_sum r E (o.1,p.val.L) (o.2,p.val.R)
    _ = _ := by
      have h := backward_expect_kernel s (fun p => |E (o.1,p.val.L) (o.2,p.val.R)|)
      exact h

/-- The very same approximating tables satisfy both the nuclear estimate and the mean-error estimate; they are not chosen separately for each secret. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A a set; r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) RectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); k, G ∈ A → ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))); old ∈ 𝒟((O × O)); s ∈ F, assume A is finite; Fiber(F, n, s) ≠ ∅; Fiber(F, (n + t), s) ≠ ∅. Then

(∑ₐ (∑_z (‖ transport(r(a), G(a), z)‖_*))) ≤ √(|Z|) · (∑ₐ (‖ G(a)‖_*)) ∧ (∑ₐ (𝔼_(op ← (old ⊗ 𝒰_(Fiber(F, n, s)))) [∑_z (|transport(r(a), k(a), z, (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R)) - transport(r(a), G(a), z, (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R))|)])) ≤ ∑ₐ (𝔼_(op ← (old ⊗ 𝒰_(Fiber(F, (n + t), s)))) [|k(a, (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R)) - G(a, (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R))|]).
-/
theorem transport_approximation {A : Type*} [Fintype A]
    (r : A → (H : FullRank F n (n+t)) → RectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (k G : A → Matrix (O × U F (n+t)) (O × U F (n+t)) ℝ)
    (old : FiniteDistribution (O × O)) (s : F) [Nonempty (Fiber F n s)]
    [Nonempty (Fiber F (n+t) s)] :
    (∑ a, ∑ z, tableNuclearNorm (transport (r a) (G a) z)) ≤
      Real.sqrt (Fintype.card Z) * (∑ a, tableNuclearNorm (G a)) ∧
    (∑ a, (old.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s))).expect (fun op =>
      ∑ z, |transport (r a) (k a) z (op.1.1,op.2.val.L) (op.1.2,op.2.val.R) -
        transport (r a) (G a) z (op.1.1,op.2.val.L) (op.1.2,op.2.val.R)|)) ≤
    ∑ a, (old.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) s))).expect (fun op =>
      |k a (op.1.1,op.2.val.L) (op.1.2,op.2.val.R) -
        G a (op.1.1,op.2.val.L) (op.1.2,op.2.val.R)|) := by
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ => transport_nuclear (r a) (G a))
  · apply Finset.sum_le_sum
    intro a _
    have he : transport (r a) (k a - G a) = transport (r a) (k a) - transport (r a) (G a) :=
      (transportLinear (r a)).map_sub _ _
    have h := transport_L1 (r a) (k a - G a) old s
    simpa only [he,Pi.sub_apply,Matrix.sub_apply] using h

end

end CircuitCompiler.Rectangular
