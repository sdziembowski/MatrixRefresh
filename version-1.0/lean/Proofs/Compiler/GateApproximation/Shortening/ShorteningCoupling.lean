import Proofs.Compiler.GateApproximation.MatrixPhase.Disintegration
import Proofs.Compiler.GateApproximation.Shortening.ShorteningExecution



/-!
# Full observed shortening and its canonical coupling

After the matrix and its tape have been erased, retained leakage and subsequent shortening leakage determine a conditional answer distribution given the old data and long encoding. The coupling retains that entire answer. The exceptional branch can use any correct fallback, and its cost is charged once.
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler.Shortening

open Refresh

variable {F Z : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype Z]

/-- Execute shortening and retain the entire answer. On failure the caller supplies a correct fallback; its output type enforces the represented value. -/
/- Mathematical definition (normal notation): Run the shortening map on the supplied long data. On success, return its output encoding together with the specified finite answer; on failure, sample a supplied fallback pair. In either case the output encoding is required to represent c+ε z. -/
noncomputable def observedRun {n t : ℕ} (c ε z : F)
    (answer : Auxiliary F (n + t) z → FiniteDistribution Z)
    (fallback : Auxiliary F (n + t) z → FiniteDistribution (Fiber F n (c + ε * z) × Z))
    (p : Auxiliary F (n + t) z) : FiniteDistribution (Fiber F n (c + ε * z) × Z) :=
  match run c ε z p with
  | some u => (answer p).map (fun a => (u, a))
  | none => fallback p

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; answer ∈ Auxiliary(F, (n + t), z) → 𝒟(Z); fallback ∈ Auxiliary(F, (n + t), z) → 𝒟((Fiber(F, n, (c + ε · z)) × Z)); p ∈ Accepted(F, n, t, c, ε, z), we have

observedRun(c, ε, z, answer, fallback, acceptedEmbedding(c, ε, z, p)) = (((a ↦ (output(c, ε, z, p), a)))_*answer(acceptedEmbedding(c, ε, z, p))).
-/
theorem observedRun_accepted {n t : ℕ} (c ε z : F)
    (answer : Auxiliary F (n + t) z → FiniteDistribution Z)
    (fallback : Auxiliary F (n + t) z → FiniteDistribution (Fiber F n (c + ε * z) × Z))
    (p : Accepted F n t c ε z) :
    observedRun c ε z answer fallback (acceptedEmbedding c ε z p) =
      (answer (acceptedEmbedding c ε z p)).map (fun a => (output c ε z p, a)) := by
  simp [observedRun, run_acceptedEmbedding]

/-- The canonical conditional answer given a prescribed fresh short encoding. It retains every dependence on the accepted long data through conditioning. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; answer ∈ Auxiliary(F, (n + t), z) → 𝒟(Z); u ∈ Fiber(F, n, (c + ε · z)), assume Accepted(F, n, t, c, ε, z) ≠ ∅. define

acceptedAnswerDistribution(c, ε, z, answer, u) := bind(conditional(𝒰_(Accepted(F, n, t, c, ε, z)), output(c, ε, z), u), ((p ↦ answer(acceptedEmbedding(c, ε, z, p))))).
-/
noncomputable def acceptedAnswerDistribution {n t : ℕ} (c ε z : F)
    [Nonempty (Accepted F n t c ε z)]
    (answer : Auxiliary F (n + t) z → FiniteDistribution Z)
    (u : Fiber F n (c + ε * z)) : FiniteDistribution Z :=
  (conditional (FiniteDistribution.uniform : FiniteDistribution (Accepted F n t c ε z))
    (output c ε z) u).bind (fun p => answer (acceptedEmbedding c ε z p))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A,B,C a set; P ∈ 𝒟(A); f ∈ A → B; Q ∈ B → 𝒟(C), assume A is finite; B is finite; C is finite. Then

bind((f_*P), Q) = bind(P, ((a ↦ Q(f(a))))).
-/
private theorem map_bind_eq {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (P : FiniteDistribution A) (f : A → B) (Q : B → FiniteDistribution C) :
    (P.map f).bind Q = P.bind (fun a => Q (f a)) := by
  simp [FiniteDistribution.map, FiniteDistribution.bind_assoc]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A,B,C a set; P ∈ 𝒟(A); Q ∈ A → 𝒟(B); f ∈ A → C, assume A is finite; B is finite; C is finite. Then

(((ab ↦ (f((ab)₁), (ab)₂)))_*P.joint(Q)) = bind(P, ((a ↦ (((b ↦ (f(a), b)))_*Q(a))))).
-/
private theorem joint_map_eq {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (P : FiniteDistribution A) (Q : A → FiniteDistribution B) (f : A → C) :
    (P.joint Q).map (fun ab => (f ab.1, ab.2)) =
      P.bind (fun a => (Q a).map (fun b => (f a, b))) := by
  classical
  ext cb
  simp only [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.joint,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- Uniform accepted long data is exactly a fresh short encoding followed by the conditional answer distribution, including all leakage. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; answer ∈ Auxiliary(F, (n + t), z) → 𝒟(Z); fallback ∈ Auxiliary(F, (n + t), z) → 𝒟((Fiber(F, n, (c + ε · z)) × Z)), assume ε ≠ 0; Accepted(F, n, t, c, ε, z) ≠ ∅; Fiber(F, n, (c + ε · z)) ≠ ∅. Then

bind((acceptedEmbedding(c, ε, z)_*𝒰_(Accepted(F, n, t, c, ε, z))), observedRun(c, ε, z, answer, fallback)) = joint(𝒰_(Fiber(F, n, (c + ε · z))))(acceptedAnswerDistribution(c, ε, z, answer)).
-/
theorem observed_accepted_canonical {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    [Nonempty (Accepted F n t c ε z)] [Nonempty (Fiber F n (c + ε * z))]
    (answer : Auxiliary F (n + t) z → FiniteDistribution Z)
    (fallback : Auxiliary F (n + t) z → FiniteDistribution (Fiber F n (c + ε * z) × Z)) :
    ((FiniteDistribution.uniform : FiniteDistribution (Accepted F n t c ε z)).map
      (acceptedEmbedding c ε z)).bind (observedRun c ε z answer fallback) =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (c + ε * z))).joint
        (acceptedAnswerDistribution c ε z answer) := by
  rw [map_bind_eq]
  simp_rw [observedRun_accepted]
  rw [← joint_map_eq]
  have h := answer_joint_conditional
    (FiniteDistribution.uniform : FiniteDistribution (Accepted F n t c ε z))
    (output c ε z) (fun p => answer (acceptedEmbedding c ε z p))
  rw [accepted_output_uniform c ε z hε] at h
  exact h.symm

/-- The real observed gate is close to the canonical fresh-output experiment for every answer distribution and correct fallback. The two explicit costs are the virtual-zero long share and the ordinary-branch failure mass. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; answer ∈ Auxiliary(F, (n + t), z) → 𝒟(Z); fallback ∈ Auxiliary(F, (n + t), z) → 𝒟((Fiber(F, n, (c + ε · z)) × Z)), assume 2 ≤ n; ε ≠ 0; Accepted(F, n, t, c, ε, z) ≠ ∅; Fiber(F, n, (c + ε · z)) ≠ ∅; Fiber(F, (n + t), z) ≠ ∅; Auxiliary(F, (n + t), z) ≠ ∅. Then

δ(bind((actualEmbedding(z)_*𝒰_(Fiber(F, (n + t), z))), observedRun(c, ε, z, answer, fallback)), joint(𝒰_(Fiber(F, n, (c + ε · z))))(acceptedAnswerDistribution(c, ε, z, answer))) ≤ 1 / (|F|)^(n + t − 1) + (|F| + 1) / (|F|)ⁿ.
-/
theorem observed_actual_canonical_distance {n t : ℕ} (hn : 2 ≤ n)
    (c ε z : F) (hε : ε ≠ 0)
    [Nonempty (Accepted F n t c ε z)] [Nonempty (Fiber F n (c + ε * z))]
    [Nonempty (Fiber F (n + t) z)] [Nonempty (Auxiliary F (n + t) z)]
    (answer : Auxiliary F (n + t) z → FiniteDistribution Z)
    (fallback : Auxiliary F (n + t) z → FiniteDistribution (Fiber F n (c + ε * z) × Z)) :
    statisticalDistance
      (((FiniteDistribution.uniform : FiniteDistribution (Fiber F (n + t) z)).map (actualEmbedding z)).bind
        (observedRun c ε z answer fallback))
      ((FiniteDistribution.uniform : FiniteDistribution (Fiber F n (c + ε * z))).joint
        (acceptedAnswerDistribution c ε z answer)) ≤
      1 / (fieldCard F : ℝ) ^ (n + t - 1) + ((fieldCard F : ℝ) + 1) / (fieldCard F : ℝ) ^ n := by
  rw [← observed_accepted_canonical c ε z hε answer fallback]
  refine (statisticalDistance_bind_le _ _ _).trans ?_
  refine (statisticalDistance_triangle _
    (FiniteDistribution.uniform : FiniteDistribution (Auxiliary F (n + t) z)) _).trans ?_
  have h₁ := auxiliary_actual_distance (by omega : 2 ≤ n + t) z
  rw [statisticalDistance_symm] at h₁
  exact add_le_add h₁ ((auxiliary_accepted_distance c ε z hε).trans (failureMass_le hn c ε z))

end CircuitCompiler.Shortening
