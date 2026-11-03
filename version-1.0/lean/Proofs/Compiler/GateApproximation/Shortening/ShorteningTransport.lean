import Proofs.Compiler.GateApproximation.Shortening.ShorteningExecution



/-!
# Squared-error transport through shortening

The ordinary branch's unique leakage leaf partitions its deterministic inputs. Averaging over the two uniform tails contracts the sum of squared errors by Jensen. Conditioning onto the explicitly counted accepted subset incurs exactly the reciprocal of its probability, proved using finite injections.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace CircuitCompiler.Shortening

open Refresh MatrixRefresh

/-- Jensen with a deterministic partition: summing the squared masked means over all answers does not introduce a factor equal to the answer count. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Ω,B a set; P ∈ 𝒟(Ω); e ∈ Ω → ℝ; answer ∈ Ω → B, assume Ω is finite; B is finite. Then

(∑_b ((𝔼_(ω ← P) [{ e(ω) if answer(ω) = b,; 0 otherwise }])²)) ≤ 𝔼_(ω ← P) [(e(ω))²].
-/
theorem partitioned_expect_sq_le {Ω B : Type*} [Fintype Ω] [Fintype B]
    [DecidableEq B] (P : FiniteDistribution Ω) (e : Ω → ℝ) (answer : Ω → B) :
    (∑ b, (P.expect (fun ω => if answer ω = b then e ω else 0)) ^ 2) ≤
      P.expect (fun ω => e ω ^ 2) := by
  calc
    _ ≤ ∑ b, P.expect (fun ω => (if answer ω = b then e ω else 0) ^ 2) := by
      apply Finset.sum_le_sum
      intro b _
      have h := expect_mul_sq_le P
        (fun ω => if answer ω = b then e ω else 0) (fun _ => 1)
      simpa only [mul_one, one_pow, FiniteDistribution.expect_const] using h
    _ = _ := by
      rw [← expect_sum]
      apply congrArg P.expect
      funext ω
      simp only [ite_pow, zero_pow (by omega : 2 ≠ 0), Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]

/-- Uniform conditioning on an embedded finite subset has precisely the cardinality-ratio cost for every nonnegative squared-error function. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A,B a set; e ∈ A ↪ B; f ∈ B → ℝ, assume A is finite; B is finite; A ≠ ∅; B ≠ ∅; ∀ b, 0 ≤ f(b). Then

𝔼_(a ← 𝒰_A) [f(e(a))] ≤ (|B| / |A|) · 𝔼_(v ← 𝒰_B) [f(v)].
-/
theorem uniform_embedding_expect_le {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (e : A ↪ B) (f : B → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (FiniteDistribution.uniform : FiniteDistribution A).expect (fun a => f (e a)) ≤
      ((Fintype.card B : ℝ) / Fintype.card A) *
        (FiniteDistribution.uniform : FiniteDistribution B).expect f := by
  classical
  have hsum : (∑ a, f (e a)) ≤ ∑ b, f b := by
    calc
      _ = ∑ b ∈ Finset.univ.image e, f b := by
        rw [Finset.sum_image]
        exact fun _ _ _ _ h => e.injective h
      _ ≤ ∑ b, f b := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        exact fun b _ _ => hf b
  have ha : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hb : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  simp only [FiniteDistribution.expect, FiniteDistribution.uniform, ← Finset.mul_sum]
  calc
    _ ≤ (Fintype.card A : ℝ)⁻¹ * ∑ b, f b :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr ha.le)
    _ = _ := by field_simp

/-- The error operator for a fixed ordinary-branch input/output encoding. The answer function may depend on both old sides, all reconstructed long shares, and the preceding matrix leaf. No rectangle property is needed for this squared-error statement. -/
/-
Mathematical definition (normal notation): For F,O,A,B a set; n, t ∈ ℕ; c, ε, z ∈ F; err ∈ A → O → Auxiliary(F, (n + t), z) → ℝ; answer ∈ A → O → Accepted(F, n, t, c, ε, z) → B; α ∈ A; β ∈ B; o ∈ O; p ∈ Fiber(F, n, (c + ε · z)), assume F is a field; F is finite; O is finite; A is finite; B is finite; ε ≠ 0. define

errorTransport(c, ε, z, err, answer, α, β, o, p) := 𝔼_(tails ← 𝒰_(V(F, t) × V(F, t))) [Let a := reconstruct(c, ε, z, p, (tails)₁, (tails)₂); { err(α, o, acceptedEmbedding(c, ε, z, a)) if answer(α, o, a) = β,; 0 otherwise }].
-/
noncomputable def errorTransport {F O A B : Type*} [Field F] [Fintype F]
    [DecidableEq F] [Fintype O] [Fintype A] [Fintype B] [DecidableEq B]
    {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    (err : A → O → Auxiliary F (n + t) z → ℝ)
    (answer : A → O → Accepted F n t c ε z → B)
    (α : A) (β : B) (o : O) (p : Fiber F n (c + ε * z)) : ℝ :=
  (FiniteDistribution.uniform : FiniteDistribution (V F t × V F t)).expect (fun tails =>
    let a := reconstruct c ε z hε p tails.1 tails.2
    if answer α o a = β then err α o (acceptedEmbedding c ε z a) else 0)

/-- Tail averaging and the deterministic partition contract the complete answer-indexed squared error at every fixed old encoding and short output. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For F,O,A,B a set; n, t ∈ ℕ; c, ε, z ∈ F; err ∈ A → O → Auxiliary(F, (n + t), z) → ℝ; answer ∈ A → O → Accepted(F, n, t, c, ε, z) → B; o ∈ O; p ∈ Fiber(F, n, (c + ε · z)), assume F is a field; F is finite; O is finite; A is finite; B is finite; ε ≠ 0. Then

(∑_α (∑ᵦ ((errorTransport(c, ε, z, err, answer, α, β, o, p))²))) ≤ 𝔼_(tails ← 𝒰_(V(F, t) × V(F, t))) [∑_α ((err(α, o, acceptedEmbedding(c, ε, z, reconstruct(c, ε, z, p, (tails)₁, (tails)₂))))²)].
-/
theorem errorTransport_pointwise {F O A B : Type*} [Field F] [Fintype F]
    [DecidableEq F] [Fintype O] [Fintype A] [Fintype B] [DecidableEq B]
    {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    (err : A → O → Auxiliary F (n + t) z → ℝ)
    (answer : A → O → Accepted F n t c ε z → B)
    (o : O) (p : Fiber F n (c + ε * z)) :
    (∑ α, ∑ β, errorTransport c ε z hε err answer α β o p ^ 2) ≤
      (FiniteDistribution.uniform : FiniteDistribution (V F t × V F t)).expect (fun tails =>
        ∑ α, err α o (acceptedEmbedding c ε z
          (reconstruct c ε z hε p tails.1 tails.2)) ^ 2) := by
  rw [expect_sum]
  apply Finset.sum_le_sum
  intro α _
  exact partitioned_expect_sq_le _ _ _

/-- Uniform sampling of a finite product is independent sampling. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A,B a set, assume A is finite; B is finite; A ≠ ∅; B ≠ ∅. Then

𝒰_(A × B) = (𝒰_A ⊗ 𝒰_B).
-/
theorem uniform_prod {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    (FiniteDistribution.uniform : FiniteDistribution (A × B)) =
      (FiniteDistribution.uniform : FiniteDistribution A).prod (FiniteDistribution.uniform : FiniteDistribution B) := by
  ext p
  simp [FiniteDistribution.uniform, FiniteDistribution.prod, FiniteDistribution.joint, Fintype.card_prod, mul_comm]

/-- The accepted change of variables as an equality of expectations. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For F a set; n, t ∈ ℕ; c, ε, z ∈ F; f ∈ Accepted(F, n, t, c, ε, z) → ℝ, assume F is a field; F is finite; ε ≠ 0; Accepted(F, n, t, c, ε, z) ≠ ∅; Fiber(F, n, (c + ε · z)) ≠ ∅. Then

𝔼_(u ← 𝒰_(Accepted(F, n, t, c, ε, z))) [f(u)] = 𝔼_(p ← 𝒰_(Fiber(F, n, (c + ε · z)))) [𝔼_(tails ← 𝒰_(V(F, t) × V(F, t))) [f(reconstruct(c, ε, z, p, (tails)₁, (tails)₂))]].
-/
theorem accepted_expect {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    [Nonempty (Accepted F n t c ε z)] [Nonempty (Fiber F n (c + ε * z))]
    (f : Accepted F n t c ε z → ℝ) :
    (FiniteDistribution.uniform : FiniteDistribution (Accepted F n t c ε z)).expect f =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (c + ε * z))).expect (fun p =>
        (FiniteDistribution.uniform : FiniteDistribution (V F t × V F t)).expect (fun tails =>
          f (reconstruct c ε z hε p tails.1 tails.2))) := by
  have h := congrArg
    (fun P : FiniteDistribution (Fiber F n (c + ε * z) × (V F t × V F t)) =>
      P.expect (fun p => f (reconstruct c ε z hε p.1 p.2.1 p.2.2)))
    (accepted_joint_uniform (n := n) (t := t) c ε z hε)
  try dsimp only at h
  rw [expect_map, expect_prod, ← uniform_prod] at h
  change (FiniteDistribution.uniform : FiniteDistribution (Accepted F n t c ε z)).expect
    (fun a => f (reconstruct c ε z hε (output c ε z a) a.val.B a.val.D)) = _ at h
  simpa only [reconstruct_output] using h

/-- Complete `L₂` transport in the auxiliary experiment, with the exact conditioning cost `1/a_w` and no factor for the number of leakage leaves. The mean-square input bound may now be supplied by the joint matrix lemma. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For F,O,A,B a set; n, t ∈ ℕ; c, ε, z ∈ F; Pold ∈ 𝒟(O); err ∈ A → O → Auxiliary(F, (n + t), z) → ℝ; answer ∈ A → O → Accepted(F, n, t, c, ε, z) → B, assume F is a field; F is finite; O is finite; A is finite; B is finite; ε ≠ 0; Accepted(F, n, t, c, ε, z) ≠ ∅; Fiber(F, n, (c + ε · z)) ≠ ∅; Auxiliary(F, (n + t), z) ≠ ∅. Then

𝔼_(op ← (Pold ⊗ 𝒰_(Fiber(F, n, (c + ε · z))))) [∑_α (∑ᵦ ((errorTransport(c, ε, z, err, answer, α, β, (op)₁, (op)₂))²))] ≤ (acceptanceMass(n = n, t = t, c, ε, z))⁻¹ · 𝔼_(op ← (Pold ⊗ 𝒰_(Auxiliary(F, (n + t), z)))) [∑_α ((err(α, (op)₁, (op)₂))²)].
-/
theorem errorTransport_L2 {F O A B : Type*} [Field F] [Fintype F]
    [DecidableEq F] [Fintype O] [Fintype A] [Fintype B] [DecidableEq B]
    {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    [Nonempty (Accepted F n t c ε z)] [Nonempty (Fiber F n (c + ε * z))]
    [Nonempty (Auxiliary F (n + t) z)]
    (Pold : FiniteDistribution O) (err : A → O → Auxiliary F (n + t) z → ℝ)
    (answer : A → O → Accepted F n t c ε z → B) :
    (Pold.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (c + ε * z)))).expect
      (fun op => ∑ α, ∑ β, errorTransport c ε z hε err answer α β op.1 op.2 ^ 2) ≤
      (acceptanceMass (n := n) (t := t) c ε z)⁻¹ *
        (Pold.prod (FiniteDistribution.uniform : FiniteDistribution (Auxiliary F (n + t) z))).expect
          (fun op => ∑ α, err α op.1 op.2 ^ 2) := by
  have hratio : (Fintype.card (Auxiliary F (n + t) z) : ℝ) /
      Fintype.card (Accepted F n t c ε z) =
      (acceptanceMass (n := n) (t := t) c ε z)⁻¹ := by
    simp only [acceptanceMass, auxiliary_card, accepted_card c ε z hε,
      Nat.cast_mul, Nat.cast_pow, inv_div]
  rw [expect_prod, expect_prod, ← expect_smul]
  apply Pold.expect_mono
  intro o
  calc
    _ ≤ (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (c + ε * z))).expect (fun p =>
        (FiniteDistribution.uniform : FiniteDistribution (V F t × V F t)).expect (fun tails =>
          ∑ α, err α o (acceptedEmbedding c ε z
            (reconstruct c ε z hε p tails.1 tails.2)) ^ 2)) :=
      FiniteDistribution.expect_mono _ (errorTransport_pointwise c ε z hε err answer o)
    _ = (FiniteDistribution.uniform : FiniteDistribution (Accepted F n t c ε z)).expect
        (fun a => ∑ α, err α o (acceptedEmbedding c ε z a) ^ 2) :=
      (accepted_expect (n := n) (t := t) c ε z hε
        (fun a : Accepted F n t c ε z => ∑ α, err α o (acceptedEmbedding c ε z a) ^ 2)).symm
    _ ≤ _ := by
      rw [← hratio]
      exact uniform_embedding_expect_le (acceptedEmbedding c ε z)
        (fun p => ∑ α, err α o p ^ 2)
        (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end CircuitCompiler.Shortening
