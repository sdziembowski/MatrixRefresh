import Proofs.Compiler.GateApproximation.Shortening.ShorteningTransport



/-!
# Transporting the matrix error to the auxiliary shortening experiment

The error may be unbounded on actual encodings. Its squared sum is bounded by one only on the auxiliary zero-right points. A finite counting argument, not a bounded-test total-variation argument, therefore controls the extra error.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace CircuitCompiler.Shortening

open Refresh MatrixRefresh

/-- Uniformly extending a finite sample space costs only the omitted fraction when the new points contribute at most one. The function may be unbounded on the original sample space. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A,B a set; e ∈ A ↪ B; f ∈ B → ℝ, assume A is finite; B is finite; A ≠ ∅; B ≠ ∅; ∀ b, 0 ≤ f(b); ∀ b, ¬ (∃ a, e(a) = b) → f(b) ≤ 1. Then

𝔼_(u ← 𝒰_B) [f(u)] ≤ 𝔼_(a ← 𝒰_A) [f(e(a))] + (1 - |A| / |B|).
-/
theorem uniform_embedding_expect_upper {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (e : A ↪ B) (f : B → ℝ)
    (hf : ∀ b, 0 ≤ f b) (hout : ∀ b, (¬∃ a, e a = b) → f b ≤ 1) :
    (FiniteDistribution.uniform : FiniteDistribution B).expect f ≤
      (FiniteDistribution.uniform : FiniteDistribution A).expect (fun a => f (e a)) +
        (1 - (Fintype.card A : ℝ) / Fintype.card B) := by
  classical
  let S := Finset.univ.image e
  have hcard : S.card = Fintype.card A := by simp [S, Finset.card_image_of_injective, e.injective]
  have hS : (∑ b ∈ S, f b) = ∑ a, f (e a) := by
    dsimp [S]
    exact Finset.sum_image (fun _ _ _ _ h => e.injective h)
  have hOne : (∑ b : B, if b ∈ S then (1 : ℝ) else 0) = Fintype.card A := by
    rw [← Finset.sum_filter]
    simp [hcard]
  have hComplement : (∑ b : B, if b ∈ S then (0 : ℝ) else 1) =
      Fintype.card B - Fintype.card A := by
    have hp (b : B) : (if b ∈ S then (0 : ℝ) else 1) =
        1 - (if b ∈ S then 1 else 0) := by split_ifs <;> norm_num
    simp_rw [hp]
    rw [Finset.sum_sub_distrib, hOne]
    simp
  have hsum : (∑ b, f b) ≤ (∑ a, f (e a)) +
      ((Fintype.card B : ℝ) - Fintype.card A) := by
    calc
      _ ≤ ∑ b, ((if b ∈ S then f b else 0) + (if b ∈ S then (0 : ℝ) else 1)) := by
        apply Finset.sum_le_sum
        intro b _
        by_cases hb : b ∈ S
        · simp [hb]
        · simp only [hb, if_false, zero_add]
          apply hout b
          simpa [S] using hb
      _ = _ := by
        rw [Finset.sum_add_distrib, hComplement, ← Finset.sum_filter]
        simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using congrArg
          (fun v : ℝ => v + ((Fintype.card B : ℝ) - Fintype.card A)) hS
  have ha : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hb : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hc : (Fintype.card A : ℝ) ≤ Fintype.card B := by
    exact_mod_cast Fintype.card_le_of_injective e e.injective
  have hsum0 : (0 : ℝ) ≤ ∑ a, f (e a) := Finset.sum_nonneg (fun a _ => hf (e a))
  simp only [FiniteDistribution.expect, FiniteDistribution.uniform, ← Finset.mul_sum]
  calc
    _ ≤ (Fintype.card B : ℝ)⁻¹ *
        ((∑ a, f (e a)) + ((Fintype.card B : ℝ) - Fintype.card A)) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hb.le)
    _ = (∑ a, f (e a)) / Fintype.card B + (1 - (Fintype.card A : ℝ) / Fintype.card B) := by
      field_simp
    _ ≤ (∑ a, f (e a)) / Fintype.card A + (1 - (Fintype.card A : ℝ) / Fintype.card B) :=
      add_le_add (div_le_div_of_nonneg_left hsum0 ha hc) (le_refl _)
    _ = _ := by ring

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The auxiliary points omitted by the actual protocol are exactly the zero-right-share points. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; z ∈ F; p ∈ Auxiliary(F, m, z), we have

(∃ a ∈ Fiber(F, m, z), actualEmbedding(z, a) = p) ⇔ (p)₂ ≠ 0.
-/
theorem actualEmbedding_range_iff {m : ℕ} (z : F) (p : Auxiliary F m z) :
    (∃ a : Fiber F m z, actualEmbedding z a = p) ↔ p.2.val ≠ 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.val.R.property
  · intro h
    refine ⟨⟨⟨p.1, ⟨p.2.val, h⟩⟩, p.2.property⟩, ?_⟩
    apply Sigma.subtype_ext <;> rfl

/-- The fraction of auxiliary points omitted from the actual encoding carrier is at most `q^(1-m)`, including the exceptional zero-secret fiber. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; z ∈ F, assume 2 ≤ m. Then

1 - |Fiber(F, m, z)| / |Auxiliary(F, m, z)| ≤ 1 / (|F|)^(m − 1).
-/
theorem auxiliary_missing_mass_le {m : ℕ} (hm : 2 ≤ m) (z : F) :
    1 - (Fintype.card (Fiber F m z) : ℝ) / Fintype.card (Auxiliary F m z) ≤
      1 / (fieldCard F : ℝ) ^ (m - 1) := by
  have hN : 0 < fieldCard F ^ m - 1 := by have := four_le_pow (F := F) hm; omega
  have hP : 0 < fieldCard F ^ (m - 1) := Nat.pow_pos (fieldCard_pos (F := F))
  have hNr : (0 : ℝ) < (fieldCard F ^ m - 1 : ℕ) := by exact_mod_cast hN
  have hPr : (0 : ℝ) < fieldCard F ^ (m - 1) := by exact_mod_cast hP
  rw [auxiliary_card]
  by_cases hz : z = 0
  · subst z
    rw [fiber_card_zero, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega :
      1 ≤ fieldCard F ^ (m - 1))]
    push_cast
    have hNr' : ((fieldCard F ^ m - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hNr
    have hPr' : (fieldCard F : ℝ) ^ (m - 1) ≠ 0 := ne_of_gt hPr
    field_simp
    nlinarith
  · rw [fiber_card_of_ne_zero m z hz]
    have hden : (((fieldCard F ^ m - 1) * fieldCard F ^ (m - 1) : ℕ) : ℝ) ≠ 0 := by positivity
    rw [div_self hden, sub_self]
    positivity

/-- Mean squared error in the auxiliary distribution is bounded by its counterpart under the actual distribution plus the virtual-zero cost, with the old input distribution retained. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For O,A a set; m ∈ ℕ; z ∈ F; P ∈ 𝒟(O); err ∈ A → O → Auxiliary(F, m, z) → ℝ, assume O is finite; A is finite; 2 ≤ m; Fiber(F, m, z) ≠ ∅; Auxiliary(F, m, z) ≠ ∅; ∀ o, p, ((p)₂ = 0) ⇒ (∑_α ((err(α, o, p))²)) ≤ 1. Then

𝔼_(op ← (P ⊗ 𝒰_(Auxiliary(F, m, z)))) [∑_α ((err(α, (op)₁, (op)₂))²)] ≤ 𝔼_(op ← (P ⊗ 𝒰_(Fiber(F, m, z)))) [∑_α ((err(α, (op)₁, actualEmbedding(z, (op)₂)))²)] + 1 / (|F|)^(m − 1).
-/
theorem auxiliary_error_extension {O A : Type*} [Fintype O] [Fintype A]
    {m : ℕ} (hm : 2 ≤ m) (z : F)
    [Nonempty (Fiber F m z)] [Nonempty (Auxiliary F m z)]
    (P : FiniteDistribution O) (err : A → O → Auxiliary F m z → ℝ)
    (hzero : ∀ o p, p.2.val = 0 → (∑ α, err α o p ^ 2) ≤ 1) :
    (P.prod (FiniteDistribution.uniform : FiniteDistribution (Auxiliary F m z))).expect
      (fun op => ∑ α, err α op.1 op.2 ^ 2) ≤
      (P.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F m z))).expect
        (fun op => ∑ α, err α op.1 (actualEmbedding z op.2) ^ 2) +
          1 / (fieldCard F : ℝ) ^ (m - 1) := by
  rw [expect_prod, expect_prod, ← FiniteDistribution.expect_const P (1 / (fieldCard F : ℝ) ^ (m - 1)),
    ← expect_add]
  apply P.expect_mono
  intro o
  refine (uniform_embedding_expect_upper (actualEmbedding z)
    (fun p => ∑ α, err α o p ^ 2) (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) ?_).trans ?_
  · intro p hp
    apply hzero o p
    simpa only [actualEmbedding_range_iff, not_not] using hp
  · exact add_le_add (le_refl _) (auxiliary_missing_mass_le hm z)

/-- Extend the genuine matrix error to virtual zero-right encodings. Exactly one selected matrix leaf receives value one on those virtual points. -/
/-
Mathematical definition (normal notation): For O,A a set; m ∈ ℕ; z ∈ F; α₀ ∈ A; err ∈ A → O → Fiber(F, m, z) → ℝ; α ∈ A; o ∈ O; p ∈ Auxiliary(F, m, z), define

extendError(z, α₀, err, α, o, p) := { err(α, o, (((p)₁, ((p)₂, h)), p.2.property)) if (p)₂ ≠ 0,; { 1 if α = α₀,; 0 otherwise } otherwise }.
-/
noncomputable def extendError {O A : Type*} [DecidableEq A] {m : ℕ} (z : F)
    (α₀ : A) (err : A → O → Fiber F m z → ℝ)
    (α : A) (o : O) (p : Auxiliary F m z) : ℝ :=
  if h : p.2.val ≠ 0 then
    err α o ⟨⟨p.1, ⟨p.2.val, h⟩⟩, p.2.property⟩
  else if α = α₀ then 1 else 0

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For O,A a set; m ∈ ℕ; z ∈ F; α₀ ∈ A; err ∈ A → O → Fiber(F, m, z) → ℝ; α ∈ A; o ∈ O; p ∈ Fiber(F, m, z), we have

extendError(z, α₀, err, α, o, actualEmbedding(z, p)) = err(α, o, p) .
-/
@[simp] theorem extendError_actual {O A : Type*} [DecidableEq A] {m : ℕ}
    (z : F) (α₀ : A) (err : A → O → Fiber F m z → ℝ)
    (α : A) (o : O) (p : Fiber F m z) :
    extendError z α₀ err α o (actualEmbedding z p) = err α o p := by
  simp [extendError, actualEmbedding, p.val.R.property]

/-- The squared sum on every virtual-zero point is exactly one. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For O,A a set; m ∈ ℕ; z ∈ F; α₀ ∈ A; err ∈ A → O → Fiber(F, m, z) → ℝ; o ∈ O; p ∈ Auxiliary(F, m, z), assume A is finite; (p)₂ = 0. Then

(∑_α ((extendError(z, α₀, err, α, o, p))²)) = 1.
-/
theorem extendError_zero_energy {O A : Type*} [Fintype A] [DecidableEq A]
    {m : ℕ} (z : F) (α₀ : A) (err : A → O → Fiber F m z → ℝ)
    (o : O) (p : Auxiliary F m z) (hp : p.2.val = 0) :
    (∑ α, extendError z α₀ err α o p ^ 2) = 1 := by
  simp [extendError, hp]

/-- Full squared-error transport from genuine long encodings through the ordinary shortening branch. The only additive term comes from virtual zero right shares, and the multiplicative term is the exact acceptance ratio. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For O,A,B a set; n, t ∈ ℕ; c, ε, z ∈ F; Pold ∈ 𝒟(O); α₀ ∈ A; err ∈ A → O → Fiber(F, (n + t), z) → ℝ; answer ∈ A → O → Accepted(F, n, t, c, ε, z) → B; η ∈ ℝ, assume O is finite; A is finite; B is finite; 2 ≤ n + t; ε ≠ 0; Accepted(F, n, t, c, ε, z) ≠ ∅; Fiber(F, n, (c + ε · z)) ≠ ∅; Fiber(F, (n + t), z) ≠ ∅; Auxiliary(F, (n + t), z) ≠ ∅; 𝔼_(op ← (Pold ⊗ 𝒰_(Fiber(F, (n + t), z)))) [∑_α ((err(α, (op)₁, (op)₂))²)] ≤ η². Then

𝔼_(op ← (Pold ⊗ 𝒰_(Fiber(F, n, (c + ε · z))))) [∑_α (∑ᵦ ((errorTransport(c, ε, z, extendError(z, α₀, err), answer, α, β, (op)₁, (op)₂))²))] ≤ (acceptanceMass(n = n, t = t, c, ε, z))⁻¹ · (η² + 1 / (|F|)^(n + t − 1)).
-/
theorem errorTransport_actual_L2 {O A B : Type*} [Fintype O] [Fintype A]
    [DecidableEq A] [Fintype B] [DecidableEq B]
    {n t : ℕ} (hm : 2 ≤ n + t) (c ε z : F) (hε : ε ≠ 0)
    [Nonempty (Accepted F n t c ε z)] [Nonempty (Fiber F n (c + ε * z))]
    [Nonempty (Fiber F (n + t) z)] [Nonempty (Auxiliary F (n + t) z)]
    (Pold : FiniteDistribution O) (α₀ : A) (err : A → O → Fiber F (n + t) z → ℝ)
    (answer : A → O → Accepted F n t c ε z → B) (η : ℝ)
    (hη : (Pold.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n + t) z))).expect
      (fun op => ∑ α, err α op.1 op.2 ^ 2) ≤ η ^ 2) :
    (Pold.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (c + ε * z)))).expect
      (fun op => ∑ α, ∑ β,
        errorTransport c ε z hε (extendError z α₀ err) answer α β op.1 op.2 ^ 2) ≤
      (acceptanceMass (n := n) (t := t) c ε z)⁻¹ *
        (η ^ 2 + 1 / (fieldCard F : ℝ) ^ (n + t - 1)) := by
  refine (errorTransport_L2 c ε z hε Pold (extendError z α₀ err) answer).trans ?_
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by unfold acceptanceMass; positivity))
  have hx := auxiliary_error_extension hm z Pold (extendError z α₀ err)
    (fun o p hp => (extendError_zero_energy z α₀ err o p hp).le)
  simp only [extendError_actual] at hx
  exact hx.trans (add_le_add hη (le_refl _))

end CircuitCompiler.Shortening
