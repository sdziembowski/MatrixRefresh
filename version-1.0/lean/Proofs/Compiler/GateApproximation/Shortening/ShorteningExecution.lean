import Proofs.Compiler.GateApproximation.Shortening.ShorteningDistribution



/-!
# The ordinary branch as a finite-field procedure

This file connects the counting carrier to a direct computation on a long encoding. `run` returns `none` precisely when the head or produced right share is zero; no repeated leakage trials are introduced. Every successful return includes its encoded-value proof. A caller may attach the manuscript's correct fallback to the `none` branch.
-/

set_option autoImplicit false

namespace CircuitCompiler.Shortening

open Refresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The first `n` coordinates of an auxiliary long left share. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; z ∈ F; p ∈ Auxiliary(F, (n + t), z), define

head(p) := (i ↦ (p)₁(Fin.castAdd(t, i))).
-/
def head {n t : ℕ} {z : F} (p : Auxiliary F (n + t) z) : V F n :=
  fun i => p.1.val (Fin.castAdd t i)

/-- Split the actual two long vectors once their left head is nonzero. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; z ∈ F; p ∈ Auxiliary(F, (n + t), z), assume head(p) ≠ 0. define

splitData(p) := (head(p), ((i ↦ (p)₁(Fin.natAdd(n, i)))), ((i ↦ (p)₂(Fin.castAdd(t, i)))), ((i ↦ (p)₂(Fin.natAdd(n, i))))).
-/
def splitData {n t : ℕ} {z : F} (p : Auxiliary F (n + t) z)
    (hA : head p ≠ 0) : Data F n t :=
  ⟨⟨head p, hA⟩, (fun i => p.1.val (Fin.natAdd n i)),
    (fun i => p.2.val (Fin.castAdd t i)), (fun i => p.2.val (Fin.natAdd n i))⟩

/-- Splitting coordinates preserves the actual long inner product. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; z ∈ F; p ∈ Auxiliary(F, (n + t), z), assume head(p) ≠ 0. Then

longSecret(splitData(p)) = z.
-/
theorem splitData_secret {n t : ℕ} {z : F} (p : Auxiliary F (n + t) z)
    (hA : head p ≠ 0) : longSecret (splitData p hA) = z := by
  have h := p.2.property
  unfold dot dotProduct at h
  rw [Fin.sum_univ_add] at h
  exact h

/-- Execute the ordinary branch, checking exactly its two specified exceptional conditions. The right long share may be zero in this auxiliary procedure. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; p ∈ Auxiliary(F, (n + t), z), define

run(c, ε, z, p) := { Let s := splitData(p, hA); { some(output(c, ε, z, (s, hR))) if outputRight(c, ε, s) ≠ 0,; none otherwise } if head(p) ≠ 0,; none otherwise }.
-/
def run {n t : ℕ} (c ε z : F) (p : Auxiliary F (n + t) z) :
    Option (Fiber F n (c + ε * z)) :=
  if hA : head p ≠ 0 then
    let s := splitData p hA
    if hR : outputRight c ε s ≠ 0 then
      some (output c ε z ⟨s, splitData_secret p hA, hR⟩)
    else none
  else none

/-- The split-data embedding really supplies a nonzero ordinary-branch head. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; p ∈ Accepted(F, n, t, c, ε, z), we have

head(acceptedEmbedding(c, ε, z, p)) = p.val.A.
-/
@[simp] theorem head_acceptedEmbedding {n t : ℕ} (c ε z : F)
    (p : Accepted F n t c ε z) : head (acceptedEmbedding c ε z p) = p.val.A.val := by
  funext i
  change Fin.append p.val.A.val p.val.B (Fin.castAdd t i) = p.val.A.val i
  simp

/-- Splitting an embedded accepted state recovers every original coordinate. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; p ∈ Accepted(F, n, t, c, ε, z), assume head(acceptedEmbedding(c, ε, z, p)) ≠ 0. Then

splitData(acceptedEmbedding(c, ε, z, p)) = p.
-/
theorem splitData_acceptedEmbedding {n t : ℕ} (c ε z : F)
    (p : Accepted F n t c ε z) (hA : head (acceptedEmbedding c ε z p) ≠ 0) :
    splitData (acceptedEmbedding c ε z p) hA = p.val := by
  apply Data.ext
  · apply Subtype.ext
    exact head_acceptedEmbedding c ε z p
  · funext i
    change Fin.append p.val.A.val p.val.B (Fin.natAdd n i) = p.val.B i
    simp
  · funext i
    change Fin.append p.val.C p.val.D (Fin.castAdd t i) = p.val.C i
    simp
  · funext i
    change Fin.append p.val.C p.val.D (Fin.natAdd n i) = p.val.D i
    simp

/-- On all counted ordinary-branch inputs the direct procedure produces the same output as the change-of-variables proof. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; p ∈ Accepted(F, n, t, c, ε, z), we have

run(c, ε, z, acceptedEmbedding(c, ε, z, p)) = some(output(c, ε, z, p)).
-/
theorem run_acceptedEmbedding {n t : ℕ} (c ε z : F)
    (p : Accepted F n t c ε z) :
    run c ε z (acceptedEmbedding c ε z p) = some (output c ε z p) := by
  have hA : head (acceptedEmbedding c ε z p) ≠ 0 := by
    rw [head_acceptedEmbedding]
    exact p.val.A.property
  have hs := splitData_acceptedEmbedding c ε z p hA
  unfold run
  rw [dif_pos hA]
  dsimp only
  have hR : outputRight c ε (splitData (acceptedEmbedding c ε z p) hA) ≠ 0 := by
    rw [hs]
    exact p.property.2
  rw [dif_pos hR]
  congr 2
  exact Subtype.ext hs

/-- The embedding loses no successful inputs: splitting and rejoining the long coordinates is the identity. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; p ∈ Auxiliary(F, (n + t), z), assume head(p) ≠ 0; outputRight(c, ε, splitData(p)) ≠ 0. Then

acceptedEmbedding(c, ε, z, splitData(p)) = p.
-/
theorem acceptedEmbedding_splitData {n t : ℕ} (c ε z : F)
    (p : Auxiliary F (n + t) z) (hA : head p ≠ 0)
    (hR : outputRight c ε (splitData p hA) ≠ 0) :
    acceptedEmbedding c ε z ⟨splitData p hA, splitData_secret p hA, hR⟩ = p := by
  apply Sigma.subtype_ext
  · apply Subtype.ext
    exact Fin.append_castAdd_natAdd
  · exact Fin.append_castAdd_natAdd

/-- Success of the direct ordinary branch is equivalent to membership in the counted accepted subset. Hence its omitted uniform mass is exactly the finite count ratio used in `acceptanceMass`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; p ∈ Auxiliary(F, (n + t), z), we have

isSome(run(c, ε, z, p)) = true ⇔ ∃ a ∈ Accepted(F, n, t, c, ε, z), acceptedEmbedding(c, ε, z, a) = p.
-/
theorem run_isSome_iff {n t : ℕ} (c ε z : F) (p : Auxiliary F (n + t) z) :
    (run c ε z p).isSome = true ↔ ∃ a : Accepted F n t c ε z,
      acceptedEmbedding c ε z a = p := by
  constructor
  · intro h
    unfold run at h
    split at h
    · rename_i hA
      dsimp only at h
      split at h
      · rename_i hR
        exact ⟨⟨splitData p hA, splitData_secret p hA, hR⟩,
          acceptedEmbedding_splitData c ε z p hA hR⟩
      · simp at h
    · simp at h
  · rintro ⟨a, rfl⟩
    rw [run_acceptedEmbedding]
    rfl

/-- The actual nonzero-share ordinary branch is the same procedure after embedding an actual encoding in the auxiliary carrier. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; p ∈ Fiber(F, (n + t), z), define

runActual(c, ε, z, p) := run(c, ε, z, actualEmbedding(z, p)).
-/
def runActual {n t : ℕ} (c ε z : F) (p : Fiber F (n + t) z) :
    Option (Fiber F n (c + ε * z)) := run c ε z (actualEmbedding z p)

/-- The successful inputs of the direct ordinary-branch procedure are in bijection with the already counted accepted long states. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F, define

successEquiv(c, ε, z) := Equiv.ofBijective(((a ↦ (acceptedEmbedding(c, ε, z, a), (run_isSome_iff(c, ε, z, x))₂(a)))), ()).
-/
noncomputable def successEquiv {n t : ℕ} (c ε z : F) :
    Accepted F n t c ε z ≃
      {p : Auxiliary F (n + t) z // (run c ε z p).isSome = true} :=
  Equiv.ofBijective
    (fun a => ⟨acceptedEmbedding c ε z a,
      (run_isSome_iff c ε z _).2 ⟨a, rfl⟩⟩)
    ⟨by
      intro a b h
      exact (acceptedEmbedding c ε z).injective (congrArg Subtype.val h),
     by
      intro p
      obtain ⟨a, ha⟩ := (run_isSome_iff c ε z p.val).1 p.property
      exact ⟨a, Subtype.ext ha⟩⟩

/-- The acceptance mass is the actual success probability of the direct procedure under the uniform auxiliary input distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F, assume ε ≠ 0; Auxiliary(F, (n + t), z) ≠ ∅. Then

(((p ↦ isSome(run(c, ε, z, p))))_*𝒰_(Auxiliary(F, (n + t), z)))(true) = acceptanceMass(n = n, t = t, c, ε, z).
-/
theorem run_success_probability {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    [Nonempty (Auxiliary F (n + t) z)] :
    ((FiniteDistribution.uniform : FiniteDistribution (Auxiliary F (n + t) z)).map
      (fun p => (run c ε z p).isSome)).weight true =
      acceptanceMass (n := n) (t := t) c ε z := by
  classical
  rw [FiniteDistribution.uniform_map_weight,
    ← Fintype.card_congr (successEquiv c ε z), accepted_card c ε z hε, auxiliary_card]
  simp only [acceptanceMass, Nat.cast_mul, Nat.cast_pow]

/-- The corresponding failure probability is exactly the complement of the acceptance mass, including both possible exceptional branches. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F, assume ε ≠ 0; Auxiliary(F, (n + t), z) ≠ ∅. Then

(((p ↦ isSome(run(c, ε, z, p))))_*𝒰_(Auxiliary(F, (n + t), z)))(false) = 1 - acceptanceMass(n = n, t = t, c, ε, z).
-/
theorem run_failure_probability {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    [Nonempty (Auxiliary F (n + t) z)] :
    ((FiniteDistribution.uniform : FiniteDistribution (Auxiliary F (n + t) z)).map
      (fun p => (run c ε z p).isSome)).weight false =
      1 - acceptanceMass (n := n) (t := t) c ε z := by
  have h := ((FiniteDistribution.uniform : FiniteDistribution (Auxiliary F (n + t) z)).map
    (fun p => (run c ε z p).isSome)).total
  simp only [Fintype.sum_bool] at h
  rw [run_success_probability c ε z hε] at h
  linarith

/-- An explicit probability bound on fallback in the auxiliary experiment. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F, assume 2 ≤ n; ε ≠ 0; Auxiliary(F, (n + t), z) ≠ ∅. Then

(((p ↦ isSome(run(c, ε, z, p))))_*𝒰_(Auxiliary(F, (n + t), z)))(false) ≤ (|F| + 1) / (|F|)ⁿ.
-/
theorem run_failure_bound {n t : ℕ} (hn : 2 ≤ n) (c ε z : F) (hε : ε ≠ 0)
    [Nonempty (Auxiliary F (n + t) z)] :
    ((FiniteDistribution.uniform : FiniteDistribution (Auxiliary F (n + t) z)).map
      (fun p => (run c ε z p).isSome)).weight false ≤
      ((fieldCard F : ℝ) + 1) / (fieldCard F : ℝ) ^ n := by
  rw [run_failure_probability c ε z hε]
  exact failureMass_le hn c ε z

/-- The actual nonzero-share protocol has fallback probability bounded by the auxiliary fallback mass plus the explicitly proved auxiliary-distribution discrepancy. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F, assume 2 ≤ n; ε ≠ 0; Fiber(F, (n + t), z) ≠ ∅; Auxiliary(F, (n + t), z) ≠ ∅. Then

(((p ↦ isSome(runActual(c, ε, z, p))))_*𝒰_(Fiber(F, (n + t), z)))(false) ≤ (|F| + 1) / (|F|)ⁿ + 1 / (|F|)^(n + t − 1).
-/
theorem runActual_failure_bound {n t : ℕ} (hn : 2 ≤ n) (c ε z : F) (hε : ε ≠ 0)
    [Nonempty (Fiber F (n + t) z)] [Nonempty (Auxiliary F (n + t) z)] :
    ((FiniteDistribution.uniform : FiniteDistribution (Fiber F (n + t) z)).map
      (fun p => (runActual c ε z p).isSome)).weight false ≤
      ((fieldCard F : ℝ) + 1) / (fieldCard F : ℝ) ^ n +
        1 / (fieldCard F : ℝ) ^ (n + t - 1) := by
  let P := (FiniteDistribution.uniform : FiniteDistribution (Auxiliary F (n + t) z)).map
    (fun p => (run c ε z p).isSome)
  let Q := (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n + t) z)).map
    (fun p => (runActual c ε z p).isSome)
  have hdist : statisticalDistance P Q ≤ 1 / (fieldCard F : ℝ) ^ (n + t - 1) := by
    have h := statisticalDistance_map_le
      (FiniteDistribution.uniform : FiniteDistribution (Auxiliary F (n + t) z))
      ((FiniteDistribution.uniform : FiniteDistribution (Fiber F (n + t) z)).map (actualEmbedding z))
      (fun p => (run c ε z p).isSome)
    rw [FiniteDistribution.map_map] at h
    exact h.trans (auxiliary_actual_distance (by omega : 2 ≤ n + t) z)
  have hpoint : Q.weight false - P.weight false ≤ statisticalDistance P Q := by
    have h := MatrixRefresh.expect_sub_expect_le_statisticalDistance Q P
      (fun b => if b = false then (1 : ℝ) else 0)
      (by intro b; cases b <;> norm_num)
      (by intro b; cases b <;> norm_num)
    rw [statisticalDistance_symm Q P] at h
    simpa [FiniteDistribution.expect, Fintype.sum_bool] using h
  have hfail : P.weight false ≤ ((fieldCard F : ℝ) + 1) / (fieldCard F : ℝ) ^ n :=
    run_failure_bound hn c ε z hε
  change Q.weight false ≤ _
  linarith

end CircuitCompiler.Shortening
