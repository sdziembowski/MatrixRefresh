import Proofs.Compiler.GateApproximation.MatrixPhase.Factorization
import Proofs.Compiler.Foundations.MatrixRefreshing.Probability.FiniteDistribution



/-!
# One product truncation for all gate answers

A common mask is formed from the total left and right factor energies over all answers. It gives a bounded factorization for every retained table and, separately, a pointwise bound on the sum of their absolute values.
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler.CommonTruncation

open Refresh

variable {X Y Z : Type*} [Fintype Z] {rank : ℕ}

/-
Mathematical definition (normal notation): For X a set; a ∈ Z → X → {0,…,rank-1} → ℝ; x ∈ X, define

energy(a, x) := ∑_z (∑ᵢ ((a(z, x, i))²)).
-/
def energy {X : Type*} (a : Z → X → Fin rank → ℝ) (x : X) : ℝ :=
  ∑ z, ∑ i, a z x i ^ 2

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ Z → X → {0,…,rank-1} → ℝ; x ∈ X, we have

0 ≤ energy(a, x).
-/
theorem energy_nonneg (a : Z → X → Fin rank → ℝ) (x : X) :
    0 ≤ energy a x := by
  unfold energy; positivity

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ Z → X → {0,…,rank-1} → ℝ; x ∈ X; z ∈ Z, we have

(∑ᵢ ((a(z, x, i))²)) ≤ energy(a, x).
-/
theorem answer_energy_le (a : Z → X → Fin rank → ℝ) (x : X) (z : Z) :
    (∑ i, a z x i ^ 2) ≤ energy a x := by
  unfold energy
  exact Finset.single_le_sum
    (fun z' _ => Finset.sum_nonneg (fun i _ => sq_nonneg (a z' x i)))
    (Finset.mem_univ z)

/-- This mask is the product of one test of the left data and one of the right. -/
/-
Mathematical definition (normal notation): For a ∈ Z → X → {0,…,rank-1} → ℝ; b ∈ Z → Y → {0,…,rank-1} → ℝ; B ∈ ℝ; f ∈ X → Y → ℝ; x ∈ X; y ∈ Y, define

cut(a, b, B, f, x, y) := { f(x, y) if energy(a, x) ≤ B ∧ energy(b, y) ≤ B,; 0 otherwise }.
-/
noncomputable def cut (a : Z → X → Fin rank → ℝ) (b : Z → Y → Fin rank → ℝ)
    (B : ℝ) (f : X → Y → ℝ) (x : X) (y : Y) : ℝ :=
  if energy a x ≤ B ∧ energy b y ≤ B then f x y else 0

/-- A certificate for each table, using the same mask for every answer. -/
/- Mathematical definition (normal notation): Given a representation G_z(x,y) = ∑ⱼ a_(z,j)(x)b_(z,j)(y), keep its left factors only where the total left energy is at most B, and likewise for the right factors. These masked factors reconstruct the common-cutoff table and each has pointwise energy at most B, assuming B ≥ 0. -/
noncomputable def cut_factorization
    (a : Z → X → Fin rank → ℝ) (b : Z → Y → Fin rank → ℝ)
    (G : Z → X → Y → ℝ) (hG : ∀ z x y, G z x y = ∑ i, a z x i * b z y i)
    (B : ℝ) (hB : 0 ≤ B) (z : Z) :
    BoundedFactorization (cut a b B (G z)) B := by
  classical
  exact
    { rank := rank
      left := fun x i => if energy a x ≤ B then a z x i else 0
      right := fun y i => if energy b y ≤ B then b z y i else 0
      reconstruct := by
        intro x y
        by_cases hx : energy a x ≤ B <;> by_cases hy : energy b y ≤ B <;>
          simp [cut, hx, hy, hG]
      left_bound := by
        intro x
        by_cases hx : energy a x ≤ B
        · simpa [hx] using (answer_energy_le a x z).trans hx
        · simpa [hx] using hB
      right_bound := by
        intro y
        by_cases hy : energy b y ≤ B
        · simpa [hy] using (answer_energy_le b y z).trans hy
        · simpa [hy] using hB }

/-- The absolute answer sum is bounded, without summing factorization norms. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ Z → X → {0,…,rank-1} → ℝ; b ∈ Z → Y → {0,…,rank-1} → ℝ; G ∈ Z → X → Y → ℝ; B ∈ ℝ; x ∈ X; y ∈ Y, assume ∀ z, x, y, G(z, x, y) = ∑ᵢ (a(z, x, i) · b(z, y, i)); 0 ≤ B. Then

(∑_z (|cut(a, b, B, G(z), x, y)|)) ≤ B.
-/
theorem cut_answer_sum_le
    (a : Z → X → Fin rank → ℝ) (b : Z → Y → Fin rank → ℝ)
    (G : Z → X → Y → ℝ) (hG : ∀ z x y, G z x y = ∑ i, a z x i * b z y i)
    (B : ℝ) (hB : 0 ≤ B) (x : X) (y : Y) :
    (∑ z, |cut a b B (G z) x y|) ≤ B := by
  classical
  by_cases h : energy a x ≤ B ∧ energy b y ≤ B
  · simp only [cut, if_pos h, hG]
    calc
      _ ≤ ∑ z, Real.sqrt (∑ i, a z x i ^ 2) * Real.sqrt (∑ i, b z y i ^ 2) :=
        Finset.sum_le_sum (fun z _ => Refresh.abs_sum_mul_le _ _)
      _ ≤ Real.sqrt (energy a x) * Real.sqrt (energy b y) :=
        Real.sum_sqrt_mul_sqrt_le _ (fun _ => by positivity) (fun _ => by positivity)
      _ ≤ Real.sqrt B * Real.sqrt B :=
        mul_le_mul (Real.sqrt_le_sqrt h.1) (Real.sqrt_le_sqrt h.2)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = B := Real.mul_self_sqrt hB
  · simpa [cut, h] using hB

variable [Fintype X] [Fintype Y]

/-- Only the one-sided energy means are needed; the two shares may be correlated. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ Z → X → {0,…,rank-1} → ℝ; b ∈ Z → Y → {0,…,rank-1} → ℝ; P ∈ 𝒟((X × Y)); Γ, B ∈ ℝ, assume 0 < B; 𝔼_(xy ← P) [energy(a, (xy)₁)] ≤ Γ; 𝔼_(xy ← P) [energy(b, (xy)₂)] ≤ Γ. Then

𝔼_(xy ← P) [{ 0 if energy(a, (xy)₁) ≤ B ∧ energy(b, (xy)₂) ≤ B,; 1 otherwise }] ≤ 2 · Γ / B.
-/
theorem bad_probability_le
    (a : Z → X → Fin rank → ℝ) (b : Z → Y → Fin rank → ℝ)
    (P : FiniteDistribution (X × Y)) (Γ B : ℝ) (hB : 0 < B)
    (hleft : P.expect (fun xy => energy a xy.1) ≤ Γ)
    (hright : P.expect (fun xy => energy b xy.2) ≤ Γ) :
    P.expect (fun xy => if energy a xy.1 ≤ B ∧ energy b xy.2 ≤ B then 0 else 1) ≤
      2 * Γ / B := by
  classical
  have hpoint (xy : X × Y) :
      B * (if energy a xy.1 ≤ B ∧ energy b xy.2 ≤ B then 0 else 1) ≤
        energy a xy.1 + energy b xy.2 := by
    split_ifs with h
    · simpa using add_nonneg (energy_nonneg a _) (energy_nonneg b _)
    · have := energy_nonneg a xy.1
      have := energy_nonneg b xy.2
      simp only [not_and_or, not_le] at h
      rcases h with h | h <;> simp only [mul_one] <;> linarith
  have hmean := P.expect_mono hpoint
  rw [MatrixRefresh.expect_smul, MatrixRefresh.expect_add] at hmean
  apply (le_div_iff₀ hB).mpr
  nlinarith

/-- Choosing a threshold at least `H² Γ` gives the manuscript's common-mask loss. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ Z → X → {0,…,rank-1} → ℝ; b ∈ Z → Y → {0,…,rank-1} → ℝ; P ∈ 𝒟((X × Y)); Γ, H ∈ ℝ, assume 0 < H; 𝔼_(xy ← P) [energy(a, (xy)₁)] ≤ Γ; 𝔼_(xy ← P) [energy(b, (xy)₂)] ≤ Γ. Then

𝔼_(xy ← P) [{ 0 if energy(a, (xy)₁) ≤ max{1, (H² · Γ)} ∧ energy(b, (xy)₂) ≤ max{1, (H² · Γ)},; 1 otherwise }] ≤ 2 / H².
-/
theorem bad_probability_le_H
    (a : Z → X → Fin rank → ℝ) (b : Z → Y → Fin rank → ℝ)
    (P : FiniteDistribution (X × Y)) (Γ H : ℝ) (hH : 0 < H)
    (hleft : P.expect (fun xy => energy a xy.1) ≤ Γ)
    (hright : P.expect (fun xy => energy b xy.2) ≤ Γ) :
    P.expect (fun xy =>
      if energy a xy.1 ≤ max 1 (H ^ 2 * Γ) ∧ energy b xy.2 ≤ max 1 (H ^ 2 * Γ)
      then 0 else 1) ≤ 2 / H ^ 2 := by
  have hB : 0 < max 1 (H ^ 2 * Γ) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  apply (bad_probability_le a b P Γ _ hB hleft hright).trans
  apply (div_le_div_iff₀ hB (sq_pos_of_pos hH)).mpr
  nlinarith [le_max_right (1 : ℝ) (H ^ 2 * Γ)]

/-- Applying a zero-one mask cannot increase any local approximation error. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ Z → X → {0,…,rank-1} → ℝ; b ∈ Z → Y → {0,…,rank-1} → ℝ; B ∈ ℝ; k, G ∈ Z → X → Y → ℝ; P ∈ 𝒟((X × Y)), we have

(∑_z (𝔼_(xy ← P) [|cut(a, b, B, k(z), (xy)₁, (xy)₂) - cut(a, b, B, G(z), (xy)₁, (xy)₂)|])) ≤ ∑_z (𝔼_(xy ← P) [|k(z, (xy)₁, (xy)₂) - G(z, (xy)₁, (xy)₂)|]).
-/
theorem cut_error_le
    (a : Z → X → Fin rank → ℝ) (b : Z → Y → Fin rank → ℝ) (B : ℝ)
    (k G : Z → X → Y → ℝ) (P : FiniteDistribution (X × Y)) :
    (∑ z, P.expect (fun xy => |cut a b B (k z) xy.1 xy.2 - cut a b B (G z) xy.1 xy.2|)) ≤
      ∑ z, P.expect (fun xy => |k z xy.1 xy.2 - G z xy.1 xy.2|) := by
  apply Finset.sum_le_sum
  intro z _
  apply P.expect_mono
  intro xy
  unfold cut
  split_ifs <;> simp

end CircuitCompiler.CommonTruncation
