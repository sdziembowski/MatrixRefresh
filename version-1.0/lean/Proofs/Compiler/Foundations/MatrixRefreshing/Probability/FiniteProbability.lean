import Proofs.EfficientSimulaiton.PublicModel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Proofs.Compiler.Construction.Parameters
set_option autoImplicit false
open scoped BigOperators
namespace Refresh
namespace FiniteDistribution
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
/-- A point-mass distribution is supported on any property satisfied by its selected point. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ α; p ∈ α → Prop, assume p(a). Then

Supports(pure(a))(p).
-/
theorem pure_supports (a : α) (p : α → Prop) (ha : p a) : (pure a).Supports p := by
  classical
  intro b hb
  by_cases hba : b = a
  · simpa [hba] using ha
  · simp [pure, hba] at hb
/-- Sequential sampling preserves an output property when the first distribution is supported on inputs whose conditional distributions all satisfy that property. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); Q ∈ α → 𝒟(β); p ∈ α → Prop; q ∈ β → Prop, assume P.Supports(p); ∀ a, p(a) → Supports(Q(a))(q). Then

Supports(bind(P, Q))(q).
-/
theorem bind_supports (P : FiniteDistribution α) (Q : α → FiniteDistribution β) (p : α → Prop) (q : β → Prop)
    (hP : P.Supports p) (hQ : ∀ a, p a → (Q a).Supports q) : (P.bind Q).Supports q := by
  classical
  intro b hb
  by_contra hqb
  apply hb
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : P.weight a = 0
  · simp [ha]
  · have hzero : (Q a).weight b = 0 := by
      by_contra h
      exact hqb (hQ a (hP a ha) b h)
    simp [hzero]
/-- A deterministic map preserves support when it sends every supported input to a point satisfying the desired output property. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f ∈ α → β; p ∈ α → Prop; q ∈ β → Prop, assume P.Supports(p); ∀ a, p(a) → q(f(a)). Then

Supports((f_*P))(q).
-/
theorem map_supports (P : FiniteDistribution α) (f : α → β) (p : α → Prop) (q : β → Prop)
    (hP : P.Supports p) (hf : ∀ a, p a → q (f a)) : (P.map f).Supports q :=
  bind_supports P (fun a => pure (f a)) p q hP
    (fun a ha => pure_supports (f a) q (hf a ha))
/-- Every probability distribution is supported on the property that is always true. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α), we have

P.Supports(((x₁ ↦ true))).
-/
theorem supports_true (P : FiniteDistribution α) : P.Supports (fun _ => True) :=
  fun _ _ => trivial
/-- There is only one probability distribution on a carrier with at most one point. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P, Q ∈ 𝒟(α), assume |α| ≤ 1. Then

P = Q.
-/
theorem eq_of_subsingleton [Subsingleton α] (P Q : FiniteDistribution α) : P = Q := by
  ext a
  rw [← Fintype.sum_subsingleton P.weight a, ← Fintype.sum_subsingleton Q.weight a,
    P.total, Q.total]
/-- The expectation of the constant one function is one, by total mass normalization. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α), we have

𝔼_(x₁ ← P) [1] = 1.
-/
@[simp] theorem expect_one (P : FiniteDistribution α) : P.expect (fun _ => 1) = 1 := by
  simpa [expect] using P.total
/-- A pointwise nonnegative function has a nonnegative expectation. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f ∈ α → ℝ, assume ∀ a, 0 ≤ f(a). Then

0 ≤ 𝔼_(u ← P) [f(u)].
-/
theorem expect_nonneg (P : FiniteDistribution α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    0 ≤ P.expect f :=
  Finset.sum_nonneg fun a _ => mul_nonneg (P.nonneg a) (hf a)
/-- Pointwise comparison of functions implies comparison of their expectations. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f, g ∈ α → ℝ, assume ∀ a, f(a) ≤ g(a). Then

𝔼_(u ← P) [f(u)] ≤ 𝔼_(v ← P) [g(v)].
-/
theorem expect_mono (P : FiniteDistribution α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    P.expect f ≤ P.expect g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (P.nonneg a)
/-- A constant has the same value after averaging under a probability distribution. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); c ∈ ℝ, we have

𝔼_(x₁ ← P) [c] = c.
-/
@[simp] theorem expect_const (P : FiniteDistribution α) (c : ℝ) : P.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, P.total]
/-- A pointwise upper bound by a constant also bounds the expectation. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f ∈ α → ℝ; c ∈ ℝ, assume ∀ a, f(a) ≤ c. Then

𝔼_(u ← P) [f(u)] ≤ c.
-/
theorem expect_le_const (P : FiniteDistribution α) {f : α → ℝ} {c : ℝ} (h : ∀ a, f a ≤ c) :
    P.expect f ≤ c := by
  simpa using P.expect_mono h
/-- Mapping the output of sequential sampling equals mapping each conditional output distribution before performing the first sampling step. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); Q ∈ α → 𝒟(β); f ∈ β → γ, we have

(f_*bind(P, Q)) = bind(P, ((a ↦ (f_*Q(a))))).
-/
theorem map_bind (P : FiniteDistribution α) (Q : α → FiniteDistribution β) (f : β → γ) :
    (P.bind Q).map f = P.bind (fun a => (Q a).map f) := by
  simp [map, bind_assoc]
/-- A bijective change of coordinates only reindexes point masses. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); e ∈ α ≃ β; b ∈ β, we have

(e_*P)(b) = P((e)⁻¹(b)).
-/
theorem map_equiv_weight (P : FiniteDistribution α) (e : α ≃ β) (b : β) :
    (P.map e).weight b = P.weight (e.symm b) := by
  classical
  obtain ⟨a, rfl⟩ := e.surjective b
  simp [map, bind, pure]
end FiniteDistribution
variable {α β : Type*} [Fintype α] [Fintype β]
/-- Total absolute signed mass is nonnegative. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ν ∈ SignedWeight(α), we have

0 ≤ variationNorm(ν).
-/
theorem variationNorm_nonneg (ν : SignedWeight α) : 0 ≤ variationNorm ν :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
/-- Adding two signed weights costs at most the sum of their total absolute masses. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ν, ξ ∈ SignedWeight(α), we have

variationNorm(((a ↦ ν(a) + ξ(a)))) ≤ variationNorm(ν) + variationNorm(ξ).
-/
theorem variationNorm_add_le (ν ξ : SignedWeight α) :
    variationNorm (fun a => ν a + ξ a) ≤ variationNorm ν + variationNorm ξ := by
  simp only [variationNorm, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a _ => abs_add_le _ _
/-- The total absolute mass of a difference satisfies the triangle inequality through any intermediate signed weight. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ν, ξ, ζ ∈ SignedWeight(α), we have

variationNorm(((a ↦ ν(a) - ζ(a)))) ≤ variationNorm(((a ↦ ν(a) - ξ(a)))) + variationNorm(((a ↦ ξ(a) - ζ(a)))).
-/
theorem variationNorm_sub_le (ν ξ ζ : SignedWeight α) :
    variationNorm (fun a => ν a - ζ a) ≤
      variationNorm (fun a => ν a - ξ a) + variationNorm (fun a => ξ a - ζ a) := by
  simpa only [sub_add_sub_cancel] using
    variationNorm_add_le (fun a => ν a - ξ a) (fun a => ξ a - ζ a)
/-- Applying a nonnegative probability transition to a signed weight cannot increase its total absolute mass. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ν ∈ SignedWeight(α); κ ∈ α → 𝒟(β), we have

variationNorm(((b ↦ ∑ₐ (ν(a) · κ(a)(b))))) ≤ variationNorm(ν).
-/
theorem variationNorm_stochastic_le (ν : SignedWeight α) (κ : α → FiniteDistribution β) :
    variationNorm (fun b => ∑ a, ν a * (κ a).weight b) ≤ variationNorm ν := by
  calc
    _ ≤ ∑ b, ∑ a, |ν a * (κ a).weight b| := by
      apply Finset.sum_le_sum
      intro b _
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, ∑ b, |ν a| * (κ a).weight b := by
      simp_rw [abs_mul, abs_of_nonneg ((κ _).nonneg _)]
      exact Finset.sum_comm
    _ = variationNorm ν := by
      simp_rw [← Finset.mul_sum, (κ _).total, mul_one]
      rfl
/-- Finite statistical distance is nonnegative. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P, Q ∈ 𝒟(α), we have

0 ≤ δ(P, Q).
-/
theorem statisticalDistance_nonneg (P Q : FiniteDistribution α) :
    0 ≤ statisticalDistance P Q :=
  mul_nonneg (by norm_num) (variationNorm_nonneg _)
/-- A probability distribution has zero statistical distance from itself. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α), we have

δ(P, P) = 0.
-/
@[simp] theorem statisticalDistance_self (P : FiniteDistribution α) : statisticalDistance P P = 0 := by
  simp [statisticalDistance, variationNorm]
/-- Exchanging the two distributions leaves their statistical distance unchanged. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P, Q ∈ 𝒟(α), we have

δ(P, Q) = δ(Q, P).
-/
theorem statisticalDistance_symm (P Q : FiniteDistribution α) :
    statisticalDistance P Q = statisticalDistance Q P := by
  simp only [statisticalDistance, variationNorm, abs_sub_comm]
/-- Statistical distance satisfies the triangle inequality through any intermediate probability distribution. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P, Q, R ∈ 𝒟(α), we have

δ(P, R) ≤ δ(P, Q) + δ(Q, R).
-/
theorem statisticalDistance_triangle (P Q R : FiniteDistribution α) :
    statisticalDistance P R ≤ statisticalDistance P Q + statisticalDistance Q R := by
  unfold statisticalDistance
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (variationNorm_sub_le P.weight Q.weight R.weight) (by norm_num)
/-- Two probability distributions have statistical distance at most one. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P, Q ∈ 𝒟(α), we have

δ(P, Q) ≤ 1.
-/
theorem statisticalDistance_le_one (P Q : FiniteDistribution α) : statisticalDistance P Q ≤ 1 := by
  have h : variationNorm (fun a => P.weight a - Q.weight a) ≤ 2 := by
    calc
      _ ≤ ∑ a, (P.weight a + Q.weight a) := by
        apply Finset.sum_le_sum
        intro a _
        calc
          |P.weight a - Q.weight a| ≤ |P.weight a| + |Q.weight a| := by
            exact abs_sub _ _
          _ = _ := by rw [abs_of_nonneg (P.nonneg a), abs_of_nonneg (Q.nonneg a)]
      _ = 2 := by rw [Finset.sum_add_distrib, P.total, Q.total]; norm_num
  unfold statisticalDistance
  linarith
/-- Applying the same randomized transition to two distributions cannot increase their statistical distance. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P, Q ∈ 𝒟(α); κ ∈ α → 𝒟(β), we have

δ(bind(P, κ), bind(Q, κ)) ≤ δ(P, Q).
-/
theorem statisticalDistance_bind_le (P Q : FiniteDistribution α) (κ : α → FiniteDistribution β) :
    statisticalDistance (P.bind κ) (Q.bind κ) ≤ statisticalDistance P Q := by
  have h := variationNorm_stochastic_le (fun a => P.weight a - Q.weight a) κ
  simp only [statisticalDistance, FiniteDistribution.bind]
  simp_rw [← Finset.sum_sub_distrib, ← sub_mul]
  exact mul_le_mul_of_nonneg_left h (by norm_num)
/-- Applying the same deterministic function to two samples cannot increase the statistical distance between their distributions. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P, Q ∈ 𝒟(α); f ∈ α → β, we have

δ((f_*P), (f_*Q)) ≤ δ(P, Q).
-/
theorem statisticalDistance_map_le (P Q : FiniteDistribution α) (f : α → β) :
    statisticalDistance (P.map f) (Q.map f) ≤ statisticalDistance P Q :=
  statisticalDistance_bind_le P Q (fun a => FiniteDistribution.pure (f a))
/-- Retaining a common first sample makes the joint distance exactly the average distance of the two conditional output distributions; the output may depend on that sample. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ν ∈ 𝒟(α); P, Q ∈ α → 𝒟(β), we have

1 / 2 · (∑_(ab ∈ α × β) (|ν((ab)₁) · P((ab)₁)((ab)₂) - ν((ab)₁) · Q((ab)₁)((ab)₂)|)) = 𝔼_(a ← ν) [δ(P(a), Q(a))].
-/
theorem statisticalDistance_joint_mixture (ν : FiniteDistribution α) (P Q : α → FiniteDistribution β) :
    (1 / 2 : ℝ) * (∑ ab : α × β,
      |ν.weight ab.1 * (P ab.1).weight ab.2 - ν.weight ab.1 * (Q ab.1).weight ab.2|) =
      ν.expect (fun a => statisticalDistance (P a) (Q a)) := by
  simp only [Fintype.sum_prod_type, ← mul_sub, abs_mul,
    abs_of_nonneg (ν.nonneg _), statisticalDistance, variationNorm, FiniteDistribution.expect,
    ← Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring
end Refresh
