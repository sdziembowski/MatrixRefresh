import Proofs.Compiler.Foundations.LinearAlgebra.RefreshBounds



/-!
# Mixing bounds for products of orthonormal features

The generic hypotheses distinguish pointwise uniformity of the action from its two-function variance bound. They imply feature-Gram expectation and variance estimates. Concrete finite-field matrix actions supply these hypotheses through their orbit and mixing properties.
-/

set_option autoImplicit false

open scoped BigOperators

namespace TableAnalysis

open MatrixRefresh Refresh

noncomputable section

variable {X G I J : Type*} [Fintype X] [Fintype G] [Fintype I] [Fintype J]

/-- Uniform matrices send each fixed point to the uniform point distribution. -/
/-
Mathematical definition (normal notation): A random refresh action e_g:X → X is uniform on points when, for every fixed x and real function f,

𝔼_(g ← G) [f(e_g(x))] = 𝔼_(y ← X) [f(y)].
-/
def UniformOnPoints (e : FiniteRefresh X G) : Prop :=
  ∀ (x : X) (f : X → ℝ), uavg (fun g => f (e g x)) = uavg f

/-- The arbitrary-function variance form of the elementary mixing bound. Products of features need not have mean zero. -/
/-
Mathematical definition (normal notation): The refresh action has variance coefficient at most κ when every pair of real functions a,b satisfies

𝔼_g [(𝔼ₓ [a(x) · b(e_g(x))] -𝔼ₓ [a(x)] · 𝔼_y [b(y)])²] ≤ κ · 𝔼ₓ [a(x)²] · 𝔼_y [b(y)²].
-/
def VarianceMixing (e : FiniteRefresh X G) (κ : ℝ) : Prop :=
  ∀ (a b : X → ℝ),
    uavg (fun g => (uavg (fun x => a x * b (e g x)) - uavg a * uavg b) ^ 2) ≤
      κ * uavg (fun x => a x ^ 2) * uavg (fun x => b x ^ 2)

/-- Real identity-matrix entry for an arbitrary finite index type. -/
/- Mathematical definition (normal notation): The Kronecker delta is δᵢⱼ := 1 when i = j, and δᵢⱼ := 0 otherwise. -/
def indexDelta {A : Type*} (a b : A) : ℝ := by
  classical
  exact if a = b then 1 else 0

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A a set; a ∈ A, we have

indexDelta(a, a) = 1.
-/
@[simp] theorem indexDelta_self {A : Type*} (a : A) : indexDelta a a = 1 := by
  simp [indexDelta]

omit [Fintype I] [Fintype J] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For i, k ∈ I; j, h ∈ J, we have

indexDelta(i, k) · indexDelta(j, h) = indexDelta((i, j), (k, h)).
-/
theorem indexDelta_prod (i k : I) (j h : J) :
    indexDelta i k * indexDelta j h = indexDelta (i, j) (k, h) := by
  classical
  by_cases hi : i = k <;> by_cases hj : j = h <;> simp [indexDelta, hi, hj]

/-- Orthonormality is with respect to normalized uniform L2 measure. -/
/-
Mathematical definition (normal notation): A real family (uᵢ) is orthonormal under uniform measure on X when

𝔼_(x ← X) [uᵢ(x) · uⱼ(x)] = δᵢⱼ for all i,j.
-/
def OrthonormalFamily (u : I → X → ℝ) : Prop :=
  ∀ i k, uavg (fun x => u i x * u k x) = indexDelta i k

/-- Gram entry of the product features `u_i(x) v_j(e_g x)`. -/
/-
Mathematical definition (normal notation): For the product functions w_(i,j)ᵍ(x) := uᵢ(x) · vⱼ(e_g(x)), define their normalized Gram matrix by

Gram_g((i,j),(k,h)) := 𝔼ₓ [w_(i,j)ᵍ(x) · w_(k,h)ᵍ(x)].
-/
def featureGram (e : FiniteRefresh X G) (u : I → X → ℝ) (v : J → X → ℝ)
    (g : G) (a b : I × J) : ℝ :=
  uavg (fun x => (u a.1 x * u b.1 x) * (v a.2 (e g x) * v b.2 (e g x)))

omit [Fintype I] [Fintype J] in
/-- Exact expectation of each feature Gram entry. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ FiniteRefresh(X, G); u ∈ I → X → ℝ; v ∈ J → X → ℝ; a, b ∈ I × J, assume UniformOnPoints(e); OrthonormalFamily(u); OrthonormalFamily(v). Then

𝔼_g [featureGram(e, u, v, g, a, b)] = indexDelta(a, b).
-/
theorem featureGram_expect (e : FiniteRefresh X G) (hunif : UniformOnPoints e)
    (u : I → X → ℝ) (v : J → X → ℝ)
    (hu : OrthonormalFamily u) (hv : OrthonormalFamily v) (a b : I × J) :
    uavg (fun g => featureGram e u v g a b) = indexDelta a b := by
  classical
  unfold featureGram
  rw [uavg_comm]
  calc
    _ = uavg (fun x => (u a.1 x * u b.1 x) *
        uavg (fun y => v a.2 y * v b.2 y)) := by
      apply uavg_congr
      intro x
      rw [uavg_const_mul, hunif x (fun y => v a.2 y * v b.2 y)]
    _ = uavg (fun x => u a.1 x * u b.1 x) *
        uavg (fun y => v a.2 y * v b.2 y) := uavg_mul_const _ _
    _ = indexDelta a b := by rw [hu, hv, indexDelta_prod]

/-- Squared counting L2 deviation from the identity, summed over both entry indices. -/
/-
Mathematical definition (normal notation): The squared Gram deviation is the sum over all matrix entries,

∑_(a,b) (Gram_g(a,b)-δ_ab)².

There is no additional averaging over the Gram-matrix indices.
-/
def gramDeviationSq (e : FiniteRefresh X G) (u : I → X → ℝ) (v : J → X → ℝ)
    (g : G) : ℝ :=
  ∑ a : I × J, ∑ b : I × J, (featureGram e u v g a b - indexDelta a b) ^ 2

/-- Pointwise squared feature factorEnergy. -/
/-
Mathematical definition (normal notation): The pointwise energy of a family (uᵢ) is

Φᵤ(x) := ∑ᵢ uᵢ(x)².
-/
def factorEnergy (u : I → X → ℝ) (x : X) : ℝ := ∑ i, u i x ^ 2

/-- The mean square of the factorEnergy function. -/
/-
Mathematical definition (normal notation): The second moment of the factor energy is

𝔼_(x ← X) [Φᵤ(x)²], Φᵤ(x) := ∑ᵢ uᵢ(x)².
-/
def factorEnergySecondMoment (u : I → X → ℝ) : ℝ := uavg (fun x => factorEnergy u x ^ 2)

omit [Fintype X] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u ∈ I → X → ℝ; x ∈ X, we have

0 ≤ factorEnergy(u, x).
-/
theorem factorEnergy_nonneg (u : I → X → ℝ) (x : X) : 0 ≤ factorEnergy u x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u ∈ I → X → ℝ, we have

0 ≤ factorEnergySecondMoment(u).
-/
theorem factorEnergySecondMoment_nonneg (u : I → X → ℝ) : 0 ≤ factorEnergySecondMoment u :=
  uavg_nonneg (fun _ => sq_nonneg _)

/-- Expand the factorEnergy moment as the sum of squared product-feature norms. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u ∈ I → X → ℝ, we have

factorEnergySecondMoment(u) = ∑ᵢ (∑ₖ (𝔼ₓ [(u(i, x) · u(k, x))²])).
-/
theorem factorEnergySecondMoment_eq_sum (u : I → X → ℝ) :
    factorEnergySecondMoment u = ∑ i, ∑ k, uavg (fun x => (u i x * u k x) ^ 2) := by
  unfold factorEnergySecondMoment factorEnergy
  calc
    _ = uavg (fun x => ∑ i, ∑ k, (u i x * u k x) ^ 2) := by
      apply uavg_congr
      intro x
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [uavg_sum]; congr 1; funext i; exact uavg_sum _

omit [Fintype I] [Fintype J] in
/-- The product-variance estimate applied to the two products defining one Gram entry. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ FiniteRefresh(X, G); κ ∈ ℝ; u ∈ I → X → ℝ; v ∈ J → X → ℝ; a, b ∈ I × J, assume VarianceMixing(e, κ); OrthonormalFamily(u); OrthonormalFamily(v). Then

𝔼_g [(featureGram(e, u, v, g, a, b) - indexDelta(a, b))²] ≤ κ · 𝔼ₓ [(u((a)₁, x) · u((b)₁, x))²] · 𝔼ₓ [(v((a)₂, x) · v((b)₂, x))²].
-/
theorem featureGram_variance_le (e : FiniteRefresh X G) (κ : ℝ)
    (hmix : VarianceMixing e κ) (u : I → X → ℝ) (v : J → X → ℝ)
    (hu : OrthonormalFamily u) (hv : OrthonormalFamily v) (a b : I × J) :
    uavg (fun g => (featureGram e u v g a b - indexDelta a b) ^ 2) ≤
      κ * uavg (fun x => (u a.1 x * u b.1 x) ^ 2) *
        uavg (fun x => (v a.2 x * v b.2 x) ^ 2) := by
  have h := hmix (fun x => u a.1 x * u b.1 x)
    (fun x => v a.2 x * v b.2 x)
  rw [hu, hv, indexDelta_prod] at h
  exact h

/-- Summed variance gives the squared counting L2 deviation bound. -/

/-
Mathematical statement (normal notation): Suppose the random action has variance coefficient at most κ, and (uᵢ),(vⱼ) are uniformly orthonormal. The Gram matrix of the product functions uᵢ(x) · vⱼ(e_g(x)) satisfies

𝔼_g [∑_(a,b) (Gram_g(a,b)-δ_ab)²] ≤ κ · 𝔼ₓ [Φᵤ(x)²] · 𝔼_y [Φᵥ(y)²].

This generic lemma takes the variance bound as a hypothesis; the concrete matrix-action lemmas establish that hypothesis.
-/
theorem gramDeviationSq_mean_le (e : FiniteRefresh X G) (κ : ℝ)
    (hmix : VarianceMixing e κ) (u : I → X → ℝ) (v : J → X → ℝ)
    (hu : OrthonormalFamily u) (hv : OrthonormalFamily v) :
    uavg (gramDeviationSq e u v) ≤ κ * factorEnergySecondMoment u * factorEnergySecondMoment v := by
  classical
  calc
    _ = ∑ a : I × J, ∑ b : I × J,
        uavg (fun g => (featureGram e u v g a b - indexDelta a b) ^ 2) := by
      unfold gramDeviationSq
      rw [uavg_sum]
      apply Finset.sum_congr rfl
      intro a _
      exact uavg_sum _
    _ ≤ ∑ a : I × J, ∑ b : I × J,
        κ * uavg (fun x => (u a.1 x * u b.1 x) ^ 2) *
          uavg (fun x => (v a.2 x * v b.2 x) ^ 2) := by
      exact Finset.sum_le_sum (fun a _ => Finset.sum_le_sum
        (fun b _ => featureGram_variance_le e κ hmix u v hu hv a b))
    _ = κ * factorEnergySecondMoment u * factorEnergySecondMoment v := by
      rw [factorEnergySecondMoment_eq_sum, factorEnergySecondMoment_eq_sum]
      simp only [Fintype.sum_prod_type]
      calc
        _ = ∑ i : I, ∑ k : I, ∑ j : J, ∑ h : J,
            κ * uavg (fun x => (u i x * u k x) ^ 2) *
              uavg (fun x => (v j x * v h x) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
        _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]

/-- Orthonormal features have total factorEnergy equal to their number. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u ∈ I → X → ℝ, assume OrthonormalFamily(u). Then

𝔼ᵥ [factorEnergy(u, v)] = |I|.
-/
theorem factorEnergy_mean (u : I → X → ℝ) (hu : OrthonormalFamily u) :
    uavg (factorEnergy u) = (Fintype.card I : ℝ) := by
  unfold factorEnergy
  rw [uavg_sum]
  have hi (i : I) : uavg (fun x => u i x ^ 2) = 1 := by
    simpa only [pow_two, indexDelta_self] using hu i i
  simp_rw [hi]
  simp

/-- A uniform factorEnergy bound controls its second moment by bound times rank. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u ∈ I → X → ℝ; L ∈ ℝ, assume OrthonormalFamily(u); ∀ x, factorEnergy(u, x) ≤ L. Then

factorEnergySecondMoment(u) ≤ L · |I|.
-/
theorem factorEnergySecondMoment_le (u : I → X → ℝ) (hu : OrthonormalFamily u)
    (L : ℝ) (hL : ∀ x, factorEnergy u x ≤ L) :
    factorEnergySecondMoment u ≤ L * (Fintype.card I : ℝ) := by
  calc
    _ ≤ uavg (fun x => L * factorEnergy u x) := by
      apply uavg_mono
      intro x
      simpa only [pow_two] using
        mul_le_mul_of_nonneg_right (hL x) (factorEnergy_nonneg u x)
    _ = _ := by rw [uavg_const_mul, factorEnergy_mean u hu]

/-- The rank and pointwise factorEnergy estimates produced by singular-value truncation give the inverse-fourth-power moment bound. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u ∈ I → X → ℝ; H, α ∈ ℝ, assume OrthonormalFamily(u); 0 < α; |I| ≤ 1 / α²; ∀ x, factorEnergy(u, x) ≤ H² / α². Then

factorEnergySecondMoment(u) ≤ H² / α⁴.
-/
theorem factorEnergySecondMoment_le_truncated (u : I → X → ℝ) (hu : OrthonormalFamily u)
    (H α : ℝ) (_hα : 0 < α) (hrank : (Fintype.card I : ℝ) ≤ 1 / α ^ 2)
    (hlev : ∀ x, factorEnergy u x ≤ H ^ 2 / α ^ 2) :
    factorEnergySecondMoment u ≤ H ^ 2 / α ^ 4 := by
  calc
    _ ≤ (H ^ 2 / α ^ 2) * (Fintype.card I : ℝ) := factorEnergySecondMoment_le u hu _ hlev
    _ ≤ (H ^ 2 / α ^ 2) * (1 / α ^ 2) :=
      mul_le_mul_of_nonneg_left hrank (div_nonneg (sq_nonneg H) (sq_nonneg α))
    _ = _ := by field_simp

/-- The final parameter estimate on page 4, written with positive-power denominators rather than negative exponents. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ FiniteRefresh(X, G); κ ∈ ℝ; u ∈ I → X → ℝ; v ∈ J → X → ℝ; H, Jbound, α, β ∈ ℝ, assume 0 ≤ κ; VarianceMixing(e, κ); OrthonormalFamily(u); OrthonormalFamily(v); 0 < α; 0 < β; |I| ≤ 1 / α²; |J| ≤ 1 / β²; ∀ x, factorEnergy(u, x) ≤ H² / α²; ∀ x, factorEnergy(v, x) ≤ Jbound² / β². Then

𝔼_w [gramDeviationSq(e, u, v, w)] ≤ κ · H² · Jbound² / (α⁴ · β⁴).
-/
theorem gramDeviationSq_mean_le_truncated (e : FiniteRefresh X G) (κ : ℝ)
    (hκ : 0 ≤ κ) (hmix : VarianceMixing e κ)
    (u : I → X → ℝ) (v : J → X → ℝ)
    (hu : OrthonormalFamily u) (hv : OrthonormalFamily v)
    (H Jbound α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (huRank : (Fintype.card I : ℝ) ≤ 1 / α ^ 2)
    (hvRank : (Fintype.card J : ℝ) ≤ 1 / β ^ 2)
    (huLev : ∀ x, factorEnergy u x ≤ H ^ 2 / α ^ 2)
    (hvLev : ∀ x, factorEnergy v x ≤ Jbound ^ 2 / β ^ 2) :
    uavg (gramDeviationSq e u v) ≤ κ * H ^ 2 * Jbound ^ 2 / (α ^ 4 * β ^ 4) := by
  have huBound := factorEnergySecondMoment_le_truncated u hu H α hα huRank huLev
  have hvBound := factorEnergySecondMoment_le_truncated v hv Jbound β hβ hvRank hvLev
  calc
    _ ≤ κ * factorEnergySecondMoment u * factorEnergySecondMoment v :=
      gramDeviationSq_mean_le e κ hmix u v hu hv
    _ ≤ κ * (H ^ 2 / α ^ 4) * (Jbound ^ 2 / β ^ 4) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left huBound hκ
      · exact hvBound
      · exact factorEnergySecondMoment_nonneg v
      · exact mul_nonneg hκ (div_nonneg (sq_nonneg H) (by positivity))
    _ = _ := by ring

end

end TableAnalysis
