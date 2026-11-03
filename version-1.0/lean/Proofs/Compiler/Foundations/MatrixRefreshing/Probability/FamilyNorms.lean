import Proofs.Compiler.Foundations.MatrixRefreshing.Probability.FiniteDistribution



/-!
# Mean-square norms of finite answer families

The answer index is summed without normalization. Probability weights occur only in the sampled state, so these bounds remain valid for empty families and incur exactly the displayed cardinality factors.
-/

set_option autoImplicit false

open scoped BigOperators

namespace MatrixRefresh

open Refresh

variable {α β γ Z J : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [Fintype Z] [Fintype J]

/-- The square root of the expected sum of squared family values. States carry probability weights; the answer index is summed without normalization. -/
/-
Mathematical definition (normal notation): For P ∈ 𝒟(α); f ∈ Z → α → ℝ, define

familyRms(P, f) := √(𝔼_(a ← P) [∑_z ((f(z, a))²)]).
-/
noncomputable def familyRms (P : FiniteDistribution α) (f : Z → α → ℝ) : ℝ :=
  Real.sqrt (P.expect (fun a => ∑ z, f z a ^ 2))

/-- A family root mean square is nonnegative, including for an empty answer family. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f ∈ Z → α → ℝ, we have

0 ≤ familyRms(P, f).
-/
theorem familyRms_nonneg (P : FiniteDistribution α) (f : Z → α → ℝ) : 0 ≤ familyRms P f :=
  Real.sqrt_nonneg _

/-- Squaring the family RMS recovers the expected sum of answer squares. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f ∈ Z → α → ℝ, we have

(familyRms(P, f))² = 𝔼_(a ← P) [∑_z ((f(z, a))²)].
-/
@[simp] theorem familyRms_sq (P : FiniteDistribution α) (f : Z → α → ℝ) :
    familyRms P f ^ 2 = P.expect (fun a => ∑ z, f z a ^ 2) :=
  Real.sq_sqrt (P.expect_nonneg _ (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- Cauchy--Schwarz with the counting measure on answers and the probability distribution on states. No nonempty-family premise or cardinality division is used. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f, g ∈ Z → α → ℝ, we have

(∑_z (𝔼_(a ← P) [f(z, a) · g(z, a)]))² ≤ (familyRms(P, f))² · (familyRms(P, g))².
-/
theorem sum_expect_mul_sq_le (P : FiniteDistribution α) (f g : Z → α → ℝ) :
    (∑ z, P.expect (fun a => f z a * g z a)) ^ 2 ≤
      (familyRms P f) ^ 2 * (familyRms P g) ^ 2 := by
  rw [familyRms_sq, familyRms_sq, expect_sum, expect_sum]
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.univ : Finset (Z × α))
    (r := fun za => P.weight za.2 * (f za.1 za.2 * g za.1 za.2))
    (f := fun za => P.weight za.2 * f za.1 za.2 ^ 2)
    (g := fun za => P.weight za.2 * g za.1 za.2 ^ 2)
    (fun za _ => mul_nonneg (P.nonneg _) (sq_nonneg _))
    (fun za _ => mul_nonneg (P.nonneg _) (sq_nonneg _))
    (by intro za _; ring)
  simpa only [Fintype.sum_prod_type, FiniteDistribution.expect] using h

/-- The absolute summed correlation of two answer families is bounded by the product of their family RMS values under the same state distribution. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f, g ∈ Z → α → ℝ, we have

|∑_z (𝔼_(a ← P) [f(z, a) · g(z, a)])| ≤ familyRms(P, f) · familyRms(P, g).
-/
theorem abs_sum_expect_mul_le_familyRms_mul_familyRms
    (P : FiniteDistribution α) (f g : Z → α → ℝ) :
    |∑ z, P.expect (fun a => f z a * g z a)| ≤ familyRms P f * familyRms P g := by
  have h := sum_expect_mul_sq_le P f g
  have hf := familyRms_nonneg P f
  have hg := familyRms_nonneg P g
  have ha := abs_nonneg (∑ z, P.expect (fun a => f z a * g z a))
  have hs := sq_abs (∑ z, P.expect (fun a => f z a * g z a))
  nlinarith [mul_nonneg hf hg]

/-- Adding two families pointwise costs at most the sum of their family RMS values. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f, g ∈ Z → α → ℝ, we have

familyRms(P, ((z, a ↦ f(z, a) + g(z, a)))) ≤ familyRms(P, f) + familyRms(P, g).
-/
theorem familyRms_add_le (P : FiniteDistribution α) (f g : Z → α → ℝ) :
    familyRms P (fun z a => f z a + g z a) ≤ familyRms P f + familyRms P g := by
  have hexpand : P.expect (fun a => ∑ z, (f z a + g z a) ^ 2) =
      P.expect (fun a => ∑ z, f z a ^ 2) +
        2 * (∑ z, P.expect (fun a => f z a * g z a)) +
          P.expect (fun a => ∑ z, g z a ^ 2) := by
    calc
      _ = P.expect (fun a => (∑ z, f z a ^ 2) +
          2 * (∑ z, f z a * g z a) + ∑ z, g z a ^ 2) := by
        congr 1
        funext a
        simp only [add_sq, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
      _ = _ := by simp only [expect_add, expect_smul, expect_sum]
  have hcs := (le_abs_self (∑ z, P.expect (fun a => f z a * g z a))).trans
    (abs_sum_expect_mul_le_familyRms_mul_familyRms P f g)
  apply (sq_le_sq₀ (familyRms_nonneg P _)
    (add_nonneg (familyRms_nonneg P f) (familyRms_nonneg P g))).mp
  rw [add_sq, familyRms_sq, familyRms_sq, familyRms_sq, hexpand]
  nlinarith

/-- A bounded coefficient vector contributes only the cardinality in the squared finite Cauchy--Schwarz estimate. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c, f ∈ J → ℝ, assume ∀ j, |c(j)| ≤ 1. Then

(∑ⱼ (c(j) · f(j)))² ≤ |J| · ∑ⱼ ((f(j))²).
-/
theorem sum_bounded_mul_sq_le (c f : J → ℝ) (hc : ∀ j, |c j| ≤ 1) :
    (∑ j, c j * f j) ^ 2 ≤ (Fintype.card J : ℝ) * ∑ j, f j ^ 2 := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.univ : Finset J)
    (r := fun j => c j * f j) (f := fun j => c j ^ 2) (g := fun j => f j ^ 2)
    (fun j _ => sq_nonneg _) (fun j _ => sq_nonneg _) (by intro j _; ring)
  have hsum : (∑ j, c j ^ 2) ≤ (Fintype.card J : ℝ) := by
    calc
      _ ≤ ∑ _j : J, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        have hj := sq_le_sq.mpr (show |c j| ≤ |(1 : ℝ)| by simpa using hc j)
        simpa using hj
      _ = _ := by simp
  exact h.trans (mul_le_mul_of_nonneg_right hsum (Finset.sum_nonneg (fun j _ => sq_nonneg _)))

/-- Average a two-answer table composition over its middle state, using continuation coefficients that may depend on both answers and the final state. The second table family may depend on the first answer; the coefficients are arbitrary here and bounded in the estimates below. -/
/-
Mathematical definition (normal notation): For Q ∈ 𝒟(β); C ∈ Z → J → γ → ℝ; A ∈ Z → α → β → ℝ; B ∈ Z → J → β → γ → ℝ, define

indexedCompose(Q, C, A, B) := (a, c ↦ 𝔼_(b ← Q) [∑_z (∑ⱼ (C(z, j, c) · A(z, a, b) · B(z, j, b, c)))]).
-/
def indexedCompose (Q : FiniteDistribution β) (C : Z → J → γ → ℝ)
    (A : Z → α → β → ℝ) (B : Z → J → β → γ → ℝ) : α → γ → ℝ :=
  fun a c => Q.expect (fun b => ∑ z, ∑ j, C z j c * A z a b * B z j b c)

omit [Fintype α] [Fintype γ] in
/-- Regroup the indexed composition by the first answer, moving finite answer sums through the middle-state expectation without changing the continuation coefficients. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Q ∈ 𝒟(β); C ∈ Z → J → γ → ℝ; A ∈ Z → α → β → ℝ; B ∈ Z → J → β → γ → ℝ; a ∈ α; c ∈ γ, we have

indexedCompose(Q, C, A, B, a, c) = ∑_z (𝔼_(b ← Q) [A(z, a, b) · ∑ⱼ (C(z, j, c) · B(z, j, b, c))]).
-/
private theorem indexedCompose_eq (Q : FiniteDistribution β) (C : Z → J → γ → ℝ)
    (A : Z → α → β → ℝ) (B : Z → J → β → γ → ℝ) (a : α) (c : γ) :
    indexedCompose Q C A B a c =
      ∑ z, Q.expect (fun b => A z a b * ∑ j, C z j c * B z j b c) := by
  unfold indexedCompose
  rw [expect_sum]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  funext b
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Squared indexed composition: Cauchy--Schwarz first uses `(z,b)`, then the second answer index. The remaining outer factors depend separately on `a,c`. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); Q ∈ 𝒟(β); R ∈ 𝒟(γ); C ∈ Z → J → γ → ℝ; A ∈ Z → α → β → ℝ; B ∈ Z → J → β → γ → ℝ, assume ∀ z, j, c, |C(z, j, c)| ≤ 1. Then

𝔼_(ac ← (P ⊗ R)) [(indexedCompose(Q, C, A, B, (ac)₁, (ac)₂))²] ≤ |J| · (familyRms((P ⊗ Q), ((z, ab ↦ A(z, (ab)₁, (ab)₂)))))² · (familyRms((Q ⊗ R), ((zj ∈ Z × J, bc ↦ B((zj)₁, (zj)₂, (bc)₁, (bc)₂)))))².
-/
theorem indexedCompose_sq_expect_le (P : FiniteDistribution α) (Q : FiniteDistribution β) (R : FiniteDistribution γ)
    (C : Z → J → γ → ℝ) (A : Z → α → β → ℝ) (B : Z → J → β → γ → ℝ)
    (hC : ∀ z j c, |C z j c| ≤ 1) :
    (P.prod R).expect (fun ac => indexedCompose Q C A B ac.1 ac.2 ^ 2) ≤
      (Fintype.card J : ℝ) *
        familyRms (P.prod Q) (fun z ab => A z ab.1 ab.2) ^ 2 *
        familyRms (Q.prod R) (fun (zj : Z × J) bc => B zj.1 zj.2 bc.1 bc.2) ^ 2 := by
  let A₂ : α → ℝ := fun a => Q.expect (fun b => ∑ z, A z a b ^ 2)
  let B₂ : γ → ℝ := fun c => Q.expect (fun b => ∑ z, ∑ j, B z j b c ^ 2)
  have hpoint (a : α) (c : γ) : indexedCompose Q C A B a c ^ 2 ≤
      (Fintype.card J : ℝ) * (A₂ a * B₂ c) := by
    rw [indexedCompose_eq]
    have hcs := sum_expect_mul_sq_le Q (fun z b => A z a b)
      (fun z b => ∑ j, C z j c * B z j b c)
    rw [familyRms_sq, familyRms_sq] at hcs
    have hg : Q.expect (fun b => ∑ z, (∑ j, C z j c * B z j b c) ^ 2) ≤
        (Fintype.card J : ℝ) * B₂ c := by
      calc
        _ ≤ Q.expect (fun b => ∑ z, (Fintype.card J : ℝ) * ∑ j, B z j b c ^ 2) := by
          apply Q.expect_mono
          intro b
          exact Finset.sum_le_sum (fun z _ => sum_bounded_mul_sq_le _ _ (hC z · c))
        _ = _ := by simp only [← Finset.mul_sum, expect_smul, B₂]
    have ha : 0 ≤ A₂ a := Q.expect_nonneg _ (fun b => Finset.sum_nonneg (fun z _ => sq_nonneg _))
    calc
      _ ≤ A₂ a * Q.expect (fun b => ∑ z, (∑ j, C z j c * B z j b c) ^ 2) := hcs
      _ ≤ A₂ a * ((Fintype.card J : ℝ) * B₂ c) := mul_le_mul_of_nonneg_left hg ha
      _ = _ := by ring
  have hA : P.expect A₂ = familyRms (P.prod Q) (fun z ab => A z ab.1 ab.2) ^ 2 := by
    rw [familyRms_sq, expect_prod]
  have hB : R.expect B₂ = familyRms (Q.prod R) (fun (zj : Z × J) bc => B zj.1 zj.2 bc.1 bc.2) ^ 2 := by
    rw [familyRms_sq, expect_prod]
    dsimp [B₂]
    rw [expect_comm R Q]
    simp only [Fintype.sum_prod_type]
  calc
    _ ≤ (P.prod R).expect (fun ac => (Fintype.card J : ℝ) * (A₂ ac.1 * B₂ ac.2)) :=
      (P.prod R).expect_mono (fun ac => hpoint ac.1 ac.2)
    _ = (Fintype.card J : ℝ) * (P.expect A₂ * R.expect B₂) := by
      rw [expect_smul, expect_prod_mul]
    _ = _ := by rw [hA, hB]; ring

/-- The composition cost is the square root of the second answer count, with both table-family norms retaining their unnormalized answer sums. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); Q ∈ 𝒟(β); R ∈ 𝒟(γ); C ∈ Z → J → γ → ℝ; A ∈ Z → α → β → ℝ; B ∈ Z → J → β → γ → ℝ, assume ∀ z, j, c, |C(z, j, c)| ≤ 1. Then

‖ ((ac ↦ indexedCompose(Q, C, A, B, (ac)₁, (ac)₂)))‖_(2,(P ⊗ R)) ≤ √(|J|) · familyRms((P ⊗ Q), ((z, ab ↦ A(z, (ab)₁, (ab)₂)))) · familyRms((Q ⊗ R), ((zj ∈ Z × J, bc ↦ B((zj)₁, (zj)₂, (bc)₁, (bc)₂)))).
-/
theorem rms_indexed_compose_le (P : FiniteDistribution α) (Q : FiniteDistribution β) (R : FiniteDistribution γ)
    (C : Z → J → γ → ℝ) (A : Z → α → β → ℝ) (B : Z → J → β → γ → ℝ)
    (hC : ∀ z j c, |C z j c| ≤ 1) :
    rms (P.prod R) (fun ac => indexedCompose Q C A B ac.1 ac.2) ≤
      Real.sqrt (Fintype.card J : ℝ) *
        familyRms (P.prod Q) (fun z ab => A z ab.1 ab.2) *
        familyRms (Q.prod R) (fun (zj : Z × J) bc => B zj.1 zj.2 bc.1 bc.2) := by
  have h := Real.sqrt_le_sqrt (indexedCompose_sq_expect_le P Q R C A B hC)
  simpa only [rms, Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg (Fintype.card J)) (sq_nonneg _)),
    Real.sqrt_mul (Nat.cast_nonneg (Fintype.card J)), Real.sqrt_sq (familyRms_nonneg _ _)] using h

end MatrixRefresh
