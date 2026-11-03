import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Proofs.Compiler.GateApproximation.Refreshing.EnergyCompression.Security



/-!
# Arbitrary independent measurable tapes

The tape space need not be finite. For a finite public transcript, integrate its conditional weights over the common tape distribution. Measurability is the usual requirement for this randomized experiment to define a probability distribution.
-/

set_option autoImplicit false

open scoped BigOperators

open MeasureTheory

namespace TableAnalysis.EnergyCompression

open MatrixRefresh Refresh TableAnalysis

noncomputable section

variable {Ω H : Type*} [MeasurableSpace Ω] [Fintype H]

-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(H); h ∈ H, we have

P(h) ≤ 1.
-/
theorem probability_weight_le_one (P : FiniteDistribution H) (h : H) : P.weight h ≤ 1 := by
  classical
  calc
    P.weight h ≤ ∑ x, P.weight x := Finset.single_le_sum (fun x _ => P.nonneg x)
      (Finset.mem_univ h)
    _ = 1 := P.total

-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For μ ∈ Measure(Ω); P ∈ Ω → 𝒟(H); h ∈ H; hm ∈ AEStronglyMeasurable(((ω ↦ P(ω)(h))), μ), assume IsProbabilityMeasure(μ). Then

Integrable(((ω ↦ P(ω)(h))), μ).
-/
theorem conditional_weight_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Ω → FiniteDistribution H) (h : H)
    (hm : AEStronglyMeasurable (fun ω => (P ω).weight h) μ) :
    Integrable (fun ω => (P ω).weight h) μ := by
  apply Integrable.of_bound hm 1
  filter_upwards [] with ω
  simpa only [Real.norm_eq_abs, abs_of_nonneg ((P ω).nonneg h)] using
    probability_weight_le_one (P ω) h

/- Mathematical definition (normal notation): Given a probability measure μ on random tapes and measurable finite conditional distributions P_ω, define their mixture by P(h) := ∫ P_ω(h) dμ(ω). -/
def measuredMixture (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Ω → FiniteDistribution H)
    (hm : ∀ h, AEStronglyMeasurable (fun ω => (P ω).weight h) μ) : FiniteDistribution H where
  weight h := ∫ ω, (P ω).weight h ∂μ
  nonneg h := integral_nonneg (fun ω => (P ω).nonneg h)
  total := by
    classical
    rw [← integral_finset_sum Finset.univ
      (fun h _ => conditional_weight_integrable μ P h (hm h))]
    simp only [FiniteDistribution.total]
    simp

/-- Averaging over any independent probability space preserves a uniform conditional statistical-distance bound. -/
-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For μ ∈ Measure(Ω); P, Q ∈ Ω → 𝒟(H); hP ∈ ∀ h, AEStronglyMeasurable(((ω ↦ P(ω)(h))), μ); hQ ∈ ∀ h, AEStronglyMeasurable(((ω ↦ Q(ω)(h))), μ); B ∈ ℝ, assume IsProbabilityMeasure(μ); ∀ ω, δ(P(ω), Q(ω)) ≤ B. Then

δ(measuredMixture(μ, P, hP), measuredMixture(μ, Q, hQ)) ≤ B.
-/
theorem measuredMixture_distance_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Ω → FiniteDistribution H)
    (hP : ∀ h, AEStronglyMeasurable (fun ω => (P ω).weight h) μ)
    (hQ : ∀ h, AEStronglyMeasurable (fun ω => (Q ω).weight h) μ)
    (B : ℝ) (hB : ∀ ω, statisticalDistance (P ω) (Q ω) ≤ B) :
    statisticalDistance (measuredMixture μ P hP) (measuredMixture μ Q hQ) ≤ B := by
  classical
  have hiP := fun h => conditional_weight_integrable μ P h (hP h)
  have hiQ := fun h => conditional_weight_integrable μ Q h (hQ h)
  have hi : ∀ h, Integrable (fun ω => |(P ω).weight h - (Q ω).weight h|) μ :=
    fun h => (hiP h |>.sub (hiQ h)).abs
  have hisum : Integrable (fun ω => ∑ h, |(P ω).weight h - (Q ω).weight h|) μ :=
    integrable_finset_sum Finset.univ (fun h _ => hi h)
  have hidist : Integrable (fun ω => statisticalDistance (P ω) (Q ω)) μ :=
    hisum.const_mul (1 / 2)
  calc
    _ = (1 / 2 : ℝ) * ∑ h, |∫ ω, ((P ω).weight h - (Q ω).weight h) ∂μ| := by
      simp only [statisticalDistance, variationNorm, measuredMixture,
        integral_sub (hiP _) (hiQ _)]
    _ ≤ (1 / 2 : ℝ) * ∑ h, ∫ ω, |(P ω).weight h - (Q ω).weight h| ∂μ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun h _ => abs_integral_le_integral_abs)
    _ = ∫ ω, statisticalDistance (P ω) (Q ω) ∂μ := by
      rw [← integral_finset_sum Finset.univ (fun h _ => hi h)]
      simp only [statisticalDistance, variationNorm, integral_const_mul]
    _ ≤ ∫ _ : Ω, B ∂μ := integral_mono hidist (integrable_const B) hB
    _ = B := by simp

variable {F Z : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype Z] [Nonempty Z] {n : ℕ}

/-- The security bound averaged over an independent measurable random tape. -/
-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For μ ∈ Measure(Ω); p ∈ Ω → RectangleProtocol(F, n, Z); s, t ∈ F; T ∈ ℕ; compress ∈ CompressionProcedure(F, n, Z, θ(F, n)); hs ∈ ∀ h, AEStronglyMeasurable(((ω ↦ ((Prod)₂_*rectangleExecution(p(ω), μₛ, T))(h))), μ); ht ∈ ∀ h, AEStronglyMeasurable(((ω ↦ ((Prod)₂_*rectangleExecution(p(ω), μₜ, T))(h))), μ), assume 2 ≤ n; IsProbabilityMeasure(μ). Then

δ(measuredMixture(μ, ((ω ↦ ((Prod)₂_*rectangleExecution(p(ω), μₛ, T)))), hs), measuredMixture(μ, ((ω ↦ ((Prod)₂_*rectangleExecution(p(ω), μₜ, T)))), ht)) ≤ min{securityBound(|Z|, minSecretProbability(F, n), θ(F, n), |F|, |F|ⁿ, T), 1}.
-/
theorem arbitrary_tape_refresh_security_of_compression (hn : 2 ≤ n)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Ω → RectangleProtocol F n Z)
    (s t : F) (T : ℕ)
    (compress : CompressionProcedure F n Z (theta F n))
    (hs : ∀ h, AEStronglyMeasurable (fun ω =>
      ((rectangleExecution (p ω) (mu F n hn s) T).map Prod.snd).weight h) μ)
    (ht : ∀ h, AEStronglyMeasurable (fun ω =>
      ((rectangleExecution (p ω) (mu F n hn t) T).map Prod.snd).weight h) μ) :
    statisticalDistance
      (measuredMixture μ (fun ω =>
        (rectangleExecution (p ω) (mu F n hn s) T).map Prod.snd) hs)
      (measuredMixture μ (fun ω =>
        (rectangleExecution (p ω) (mu F n hn t) T).map Prod.snd) ht) ≤
      min (securityBound (Fintype.card Z) (minSecretProbability F n)
        (theta F n) (fieldCard F) (vectorCard F n) T) 1 :=
  measuredMixture_distance_le μ _ _ hs ht _
    (fun ω => security_of_compression_all hn (p ω) s t T (theta F n)
      (theta_pos hn).le compress)

/-- An observer may use the entire independent tape together with the transcript. This includes arbitrary measurable randomized distinguishers: choose a Boolean output alphabet for their acceptance decision. -/
-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A a set; μ ∈ Measure(Ω); p ∈ Ω → RectangleProtocol(F, n, Z); T ∈ ℕ; view ∈ Ω → PublicHistory(Z, T) → A; s, t ∈ F; compress ∈ CompressionProcedure(F, n, Z, θ(F, n)); hs ∈ ∀ a, AEStronglyMeasurable(((ω ↦ (view(ω)_*((Prod)₂_*rectangleExecution(p(ω), μₛ, T)))(a))), μ); ht ∈ ∀ a, AEStronglyMeasurable(((ω ↦ (view(ω)_*((Prod)₂_*rectangleExecution(p(ω), μₜ, T)))(a))), μ), assume A is finite; 2 ≤ n; IsProbabilityMeasure(μ). Then

δ(measuredMixture(μ, ((ω ↦ (view(ω)_*((Prod)₂_*rectangleExecution(p(ω), μₛ, T))))), hs), measuredMixture(μ, ((ω ↦ (view(ω)_*((Prod)₂_*rectangleExecution(p(ω), μₜ, T))))), ht)) ≤ min{securityBound(|Z|, minSecretProbability(F, n), θ(F, n), |F|, |F|ⁿ, T), 1}.
-/
theorem arbitrary_tape_view_security_of_compression {A : Type*} [Fintype A] (hn : 2 ≤ n)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Ω → RectangleProtocol F n Z) (T : ℕ)
    (view : Ω → PublicHistory Z T → A) (s t : F)
    (compress : CompressionProcedure F n Z (theta F n))
    (hs : ∀ a, AEStronglyMeasurable (fun ω =>
      (((rectangleExecution (p ω) (mu F n hn s) T).map Prod.snd).map
        (view ω)).weight a) μ)
    (ht : ∀ a, AEStronglyMeasurable (fun ω =>
      (((rectangleExecution (p ω) (mu F n hn t) T).map Prod.snd).map
        (view ω)).weight a) μ) :
    statisticalDistance
      (measuredMixture μ (fun ω =>
        ((rectangleExecution (p ω) (mu F n hn s) T).map Prod.snd).map (view ω)) hs)
      (measuredMixture μ (fun ω =>
        ((rectangleExecution (p ω) (mu F n hn t) T).map Prod.snd).map (view ω)) ht) ≤
      min (securityBound (Fintype.card Z) (minSecretProbability F n)
        (theta F n) (fieldCard F) (vectorCard F n) T) 1 :=
  measuredMixture_distance_le μ _ _ hs ht _ (fun ω =>
    (statisticalDistance_map_le _ _ (view ω)).trans
      (security_of_compression_all hn (p ω) s t T (theta F n)
      (theta_pos hn).le compress))

section FiniteTape

variable {Ξ : Type*} [Fintype Ξ]

/-
Mathematical definition (normal notation): For tape ∈ 𝒟(Ξ); p ∈ Ξ → RectangleProtocol(F, n, Z); s ∈ F; T ∈ ℕ, assume 2 ≤ n. define

randomizedRectangleTranscript(tape, p, s, T) := tape.joint(((ω ↦ ((Prod)₂_*rectangleExecution(p(ω), μₛ, T))))).
-/
def randomizedRectangleTranscript (tape : FiniteDistribution Ξ)
    (p : Ξ → RectangleProtocol F n Z) (hn : 2 ≤ n) (s : F) (T : ℕ) :
    FiniteDistribution (Ξ × PublicHistory Z T) :=
  tape.joint (fun ω => (rectangleExecution (p ω) (mu F n hn s) T).map Prod.snd)

/-- Finite secret-independent tapes may be included in the observed view. -/
-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For tape ∈ 𝒟(Ξ); p ∈ Ξ → RectangleProtocol(F, n, Z); s, t ∈ F; T ∈ ℕ; compress ∈ CompressionProcedure(F, n, Z, θ(F, n)), assume 2 ≤ n. Then

δ(randomizedRectangleTranscript(tape, p, s, T), randomizedRectangleTranscript(tape, p, t, T)) ≤ min{securityBound(|Z|, minSecretProbability(F, n), θ(F, n), |F|, |F|ⁿ, T), 1}.
-/
theorem randomized_refresh_security_of_compression (hn : 2 ≤ n)
    (tape : FiniteDistribution Ξ) (p : Ξ → RectangleProtocol F n Z) (s t : F) (T : ℕ)
    (compress : CompressionProcedure F n Z (theta F n)) :
    statisticalDistance (randomizedRectangleTranscript tape p hn s T)
      (randomizedRectangleTranscript tape p hn t T) ≤
      min (securityBound (Fintype.card Z) (minSecretProbability F n)
        (theta F n) (fieldCard F) (vectorCard F n) T) 1 := by
  let P := fun ω => (rectangleExecution (p ω) (mu F n hn s) T).map Prod.snd
  let Q := fun ω => (rectangleExecution (p ω) (mu F n hn t) T).map Prod.snd
  have hmix : statisticalDistance (tape.joint P) (tape.joint Q) =
      tape.expect (fun ω => statisticalDistance (P ω) (Q ω)) :=
    statisticalDistance_joint_mixture tape P Q
  change statisticalDistance (tape.joint P) (tape.joint Q) ≤ _
  rw [hmix]
  exact tape.expect_le_const (fun ω => security_of_compression_all hn (p ω) s t T
    (theta F n) (theta_pos hn).le compress)

/-- Hiding the tape can only decrease the transcript distance. -/
-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For tape ∈ 𝒟(Ξ); p ∈ Ξ → RectangleProtocol(F, n, Z); s, t ∈ F; T ∈ ℕ; compress ∈ CompressionProcedure(F, n, Z, θ(F, n)), assume 2 ≤ n. Then

δ(((Prod)₂_*randomizedRectangleTranscript(tape, p, s, T)), ((Prod)₂_*randomizedRectangleTranscript(tape, p, t, T))) ≤ min{securityBound(|Z|, minSecretProbability(F, n), θ(F, n), |F|, |F|ⁿ, T), 1}.
-/
theorem randomized_refresh_security_hidden_tape_of_compression (hn : 2 ≤ n)
    (tape : FiniteDistribution Ξ) (p : Ξ → RectangleProtocol F n Z) (s t : F) (T : ℕ)
    (compress : CompressionProcedure F n Z (theta F n)) :
    statisticalDistance ((randomizedRectangleTranscript tape p hn s T).map Prod.snd)
      ((randomizedRectangleTranscript tape p hn t T).map Prod.snd) ≤
      min (securityBound (Fintype.card Z) (minSecretProbability F n)
        (theta F n) (fieldCard F) (vectorCard F n) T) 1 :=
  (statisticalDistance_map_le _ _ Prod.snd).trans
    (randomized_refresh_security_of_compression hn tape p s t T compress)

omit [Nonempty Z] in
/-- No transcript bits exist at time zero, even with the tape exposed. -/
-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For tape ∈ 𝒟(Ξ); p ∈ Ξ → RectangleProtocol(F, n, Z); s, t ∈ F, assume 2 ≤ n. Then

δ(randomizedRectangleTranscript(tape, p, s, 0), randomizedRectangleTranscript(tape, p, t, 0)) = 0.
-/
theorem randomizedRectangleTranscript_zero_distance (hn : 2 ≤ n)
    (tape : FiniteDistribution Ξ) (p : Ξ → RectangleProtocol F n Z) (s t : F) :
    statisticalDistance (randomizedRectangleTranscript tape p hn s 0)
      (randomizedRectangleTranscript tape p hn t 0) = 0 := by
  let P := fun ω => (rectangleExecution (p ω) (mu F n hn s) 0).map Prod.snd
  let Q := fun ω => (rectangleExecution (p ω) (mu F n hn t) 0).map Prod.snd
  have h : P = Q := by
    funext ω
    exact FiniteDistribution.eq_of_subsingleton (P ω) (Q ω)
  change statisticalDistance (tape.joint P) (tape.joint Q) = 0
  rw [h, statisticalDistance_self]

end FiniteTape

end

end TableAnalysis.EnergyCompression
