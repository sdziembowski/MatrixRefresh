import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Proofs.Compiler.GateApproximation.Shortening.RectangularPhysicalStochastic
import Proofs.Compiler.GateApproximation.MatrixPhase.RejectionPrefix
import Proofs.Compiler.GateApproximation.Refreshing.EnergyCompression.Randomized
import Proofs.Compiler.Construction.Parameters



/-!
# Finite observations of countable mixtures
-/
set_option autoImplicit false

open scoped BigOperators ENNReal

namespace CircuitCompiler.Sampling.Unbounded

open Refresh MeasureTheory TableAnalysis

noncomputable section

variable {Ω V : Type*} [Countable Ω] [Fintype V]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For tape ∈ PMF(Ω); P ∈ Ω → 𝒟(V); v ∈ V, we have

countableMixture(tape, P)(v) = ∑_ω (toReal(tape(ω)) · P(ω)(v)).
-/
theorem countableMixture_weight (tape : PMF Ω) (P : Ω → FiniteDistribution V) (v : V) :
    (countableMixture tape P).weight v = ∑' ω, (tape ω).toReal * (P ω).weight v := by
  change ((tape.bind (fun ω => toPMF (P ω))) v).toReal = _
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq
    (fun ω => ENNReal.mul_ne_top (tape.apply_ne_top ω) ((toPMF (P ω)).apply_ne_top v))]
  simp only [ENNReal.toReal_mul, toPMF_apply, ENNReal.toReal_ofReal ((P _).nonneg v)]

/-- PMF mixtures agree exactly with integration against their discrete measure. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For tape ∈ PMF(Ω); P ∈ Ω → 𝒟(V), assume MeasurableSpace(Ω); MeasurableSingletonClass(Ω). Then

countableMixture(tape, P) = EnergyCompression.measuredMixture(tape.toMeasure, P, ((v ↦ aestronglyMeasurable(measurable_of_countable(((ω ↦ P(ω)(v)))))))).
-/
theorem countableMixture_eq_measured [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (tape : PMF Ω) (P : Ω → FiniteDistribution V) :
    countableMixture tape P = EnergyCompression.measuredMixture tape.toMeasure P
      (fun v => (measurable_of_countable (fun ω => (P ω).weight v)).aestronglyMeasurable) := by
  ext v
  rw [countableMixture_weight]
  change _ = ∫ ω, (P ω).weight v ∂tape.toMeasure
  rw [PMF.integral_eq_tsum tape _ (EnergyCompression.conditional_weight_integrable tape.toMeasure P v
    (measurable_of_countable _).aestronglyMeasurable)]
  rfl

/-- Uniform conditional privacy bounds survive arbitrary countable mixtures. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For tape ∈ PMF(Ω); P, Q ∈ Ω → 𝒟(V); ε ∈ ℝ, assume ∀ ω, δ(P(ω), Q(ω)) ≤ ε. Then

δ(countableMixture(tape, P), countableMixture(tape, Q)) ≤ ε.
-/
theorem countableMixture_distance_le (tape : PMF Ω) (P Q : Ω → FiniteDistribution V)
    (ε : ℝ) (h : ∀ ω, statisticalDistance (P ω) (Q ω) ≤ ε) :
    statisticalDistance (countableMixture tape P) (countableMixture tape Q) ≤ ε := by
  letI : MeasurableSpace Ω := ⊤
  rw [countableMixture_eq_measured, countableMixture_eq_measured]
  exact EnergyCompression.measuredMixture_distance_le tape.toMeasure P Q _ _ ε h

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For W a set; tape ∈ PMF(Ω); P ∈ Ω → 𝒟(V); Q ∈ V → 𝒟(W), assume W is finite. Then

bind(countableMixture(tape, P), Q) = countableMixture(tape, ((ω ↦ bind(P(ω), Q)))).
-/
theorem countableMixture_bind {W : Type*} [Fintype W]
    (tape : PMF Ω) (P : Ω → FiniteDistribution V) (Q : V → FiniteDistribution W) :
    (countableMixture tape P).bind Q = countableMixture tape (fun ω => (P ω).bind Q) := by
  unfold countableMixture
  have h := toFinite_bind (tape.bind (fun ω => toPMF (P ω))) (fun v => toPMF (Q v))
  simp only [toFinite_toPMF] at h
  rw [← h]
  simp only [PMF.bind_bind, ← toPMF_bind]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For W a set; tape ∈ PMF(Ω); P ∈ Ω → 𝒟(V); f ∈ V → W, assume W is finite. Then

(f_*countableMixture(tape, P)) = countableMixture(tape, ((ω ↦ (f_*P(ω))))).
-/
theorem countableMixture_map {W : Type*} [Fintype W]
    (tape : PMF Ω) (P : Ω → FiniteDistribution V) (f : V → W) :
    (countableMixture tape P).map f = countableMixture tape (fun ω => (P ω).map f) :=
  countableMixture_bind tape P (fun v => FiniteDistribution.pure (f v))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Ξ a set; tape ∈ PMF(Ω); next ∈ Ω → PMF(Ξ); P ∈ Ξ → 𝒟(V), assume Countable(Ξ). Then

countableMixture(bind(tape, next), P) = countableMixture(tape, ((ω ↦ countableMixture(next(ω), P)))).
-/
theorem countableMixture_assoc {Ξ : Type*} [Countable Ξ]
    (tape : PMF Ω) (next : Ω → PMF Ξ) (P : Ξ → FiniteDistribution V) :
    countableMixture (tape.bind next) P =
      countableMixture tape (fun ω => countableMixture (next ω) P) := by
  unfold countableMixture
  simp only [toPMF_toFinite, PMF.bind_bind]

end

end CircuitCompiler.Sampling.Unbounded
