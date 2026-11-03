import Proofs.Compiler.LocalComparisons.GateInterface
import Proofs.Compiler.GateApproximation.Interfaces.Gadget.Shortened



/-!
# A concrete compiler-gate instance of the local comparison interface

The original table below is the actual accepted gadget's conditional answer probability. The approximation and its chosen factors are independent of all three plaintext labels. Only the error statement requires the gate equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical

namespace CircuitCompiler.GadgetApproximation

open Refresh MatrixRefresh TableAnalysis RefreshAnalysis

open AveragedEnergyComparison ShorteningTransport Shortening Rectangular

noncomputable section

variable {F A B : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype A] [Fintype B] {n t : ℕ}

variable [Nonempty (U F n)] [Nonempty (U F (n+t))]
  [Nonempty (FullRank F n (n+t))]

/-- Extend the actual conditional answer probability by zero outside the chosen output fiber. The extension has no effect under the labelled distribution. -/
/-
Mathematical definition (normal notation): For c ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n + 1)(F), A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(B, GateSide(F, n, n), (GateSide(F, n, n) × Kernel(H))); z ∈ A × B; v ∈ F; x, y ∈ GateSide(F, n, n), assume n · n + 1 = n + t. define

shortenedProbability(c, p, r, z, v, x, y) := { Fractional.shortenedAnswerDistribution(((o, (, u, :, Fiber, F, (, n, +, t,), v,) ↦ augmentedLongAnswerDistribution(c, p, o, u))), r, ((x)₁, (y)₁), (((x)₂, (y)₂), hv))(z) if secret(((x)₂, (y)₂)) = v,; 0 otherwise }.
-/
def shortenedProbability (hdim : n*n+1 = n+t) (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (GateSide F n n) ((GateSide F n n) × Kernel H)) (z : A × B) (v : F)
    (x y : GateSide F n n) : ℝ :=
  if hv : secret (⟨x.2,y.2⟩ : State F n) = v then
    (Fractional.shortenedAnswerDistribution
      (fun o (u : Fiber F (n+t) v) => augmentedLongAnswerDistribution hdim c p o u.val)
      r (x.1,y.1) ⟨⟨x.2,y.2⟩,hv⟩).weight z
  else 0

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c, v ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n + 1)(F), A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(B, GateSide(F, n, n), (GateSide(F, n, n) × Kernel(H))); z ∈ A × B; o ∈ (U(F, n) × U(F, n)) × (U(F, n) × U(F, n)); u ∈ Fiber(F, n, v), assume n · n + 1 = n + t. Then

shortenedProbability(c, p, r, z, v, ((o)₁, u.val.L), ((o)₂, u.val.R)) = Fractional.shortenedAnswerDistribution(((o, (, u, :, Fiber, F, (, n, +, t,), v,) ↦ augmentedLongAnswerDistribution(c, p, o, u))), r, o, u)(z).
-/
theorem shortenedProbability_on_fiber (hdim : n*n+1 = n+t) (c v : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (GateSide F n n) ((GateSide F n n) × Kernel H)) (z : A × B)
    (o : (U F n × U F n) × (U F n × U F n)) (u : Fiber F n v) :
    shortenedProbability hdim c p r z v (o.1,u.val.L) (o.2,u.val.R) =
      (Fractional.shortenedAnswerDistribution
        (fun o (u : Fiber F (n+t) v) => augmentedLongAnswerDistribution hdim c p o u.val)
        r o u).weight z := by
  unfold shortenedProbability
  simp only [show secret (⟨u.val.L,u.val.R⟩ : State F n) = v from u.property, dite_true]

/-- Actual multiplication/NAND local interface, including rectangular shortening. Taking `c=0` gives multiplication and `c=1` gives NAND over the binary field. All analytic hypotheses are discharged by the direct proof. -/

/-
Mathematical definition (normal notation): For the binary gadget computing s₁ · s₂+c, construct the local certificate for every matrix-phase/shortening-phase answer z. Assume n ≥ 2, n²+1 = n+t, 0<β ≤ 1, and (2ⁿ-1)² · β³ ≥ 1. Under independent input/output encoding distributions, the certificate has pointwise energies at most 2/β, mean energies at most 8, all-label L₂ bound 12, and valid-label error

ε = 396 · β^(1/3).

Validity means s_out = s₁ · s₂+c. This certificate concerns the accepted conditional answer distribution.
-/
def shortenedGateLocalEstimates (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (hdim : n*n+1 = n+t) (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (GateSide F n n) ((GateSide F n n) × Kernel H))
    (z : A × B) (β : ℝ) (hβ : 0 < β) (hβone : β ≤ 1)
    (hthreshold : 1 ≤ (Fintype.card (U F n × U F n) : ℝ) * β ^ 3) :
    GateLocalEstimates
      (fun labels : (F × F) × F => independentLabelledPortDistribution hn hn
        labels.1.1 labels.1.2 labels.2)
      (fun labels => labels.2 = labels.1.1 * labels.1.2 + c)
      (fun labels => shortenedProbability hdim c p r z labels.2)
      β (396 * β ^ (1 / 3 : ℝ)) where
  approximation := shortenedApproximation hdim c p r z β
  factors := shortenedFactors hdim c p r z β
  left_max := (shortenedFactors_pointwise hn hdim c p r z β hβ).1
  right_max := (shortenedFactors_pointwise hn hdim c p r z β hβ).2
  left_mean := by
    rw [← uavg_eq_expect_uniform]
    exact (shortenedFactors_mean hq hn hdim c p r z β hβ hβone hthreshold).1
  right_mean := by
    rw [← uavg_eq_expect_uniform]
    exact (shortenedFactors_mean hq hn hdim c p r z β hβ hβone hthreshold).2
  all_labels_rms labels := by
    letI := encoding_fiber_nonempty hn labels.2
    letI := encoding_fiber_nonempty (show 2 ≤ n+t by omega) labels.2
    rw [← fiberTable_rms_eq_labelled hn hn labels.1.1 labels.1.2 labels.2]
    exact shortenedApproximation_arbitrary_labels hq hn hdim c
      labels.1.1 labels.1.2 labels.2 p r z β
  valid_error_rms labels hv := by
    rcases labels with ⟨⟨s₁,s₂⟩,v⟩
    dsimp only at hv ⊢
    subst v
    letI := encoding_fiber_nonempty hn (s₁*s₂+c)
    letI := encoding_fiber_nonempty (show 2 ≤ n+t by omega) (s₁*s₂+c)
    rw [← fiberTable_rms_eq_labelled hn hn s₁ s₂ (s₁*s₂+c)
      (fun x y => shortenedProbability hdim c p r z (s₁*s₂+c) x y -
        shortenedApproximation hdim c p r z β x y)]
    simp only [shortenedProbability_on_fiber]
    exact shortenedApproximation_physical_error hq hn hdim c s₁ s₂ p r z β
      hβ hβone hthreshold

end

end CircuitCompiler.GadgetApproximation
