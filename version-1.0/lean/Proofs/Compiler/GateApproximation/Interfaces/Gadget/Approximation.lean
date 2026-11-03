import Proofs.Compiler.GateApproximation.Interfaces.DirectApproximation
import Proofs.Compiler.GateApproximation.Interfaces.Gadget.Labelled



/-!
# The direct local interface for the augmented matrix gadget

The same explicit table is used for every assignment of plaintext labels. The approximation error is required only on the valid multiplication/NAND labels; its own `L₂` bound holds on every three-label distribution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical

namespace CircuitCompiler.GadgetApproximation

open Refresh MatrixRefresh TableAnalysis RefreshAnalysis SingularTruncation

open TruncatedAnswerNorm AveragedEnergyComparison

noncomputable section

variable {F Z : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype Z] {n : ℕ}

/-
Mathematical definition (normal notation): The matrix-phase answer table for an augmented multiplication gadget is prob_z formed from the encoding maps

a_c(L₁,L₂) = (L₁ ⊗ L₂,c), b(R₁,R₂) = (R₁ ⊗ R₂,1).

Its rows and columns include the old operand shares and the long refreshed share.
-/
def augmentedProbability (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) Z) (z : Z) :
    Matrix (GateSide F n (n*n+1)) (GateSide F n (n*n+1)) ℝ :=
  answerProb (Rectangular.augmentedShare c) (Rectangular.augmentedShare 1) p z

/-
Mathematical definition (normal notation): For answer z, take the same signed approximation for every labeling:

G_z := 2 · (prob_z)^(>β).

The strict cutoff uses the normalized singular coefficients of the augmented answer table.
-/
def augmentedApproximation (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) Z)
    (z : Z) (β : ℝ) : Matrix (GateSide F n (n*n+1)) (GateSide F n (n*n+1)) ℝ :=
  strictDoubled (augmentedProbability c p z) β

/- Mathematical definition (normal notation): Use the balanced factors of the strict singular expansion of prob_z, each multiplied by √2. Their products sum to G_z = 2 · (prob_z)^(>β). This chooses one concrete representation for all labels. -/
def augmentedFactors (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) Z)
    (z : Z) (β : ℝ) : Factors (augmentedApproximation c p z β) :=
  strictDoubledFactors (augmentedProbability c p z) β


/-
Mathematical statement (normal notation): For every answer z of the augmented tensor gadget and every β>0, the chosen factors of the doubled strict-truncation approximation satisfy, at every left and right input,

Φ_z(x) ≤ 2/β, Ψ_z(y) ≤ 2/β.

The dimension assumption is n ≥ 2; this bound does not require the binary-field or threshold-size assumptions.
-/
theorem augmentedFactors_pointwise (hn : 2 ≤ n) (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) Z)
    (z : Z) (β : ℝ) (hβ : 0 < β) :
    (∀ x, (augmentedFactors c p z β).leftEnergy x ≤ 2 / β) ∧
      (∀ y, (augmentedFactors c p z β).rightEnergy y ≤ 2 / β) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  letI : Nonempty (U F (n*n+1)) := ⟨unitShare ⟨0, by omega⟩⟩
  exact ⟨strictDoubledFactors_left_le _ β hβ (AnswerApproximation.answerProb_le_one _ _ p z),
    strictDoubledFactors_right_le _ β hβ (AnswerApproximation.answerProb_le_one _ _ p z)⟩


/-
Mathematical statement (normal notation): Over the binary field, assume n ≥ 2, 0<β ≤ 1, and (2ⁿ-1)² · β³ ≥ 1. For every answer of the augmented tensor gadget, the same chosen factors satisfy

𝔼ₓ [Φ_z(x)] ≤ 8, 𝔼_y [Ψ_z(y)] ≤ 8.

The averages are uniform. The formalized constant is eight, rather than the paper's four.
-/
theorem augmentedFactors_mean (hq : fieldCard F = 2) (hn : 2 ≤ n) (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) Z)
    (z : Z) (β : ℝ) (hβ : 0 < β) (hβone : β ≤ 1)
    (hthreshold : 1 ≤ (Fintype.card (U F n × U F n) : ℝ) * β ^ 3) :
    uavg (augmentedFactors c p z β).leftEnergy ≤ 8 ∧
      uavg (augmentedFactors c p z β).rightEnergy ≤ 8 := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  exact feature_answer_factors_mean_le_eight hq (by nlinarith)
    (Rectangular.augmentedShare c) (Rectangular.augmentedShare 1)
    (Rectangular.augmentedShare_injective_binary hq c)
    (Rectangular.augmentedShare_injective_binary hq 1) p z β hβ hβone hthreshold

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For any binary augmented gadget with n ≥ 2, any answer z, and any threshold β, its signed approximation G_z = 2 · (prob_z)^(>β) satisfies

‖G_z‖_(2,μₛ ⊗ μₜ ⊗ μᵥ) ≤ 12

for every three labels s,t,v. The output encoding is long; no equation v = s · t+c is required.
-/
theorem augmentedApproximation_arbitrary_labels (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (c s t v : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) Z)
    (z : Z) (β : ℝ) :
    rms (independentLabelledPortDistribution hn (by nlinarith) s t v)
      (fun xy => augmentedApproximation c p z β xy.1 xy.2) ≤ 12 :=
  independentLabelledPortDistribution_doubled_rms_le_twelve hq hn (by nlinarith) s t v
    (augmentedProbability c p z) β (AnswerApproximation.answerProb_le_one _ _ p z)


/-
Mathematical statement (normal notation): For the binary augmented tensor gadget computing s · t+c, fix any answer z. If n ≥ 2, 0<β ≤ 1, and (2ⁿ-1)² · β³ ≥ 1, its chosen doubled strict-truncation approximation G_z satisfies

‖prob_z-G_z‖_(2, μₛ ⊗ μₜ ⊗ μ_(s · t+c)) ≤ 396 · β^(1/3).

The output encoding in this statement has long dimension n²+1.
-/
theorem augmentedApproximation_valid_error (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (c s t : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) Z)
    (z : Z) (β : ℝ) (hβ : 0 < β) (hβone : β ≤ 1)
    (hthreshold : 1 ≤ (Fintype.card (U F n × U F n) : ℝ) * β ^ 3) :
    rms (independentLabelledPortDistribution hn (by nlinarith) s t (s*t+c))
      (fun xy => augmentedProbability c p z xy.1 xy.2 -
        augmentedApproximation c p z β xy.1 xy.2) ≤ 396 * β ^ (1 / 3 : ℝ) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  letI : Nonempty (U F (n*n+1)) := ⟨unitShare ⟨0, by omega⟩⟩
  let A := augmentedProbability c p z
  let valid := refreshConsistent (Rectangular.augmentedShare (n := n) c)
    (Rectangular.augmentedShare (n := n) 1)
  have h := AnswerApproximation.feature_answer_strict_error hq (show 2 ≤ n*n+1 by nlinarith)
    (Rectangular.augmentedShare c) (Rectangular.augmentedShare 1)
    (Rectangular.augmentedShare_injective_binary hq c)
    (Rectangular.augmentedShare_injective_binary hq 1) p z β hβ hβone hthreshold
  change rms (independentLabelledPortDistribution hn (by nlinarith) s t (s*t+c))
    (fun xy => A xy.1 xy.2 - 2 * strictTruncation A β xy.1 xy.2) ≤ _
  rw [validLabelled_projection_error_rms hn c s t A (strictTruncation A β)]
  have hroot : Real.sqrt 27 ≤ 6 := by apply Real.sqrt_le_iff.mpr; norm_num
  have hr : 0 ≤ β ^ (1 / 3 : ℝ) := Real.rpow_nonneg hβ.le _
  calc
    _ ≤ Real.sqrt 27 * tableL2Norm (AnswerApproximation.approximationResidual valid A β) :=
      independentLabelledPortDistribution_rms_le hq hn (by nlinarith) s t (s*t+c) _
    _ ≤ Real.sqrt 27 * (66 * β ^ (1 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
    _ ≤ _ := (mul_le_mul_of_nonneg_right hroot (by positivity)).trans_eq (by ring)

/-- On the valid typed output fiber, the probability table agrees with the actual conditional matrix-phase answer distribution, before any shortening. -/
-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): For valid labels (s,t,s · t+c), the L₂ error of an arbitrary approximation G is unchanged when replacing the conditional answer probability by its supported table prob_z, and regrouping the sampled old encodings and long output into left/right port tuples. Both descriptions average over the same independent encodings. -/
theorem augmentedAnswerProb_error_rms_eq (hn : 2 ≤ n) (c s t : F)
    [Nonempty (Fiber F (n*n+1) (s*t+c))]
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) Z)
    (z : Z) (G : Matrix (GateSide F n (n*n+1)) (GateSide F n (n*n+1)) ℝ) :
    rms ((oldLabelDistribution hn s t).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n*n+1) (s*t+c))))
      (fun ou => (answerDistribution (Rectangular.augmentedShare c)
        (Rectangular.augmentedShare 1) p ou.1.1 ou.1.2 ou.2.val).weight z -
        G (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)) =
    rms (independentLabelledPortDistribution hn (by nlinarith) s t (s*t+c))
      (fun xy => augmentedProbability c p z xy.1 xy.2 - G xy.1 xy.2) := by
  unfold rms
  congr 1
  rw [← independentLabelledPortDistribution_fiber_expect hn (by nlinarith) s t (s*t+c)
    (fun x y => (augmentedProbability c p z x y - G x y) ^ 2)]
  unfold FiniteDistribution.expect
  apply Finset.sum_congr rfl
  intro ou _
  by_cases ho : (oldLabelDistribution hn s t).weight ou.1 = 0
  · simp [FiniteDistribution.prod, FiniteDistribution.joint, ho]
  · dsimp only
    rw [augmented_answer_prob_on_support hn c s t p ou.1 ho ou.2 z]
    rfl

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c, s, t ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n + 1)(F), Z); z ∈ Z; β ∈ ℝ, assume |F| = 2; 2 ≤ n; Fiber(F, (n · n + 1), (s · t + c)) ≠ ∅; 0 < β; β ≤ 1; 1 ≤ |(U(F, n) × U(F, n))| · β³. Then

‖ ((ou ↦ answerDistribution(Rectangular.augmentedShare(c), Rectangular.augmentedShare(1), p, ((ou)₁)₁, ((ou)₁)₂, (ou)₂)(z) - augmentedApproximation(c, p, z, β, (((ou)₁)₁, ou.2.val.L), (((ou)₁)₂, ou.2.val.R))))‖_(2,(oldLabelDistribution(s, t) ⊗ 𝒰_(Fiber(F, (n · n + 1), (s · t + c))))) ≤ 396 · β^(1 / 3).
-/
theorem augmentedAnswerProb_valid_error (hq : fieldCard F = 2) (hn : 2 ≤ n) (c s t : F)
    [Nonempty (Fiber F (n*n+1) (s*t+c))]
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) Z)
    (z : Z) (β : ℝ) (hβ : 0 < β) (hβone : β ≤ 1)
    (hthreshold : 1 ≤ (Fintype.card (U F n × U F n) : ℝ) * β ^ 3) :
    rms ((oldLabelDistribution hn s t).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n*n+1) (s*t+c))))
      (fun ou => (answerDistribution (Rectangular.augmentedShare c)
        (Rectangular.augmentedShare 1) p ou.1.1 ou.1.2 ou.2.val).weight z -
        augmentedApproximation c p z β (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)) ≤
      396 * β ^ (1 / 3 : ℝ) := by
  rw [augmentedAnswerProb_error_rms_eq]
  exact augmentedApproximation_valid_error hq hn c s t p z β hβ hβone hthreshold

end

end CircuitCompiler.GadgetApproximation
