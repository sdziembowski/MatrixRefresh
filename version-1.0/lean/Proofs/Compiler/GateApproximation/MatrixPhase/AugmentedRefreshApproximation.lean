import Proofs.Compiler.GateApproximation.MatrixPhase.AugmentedRefreshRate
import Proofs.Compiler.GateApproximation.MatrixPhase.EncodingMapApproximation



/-!
# Common local approximation of the actual augmented matrix phase

For each public offset `c`, the conditional leakage probabilities refer to refreshing the augmented product encoding in dimension `n*n+1`. The same family of real tables works for all operand labels. Its total reference error is at most `208 K 2^(-n/4)`; no operator or approximation premise remains.
-/
set_option autoImplicit false

set_option maxHeartbeats 1500000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {F Z : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype Z] {n : ℕ}

/-- The generic reference density is precisely the augmented plaintext-product fiber density; `c=0` gives multiplication and `c=1` gives binary NAND. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c ∈ F; x, y ∈ GateSide(F, n, (n · n + 1)), we have

refreshDensity(Rectangular.augmentedShare(c), Rectangular.augmentedShare(1), x, y) = encodingDensity(((((x)₁)₁ · ((y)₁)₁) · (((x)₁)₂ · ((y)₁)₂) + c), (x)₂, (y)₂) .
-/
theorem augmented_refreshDensity (c : F) (x y : GateSide F n (n*n+1)) :
    refreshDensity (Rectangular.augmentedShare c) (Rectangular.augmentedShare 1) x y =
      encodingDensity (dot x.1.1.val y.1.1.val * dot x.1.2.val y.1.2.val + c) x.2 y.2 := by
  simp only [refreshDensity, Rectangular.augmentedShare_dot]

/-- The canonical conditional distribution describes the actual shared-matrix execution on the augmented inputs, including its joint output/leakage distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): Fix two operand encodings and an offset c, with n ≥ 2. The joint distribution of the augmented refresh output and its leakage answer can be generated in either order: sample a uniform invertible matrix and then its answer, or first sample a fresh long encoding of s₁ · s₂+c and then the conditional answer given that output. The two joint distributions are exactly equal. -/
theorem augmented_execution_eq_canonical (hn : 2 ≤ n) (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) Z)
    (x y : U F n × U F n) :
    ((FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n*n+1))).joint (fixedMatrixAnswerDistribution p x y)).map
      (fun pair => (refreshedEncoding (Rectangular.augmentedShare c)
        (Rectangular.augmentedShare 1) x y pair.1, pair.2)) =
    (mu F (n*n+1) (by nlinarith) (dot x.1.val y.1.val * dot x.2.val y.2.val + c)).joint
      (answerDistribution (Rectangular.augmentedShare c) (Rectangular.augmentedShare 1) p x y) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  simpa only [Rectangular.augmentedShare_dot] using feature_execution_eq_canonical
    (show 2 ≤ n*n+1 by nlinarith) (Rectangular.augmentedShare c)
    (Rectangular.augmentedShare 1) p x y

/-- The augmented tensor's common per-answer approximation has the current exponential matrix-phase rate. All operator and counting inputs are proved. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n + 1)(F), Z), assume |F| = 2; 2 ≤ n. Then

∃ G ∈ Z → ℝ^(GateSide(F, n, (n · n + 1)) × GateSide(F, n, (n · n + 1))), (∀ z, ‖ G(z)‖_* ≤ 1) ∧ (∑_z (‖ G(z)‖_*)) ≤ |Z| ∧ (∑_z (𝔼_(xy ∈ GateSide(F, n, (n · n + 1)) × GateSide(F, n, (n · n + 1))) [refreshDensity(Rectangular.augmentedShare(c), Rectangular.augmentedShare(1), (xy)₁, (xy)₂) · |answerProb(Rectangular.augmentedShare(c), Rectangular.augmentedShare(1), p, z, (xy)₁, (xy)₂) - G(z, (xy)₁, (xy)₂)|])) ≤ 208 · |Z| · exp((-(log(2)) · n / 4)).
-/
theorem augmented_local_approximation (hq : fieldCard F = 2) (hn : 2 ≤ n) (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) Z) :
    ∃ G : Z → Matrix (GateSide F n (n*n+1)) (GateSide F n (n*n+1)) ℝ,
      (∀ z, tableNuclearNorm (G z) ≤ 1) ∧
      (∑ z, tableNuclearNorm (G z)) ≤ Fintype.card Z ∧
      (∑ z, uavg (fun xy : GateSide F n (n*n+1) × GateSide F n (n*n+1) =>
        refreshDensity (Rectangular.augmentedShare c) (Rectangular.augmentedShare 1)
          xy.1 xy.2 *
          |answerProb (Rectangular.augmentedShare c) (Rectangular.augmentedShare 1)
            p z xy.1 xy.2 - G z xy.1 xy.2|)) ≤
          208 * Fintype.card Z * Real.exp (-Real.log 2 * (n : ℝ) / 4) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  obtain ⟨G, hG, hsum, herr⟩ := feature_local_approximation hq
    (show 2 ≤ n*n+1 by nlinarith) (Rectangular.augmentedShare c)
    (Rectangular.augmentedShare 1) (Rectangular.augmentedShare_injective_binary hq c)
    (Rectangular.augmentedShare_injective_binary hq 1) p
  refine ⟨G, hG, hsum, herr.trans ?_⟩
  have h := mul_le_mul_of_nonneg_left (binary_augmented_local_rate hq hn)
    (Nat.cast_nonneg (Fintype.card Z) : (0 : ℝ) ≤ _)
  simpa only [augmentedOperatorError, tensorShareCount_card, mul_assoc, mul_comm,
    mul_left_comm] using h

end

end CircuitCompiler.RefreshAnalysis
