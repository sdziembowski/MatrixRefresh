import Proofs.Compiler.GateApproximation.Shortening.RectangularAugmentedApproximation
import Proofs.Compiler.GateApproximation.Shortening.RectangularFractionalAnswerProbabilities



/-!
# Common augmented-gate tables with fractional private-tape masks
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical

namespace CircuitCompiler.Rectangular.Fractional

open Refresh MatrixRefresh TableAnalysis Shortening RefreshAnalysis

noncomputable section

variable {F A B : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype A] [Fintype B] {n t : ℕ}

variable [Nonempty (U F n)] [Nonempty (U F (n+t))] [Nonempty (FullRank F n (n+t))]

/-- The accepted physical gadget has one common family with the sharp rectangular nuclear budget and the `2^(-n/4)` mean-error rate. Retry effects are handled separately by the actual-to-accepted execution coupling. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Over the binary field, assume n ≥ 2 and n²+1 = n+t. For an augmented matrix gadget followed by rectangular shortening, there is one family of signed short-port tables G_(a,b), shared by all input secrets, with

∑_(a ∈ A,b ∈ B) ‖G_(a,b)‖_* ≤ |A| · √(|B|).

For each input-label pair (s₁,s₂), under independent input encodings and a short output encoding of s₁ · s₂+c,

𝔼[∑_(a,b) |prob_(a,b)-G_(a,b)|] ≤ 3328 · |A| · 2^(−n/4).

The shortening answer is conditional on acceptance. The shortening masks may be fractional.
-/
theorem augmented_shortened_local_approximation (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (hdim : n*n+1 = n+t) (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (GateSide F n n) ((GateSide F n n) × Kernel H)) :
    ∃ G : A × B → Matrix (GateSide F n n) (GateSide F n n) ℝ,
      (∑ ab, tableNuclearNorm (G ab)) ≤ Real.sqrt (Fintype.card B) * Fintype.card A ∧
      ∀ s₁ s₂ : F,
        letI := encoding_fiber_nonempty hn (s₁*s₂+c)
        ((oldLabelDistribution hn s₁ s₂).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (s₁*s₂+c)))).expect
          (fun op => ∑ ab, |(shortenedAnswerDistribution
            (fun o (u : Fiber F (n+t) (s₁*s₂+c)) => augmentedLongAnswerDistribution hdim c p o u.val)
            r op.1 op.2).weight ab - G ab (op.1.1,op.2.val.L) (op.1.2,op.2.val.R)|) ≤
              16*208*Fintype.card A*Real.exp (-Real.log 2 * (n : ℝ) / 4) := by
  obtain ⟨H,_,hH,herr⟩ := augmented_labelled_table_approximation hq hn c p
  let k : A → Matrix (GateSide F n (n*n+1)) (GateSide F n (n*n+1)) ℝ := answerProb (augmentedShare c) (augmentedShare 1) p
  let G := fun ab : A × B => transport (r ab.1) (reindexGateTable hdim (H ab.1)) ab.2
  refine ⟨G,?_,?_⟩
  · dsimp only [G]
    rw [Fintype.sum_prod_type]
    calc
      _ ≤ Real.sqrt (Fintype.card B) * ∑ a, tableNuclearNorm (reindexGateTable hdim (H a)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun a _ => transport_nuclear (O := U F n × U F n) (n := n) (t := t) (r a) (reindexGateTable hdim (H a)))
      _ ≤ _ := by
        simp only [reindexGateTable_nuclear]
        exact mul_le_mul_of_nonneg_left hH (Real.sqrt_nonneg _)
  · intro s₁ s₂
    letI := encoding_fiber_nonempty hn (s₁*s₂+c)
    letI := encoding_fiber_nonempty (show 2 ≤ n+t by omega) (s₁*s₂+c)
    letI := encoding_fiber_nonempty (show 2 ≤ n*n+1 by nlinarith) (s₁*s₂+c)
    have h := physical_accepted_approximation
      (fun o (u : Fiber F (n+t) (s₁*s₂+c)) => augmentedLongAnswerDistribution hdim c p o u.val)
      r (fun a => reindexGateTable hdim (k a)) (fun a => reindexGateTable hdim (H a))
      (oldLabelDistribution hn s₁ s₂)
      (fun o ho a u => augmentedLongAnswerDistribution_on_support hn hdim c s₁ s₂ p o ho u a)
    have h' := h.2
    rw [← expect_sum, augmented_table_error_reindex hn hdim c s₁ s₂ k H] at h'
    have he := h'.trans (herr s₁ s₂)
    simpa only [G,Fintype.sum_prod_type] using he

end

end CircuitCompiler.Rectangular.Fractional
