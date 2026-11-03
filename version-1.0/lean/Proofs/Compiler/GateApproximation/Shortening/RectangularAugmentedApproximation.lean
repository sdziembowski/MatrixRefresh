import Proofs.Compiler.GateApproximation.MatrixPhase.AugmentedRefreshLabelled
import Proofs.Compiler.GateApproximation.MatrixPhase.GateDimensions
import Proofs.Compiler.GateApproximation.Shortening.RectangularAnswerProbabilities



/-!
# Common local tables for the augmented rectangular gate

The operator theorem for dimension `n*n+1` and the physical shortening transport are combined here. One family works simultaneously for all operand labels, with no analytic or local-approximation hypothesis.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical

namespace CircuitCompiler.Rectangular

open Refresh MatrixRefresh TableAnalysis Shortening RefreshAnalysis

noncomputable section

variable {F A B : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype A] [Fintype B] {n t : ℕ}

/-- The actual augmented matrix answer, with its long dimension written as `n+t` for the shortening interface. This is only a change of carrier. -/
/-
Mathematical definition (normal notation): For c ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n + 1)(F), A); o ∈ (U(F, n) × U(F, n)) × (U(F, n) × U(F, n)); u ∈ State(F, (n + t)), assume n · n + 1 = n + t. define

augmentedLongAnswerDistribution(c, p, o, u) := answerDistribution(augmentedShare(c), augmentedShare(1), p, (o)₁, (o)₂, (stateDimensionEquiv)⁻¹(u)).
-/
def augmentedLongAnswerDistribution (hdim : n*n+1 = n+t) (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A)
    (o : (U F n × U F n) × (U F n × U F n)) (u : State F (n+t)) : FiniteDistribution A :=
  answerDistribution (augmentedShare c) (augmentedShare 1) p o.1 o.2
    ((stateDimensionEquiv hdim).symm u)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c, s₁, s₂ ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n + 1)(F), A); o ∈ (U(F, n) × U(F, n)) × (U(F, n) × U(F, n)); u ∈ Fiber(F, (n + t), (s₁ · s₂ + c)); a ∈ A, assume 2 ≤ n; n · n + 1 = n + t; oldLabelDistribution(s₁, s₂)(o) ≠ 0. Then

augmentedLongAnswerDistribution(c, p, o, u)(a) = reindexGateTable(answerProb(augmentedShare(c), augmentedShare(1), p, a), ((o)₁, u.val.L), ((o)₂, u.val.R)).
-/
theorem augmentedLongAnswerDistribution_on_support (hn : 2 ≤ n) (hdim : n*n+1 = n+t) (c s₁ s₂ : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A)
    (o : (U F n × U F n) × (U F n × U F n))
    (ho : (oldLabelDistribution hn s₁ s₂).weight o ≠ 0)
    (u : Fiber F (n+t) (s₁*s₂+c)) (a : A) :
    (augmentedLongAnswerDistribution hdim c p o u.val).weight a =
      reindexGateTable hdim (answerProb (augmentedShare c) (augmentedShare 1) p a)
        (o.1,u.val.L) (o.2,u.val.R) := by
  have h := augmented_answer_prob_on_support hn c s₁ s₂ p o ho
    ((fiberDimensionEquiv hdim (s₁*s₂+c)).symm u) a
  simpa only [augmentedLongAnswerDistribution, fiberDimensionEquiv_symm_val,
    stateDimensionEquiv_symm_left, stateDimensionEquiv_symm_right,
    reindexGateTable, reindexTable, sideDimensionEquiv, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map, Equiv.refl_symm, Equiv.refl_apply] using h

/-- Reindexing preserves the labelled summed error exactly. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c, s₁, s₂ ∈ F; k, G ∈ A → ℝ^(GateSide(F, n, (n · n + 1)) × GateSide(F, n, (n · n + 1))), assume 2 ≤ n; n · n + 1 = n + t; Fiber(F, (n · n + 1), (s₁ · s₂ + c)) ≠ ∅; Fiber(F, (n + t), (s₁ · s₂ + c)) ≠ ∅. Then

𝔼_(op ← (oldLabelDistribution(s₁, s₂) ⊗ 𝒰_(Fiber(F, (n + t), (s₁ · s₂ + c))))) [∑ₐ (|reindexGateTable(k(a), (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R)) - reindexGateTable(G(a), (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R))|)] = 𝔼_(op ← (oldLabelDistribution(s₁, s₂) ⊗ 𝒰_(Fiber(F, (n · n + 1), (s₁ · s₂ + c))))) [∑ₐ (|k(a, (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R)) - G(a, (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R))|)].
-/
theorem augmented_table_error_reindex (hn : 2 ≤ n) (hdim : n*n+1 = n+t) (c s₁ s₂ : F)
    [Nonempty (Fiber F (n*n+1) (s₁*s₂+c))] [Nonempty (Fiber F (n+t) (s₁*s₂+c))]
    (k G : A → Matrix (GateSide F n (n*n+1)) (GateSide F n (n*n+1)) ℝ) :
    ((oldLabelDistribution hn s₁ s₂).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) (s₁*s₂+c)))).expect
      (fun op => ∑ a, |reindexGateTable hdim (k a) (op.1.1,op.2.val.L) (op.1.2,op.2.val.R) -
        reindexGateTable hdim (G a) (op.1.1,op.2.val.L) (op.1.2,op.2.val.R)|) =
    ((oldLabelDistribution hn s₁ s₂).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n*n+1) (s₁*s₂+c)))).expect
      (fun op => ∑ a, |k a (op.1.1,op.2.val.L) (op.1.2,op.2.val.R) -
        G a (op.1.1,op.2.val.L) (op.1.2,op.2.val.R)|) := by
  rw [fiberDimension_expect hdim]
  apply congrArg (FiniteDistribution.expect _)
  funext op
  simp only [fiberDimensionEquiv_val, stateDimensionEquiv_left, stateDimensionEquiv_right,
    reindexGateTable, reindexTable, sideDimensionEquiv, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Equiv.refl_symm, Prod.map_apply, Equiv.refl_apply, Equiv.symm_apply_apply]

variable [Nonempty (U F n)] [Nonempty (U F (n+t))] [Nonempty (FullRank F n (n+t))]

/-- The accepted physical gadget has one common family with the sharp rectangular nuclear budget and the `2^(-n/4)` mean-error rate. Retry effects are handled separately by the actual-to-accepted execution coupling. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Over the binary field, assume n ≥ 2 and n²+1 = n+t. For an augmented matrix gadget followed by rectangular shortening, there is one family of signed short-port tables G_(a,b), shared by all input secrets, with

∑_(a ∈ A,b ∈ B) ‖G_(a,b)‖_* ≤ |A| · √(|B|).

For each input-label pair (s₁,s₂), under independent input encodings and a short output encoding of s₁ · s₂+c,

𝔼[∑_(a,b) |prob_(a,b)-G_(a,b)|] ≤ 3328 · |A| · 2^(−n/4).

The shortening answer is conditional on acceptance. The shortening masks are Boolean rectangles.
-/
theorem augmented_shortened_local_approximation (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (hdim : n*n+1 = n+t) (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A)
    (r : A → (H : FullRank F n (n+t)) → RectanglePartition B
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

end CircuitCompiler.Rectangular
