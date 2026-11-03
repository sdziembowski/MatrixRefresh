import Proofs.Compiler.LocalComparisons.GateInterface
import Proofs.Compiler.GateApproximation.Interfaces.DirectApproximation
import Proofs.Compiler.GateApproximation.Interfaces.Gadget.Labelled



/-!
# The refreshing/copy-gate local interface

The input and output encodings are separate ports. One explicit approximation works for every pair of labels, including unequal labels. The valid-label error is proved for the actual conditional refreshing answer probability.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical

namespace CircuitCompiler.RefreshApproximation

open Refresh MatrixRefresh TableAnalysis RefreshAnalysis SingularTruncation

open AveragedEnergyComparison GadgetApproximation

noncomputable section

variable {F Z : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype Z] {n : ℕ}

/-- Group the old and new shares by party. -/
/-
Mathematical definition (normal notation): Regroup a pair of encoding states by party:

((ℓ,r),(ℓ',r'))↔((ℓ,ℓ'),(r,r')).

This is only a change of coordinates.
-/
def copyRegroup : (State F n × State F n) ≃ ((U F n × U F n) × (U F n × U F n)) where
  toFun xy := ((xy.1.L,xy.2.L),(xy.1.R,xy.2.R))
  invFun xy := (⟨xy.1.1,xy.2.1⟩,⟨xy.1.2,xy.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

/- Mathematical definition (normal notation): Sample (L,R) ← μₛ and (L',R') ← μₜ independently, and return ((L,L'),(R,R')). This is the distribution μₛ ⊗ μₜ written in table coordinates. -/
def copyLabelDistribution (hn : 2 ≤ n) (s t : F) :
    FiniteDistribution ((U F n × U F n) × (U F n × U F n)) :=
  ((mu F n hn s).prod (mu F n hn t)).map copyRegroup

-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s, t ∈ F; xy ∈ (U(F, n) × U(F, n)) × (U(F, n) × U(F, n)), assume |F| = 2; 2 ≤ n; U(F, n) ≠ ∅. Then

copyLabelDistribution(s, t)(xy) ≤ 9 · 𝒰_((U(F, n) × U(F, n)) × (U(F, n) × U(F, n)))(xy).
-/
theorem copyLabelDistribution_weight_le (hq : fieldCard F = 2) (hn : 2 ≤ n) (s t : F)
    [Nonempty (U F n)] (xy : (U F n × U F n) × (U F n × U F n)) :
    (copyLabelDistribution hn s t).weight xy ≤
      9 * (FiniteDistribution.uniform : FiniteDistribution ((U F n × U F n) × (U F n × U F n))).weight xy := by
  rw [copyLabelDistribution, FiniteDistribution.map_equiv_weight]
  change (mu F n hn s).weight ⟨xy.1.1,xy.2.1⟩ *
    (mu F n hn t).weight ⟨xy.1.2,xy.2.2⟩ ≤ _
  have h := mul_le_mul (mu_weight_le_three hq hn s ⟨xy.1.1,xy.2.1⟩)
    (mu_weight_le_three hq hn t ⟨xy.1.2,xy.2.2⟩)
    ((mu F n hn t).nonneg _) (mul_nonneg (by norm_num) ((independentStateDistribution F n hn).nonneg _))
  refine h.trans_eq ?_
  simp only [independentStateDistribution_weight, FiniteDistribution.uniform, Fintype.card_prod,
    Nat.cast_mul, nonzero_vector_card, mul_inv_rev, div_eq_mul_inv, shareCard, vectorCard]
  ring


/-
Mathematical statement (normal notation): For binary shares with n ≥ 2, any secrets s,t, and every real endpoint table G,

‖G‖_(2,μₛ ⊗ μₜ) ≤ 3 · ‖G‖₂.

The norm on the right uses independent uniform nonzero shares for all four coordinates.
-/
theorem copyLabelDistribution_rms_le (hq : fieldCard F = 2) (hn : 2 ≤ n) (s t : F)
    (G : Matrix (U F n × U F n) (U F n × U F n) ℝ) :
    rms (copyLabelDistribution hn s t) (fun xy => G xy.1 xy.2) ≤ 3 * tableL2Norm G := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  have h : (copyLabelDistribution hn s t).expect (fun xy => G xy.1 xy.2 ^ 2) ≤
      9 * uavg (fun xy : (U F n × U F n) × (U F n × U F n) => G xy.1 xy.2 ^ 2) := by
    rw [uavg_eq_expect_uniform]
    unfold FiniteDistribution.expect
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro xy _
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (copyLabelDistribution_weight_le hq hn s t xy) (sq_nonneg _)
  have hsq : uavg (fun xy : (U F n × U F n) × (U F n × U F n) =>
      G xy.1 xy.2 ^ 2) = tableL2Norm G ^ 2 := (tableL2Norm_sq G).symm
  rw [hsq] at h
  have hr := Real.sqrt_le_sqrt h
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9),
    Real.sqrt_sq (tableL2Norm_nonneg G)] at hr
  norm_num at hr
  exact hr

-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F; xy ∈ (U(F, n) × U(F, n)) × (U(F, n) × U(F, n)), assume 2 ≤ n; copyLabelDistribution(s, s)(xy) ≠ 0. Then

refreshConsistent(id, id, (xy)₁, (xy)₂).
-/
theorem copyLabelDistribution_valid (hn : 2 ≤ n) (s : F)
    (xy : (U F n × U F n) × (U F n × U F n))
    (hxy : (copyLabelDistribution hn s s).weight xy ≠ 0) :
    refreshConsistent (id : U F n → U F n) id xy.1 xy.2 := by
  rw [copyLabelDistribution, FiniteDistribution.map_equiv_weight] at hxy
  change (mu F n hn s).weight ⟨xy.1.1,xy.2.1⟩ *
    (mu F n hn s).weight ⟨xy.1.2,xy.2.2⟩ ≠ 0 at hxy
  have ha := mu_supports n hn s ⟨xy.1.1,xy.2.1⟩ (mul_ne_zero_iff.mp hxy).1
  have hb := mu_supports n hn s ⟨xy.1.2,xy.2.2⟩ (mul_ne_zero_iff.mp hxy).2
  exact hb.trans ha.symm

variable [Nonempty (U F n)]

/- Mathematical definition (normal notation): For a fixed leakage answer z and endpoint tuple ω = ((ℓ,ℓ'),(r,r')), let prob_z(ω) be the conditional probability of answer z for a refresh with those endpoints, using the fixed leakage partition. On impossible endpoint tuples, this auxiliary totalized conditional distribution samples the matrix unconditionally and returns its answer probability; the zero-extended answer table used for truncation is defined separately. -/
def copyProbability (p : TableRectanglePartition (U F n) (Refresh.«GL» F n) Z)
    (z : Z) (x y : U F n × U F n) : ℝ :=
  (answerDistribution id id p x.1 y.1 ⟨x.2,y.2⟩).weight z

/-
Mathematical definition (normal notation): Let prob_z^(>β) retain the singular coefficients of the answer table strictly larger than β. Define the signed approximation

G_z := 2 · prob_z^(>β).

This definition is on all endpoint tuples, including inconsistent ones.
-/
def copyApproximation (p : TableRectanglePartition (U F n) (Refresh.«GL» F n) Z)
    (z : Z) (β : ℝ) : Matrix (U F n × U F n) (U F n × U F n) ℝ :=
  strictDoubled (answerProb id id p z) β

/- Mathematical definition (normal notation): Choose the balanced singular factors of G_z = 2 · prob_z^(>β): for each retained coefficient σⱼ, set aⱼ := √2σⱼ · uⱼ and bⱼ := √2σⱼ · vⱼ. Then G_z = ∑ⱼ aⱼ · bⱼᵀ. -/
def copyFactors (p : TableRectanglePartition (U F n) (Refresh.«GL» F n) Z)
    (z : Z) (β : ℝ) : Factors (copyApproximation p z β) :=
  strictDoubledFactors (answerProb id id p z) β


/-
Mathematical statement (normal notation): For binary shares with n ≥ 2, a fixed answer z, and 0<β ≤ 1 satisfying qβ³ ≥ 1 where q = 2ⁿ-1, the approximation G_z = 2prob_z^(>β) satisfies

‖prob_z-G_z‖_(2,μₛ ⊗ μₛ) ≤ 396 · β^(1/3) for every secret s.
-/
theorem copyApproximation_valid_error (hq : fieldCard F = 2) (hn : 2 ≤ n) (s : F)
    (p : TableRectanglePartition (U F n) (Refresh.«GL» F n) Z)
    (z : Z) (β : ℝ) (hβ : 0 < β) (hβone : β ≤ 1)
    (hthreshold : 1 ≤ (Fintype.card (U F n) : ℝ) * β ^ 3) :
    rms (copyLabelDistribution hn s s)
      (fun xy => copyProbability p z xy.1 xy.2 - copyApproximation p z β xy.1 xy.2) ≤
      396 * β ^ (1/3 : ℝ) := by
  let A := answerProb (id : U F n → U F n) id p z
  let valid := refreshConsistent (id : U F n → U F n) id
  have he : rms (copyLabelDistribution hn s s)
      (fun xy => copyProbability p z xy.1 xy.2 - copyApproximation p z β xy.1 xy.2) =
      rms (copyLabelDistribution hn s s)
        (fun xy => AnswerApproximation.approximationResidual valid A β xy.1 xy.2) := by
    unfold rms
    congr 1
    unfold FiniteDistribution.expect
    apply Finset.sum_congr rfl
    intro xy _
    by_cases hxy : (copyLabelDistribution hn s s).weight xy = 0
    · simp [hxy]
    · have hv := copyLabelDistribution_valid hn s xy hxy
      simp only [copyProbability, copyApproximation, strictDoubled, AnswerApproximation.approximationResidual,
        Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, project, valid, if_pos hv]
      dsimp only [A, answerProb]
      unfold refreshConsistent at hv
      rw [if_pos hv]
  rw [he]
  have ha := AnswerApproximation.feature_answer_strict_error hq hn
    (id : U F n → U F n) id Function.injective_id Function.injective_id p z β hβ hβone hthreshold
  have hr : 0 ≤ β ^ (1/3 : ℝ) := Real.rpow_nonneg hβ.le _
  have h := (copyLabelDistribution_rms_le hq hn s s (AnswerApproximation.approximationResidual valid A β)).trans
    (mul_le_mul_of_nonneg_left ha (by norm_num : (0:ℝ) ≤ 3))
  linarith

/-- Copy/refresh is a concrete instance of precisely the same compiler local interface, with no rectangular reduction and no retry loss. -/

/- Mathematical definition (normal notation): For binary shares with n ≥ 2, 0<β ≤ 1, and qβ³ ≥ 1, construct the local approximation G_z = 2prob_z^(>β) with chosen product factors. Their pointwise energies are at most 2/β, their uniform mean energies are at most 8, the all-label L₂ bound is 12, and the valid-label approximation error is at most 396β^(1/3). Valid labels are exactly s = t. The mean-energy constant is 8 here, rather than the paper's 4. -/
def copyGateLocalEstimates (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (p : TableRectanglePartition (U F n) (Refresh.«GL» F n) Z)
    (z : Z) (β : ℝ) (hβ : 0 < β) (hβone : β ≤ 1)
    (hthreshold : 1 ≤ (Fintype.card (U F n) : ℝ) * β ^ 3) :
    GateLocalEstimates (fun labels : F × F => copyLabelDistribution hn labels.1 labels.2)
      (fun labels => labels.1 = labels.2) (fun _ => copyProbability p z)
      β (396 * β ^ (1/3 : ℝ)) where
  approximation := copyApproximation p z β
  factors := copyFactors p z β
  left_max := strictDoubledFactors_left_le _ β hβ (AnswerApproximation.answerProb_le_one _ _ p z)
  right_max := strictDoubledFactors_right_le _ β hβ (AnswerApproximation.answerProb_le_one _ _ p z)
  left_mean := by
    rw [← uavg_eq_expect_uniform]
    exact (feature_answer_factors_mean_le_eight hq hn (id : U F n → U F n) id
      Function.injective_id Function.injective_id p z β hβ hβone hthreshold).1
  right_mean := by
    rw [← uavg_eq_expect_uniform]
    exact (feature_answer_factors_mean_le_eight hq hn (id : U F n → U F n) id
      Function.injective_id Function.injective_id p z β hβ hβone hthreshold).2
  all_labels_rms labels := by
    have h := (copyLabelDistribution_rms_le hq hn labels.1 labels.2 (copyApproximation p z β)).trans
      (mul_le_mul_of_nonneg_left (strictDoubled_l2_le_two _ β
        (AnswerApproximation.answerProb_le_one _ _ p z)) (by norm_num : (0:ℝ) ≤ 3))
    norm_num at h ⊢
    linarith
  valid_error_rms labels hv := by
    rcases labels with ⟨s,t⟩
    dsimp only at hv ⊢
    subst t
    exact copyApproximation_valid_error hq hn s p z β hβ hβone hthreshold

end

end CircuitCompiler.RefreshApproximation
