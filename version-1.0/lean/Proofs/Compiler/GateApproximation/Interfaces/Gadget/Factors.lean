import Proofs.Compiler.LocalComparisons.FactorEnergies
import Proofs.Compiler.GateApproximation.Interfaces.NuclearBound



/-!
# Explicit factors of twice the strict answer-table truncation

These are the actual square-root-weighted singular factors, including zero coordinates for discarded directions. Their mean energies equal twice the nuclear norm, so the direct answer-table bound gives an absolute budget.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.GadgetApproximation

open Refresh MatrixRefresh TableAnalysis RefreshAnalysis SingularTruncation

open TruncatedAnswerNorm AveragedEnergyComparison

noncomputable section

variable {n : ℕ}

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ, we have

𝔼ᵢ [(‖ strictFiniteLeft(A, β, i)‖)²] = ‖ strictFinitePart(A, β)‖_*.
-/
theorem strictFiniteLeft_mean_energy (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) :
    uavg (fun i => ‖strictFiniteLeft A β i‖ ^ 2) = tableNuclearNorm (strictFinitePart A β) := by
  simp_rw [strictFiniteLeft_norm_sq]
  rw [uavg_sum, strictFinitePart_nuclear_eq]
  simp only [uavg, Fintype.card_fin]
  have hs (k : Fin n) : ∑ i, (matrixSVD A).left k i ^ 2 = 1 := by
    simpa only [pow_two, ite_true] using
      orthonormalBasis_coordinate_inner (matrixSVD A).left k k
  simp_rw [← Finset.mul_sum, hs, mul_one]
  ring

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^({0,…,n−1} × {0,…,n−1}); β ∈ ℝ, we have

𝔼ᵢ [(‖ strictFiniteRight(A, β, i)‖)²] = ‖ strictFinitePart(A, β)‖_*.
-/
theorem strictFiniteRight_mean_energy (A : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) :
    uavg (fun i => ‖strictFiniteRight A β i‖ ^ 2) = tableNuclearNorm (strictFinitePart A β) := by
  simp_rw [strictFiniteRight_norm_sq]
  rw [uavg_sum, strictFinitePart_nuclear_eq]
  simp only [uavg, Fintype.card_fin]
  have hs (k : Fin n) : ∑ i, (matrixSVD A).right k i ^ 2 = 1 := by
    simpa only [pow_two, ite_true] using
      orthonormalBasis_coordinate_inner (matrixSVD A).right k k
  simp_rw [← Finset.mul_sum, hs, mul_one]
  ring

variable {I : Type*} [Fintype I] [DecidableEq I]

/-
Mathematical definition (normal notation): Define the doubled strict-truncation approximation by

G := 2 · A^(>β).

The table may have negative entries and is not required to be a probability distribution.
-/
def strictDoubled (A : Matrix I I ℝ) (β : ℝ) : Matrix I I ℝ :=
  fun x y => 2 * strictTruncation A β x y

/- Mathematical definition (normal notation): If A^(>β) = ∑ₖ σₖ · uₖ · vₖᵀ, choose factors √2σₖ · uₖ and √2σₖ · vₖ. Their products give a concrete representation of 2 · A^(>β), including zero coordinates for discarded directions. -/
def strictDoubledFactors (A : Matrix I I ℝ) (β : ℝ) : Factors (strictDoubled A β) where
  rank := Fintype.card I
  left x j := Real.sqrt 2 * truncationLeftFactor A β x j
  right y j := Real.sqrt 2 * truncationRightFactor A β y j
  reconstruct x y := by
    simp only [strictDoubled, strictTruncation_factorization, PiLp.inner_apply,
      RCLike.inner_apply, starRingEnd_apply, star_trivial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    calc
      _ = (Real.sqrt 2 * Real.sqrt 2) *
          (truncationLeftFactor A β x j * truncationRightFactor A β y j) := by rw [hs]; ring
      _ = _ := by ring

omit [DecidableEq I] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; x ∈ I, we have

leftEnergy(strictDoubledFactors(A, β))(x) = 2 · (‖ truncationLeftFactor(A, β, x)‖)².
-/
theorem strictDoubledFactors_leftEnergy (A : Matrix I I ℝ) (β : ℝ) (x : I) :
    (strictDoubledFactors A β).leftEnergy x = 2 * ‖truncationLeftFactor A β x‖ ^ 2 := by
  simp only [Factors.leftEnergy, strictDoubledFactors, EuclideanSpace.norm_sq_eq,
    Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Finset.mul_sum]

omit [DecidableEq I] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; y ∈ I, we have

rightEnergy(strictDoubledFactors(A, β))(y) = 2 · (‖ truncationRightFactor(A, β, y)‖)².
-/
theorem strictDoubledFactors_rightEnergy (A : Matrix I I ℝ) (β : ℝ) (y : I) :
    (strictDoubledFactors A β).rightEnergy y = 2 * ‖truncationRightFactor A β y‖ ^ 2 := by
  simp only [Factors.rightEnergy, strictDoubledFactors, EuclideanSpace.norm_sq_eq,
    Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Finset.mul_sum]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

𝔼ᵤ [leftEnergy(strictDoubledFactors(A, β))(u)] = 2 · ‖ strictTruncation(A, β)‖_*.
-/
theorem strictDoubledFactors_left_mean (A : Matrix I I ℝ) (β : ℝ) :
    uavg (strictDoubledFactors A β).leftEnergy = 2 * tableNuclearNorm (strictTruncation A β) := by
  change uavg (fun x => (strictDoubledFactors A β).leftEnergy x) = _
  simp_rw [strictDoubledFactors_leftEnergy]
  rw [uavg_const_mul]
  congr 1
  unfold truncationLeftFactor strictTruncation
  rw [uavg_equiv (Fintype.equivFin I) (fun i => ‖strictFiniteLeft (svdFiniteTable A) β i‖ ^ 2),
    strictFiniteLeft_mean_energy, reindexTable_tableNuclearNorm]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, we have

𝔼ᵤ [rightEnergy(strictDoubledFactors(A, β))(u)] = 2 · ‖ strictTruncation(A, β)‖_*.
-/
theorem strictDoubledFactors_right_mean (A : Matrix I I ℝ) (β : ℝ) :
    uavg (strictDoubledFactors A β).rightEnergy = 2 * tableNuclearNorm (strictTruncation A β) := by
  change uavg (fun y => (strictDoubledFactors A β).rightEnergy y) = _
  simp_rw [strictDoubledFactors_rightEnergy]
  rw [uavg_const_mul]
  congr 1
  unfold truncationRightFactor strictTruncation
  rw [uavg_equiv (Fintype.equivFin I) (fun i => ‖strictFiniteRight (svdFiniteTable A) β i‖ ^ 2),
    strictFiniteRight_mean_energy, reindexTable_tableNuclearNorm]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; x ∈ I, assume I ≠ ∅; 0 < β; ∀ x, y, |A(x, y)| ≤ 1. Then

leftEnergy(strictDoubledFactors(A, β))(x) ≤ 2 / β.
-/
theorem strictDoubledFactors_left_le [Nonempty I]
    (A : Matrix I I ℝ) (β : ℝ) (hβ : 0 < β) (hA : ∀ x y, |A x y| ≤ 1) (x : I) :
    (strictDoubledFactors A β).leftEnergy x ≤ 2 / β := by
  rw [strictDoubledFactors_leftEnergy]
  have h := truncationLeftFactor_energy A β hβ hA x
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; y ∈ I, assume I ≠ ∅; 0 < β; ∀ x, y, |A(x, y)| ≤ 1. Then

rightEnergy(strictDoubledFactors(A, β))(y) ≤ 2 / β.
-/
theorem strictDoubledFactors_right_le [Nonempty I]
    (A : Matrix I I ℝ) (β : ℝ) (hβ : 0 < β) (hA : ∀ x y, |A x y| ≤ 1) (y : I) :
    (strictDoubledFactors A β).rightEnergy y ≤ 2 / β := by
  rw [strictDoubledFactors_rightEnergy]
  have h := truncationRightFactor_energy A β hβ hA y
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ, assume I ≠ ∅; ∀ x, y, |A(x, y)| ≤ 1. Then

‖ strictDoubled(A, β)‖₂ ≤ 2.
-/
theorem strictDoubled_l2_le_two [Nonempty I]
    (A : Matrix I I ℝ) (β : ℝ) (hA : ∀ x y, |A x y| ≤ 1) :
    tableL2Norm (strictDoubled A β) ≤ 2 := by
  have he : strictDoubled A β = (2 : ℝ) • strictTruncation A β := rfl
  rw [he, tableL2Norm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := (strictTruncation_l2 A β).trans (tableL2Norm_le_one_of_entry_bound A hA)
  linarith

variable {F X Z : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Z] {m : ℕ}

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); p ∈ TableRectanglePartition(X, GLₘ(F), Z); z ∈ Z; β ∈ ℝ, assume |F| = 2; 2 ≤ m; a is injective; b is injective; 0 < β; β ≤ 1; 1 ≤ |X| · β³. Then

𝔼ᵤ [leftEnergy(strictDoubledFactors(answerProb(a, b, p, z), β))(u)] ≤ 8 ∧ 𝔼ᵥ [rightEnergy(strictDoubledFactors(answerProb(a, b, p, z), β))(v)] ≤ 8.
-/
theorem feature_answer_factors_mean_le_eight (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (p : TableRectanglePartition X (Refresh.«GL» F m) Z) (z : Z)
    (β : ℝ) (hβ : 0 < β) (hβone : β ≤ 1)
    (hthreshold : 1 ≤ (Fintype.card X : ℝ) * β ^ 3) :
    uavg (strictDoubledFactors (answerProb a b p z) β).leftEnergy ≤ 8 ∧
      uavg (strictDoubledFactors (answerProb a b p z) β).rightEnergy ≤ 8 := by
  letI : Nonempty (U F m) := ⟨a (Classical.choice inferInstance)⟩
  have h := feature_answer_strict_nuclear_le_four hq hm a b ha hb p z β hβ hβone hthreshold
  rw [strictDoubledFactors_left_mean, strictDoubledFactors_right_mean]
  constructor <;> linarith

end

end CircuitCompiler.GadgetApproximation
