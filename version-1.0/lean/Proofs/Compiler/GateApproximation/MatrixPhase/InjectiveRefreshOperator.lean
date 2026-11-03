import Proofs.Compiler.GateApproximation.MatrixPhase.Operator
import Proofs.Compiler.GateApproximation.MatrixPhase.ResidualBound
import Proofs.Compiler.GateApproximation.MatrixPhase.RefreshGramEstimates



/-!
# Random-refresh estimates for injective maps to binary nonzero shares

The ambient dimension is independent of the old-data space. In particular, these residual bounds apply to the augmented tensor in dimension `n*n+1`.
-/
set_option autoImplicit false

set_option maxHeartbeats 1600000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {F X : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype X] [DecidableEq X] [Nonempty X] {m : ℕ}

omit [DecidableEq X] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m), assume a is injective. Then

1 ≤ |X| ∧ |X| ≤ |F|ᵐ.
-/
theorem feature_card_geometry (a : X → U F m) (ha : Function.Injective a) :
    1 ≤ (Fintype.card X : ℝ) ∧ (Fintype.card X : ℝ) ≤ (vectorCard F m : ℝ) := by
  have hcard := Fintype.card_le_of_injective a ha
  have hN : Fintype.card (U F m) ≤ vectorCard F m := by
    rw [nonzero_vector_card]
    exact Nat.sub_le _ _
  exact ⟨by exact_mod_cast Fintype.card_pos, by exact_mod_cast hcard.trans hN⟩

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); A ∈ ℝ^((X × U(F, m)) × (X × U(F, m))), assume |F| = 2; 2 ≤ m; a is injective; ∀ i, j, |A(i, j)| ≤ 1. Then

‖ supportedSVDResidual(a, b, A, refreshThreshold(|X|))‖ₒₚ ≤ 3 · refreshThreshold(|X|).
-/
theorem feature_residual_op_at_threshold (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a)
    (A : Matrix (X × U F m) (X × U F m) ℝ) (hA : ∀ i j, |A i j| ≤ 1) :
    largestSingularCoefficient (supportedSVDResidual a b A (refreshThreshold (Fintype.card X))) ≤
      3 * refreshThreshold (Fintype.card X) := by
  have hg := feature_card_geometry a ha
  have hD : 0 < (Fintype.card X : ℝ) := lt_of_lt_of_le zero_lt_one hg.1
  have hβ := refreshThreshold_pos hD
  have h := supportedSVDResidual_op hq a b A _ hβ hA
  have hQ := vectorCard_real_ge_four (F := F) hm
  have hmask := binary_mask_threshold_bound hD (by linarith : 2 ≤ (vectorCard F m : ℝ)) hg.2
  have heq : ((fieldCard F ^ m-1 : ℕ) : ℝ) = (vectorCard F m : ℝ)-1 := by
    exact_mod_cast Nat.cast_sub (Nat.one_le_pow _ _ (fieldCard_pos (F := F)))
  rw [heq] at h
  have hdiv := div_le_div_of_nonneg_right hmask hβ.le
  have hc : (2 * refreshThreshold (Fintype.card X)^2) /
      refreshThreshold (Fintype.card X) = 2 * refreshThreshold (Fintype.card X) := by
    field_simp
  rw [hc] at hdiv
  exact h.trans (by dsimp only [vectorCard] at hdiv ⊢; linarith)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); A ∈ ℝ^((X × U(F, m)) × (X × U(F, m))), assume |F| = 2; 2 ≤ m; a is injective; ∀ i, j, |A(i, j)| ≤ 1. Then

Let β := refreshThreshold(|X|); Let E := supportedSVDResidual(a, b, A, β); fourCycle(E) ≤ 3² · β² · 𝔼ₓ [𝔼_y [(E(x, y))²]].
-/
theorem feature_residual_cycle_at_threshold (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a)
    (A : Matrix (X × U F m) (X × U F m) ℝ) (hA : ∀ i j, |A i j| ≤ 1) :
    let β := refreshThreshold (Fintype.card X)
    let E := supportedSVDResidual a b A β
    fourCycle E ≤ 3^2 * β^2 * uavg (fun x => uavg (fun y => E x y ^ 2)) := by
  dsimp only
  have h := feature_residual_op_at_threshold hq hm a b ha A hA
  have hs := pow_le_pow_left₀ (largestSingularCoefficient_nonneg _) h 2
  have he := uavg_nonneg (fun x => uavg_nonneg (fun y => sq_nonneg
    (supportedSVDResidual a b A (refreshThreshold (Fintype.card X)) x y)))
  have hc := (fourCycle_le_op_sq_energy _).trans (mul_le_mul_of_nonneg_right hs he)
  simpa only [mul_pow] using hc

/-- The fourth moment is proved on the actual random invertible matrix, for any injective feature maps, including unequal left and right maps. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); A ∈ ℝ^((X × U(F, m)) × (X × U(F, m))), assume |F| = 2; 2 ≤ m; a is injective; b is injective; ∀ x, y, ¬ (refreshConsistent(a, b, x, y)) → A(x, y) = 0; ∀ i, j, |A(i, j)| ≤ 1. Then

Let D := |X|; Let β := refreshThreshold(D); Let E := supportedSVDResidual(a, b, A, β); 𝔼_(M ∈ GLₘ(F)) [(‖ refreshTable(a, b, E, M)‖ₒₚ)⁴] ≤ 64 · fourCycle(E) + 168 / D · (1 + 2 / β)² · 𝔼ₓ [𝔼_y [(E(x, y))²]].
-/
theorem feature_residual_moment_at_threshold (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (A : Matrix (X × U F m) (X × U F m) ℝ)
    (hsupport : ∀ x y, ¬refreshConsistent a b x y → A x y = 0)
    (hA : ∀ i j, |A i j| ≤ 1) :
    let D := (Fintype.card X : ℝ)
    let β := refreshThreshold D
    let E := supportedSVDResidual a b A β
    uavg (fun M : Refresh.«GL» F m => largestSingularCoefficient (refreshTable a b E M)^4) ≤
      64 * fourCycle E + 168/D * (1+2/β)^2 * uavg (fun x => uavg (fun y => E x y ^ 2)) := by
  dsimp only
  let β := refreshThreshold (Fintype.card X)
  let E := supportedSVDResidual a b A β
  have hg := feature_card_geometry a ha
  have hβ : 0 < β := refreshThreshold_pos (lt_of_lt_of_le zero_lt_one hg.1)
  have hs : ∀ x y, dot (a x.1).val (b y.1).val ≠ dot x.2.val y.2.val → E x y = 0 := by
    intro x y hxy
    exact supportedSVDResidual_support a b A β hsupport x y (Ne.symm hxy)
  have h := refreshTable_residual_fourth hq hm a b ha hb E hs (1+2/β)
    (Fintype.card X) (by positivity) (supportedSVDResidual_entry a b A β hβ hA)
    hg.1 le_rfl hg.2
  have hnrm (M : Refresh.«GL» F m) :
      GateTruncation.opNorm (fun x y => (refreshTable a b E M x y : ℂ)) =
        largestSingularCoefficient (refreshTable a b E M) := refreshTable_op_complex a b E M
  simp_rw [hnrm] at h
  exact h

/-- The retained singular part is stable at the feature-count threshold. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); A ∈ ℝ^((X × U(F, m)) × (X × U(F, m))), assume |F| = 2; 2 ≤ m; a is injective; b is injective; ∀ i, j, |A(i, j)| ≤ 1. Then

𝔼_(M ∈ GLₘ(F)) [‖ refreshTable(a, b, refreshSVDPart(A, refreshThreshold(|X|)), M)‖ₒₚ] ≤ ‖ A‖ₒₚ + √3 · refreshThreshold(|X|).
-/
theorem feature_large_at_threshold (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (A : Matrix (X × U F m) (X × U F m) ℝ) (hA : ∀ i j, |A i j| ≤ 1) :
    uavg (fun M : Refresh.«GL» F m =>
      largestSingularCoefficient (refreshTable a b (refreshSVDPart A (refreshThreshold (Fintype.card X))) M)) ≤
      largestSingularCoefficient A + Real.sqrt 3 * refreshThreshold (Fintype.card X) := by
  have hD : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := featureSVDPart_large_mean_binary hq hm a b ha hb A _ (refreshThreshold_pos hD) hA
  apply h.trans
  have hb := mul_le_mul_of_nonneg_left (gram_threshold_bound hD (le_refl (Real.sqrt _)))
    (Real.sqrt_nonneg 3)
  simpa only [mul_one_div, add_comm] using add_le_add_left hb (largestSingularCoefficient A)

/-- Operator-norm bound under a random refresh. All analytic inputs are proved for arbitrary injective binary features and every bounded supported table. The long dimension is unrestricted except for `2 ≤ m`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); A ∈ ℝ^((X × U(F, m)) × (X × U(F, m))), assume |F| = 2; 2 ≤ m; a is injective; b is injective; ∀ x, y, ¬ (refreshConsistent(a, b, x, y)) → A(x, y) = 0; ∀ i, j, |A(i, j)| ≤ 1. Then

𝔼_(M ∈ GLₘ(F)) [‖ refreshTable(a, b, A, M)‖ₒₚ] ≤ 2 · ‖ A‖ₒₚ + (2 · √3 + 96) · (|X|)^(−(1 / 8)).
-/
theorem feature_operator_bound (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (A : Matrix (X × U F m) (X × U F m) ℝ)
    (hsupport : ∀ x y, ¬refreshConsistent a b x y → A x y = 0)
    (hA : ∀ i j, |A i j| ≤ 1) :
    uavg (fun M : Refresh.«GL» F m => largestSingularCoefficient (refreshTable a b A M)) ≤
      2 * largestSingularCoefficient A + (2 * Real.sqrt 3 + 96) * (Fintype.card X : ℝ) ^ (-(1/8 : ℝ)) := by
  letI : Nonempty (U F m) := ⟨a (Classical.choice inferInstance)⟩
  let D := (Fintype.card X : ℝ)
  let β := refreshThreshold D
  let E := supportedSVDResidual a b A β
  have hD : 1 ≤ D := (feature_card_geometry a ha).1
  have hβ : 0 < β := refreshThreshold_pos (lt_of_lt_of_le zero_lt_one hD)
  have hβ1 : β ≤ 1 := refreshThreshold_le_one hD
  have hentry : β^2 * (1+2/β)^2 ≤ 9 := by
    have heq : β^2 * (1+2/β)^2 = (β+2)^2 := by field_simp
    rw [heq]
    nlinarith
  have hsplit (M : Refresh.«GL» F m) :
      largestSingularCoefficient (refreshTable a b A M) ≤
        2 * largestSingularCoefficient (refreshTable a b (refreshSVDPart A β) M) +
          largestSingularCoefficient (refreshTable a b E M) := by
    have h := supportedSVDResidual_graph_triangle a b A β M
    simpa only [refreshTable_op_complex] using h
  have hlarge := feature_large_at_threshold hq hm a b ha hb A hA
  have henergy := supportedSVDResidual_energy a b A β hA
  have hcycle := feature_residual_cycle_at_threshold hq hm a b ha A hA
  have hmoment := feature_residual_moment_at_threshold hq hm a b ha hb A hsupport hA
  have h := operator_mean_at_feature_count
    (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F m))
    (fun M => largestSingularCoefficient (refreshTable a b A M))
    (fun M => largestSingularCoefficient (refreshTable a b (refreshSVDPart A β) M))
    (fun M => largestSingularCoefficient (refreshTable a b E M))
    D (largestSingularCoefficient A) (Real.sqrt 3) 3 (fourCycle E) (1+2/β)
    (uavg (fun x => uavg (fun y => E x y ^ 2)))
    hD (Real.sqrt_nonneg _) (by norm_num) (fun M => largestSingularCoefficient_nonneg _) hsplit
    (by simpa only [uavg_eq_expect_uniform] using hlarge)
    (uavg_nonneg (fun x => uavg_nonneg (fun y => sq_nonneg _))) henergy hcycle hentry
    (by simpa only [uavg_eq_expect_uniform] using hmoment)
  norm_num only [show (24 : ℝ)*(3+1)=96 by norm_num] at h
  simpa only [uavg_eq_expect_uniform] using h

end

end CircuitCompiler.RefreshAnalysis
