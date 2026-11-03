import Proofs.Compiler.GateApproximation.MatrixPhase.InjectiveRefreshOperator
import Proofs.Compiler.GateApproximation.MatrixPhase.RefreshAnswerProbabilities



/-!
# Common nuclear approximations for arbitrary injective binary features

The approximated answer probabilities are those of the actual common-matrix experiment. The operator estimate, density conversion and separation theorem are all proved dependencies; the approximation family is independent of labels.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1600000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {F X Z : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Z] {m : ℕ}

omit [Fintype X] [DecidableEq X] [Nonempty X] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); M ∈ GLₘ(F); x, y ∈ X, we have

consistencyIndicator(a, b, (x, rowRefresh(a(x), M)), (y, columnRefresh(b(y), M))) = 1.
-/
@[simp] theorem consistencyIndicator_on_graph (a b : X → U F m)
    (M : Refresh.«GL» F m) (x y : X) :
    consistencyIndicator a b (x,rowRefresh (a x) M) (y,columnRefresh (b y) M) = 1 := by
  unfold consistencyIndicator
  rw [rowRefresh_val, columnRefresh_val, shared_pairing]
  exact if_pos rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); A ∈ ℝ^((X × U(F, m)) × (X × U(F, m))); M ∈ GLₘ(F), we have

refreshTable(a, b, (consistencyIndicator(a, b) ⊙ A), M) = refreshTable(a, b, A, M).
-/
@[simp] theorem refreshTable_project (a b : X → U F m)
    (A : Matrix (X × U F m) (X × U F m) ℝ) (M : Refresh.«GL» F m) :
    refreshTable a b (consistencyIndicator a b ⊙ A) M = refreshTable a b A M := by
  funext x y
  simp only [refreshTable, Matrix.hadamard_apply, consistencyIndicator_on_graph, one_mul]

/-- The supported operator estimate applies directly to a bounded leakage rectangle. Both masks still see the same refresh matrix. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); p ∈ TableRectanglePartition(X, GLₘ(F), Z); z ∈ Z; W ∈ ℝ^((X × U(F, m)) × (X × U(F, m))), assume |F| = 2; 2 ≤ m; a is injective; b is injective; ∀ x, y, |W(x, y)| ≤ 1. Then

𝔼_(xy ∈ (X × U(F, m)) × (X × U(F, m))) [refreshDensity(a, b, (xy)₁, (xy)₂) · answerProb(a, b, p, z, (xy)₁, (xy)₂) · W((xy)₁, (xy)₂)] ≤ 2 · ‖ (consistencyIndicator(a, b) ⊙ W)‖ₒₚ + (2 · √3 + 96) · (|X|)^(−(1 / 8)).
-/
theorem feature_supported_dual (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (p : TableRectanglePartition X (Refresh.«GL» F m) Z)
    (z : Z) (W : Matrix (X × U F m) (X × U F m) ℝ)
    (hW : ∀ x y, |W x y| ≤ 1) :
    uavg (fun xy : (X × U F m) × (X × U F m) =>
      refreshDensity a b xy.1 xy.2 * answerProb a b p z xy.1 xy.2 * W xy.1 xy.2) ≤
        2 * largestSingularCoefficient (consistencyIndicator a b ⊙ W) +
          (2 * Real.sqrt 3 + 96) * (Fintype.card X : ℝ) ^ (-(1/8 : ℝ)) := by
  rw [uavg_prod, answerDistribution_density_pairing hm]
  have hpoint (M : Refresh.«GL» F m) :
      uavg (fun x => uavg (fun y =>
        p.leftIndicator z M x * p.rightIndicator z M y *
          W (x,rowRefresh (a x) M) (y,columnRefresh (b y) M))) ≤
      largestSingularCoefficient (refreshTable a b (consistencyIndicator a b ⊙ W) M) := by
    rw [refreshTable_project]
    have h := abs_rectanglePairing_le (refreshTable a b W M)
      (p.leftIndicator z M) (p.rightIndicator z M)
    have hrect := gate_rectangle_weight_le_one p M z
    have hpair : pairing (refreshTable a b W M)
        (fun x y => p.leftIndicator z M x * p.rightIndicator z M y) =
        uavg (fun x => uavg (fun y =>
          p.leftIndicator z M x * p.rightIndicator z M y *
            W (x,rowRefresh (a x) M) (y,columnRefresh (b y) M))) := by
      unfold pairing refreshTable
      congr 1
      funext x
      congr 1
      funext y
      ring
    rw [hpair] at h
    exact (le_abs_self _).trans (h.trans (by
      simpa using mul_le_mul_of_nonneg_right hrect (largestSingularCoefficient_nonneg (refreshTable a b W M))))
  refine (uavg_mono hpoint).trans (feature_operator_bound hq hm a b ha hb
    (consistencyIndicator a b ⊙ W) ?_ ?_)
  · intro x y hxy
    simp only [Matrix.hadamard_apply, consistencyIndicator, refreshConsistent] at hxy ⊢
    simp [hxy]
  · intro x y
    simp only [Matrix.hadamard_apply, consistencyIndicator]
    split_ifs <;> simp [hW x y]

/-- One common family approximates all answers on the exact reference distribution. Its existence follows from the proved random-refresh estimate, not from an assumed local approximation or an assumed factorization. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); p ∈ TableRectanglePartition(X, GLₘ(F), Z), assume |F| = 2; 2 ≤ m; a is injective; b is injective. Then

∃ G ∈ Z → ℝ^((X × U(F, m)) × (X × U(F, m))), (∀ z, ‖ G(z)‖_* ≤ 1) ∧ (∑_z (‖ G(z)‖_*)) ≤ |Z| ∧ (∑_z (𝔼_(xy ∈ (X × U(F, m)) × (X × U(F, m))) [refreshDensity(a, b, (xy)₁, (xy)₂) · |answerProb(a, b, p, z, (xy)₁, (xy)₂) - G(z, (xy)₁, (xy)₂)|])) ≤ |Z| · ((2 · √3 + 96) · (|X|)^(−(1 / 8)) + 2 / (|F|ᵐ - 2)).
-/
theorem feature_local_approximation (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (p : TableRectanglePartition X (Refresh.«GL» F m) Z) :
    ∃ G : Z → Matrix (X × U F m) (X × U F m) ℝ,
      (∀ z, tableNuclearNorm (G z) ≤ 1) ∧
      (∑ z, tableNuclearNorm (G z)) ≤ Fintype.card Z ∧
      (∑ z, uavg (fun xy : (X × U F m) × (X × U F m) =>
        refreshDensity a b xy.1 xy.2 * |answerProb a b p z xy.1 xy.2 - G z xy.1 xy.2|)) ≤
          Fintype.card Z * ((2 * Real.sqrt 3 + 96) * (Fintype.card X : ℝ) ^ (-(1/8 : ℝ)) +
            2 / ((vectorCard F m : ℝ) - 2)) := by
  letI : Nonempty (U F m) := ⟨a (Classical.choice inferInstance)⟩
  have he : 0 ≤ (2 * Real.sqrt 3 + 96) * (Fintype.card X : ℝ) ^ (-(1/8 : ℝ)) := by positivity
  exact answer_family_approximation_of_supported_dual (refreshDensity a b) (consistencyIndicator a b)
    (answerProb a b p) _ _ (refreshDensity_nonneg hm a b) he
    (by have := vectorCard_real_ge_four (F := F) hm
        exact div_nonneg (by norm_num) (by linarith))
    (feature_density_close hq hm a b) (feature_supported_dual hq hm a b ha hb p)

end

end CircuitCompiler.RefreshAnalysis
