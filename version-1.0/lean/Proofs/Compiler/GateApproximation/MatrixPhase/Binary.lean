import Proofs.Compiler.GateApproximation.MatrixPhase.GateDual
import Proofs.Compiler.GateApproximation.MatrixPhase.GateDualBounds
import Proofs.Compiler.GateApproximation.MatrixPhase.Local



/-!
# Binary density and tensor answer probabilities

These statements refer to the actual tensor shares, uniform invertible matrix, conditional leakage probability table, and encoding density already defined in the compiler model. The supported random-refresh operator estimate is an explicit premise of the reusable `tensor_approximation_of_operator_bound` theorem; `Proofs/Compiler/GateApproximation/MatrixPhase/InjectiveRefreshOperator.lean` supplies that estimate unconditionally and obtains the concrete approximation for every leakage answer.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {F Z : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype Z]

/-- The exact binary density lies within `2/(Q-2)` of two, for both secrets. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; s ∈ F, assume |F| = 2; 2 ≤ m. Then

|densityWeight(F, m, s) - 2| ≤ 2 / (|F|ᵐ - 2).
-/
theorem binary_densityWeight_close (hq : fieldCard F = 2) {m : ℕ} (hm : 2 ≤ m) (s : F) :
    |densityWeight F m s - 2| ≤ 2 / ((vectorCard F m : ℝ) - 2) := by
  have hQ := vectorCard_real_ge_four (F := F) hm
  have hQ0 : 0 < (vectorCard F m : ℝ) := by linarith
  have hQ2 : 0 < (vectorCard F m : ℝ) - 2 := by linarith
  by_cases hs : s = 0
  · subst s
    rw [densityWeight_zero hm, shareCard_cast_real, hq]
    norm_num only [Nat.cast_ofNat]
    have he : 2 * ((vectorCard F m : ℝ) - 1) / ((vectorCard F m : ℝ) - 2) - 2 =
        2 / ((vectorCard F m : ℝ) - 2) := by field_simp; ring
    rw [he, abs_of_pos (div_pos (by norm_num) hQ2)]
  · rw [densityWeight_of_ne_zero hm s hs, shareCard_cast_real, hq]
    norm_num only [Nat.cast_ofNat]
    have he : 2 * ((vectorCard F m : ℝ) - 1) / (vectorCard F m : ℝ) - 2 =
        -(2 / (vectorCard F m : ℝ)) := by field_simp; ring
    rw [he, abs_neg, abs_of_pos (div_pos (by norm_num) hQ0)]
    exact div_le_div_of_nonneg_left (by norm_num) hQ2 (by linarith)

/-- Consistency mask of the actual tensor ports, independent of labels. -/
/-
Mathematical definition (normal notation): For n, m ∈ ℕ; x, y ∈ GateSide(F, n, m), define

tensorConsistency(x, y) := { 1 if ((x)₂ · (y)₂) = portProduct(x, y),; 0 otherwise }.
-/
def tensorConsistency {n m : ℕ} (x y : GateSide F n m) : ℝ :=
  if dot x.2.val y.2.val = portProduct x y then 1 else 0

/-- The density conversion hypothesis is proved for the actual binary gadget. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; x, y ∈ GateSide(F, n, m), assume |F| = 2; 2 ≤ m. Then

|gateDensity(x, y) - 2 · tensorConsistency(x, y)| ≤ 2 / (|F|ᵐ - 2).
-/
theorem tensor_density_close (hq : fieldCard F = 2) {n m : ℕ} (hm : 2 ≤ m)
    (x y : GateSide F n m) :
    |gateDensity x y - 2 * tensorConsistency x y| ≤ 2 / ((vectorCard F m : ℝ) - 2) := by
  unfold gateDensity encodingDensity tensorConsistency
  split_ifs
  · simpa only [mul_one] using binary_densityWeight_close hq hm (portProduct x y)
  · simp only [mul_zero, sub_self, abs_zero]
    have := vectorCard_real_ge_four (F := F) hm
    exact div_nonneg (by norm_num) (by linarith)

/-- The real table obtained by substituting the refresh equations. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; A ∈ ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))); M ∈ GL_(n · n)(F), define

tensorRestriction(A, M) := (x, y ↦ A((x, rowRefresh(inputTensor(x), M)), (y, columnRefresh(inputTensor(y), M)))).
-/
def tensorRestriction {n : ℕ}
    (A : Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℝ)
    (M : Refresh.«GL» F (n*n)) : Matrix (U F n × U F n) (U F n × U F n) ℝ :=
  fun x y => A (x, rowRefresh (inputTensor x) M) (y, columnRefresh (inputTensor y) M)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; M ∈ GL_(n · n)(F); x, y ∈ U(F, n) × U(F, n), we have

tensorConsistency((x, rowRefresh(inputTensor(x), M)), (y, columnRefresh(inputTensor(y), M))) = 1.
-/
@[simp] theorem tensorConsistency_on_graph {n : ℕ}
    (M : Refresh.«GL» F (n*n)) (x y : U F n × U F n) :
    tensorConsistency (x, rowRefresh (inputTensor x) M)
      (y, columnRefresh (inputTensor y) M) = 1 := by
  have h := graphConstraint_on_graph (inputTensor (F := F) (n := n)) inputTensor M x y
  change dot (inputTensor x).val (inputTensor y).val -
    dot (rowRefresh (inputTensor x) M).val (columnRefresh (inputTensor y) M).val = 0 at h
  have hp : dot (rowRefresh (inputTensor x) M).val (columnRefresh (inputTensor y) M).val =
      portProduct (x, rowRefresh (inputTensor x) M) (y, columnRefresh (inputTensor y) M) := by
    rw [← sub_eq_zero.mp h]
    exact tensorVector_dot x.1.val x.2.val y.1.val y.2.val
  simp only [tensorConsistency, hp, if_true]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; A ∈ ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))); M ∈ GL_(n · n)(F), we have

tensorRestriction((tensorConsistency ⊙ A), M) = tensorRestriction(A, M).
-/
@[simp] theorem tensorRestriction_project {n : ℕ}
    (A : Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℝ)
    (M : Refresh.«GL» F (n*n)) :
    tensorRestriction (tensorConsistency ⊙ A) M = tensorRestriction A M := by
  ext x y
  change tensorConsistency (x, rowRefresh (inputTensor x) M)
      (y, columnRefresh (inputTensor y) M) *
      A (x, rowRefresh (inputTensor x) M) (y, columnRefresh (inputTensor y) M) = _
  rw [tensorConsistency_on_graph, one_mul]
  rfl

/-- One real answer rectangle obeys the bounded-test inequality once the supported operator estimate is supplied. This uses the exact conditional answer table identity; no plaintext probabilities are introduced and replaced later. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z); e ∈ ℝ; z ∈ Z; W ∈ ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))), assume 2 ≤ n; ∀ A ∈ ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))), (tensorConsistency ⊙ A = A) ⇒ (∀ x, y, |A(x, y)| ≤ 1) → 𝔼_(M ∈ GL_(n · n)(F)) [‖ tensorRestriction(A, M)‖ₒₚ] ≤ 2 · ‖ A‖ₒₚ + e; ∀ x, y, |W(x, y)| ≤ 1. Then

𝔼_(xy ∈ GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))) [gateDensity((xy)₁, (xy)₂) · groupedMatrixAnswerProb(p, z, (xy)₁, (xy)₂) · W((xy)₁, (xy)₂)] ≤ 2 · ‖ (tensorConsistency ⊙ W)‖ₒₚ + e.
-/
theorem tensor_supported_dual_of_operator_bound {n : ℕ} (hn : 2 ≤ n)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n)) Z)
    (e : ℝ)
    (hop : ∀ A : Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℝ,
      tensorConsistency ⊙ A = A → (∀ x y, |A x y| ≤ 1) →
      uavg (fun M : Refresh.«GL» F (n*n) => largestSingularCoefficient (tensorRestriction A M)) ≤
        2 * largestSingularCoefficient A + e)
    (z : Z) (W : Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℝ)
    (hW : ∀ x y, |W x y| ≤ 1) :
    uavg (fun xy : GateSide F n (n*n) × GateSide F n (n*n) =>
      gateDensity xy.1 xy.2 * groupedMatrixAnswerProb p z xy.1 xy.2 * W xy.1 xy.2) ≤
        2 * largestSingularCoefficient (tensorConsistency ⊙ W) + e := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  have hm : 2 ≤ n*n := by nlinarith
  rw [uavg_prod]
  change uavg (fun x => uavg (fun y => gateDensity x y * groupedMatrixAnswerProb p z x y * W x y)) ≤ _
  rw [groupedMatrixAnswerProb_pairing hn hm]
  have hpoint (M : Refresh.«GL» F (n*n)) :
      uavg (fun x => uavg (fun y =>
        p.leftIndicator z M x * p.rightIndicator z M y *
          W (x, rowRefresh (inputTensor x) M) (y, columnRefresh (inputTensor y) M))) ≤
      largestSingularCoefficient (tensorRestriction (tensorConsistency ⊙ W) M) := by
    rw [tensorRestriction_project]
    have h := abs_rectanglePairing_le (tensorRestriction W M)
      (p.leftIndicator z M) (p.rightIndicator z M)
    have hrect := gate_rectangle_weight_le_one p M z
    have hpair : pairing (tensorRestriction W M)
        (fun x y => p.leftIndicator z M x * p.rightIndicator z M y) =
        uavg (fun x => uavg (fun y =>
          p.leftIndicator z M x * p.rightIndicator z M y *
            W (x, rowRefresh (inputTensor x) M) (y, columnRefresh (inputTensor y) M))) := by
      unfold pairing tensorRestriction
      congr 1
      funext x
      congr 1
      funext y
      ring
    rw [hpair] at h
    exact (le_abs_self _).trans (h.trans (by
      simpa using mul_le_mul_of_nonneg_right hrect (largestSingularCoefficient_nonneg (tensorRestriction W M))))
  refine (uavg_mono hpoint).trans (hop (tensorConsistency ⊙ W) ?_ ?_)
  · ext x y
    simp only [Matrix.hadamard_apply, tensorConsistency]
    split_ifs <;> simp
  · intro x y
    simp only [Matrix.hadamard_apply, tensorConsistency]
    split_ifs <;> simp [hW x y]

/-- Concrete norm-one approximations for every tensor-leakage answer, conditional only on the supported operator estimate. The same family serves all labels. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z); e ∈ ℝ, assume |F| = 2; 2 ≤ n; 0 ≤ e; ∀ A ∈ ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))), (tensorConsistency ⊙ A = A) ⇒ (∀ x, y, |A(x, y)| ≤ 1) → 𝔼_(M ∈ GL_(n · n)(F)) [‖ tensorRestriction(A, M)‖ₒₚ] ≤ 2 · ‖ A‖ₒₚ + e. Then

∃ G ∈ Z → ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))), (∀ z, ‖ G(z)‖_* ≤ 1) ∧ (∑_z (‖ G(z)‖_*)) ≤ |Z| ∧ (∑_z (𝔼_(xy ∈ GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))) [gateDensity((xy)₁, (xy)₂) · |groupedMatrixAnswerProb(p, z, (xy)₁, (xy)₂) - G(z, (xy)₁, (xy)₂)|])) ≤ |Z| · (e + 2 / (|F|^(n · n) - 2)).
-/
theorem tensor_approximation_of_operator_bound (hq : fieldCard F = 2) {n : ℕ} (hn : 2 ≤ n)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n)) Z)
    (e : ℝ) (he : 0 ≤ e)
    (hop : ∀ A : Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℝ,
      tensorConsistency ⊙ A = A → (∀ x y, |A x y| ≤ 1) →
      uavg (fun M : Refresh.«GL» F (n*n) => largestSingularCoefficient (tensorRestriction A M)) ≤
        2 * largestSingularCoefficient A + e) :
    ∃ G : Z → Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℝ,
      (∀ z, tableNuclearNorm (G z) ≤ 1) ∧
      (∑ z, tableNuclearNorm (G z)) ≤ Fintype.card Z ∧
      (∑ z, uavg (fun xy : GateSide F n (n*n) × GateSide F n (n*n) =>
        gateDensity xy.1 xy.2 * |groupedMatrixAnswerProb p z xy.1 xy.2 - G z xy.1 xy.2|)) ≤
          Fintype.card Z * (e + 2 / ((vectorCard F (n*n) : ℝ) - 2)) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  letI : Nonempty (U F (n*n)) := ⟨unitShare ⟨0, by nlinarith⟩⟩
  have hm : 2 ≤ n*n := by nlinarith
  exact answer_family_approximation_of_supported_dual gateDensity tensorConsistency
    (groupedMatrixAnswerProb p) e _ (gateDensity_nonneg hm) he
    (by have := vectorCard_real_ge_four (F := F) hm
        exact div_nonneg (by norm_num) (by linarith))
    (tensor_density_close hq hm) (tensor_supported_dual_of_operator_bound hn p e hop)

end

end CircuitCompiler.RefreshAnalysis
