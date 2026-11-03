import Proofs.Compiler.GateApproximation.MatrixPhase.EncodingMapApproximation



/-!
# Pairing the actual answer probabilities with a test table

This uses the conditional answer distribution of the actual matrix experiment. The density correction is kept explicit; the test table need not be supported.
-/
set_option autoImplicit false

set_option maxHeartbeats 1500000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical

namespace CircuitCompiler.AnswerApproximation

open Refresh MatrixRefresh TableAnalysis RefreshAnalysis

noncomputable section

variable {F X Z : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Z] {m : ℕ}

omit [Fintype X] [DecidableEq X] [Nonempty X] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); p ∈ TableRectanglePartition(X, GLₘ(F), Z); z ∈ Z; x, y ∈ X × U(F, m), assume ¬ (refreshConsistent(a, b, x, y)). Then

answerProb(a, b, p, z, x, y) = 0.
-/
theorem answerProb_supported (a b : X → U F m)
    (p : TableRectanglePartition X (Refresh.«GL» F m) Z) (z : Z)
    (x y : X × U F m) (h : ¬refreshConsistent a b x y) :
    answerProb a b p z x y = 0 := by
  exact if_neg h

omit [Fintype X] [DecidableEq X] [Nonempty X] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); p ∈ TableRectanglePartition(X, GLₘ(F), Z); z ∈ Z; x, y ∈ X × U(F, m), we have

|answerProb(a, b, p, z, x, y)| ≤ 1.
-/
theorem answerProb_le_one (a b : X → U F m)
    (p : TableRectanglePartition X (Refresh.«GL» F m) Z) (z : Z)
    (x y : X × U F m) : |answerProb a b p z x y| ≤ 1 := by
  rw [abs_of_nonneg (answerProb_nonneg a b p z x y)]
  unfold answerProb
  split_ifs
  · have h := Finset.single_le_sum
      (fun k (_ : k ∈ (Finset.univ : Finset Z)) =>
        (answerDistribution a b p x.1 y.1 ⟨x.2,y.2⟩).nonneg k)
      (Finset.mem_univ z)
    simpa only [FiniteDistribution.total] using h
  · norm_num

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); p ∈ TableRectanglePartition(X, GLₘ(F), Z); z ∈ Z; W ∈ ℝ^((X × U(F, m)) × (X × U(F, m))); B ∈ ℝ, assume |F| = 2; 2 ≤ m; 0 ≤ B; ∀ x, y, |W(x, y)| ≤ B. Then

2 · |pairing(answerProb(a, b, p, z), W)| ≤ 𝔼_(M ∈ GLₘ(F)) [‖ refreshTable(a, b, W, M)‖ₒₚ] + (2 / (|F|ᵐ - 2)) · B.
-/
theorem feature_answer_pairing_le_graph_op (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (p : TableRectanglePartition X (Refresh.«GL» F m) Z)
    (z : Z) (W : Matrix (X × U F m) (X × U F m) ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hW : ∀ x y, |W x y| ≤ B) :
    2 * |pairing (answerProb a b p z) W| ≤
      uavg (fun M : Refresh.«GL» F m => largestSingularCoefficient (refreshTable a b W M)) +
        (2 / ((vectorCard F m : ℝ) - 2)) * B := by
  letI : Nonempty (U F m) := ⟨a (Classical.choice inferInstance)⟩
  let A := answerProb a b p z
  let δ := 2 / ((vectorCard F m : ℝ) - 2)
  have hδ : 0 ≤ δ := by
    have h := vectorCard_real_ge_four (F := F) hm
    dsimp [δ]
    exact div_nonneg (by norm_num) (by linarith)
  let L := uavg (fun x => uavg (fun y => refreshDensity a b x y * A x y * W x y))
  let E := uavg (fun x => uavg (fun y => (2 - refreshDensity a b x y) * A x y * W x y))
  have hid : 2 * pairing A W = L + E := by
    dsimp [L, E, pairing]
    rw [← uavg_const_mul, ← uavg_add]
    apply uavg_congr
    intro x
    rw [← uavg_const_mul, ← uavg_add]
    apply uavg_congr
    intro y
    ring
  have hepoint (x y : X × U F m) :
      |(2 - refreshDensity a b x y) * A x y * W x y| ≤ δ * B := by
    by_cases h : refreshConsistent a b x y
    · have hd := feature_density_close hq hm a b x y
      have hc : consistencyIndicator a b x y = 1 := if_pos h
      rw [hc, mul_one, abs_sub_comm] at hd
      rw [abs_mul, abs_mul]
      calc
        _ ≤ (δ * 1) * B := by
          exact mul_le_mul (mul_le_mul hd (answerProb_le_one a b p z x y)
            (abs_nonneg _) hδ) (hW x y) (abs_nonneg _) (by positivity)
        _ = δ * B := by ring
    · simp only [A, answerProb_supported a b p z x y h, mul_zero,
        zero_mul, abs_zero]
      positivity
  have he : |E| ≤ δ * B := by
    apply (abs_uavg_le _).trans
    apply (uavg_mono (fun x => (abs_uavg_le _).trans
      ((uavg_mono (hepoint x)).trans_eq (uavg_const _)))).trans_eq
    exact uavg_const _
  have hl : |L| ≤ uavg (fun M : Refresh.«GL» F m => largestSingularCoefficient (refreshTable a b W M)) := by
    dsimp only [L, A]
    rw [answerDistribution_density_pairing hm]
    apply (abs_uavg_le _).trans
    apply uavg_mono
    intro M
    have h := abs_rectanglePairing_le (refreshTable a b W M)
      (p.leftIndicator z M) (p.rightIndicator z M)
    have hr := gate_rectangle_weight_le_one p M z
    have hp : pairing (refreshTable a b W M)
        (fun x y => p.leftIndicator z M x * p.rightIndicator z M y) =
        uavg (fun x => uavg (fun y => p.leftIndicator z M x *
          p.rightIndicator z M y * W (x,rowRefresh (a x) M) (y,columnRefresh (b y) M))) := by
      unfold pairing refreshTable
      apply uavg_congr
      intro x
      apply uavg_congr
      intro y
      ring
    rw [hp] at h
    exact h.trans (by simpa using
      mul_le_mul_of_nonneg_right hr (largestSingularCoefficient_nonneg (refreshTable a b W M)))
  have htri := (abs_add_le L E).trans (add_le_add hl he)
  rw [← hid, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
  exact htri

end

end CircuitCompiler.AnswerApproximation
