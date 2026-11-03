import Proofs.Compiler.GateApproximation.MatrixPhase.GateDensity
import Proofs.Compiler.GateApproximation.MatrixPhase.Moments



/-!
# Norm-one local approximations by finite-dimensional separation

The bounded-test conversion `2‖PW‖op ≤ ‖φW‖op + ε`, followed by actual finite-dimensional separation, is verified here. This local approximation theorem takes the random-refresh operator estimate as an explicit premise. The actual tensor estimate and its unconditional local approximation are proved by specializing this theorem in `Proofs/Compiler/GateApproximation/MatrixPhase/InjectiveRefreshOperator.lean`.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {I X M Z : Type*}

/-- The uniform operator norm is bounded by the largest absolute entry. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); B ∈ ℝ, assume I is finite; I ≠ ∅; 0 ≤ B; ∀ i, j, |A(i, j)| ≤ B. Then

‖ A‖ₒₚ ≤ B.
-/
theorem largestSingularCoefficient_le_entry_bound [Fintype I] [DecidableEq I] [Nonempty I]
    (A : Matrix I I ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hA : ∀ i j, |A i j| ≤ B) : largestSingularCoefficient A ≤ B := by
  apply (largestSingularCoefficient_le_tableL2Norm A).trans
  have hsq : tableL2Norm A ^ 2 ≤ B ^ 2 := by
    rw [tableL2Norm_sq]
    exact (uavg_mono (fun p : I × I => by
      have h := hA p.1 p.2
      nlinarith [sq_abs (A p.1 p.2), abs_nonneg (A p.1 p.2)])).trans_eq
        (uavg_const (B ^ 2))
  nlinarith [tableL2Norm_nonneg A]

/-- Density conversion used immediately before separation. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For φ, P, W ∈ ℝ^(I × I); ε ∈ ℝ, assume I is finite; I ≠ ∅; 0 ≤ ε; ∀ i, j, |φ(i, j) - 2 · P(i, j)| ≤ ε; ∀ i, j, |W(i, j)| ≤ 1. Then

2 · ‖ (P ⊙ W)‖ₒₚ ≤ ‖ (φ ⊙ W)‖ₒₚ + ε.
-/
theorem density_operator_conversion [Fintype I] [DecidableEq I] [Nonempty I]
    (φ P W : Matrix I I ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hclose : ∀ i j, |φ i j - 2 * P i j| ≤ ε)
    (hW : ∀ i j, |W i j| ≤ 1) :
    2 * largestSingularCoefficient (P ⊙ W) ≤ largestSingularCoefficient (φ ⊙ W) + ε := by
  let E : Matrix I I ℝ := fun i j => (φ i j - 2 * P i j) * W i j
  have hE : largestSingularCoefficient E ≤ ε := largestSingularCoefficient_le_entry_bound E ε hε (fun i j => by
    dsimp [E]
    rw [abs_mul]
    exact (mul_le_mul (hclose i j) (hW i j) (abs_nonneg _) hε).trans_eq (mul_one ε))
  have hdecomp : (2 : ℝ) • (P ⊙ W) = φ ⊙ W - E := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.hadamard_apply, Matrix.sub_apply, smul_eq_mul, E]
    ring
  have hnorm := norm_sub_le (φ ⊙ W) E
  have h := div_le_div_of_nonneg_right hnorm
    (Nat.cast_nonneg (Fintype.card I) : (0 : ℝ) ≤ _)
  rw [← hdecomp, norm_smul] at h
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  change 2 * ‖P ⊙ W‖ / Fintype.card I ≤ (‖φ ⊙ W‖ + ‖E‖) / Fintype.card I at h
  unfold largestSingularCoefficient at *
  rw [add_div] at h
  rw [mul_div_assoc] at h
  exact h.trans (add_le_add le_rfl hE)

/-- The paper's one-answer weighted L1 approximation with nuclear budget one. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For φ, P, k ∈ ℝ^(I × I); e, ε ∈ ℝ, assume I is finite; I ≠ ∅; ∀ i, j, 0 ≤ φ(i, j); 0 ≤ e; 0 ≤ ε; ∀ i, j, |φ(i, j) - 2 · P(i, j)| ≤ ε; ∀ W ∈ ℝ^(I × I), (∀ i, j, |W(i, j)| ≤ 1) → 𝔼_(p ∈ I × I) [φ((p)₁, (p)₂) · k((p)₁, (p)₂) · W((p)₁, (p)₂)] ≤ 2 · ‖ (P ⊙ W)‖ₒₚ + e. Then

∃ G ∈ ℝ^(I × I), ‖ G‖_* ≤ 1 ∧ 𝔼_(p ∈ I × I) [φ((p)₁, (p)₂) · |k((p)₁, (p)₂) - G((p)₁, (p)₂)|] ≤ e + ε.
-/
theorem answer_approximation_of_supported_dual
    [Fintype I] [DecidableEq I] [Nonempty I]
    (φ P k : Matrix I I ℝ) (e ε : ℝ)
    (hφ : ∀ i j, 0 ≤ φ i j) (he : 0 ≤ e) (hε : 0 ≤ ε)
    (hclose : ∀ i j, |φ i j - 2 * P i j| ≤ ε)
    (hdual : ∀ W : Matrix I I ℝ, (∀ i j, |W i j| ≤ 1) →
      uavg (fun p : I × I => φ p.1 p.2 * k p.1 p.2 * W p.1 p.2) ≤
        2 * largestSingularCoefficient (P ⊙ W) + e) :
    ∃ G : Matrix I I ℝ, tableNuclearNorm G ≤ 1 ∧
      uavg (fun p : I × I => φ p.1 p.2 * |k p.1 p.2 - G p.1 p.2|) ≤ e + ε := by
  obtain ⟨G, hG, herr⟩ := exists_density_tableNuclearNormProjection_L1
    (Z := Unit) φ hφ 1 (e + ε) (by norm_num) (add_nonneg he hε) (fun _ => k) (by
      intro W hW
      have hd := hdual (W ()) (hW ())
      have hc := density_operator_conversion φ P (W ()) ε hε hclose (hW ())
      have hnorm : ‖fun z : Unit => largestSingularCoefficient (φ ⊙ W z)‖ = largestSingularCoefficient (φ ⊙ W ()) := by
        have hw : (fun z : Unit => largestSingularCoefficient (φ ⊙ W z)) =
            (fun _ : Unit => largestSingularCoefficient (φ ⊙ W ())) := by funext z; cases z; rfl
        rw [hw, pi_norm_const]
        exact abs_of_nonneg (largestSingularCoefficient_nonneg _)
      simp only [densityTablePair, Fintype.sum_unique, hnorm, one_mul]
      linarith)
  refine ⟨G (), ?_, ?_⟩
  · simpa only [Fintype.sum_unique] using hG
  · simpa only [Fintype.sum_unique] using herr

/-- Apply the same plaintext-independent construction separately to every answer. Neither the budget nor the L1 error acquires a square-root convention. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For φ, P ∈ ℝ^(I × I); k ∈ Z → ℝ^(I × I); e, ε ∈ ℝ, assume I is finite; I ≠ ∅; Z is finite; ∀ i, j, 0 ≤ φ(i, j); 0 ≤ e; 0 ≤ ε; ∀ i, j, |φ(i, j) - 2 · P(i, j)| ≤ ε; ∀ z, (, W, :, Matrix, I, I, ℝ, ), (∀ i, j, |W(i, j)| ≤ 1) → 𝔼_(p ∈ I × I) [φ((p)₁, (p)₂) · k(z, (p)₁, (p)₂) · W((p)₁, (p)₂)] ≤ 2 · ‖ (P ⊙ W)‖ₒₚ + e. Then

∃ G ∈ Z → ℝ^(I × I), (∀ z, ‖ G(z)‖_* ≤ 1) ∧ (∑_z (‖ G(z)‖_*)) ≤ |Z| ∧ (∑_z (𝔼_(p ∈ I × I) [φ((p)₁, (p)₂) · |k(z, (p)₁, (p)₂) - G(z, (p)₁, (p)₂)|])) ≤ |Z| · (e + ε).
-/
theorem answer_family_approximation_of_supported_dual
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Z]
    (φ P : Matrix I I ℝ) (k : Z → Matrix I I ℝ) (e ε : ℝ)
    (hφ : ∀ i j, 0 ≤ φ i j) (he : 0 ≤ e) (hε : 0 ≤ ε)
    (hclose : ∀ i j, |φ i j - 2 * P i j| ≤ ε)
    (hdual : ∀ z (W : Matrix I I ℝ), (∀ i j, |W i j| ≤ 1) →
      uavg (fun p : I × I => φ p.1 p.2 * k z p.1 p.2 * W p.1 p.2) ≤
        2 * largestSingularCoefficient (P ⊙ W) + e) :
    ∃ G : Z → Matrix I I ℝ,
      (∀ z, tableNuclearNorm (G z) ≤ 1) ∧
      (∑ z, tableNuclearNorm (G z)) ≤ Fintype.card Z ∧
      (∑ z, uavg (fun p : I × I =>
        φ p.1 p.2 * |k z p.1 p.2 - G z p.1 p.2|)) ≤ Fintype.card Z * (e + ε) := by
  classical
  choose G hG herr using fun z => answer_approximation_of_supported_dual
    φ P (k z) e ε hφ he hε hclose (hdual z)
  refine ⟨G, hG, ?_, ?_⟩
  · exact (Finset.sum_le_sum (fun z _ => hG z)).trans_eq (by simp)
  · exact (Finset.sum_le_sum (fun z _ => herr z)).trans_eq (by simp; ring)

/-- A density bound transports the *same* answer-family approximations to fixed plaintexts. The paper uses `c=3` for copies and `c=9` for tensor inputs. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For φ, D ∈ ℝ^(I × I); k, G ∈ Z → ℝ^(I × I); c, e ∈ ℝ, assume I is finite; Z is finite; 0 ≤ c; ∀ i, j, D(i, j) ≤ c · φ(i, j); (∑_z (𝔼_(p ∈ I × I) [φ((p)₁, (p)₂) · |k(z, (p)₁, (p)₂) - G(z, (p)₁, (p)₂)|])) ≤ e. Then

(∑_z (𝔼_(p ∈ I × I) [D((p)₁, (p)₂) · |k(z, (p)₁, (p)₂) - G(z, (p)₁, (p)₂)|])) ≤ c · e.
-/
theorem conditioned_family_error [Fintype I] [Fintype Z]
    (φ D : Matrix I I ℝ) (k G : Z → Matrix I I ℝ) (c e : ℝ)
    (hc : 0 ≤ c) (hD : ∀ i j, D i j ≤ c * φ i j)
    (herr : (∑ z, uavg (fun p : I × I =>
      φ p.1 p.2 * |k z p.1 p.2 - G z p.1 p.2|)) ≤ e) :
    (∑ z, uavg (fun p : I × I =>
      D p.1 p.2 * |k z p.1 p.2 - G z p.1 p.2|)) ≤ c * e := by
  calc
    _ ≤ ∑ z, uavg (fun p : I × I =>
        c * (φ p.1 p.2 * |k z p.1 p.2 - G z p.1 p.2|)) := by
      apply Finset.sum_le_sum
      intro z _
      exact uavg_mono (fun p => by
        convert mul_le_mul_of_nonneg_right (hD p.1 p.2)
          (abs_nonneg (k z p.1 p.2 - G z p.1 p.2)) using 1; ring)
    _ = c * ∑ z, uavg (fun p : I × I =>
        φ p.1 p.2 * |k z p.1 p.2 - G z p.1 p.2|) := by
      simp only [uavg_const_mul, Finset.mul_sum]
    _ ≤ c * e := mul_le_mul_of_nonneg_left herr hc

end

end CircuitCompiler.RefreshAnalysis
