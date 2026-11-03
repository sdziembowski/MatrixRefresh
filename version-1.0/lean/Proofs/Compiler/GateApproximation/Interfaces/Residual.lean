import Proofs.Compiler.GateApproximation.Interfaces.StrictTruncation
import Proofs.Compiler.GateApproximation.MatrixPhase.SVDResidual



/-!
# The exact residual identity in the direct truncation proof

This module formalizes the consistency projection and its cancellation identity used in the local-approximation proof. It applies to any orthogonal retained part `H` of the supported table `A`; the general identity states its retained-pairing hypothesis explicitly. The specialization to the exact strict cutoff proves that hypothesis from the SVD. Neither assumes the residual error estimate.

All pairings and L2 norms use uniform probability measures, as in the paper. The existing `refreshSign` has values ±1, so the paper's table `J` is half of it.
-/

set_option autoImplicit false

open scoped BigOperators Matrix

namespace CircuitCompiler.AnswerApproximation

open MatrixRefresh TableAnalysis RefreshAnalysis

noncomputable section

variable {I : Type*} [Fintype I]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, H ∈ ℝ^(I × I), we have

pairing(A, H) = 𝔼_(p ∈ I × I) [A((p)₁, (p)₂) · H((p)₁, (p)₂)].
-/
private theorem normalized_pairing (A H : Matrix I I ℝ) :
    pairing A H = uavg (fun p : I × I => A p.1 p.2 * H p.1 p.2) :=
  (uavg_prod (fun p : I × I => A p.1 p.2 * H p.1 p.2)).symm

/-- The paper's consistency sign table: one half on possible tuples and minus one half on impossible tuples. -/
/-
Mathematical definition (normal notation): For valid ∈ I → I → Prop, assume DecidableRel(valid). define

consistencySign(valid) := 1 / 2 · refreshSign(valid).
-/
def consistencySign (valid : I → I → Prop) [DecidableRel valid] : Matrix I I ℝ :=
  (1 / 2 : ℝ) • refreshSign valid

omit [Fintype I] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For valid ∈ I → I → Prop; H ∈ ℝ^(I × I), assume DecidableRel(valid). Then

project(valid, H) = 1 / 2 · H + consistencySign(valid) ⊙ H.
-/
theorem consistency_projection_split (valid : I → I → Prop) [DecidableRel valid]
    (H : Matrix I I ℝ) :
    project valid H = (1 / 2 : ℝ) • H + consistencySign valid ⊙ H := by
  ext i j
  simp only [project, consistencySign, refreshSign, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.hadamard_apply]
  split_ifs <;> ring

/-- Pairing a supported table with a projected table changes nothing. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For valid ∈ I → I → Prop; A, H ∈ ℝ^(I × I), assume DecidableRel(valid); ∀ i, j, ¬ (valid(i, j)) → A(i, j) = 0. Then

pairing(A, project(valid, H)) = pairing(A, H).
-/
theorem supported_pairing_projection (valid : I → I → Prop) [DecidableRel valid]
    (A H : Matrix I I ℝ) (hA : ∀ i j, ¬valid i j → A i j = 0) :
    pairing A (project valid H) = pairing A H := by
  unfold pairing
  apply uavg_congr
  intro i
  apply uavg_congr
  intro j
  by_cases hij : valid i j
  · simp [project, hij]
  · simp [project, hij, hA i j hij]

/-- The projection keeps or zeros each entry, giving the paper's projected norm identity without any spectral or probabilistic assumptions. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For valid ∈ I → I → Prop; H ∈ ℝ^(I × I), assume DecidableRel(valid). Then

(‖ project(valid, H)‖₂)² = 1 / 2 · (‖ H‖₂)² + pairing(H, (consistencySign(valid) ⊙ H)).
-/
theorem consistency_projected_l2_sq (valid : I → I → Prop) [DecidableRel valid]
    (H : Matrix I I ℝ) :
    tableL2Norm (project valid H) ^ 2 =
      (1 / 2 : ℝ) * tableL2Norm H ^ 2 + pairing H (consistencySign valid ⊙ H) := by
  simp only [tableL2Norm_sq, signedL2Sq, normalized_pairing]
  rw [← uavg_const_mul, ← uavg_add]
  apply uavg_congr
  intro p
  simp only [project, consistencySign, refreshSign, Matrix.smul_apply,
    smul_eq_mul, Matrix.hadamard_apply]
  split_ifs <;> ring

/-- Exact identity for Δ = A − 2 project(H), assuming H is an orthogonal retained part: ⟨A,H⟩ = ‖H‖₂². The support condition is essential. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For valid ∈ I → I → Prop; A, H ∈ ℝ^(I × I), assume DecidableRel(valid); ∀ i, j, ¬ (valid(i, j)) → A(i, j) = 0; pairing(A, H) = (‖ H‖₂)². Then

(‖ (A - 2 · project(valid, H))‖₂)² = pairing(A, (A - 2 · project(valid, H))) + 4 · pairing(H, (consistencySign(valid) ⊙ H)).
-/
theorem truncation_residual_identity (valid : I → I → Prop) [DecidableRel valid]
    (A H : Matrix I I ℝ) (hA : ∀ i j, ¬valid i j → A i j = 0)
    (hretained : pairing A H = tableL2Norm H ^ 2) :
    tableL2Norm (A - (2 : ℝ) • project valid H) ^ 2 =
      pairing A (A - (2 : ℝ) • project valid H) +
        4 * pairing H (consistencySign valid ⊙ H) := by
  have hexpand :
      tableL2Norm (A - (2 : ℝ) • project valid H) ^ 2 =
        pairing A (A - (2 : ℝ) • project valid H) +
          4 * pairing H (consistencySign valid ⊙ H) +
          2 * (tableL2Norm H ^ 2 - pairing A H) := by
    simp only [tableL2Norm_sq, signedL2Sq, normalized_pairing]
    rw [← uavg_sub, ← uavg_const_mul, ← uavg_const_mul,
      ← uavg_add, ← uavg_add]
    apply uavg_congr
    intro p
    by_cases hp : valid p.1 p.2
    · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        project, consistencySign, refreshSign, Matrix.hadamard_apply, hp, if_true]
      ring
    · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        project, consistencySign, refreshSign, Matrix.hadamard_apply, hp, if_false,
        hA p.1 p.2 hp]
      ring
  simpa only [hretained, sub_self, mul_zero, add_zero] using hexpand

/-- The residual identity for the manuscript's actual strict `> β` cutoff. Only support is assumed; the retained-pairing property is proved by the SVD. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Let A vanish on invalid pairs, set H = A^(>β), and let J equal 1/2 on valid pairs and -1/2 elsewhere. For Δ = A-2 · project(H),

‖Δ‖₂² = ⟨ A,Δ⟩+4 · ⟨ H,J ⊙ H⟩.

The pairing and L₂ norm use uniform measures; ⊙ denotes entrywise multiplication.
-/
theorem strict_truncation_residual_identity
    (valid : I → I → Prop) [DecidableRel valid] (A : Matrix I I ℝ) (β : ℝ)
    (hA : ∀ i j, ¬valid i j → A i j = 0) :
    let H := SingularTruncation.strictTruncation A β
    tableL2Norm (A - (2 : ℝ) • project valid H) ^ 2 =
      pairing A (A - (2 : ℝ) • project valid H) +
        4 * pairing H (consistencySign valid ⊙ H) :=
  truncation_residual_identity valid A _ hA
    (SingularTruncation.strictTruncation_pairing A β)

/-- The last scalar step of the nuclear-norm bootstrap: if twice the nuclear norm is B and B ≤ 2 + √B, then the nuclear norm is at most two. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For B ∈ ℝ, assume 0 ≤ B; B ≤ 2 + √B. Then

B ≤ 4.
-/
theorem nuclear_bootstrap (B : ℝ) (hB : 0 ≤ B)
    (h : B ≤ 2 + Real.sqrt B) : B ≤ 4 := by
  have hs := Real.sq_sqrt hB
  have hp := Real.sqrt_nonneg B
  by_contra hnot
  have hb : 4 < B := lt_of_not_ge hnot
  have ht : 2 < Real.sqrt B := by nlinarith
  nlinarith [mul_pos (sub_pos.mpr ht) (by linarith : 0 < Real.sqrt B + 1)]

end

end CircuitCompiler.AnswerApproximation
