import Proofs.Compiler.GateApproximation.MatrixPhase.JointLocalRates
import Proofs.Compiler.GateApproximation.MatrixPhase.JointProjection



/-!
# Real dual tests, density multiplication, and truncation costs

The auxiliary complex tables are casts of real tests. Pairing real parts lets the final projection use the real nuclear ball directly.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler

open Refresh MatrixRefresh TableAnalysis GateTruncation

noncomputable section

variable {I Z : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Z] [Nonempty Z]

/-
Mathematical definition (normal notation): For k, V ∈ Z → ℝ^(I × I), define

answerTablePairing(k, V) := ∑_z (𝔼ᵢ [𝔼ⱼ [k(z, i, j) · V(z, i, j)]]).
-/
def answerTablePairing (k V : Z → Matrix I I ℝ) : ℝ :=
  ∑ z, uavg (fun i => uavg (fun j => k z i j * V z i j))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For k, A, B ∈ Z → ℝ^(I × I), we have

answerTablePairing(k, (A - B)) = answerTablePairing(k, A) - answerTablePairing(k, B).
-/
lemma answerTablePairing_sub (k A B : Z → Matrix I I ℝ) :
    answerTablePairing k (A - B) = answerTablePairing k A - answerTablePairing k B := by
  simp [answerTablePairing, mul_sub, uavg_sub, Finset.sum_sub_distrib]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D ∈ ℝ^(I × I); k, W ∈ Z → ℝ^(I × I), we have

answerTablePairing(k, ((z ↦ D ⊙ W(z)))) = densityTablePair(D, k, W).
-/
lemma answerTablePairing_density (D : Matrix I I ℝ) (k W : Z → Matrix I I ℝ) :
    answerTablePairing k (fun z => D ⊙ W z) = densityTablePair D k W := by
  unfold answerTablePairing densityTablePair
  simp only [uavg_prod, Matrix.hadamard_apply]
  congr 1
  ext z
  congr 1
  ext i
  congr 1
  ext j
  ring

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V ∈ ℝ^(I × I), we have

energy(((i, j ↦ V(i, j)))) = 𝔼ᵢ [𝔼ⱼ [(V(i, j))²]].
-/
lemma ofReal_table_energy (V : Matrix I I ℝ) :
    energy (fun i j => (V i j : ℂ)) = uavg (fun i => uavg (fun j => V i j ^ 2)) := by
  change uavg (fun i => uavg (fun j => ‖(V i j : ℂ)‖ ^ 2)) = _
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Multiplication by a bounded density sends a normalized weighted test to a uniformly bounded-energy family. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D ∈ ℝ^(I × I); W ∈ Z → ℝ^(I × I); H ∈ ℝ, assume 0 ≤ H; ∀ i, j, 0 ≤ D(i, j); ∀ i, j, D(i, j) ≤ H; densityTablePair(D, W, W) ≤ 1. Then

(∑_z (energy(((i, j ↦ D(i, j) · W(z, i, j)))))) ≤ H.
-/
theorem density_test_family_energy (D : Matrix I I ℝ) (W : Z → Matrix I I ℝ)
    (H : ℝ) (hH : 0 ≤ H) (hD0 : ∀ i j, 0 ≤ D i j) (hDH : ∀ i j, D i j ≤ H)
    (hW : densityTablePair D W W ≤ 1) :
    (∑ z, energy (fun i j => ((D i j * W z i j : ℝ) : ℂ))) ≤ H := by
  have hp (z : Z) (i j : I) : (D i j * W z i j) ^ 2 ≤ H * (D i j * W z i j * W z i j) := by
    have h := mul_le_mul_of_nonneg_right (hDH i j) (mul_nonneg (hD0 i j) (sq_nonneg (W z i j)))
    nlinarith
  calc
    _ = ∑ z, uavg (fun i => uavg (fun j => (D i j * W z i j) ^ 2)) := by
      simp only [ofReal_table_energy]
    _ ≤ ∑ z, uavg (fun i => uavg (fun j => H * (D i j * W z i j * W z i j))) :=
      Finset.sum_le_sum (fun z _ => uavg_mono (fun i => uavg_mono (hp z i)))
    _ = H * densityTablePair D W W := by
      simp only [densityTablePair, uavg_prod, uavg_const_mul, Finset.mul_sum]
    _ ≤ H := by nlinarith [mul_le_mul_of_nonneg_left hW hH]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V ∈ ℝ^(I × I); R ∈ ℝ; i, j ∈ I, we have

V(i, j) - re(trim(((i, j ↦ V(i, j))), R, i, j)) = V(i, j) · deleted(((i, j ↦ V(i, j))), R, (i, j)).
-/
lemma real_trim_difference (V : Matrix I I ℝ) (R : ℝ) (i j : I) :
    V i j - (trim (fun i j => (V i j : ℂ)) R i j).re =
      V i j * deleted (fun i j => (V i j : ℂ)) R (i, j) := by
  unfold trim mask deleted
  split_ifs <;> simp

/-- The real pairing loss from deleting high-energy rows and columns. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D ∈ ℝ^(I × I); P ∈ 𝒟((I × I)); W, k ∈ Z → ℝ^(I × I); R, H ∈ ℝ, assume ∀ i, j, 0 ≤ D(i, j); ∀ f ∈ I × I → ℝ, 𝔼_(u ← P) [f(u)] = 𝔼ᵢ [𝔼ⱼ [D(i, j) · f((i, j))]]; ((Prod)₁_*P) = FiniteDistribution.uniform; ((Prod)₂_*P) = FiniteDistribution.uniform; ∀ z, i, j, 0 ≤ k(z, i, j) ∧ k(z, i, j) ≤ 1; 0 < R; 0 ≤ H; (∑_z (energy(((i, j ↦ D(i, j) · W(z, i, j)))))) ≤ H; densityTablePair(D, W, W) ≤ 1. Then

densityTablePair(D, k, W) ≤ answerTablePairing(k, ((z, i, j ↦ re(trim(((i, j ↦ D(i, j) · W(z, i, j))), R, i, j))))) + √(2 · H) / R.
-/
theorem density_test_trim_pairing (D : Matrix I I ℝ) (hD : ∀ i j, 0 ≤ D i j)
    (P : FiniteDistribution (I × I))
    (hP : ∀ f : I × I → ℝ, P.expect f = uavg (fun i => uavg (fun j => D i j * f (i,j))))
    (hleft : P.map Prod.fst = FiniteDistribution.uniform) (hright : P.map Prod.snd = FiniteDistribution.uniform)
    (W k : Z → Matrix I I ℝ) (hk : ∀ z i j, 0 ≤ k z i j ∧ k z i j ≤ 1)
    (R H : ℝ) (hR : 0 < R) (hH : 0 ≤ H)
    (henergy : (∑ z, energy (fun i j => ((D i j * W z i j : ℝ) : ℂ))) ≤ H)
    (hW : densityTablePair D W W ≤ 1) :
    densityTablePair D k W ≤
      answerTablePairing k (fun z i j => (trim (fun i j => ((D i j * W z i j : ℝ) : ℂ)) R i j).re) +
        Real.sqrt (2 * H) / R := by
  let V : Z → Matrix I I ℂ := fun z i j => ((D i j * W z i j : ℝ) : ℂ)
  let WC : Z → Matrix I I ℂ := fun z i j => (W z i j : ℂ)
  have hW' : P.expect (fun xy => ∑ z, ‖WC z xy.1 xy.2‖ ^ 2) ≤ 1 := by
    rw [hP]
    simp only [WC, Complex.norm_real, Real.norm_eq_abs, sq_abs, Finset.mul_sum, uavg_sum]
    simpa only [densityTablePair, uavg_prod, pow_two, mul_assoc] using hW
  have ht := trim_pairing_cost P hleft hright V WC (fun z xy => k z xy.1 xy.2)
    (fun z xy => hk z xy.1 xy.2) R H hR hH henergy hW'
  have hdiff : densityTablePair D k W -
      answerTablePairing k (fun z i j => (trim (V z) R i j).re) ≤
      ∑ z, P.expect (fun xy => ‖WC z xy.1 xy.2‖ * (k z xy.1 xy.2 * deleted (V z) R xy)) := by
    rw [← answerTablePairing_density, ← answerTablePairing_sub]
    unfold answerTablePairing
    apply Finset.sum_le_sum
    intro z _
    rw [hP]
    apply uavg_mono
    intro i
    apply uavg_mono
    intro j
    change k z i j * ((D ⊙ W z) i j - (trim (V z) R i j).re) ≤ _
    rw [show (D ⊙ W z) i j = D i j * W z i j by rfl,
      real_trim_difference (fun i j => D i j * W z i j)]
    have hd : 0 ≤ deleted (V z) R (i,j) := by unfold deleted; split_ifs <;> norm_num
    have hp := mul_le_mul_of_nonneg_right (le_abs_self (W z i j))
      (mul_nonneg (hD i j) (mul_nonneg (hk z i j).1 hd))
    simpa only [WC, Complex.norm_real, Real.norm_eq_abs] using (by convert hp using 1 <;> ring)
  dsimp [V] at hdiff ht
  linarith

/-- Entry capping changes the real pairing by at most the total energy over the cap level. This uses the product-measure answer table bound `0 ≤ k ≤ 1`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V ∈ Z → ℂ^(I × I); k ∈ Z → ℝ^(I × I); R, L, H ∈ ℝ, assume ∀ z, i, j, 0 ≤ k(z, i, j) ∧ k(z, i, j) ≤ 1; 0 < L; (∑_z (energy(V(z)))) ≤ H. Then

answerTablePairing(k, ((z, i, j ↦ re(trim(V(z), R, i, j))))) ≤ answerTablePairing(k, ((z, i, j ↦ re(capped(V(z), R, L, i, j))))) + H / L.
-/
theorem real_cap_pairing_loss (V : Z → Matrix I I ℂ) (k : Z → Matrix I I ℝ)
    (hk : ∀ z i j, 0 ≤ k z i j ∧ k z i j ≤ 1)
    (R L H : ℝ) (hL : 0 < L) (henergy : (∑ z, energy (V z)) ≤ H) :
    answerTablePairing k (fun z i j => (trim (V z) R i j).re) ≤
      answerTablePairing k (fun z i j => (capped (V z) R L i j).re) + H / L := by
  have hpoint (z : Z) (i j : I) : k z i j *
      ((trim (V z) R i j).re - (capped (V z) R L i j).re) ≤
      ‖trim (V z) R i j - capped (V z) R L i j‖ := by
    have h := mul_le_mul_of_nonneg_left (Complex.re_le_norm
      (trim (V z) R i j - capped (V z) R L i j)) (hk z i j).1
    have h' := mul_le_mul_of_nonneg_right (hk z i j).2
      (norm_nonneg (trim (V z) R i j - capped (V z) R L i j))
    simpa only [Complex.sub_re, one_mul] using h.trans h'
  have h := Finset.sum_le_sum (s := Finset.univ) (fun z _ =>
    uavg_mono (fun i => uavg_mono (hpoint z i)))
  have he := h.trans (cap_error_family_mean_le V R L H hL henergy)
  simp only [mul_sub, uavg_sub, Finset.sum_sub_distrib] at he
  change answerTablePairing k (fun z i j => (trim (V z) R i j).re) -
    answerTablePairing k (fun z i j => (capped (V z) R L i j).re) ≤ H / L at he
  linarith

end

end CircuitCompiler
