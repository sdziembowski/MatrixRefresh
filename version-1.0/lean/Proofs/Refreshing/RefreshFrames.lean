import Proofs.Refreshing.FrameBounds
import Proofs.Refreshing.GramVariance
import Proofs.Refreshing.Comparison

/-!
# Gram deviations and leakage-mask coefficients after a refresh

The scalar GL variance theorem is summed over the actual frame Gram entries. All uniformity properties come from the proved binary matrix action.
-/

noncomputable section
open scoped BigOperators Matrix

namespace RefreshingProof.Local

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Transposition is a bijection of the actual matrix coin space. -/
def transposeMatrixUnitEquiv :
    (Matrix I I (ZMod 2))ˣ ≃ (Matrix I I (ZMod 2))ˣ where
  toFun := transposeMatrixUnit
  invFun := transposeMatrixUnit
  left_inv _ := by apply Units.ext; rfl
  right_inv _ := by apply Units.ext; rfl

/-- Column action after transposition is exactly the left party's row action. -/
theorem transposeMatrixUnitEquiv_action (M : (Matrix I I (ZMod 2))ˣ)
    (x : NonzeroBinary I) :
    (matrixUnitNonzeroApply (transposeMatrixUnitEquiv M) x).val =
      x.val ᵥ* (M : Matrix I I (ZMod 2)) := by
  simp [transposeMatrixUnitEquiv, matrixUnitNonzeroApply, transposeMatrixUnit]
  exact Matrix.mulVec_transpose _ _

/-- Restrict each two-endpoint frame function to pairs related by the specified invertible matrix. -/
def matrixImageFrame (u : J → NonzeroBinary I → NonzeroBinary I → ℝ)
    (ψ : (Matrix I I (ZMod 2))ˣ ≃ (Matrix I I (ZMod 2))ˣ)
    (M : (Matrix I I (ZMod 2))ˣ) (j : J) (x : NonzeroBinary I) : ℝ :=
  u j x (matrixUnitNonzeroApply (ψ M) x)

/-- Actual Frobenius Gram deviation of a refreshed orthonormal family. -/
theorem matrix_frame_deviation_sq_le [Fintype ((Matrix I I (ZMod 2))ˣ)]
    [Nonempty (NonzeroBinary I)] (hI : 2 ≤ Fintype.card (NonzeroBinary I))
    (u : J → NonzeroBinary I → NonzeroBinary I → ℝ)
    (ψ : (Matrix I I (ZMod 2))ˣ ≃ (Matrix I I (ZMod 2))ˣ)
    (horth : ∀ j k, average (fun x => average (fun y => u j x y * u k x y)) =
      if j = k then 1 else 0) :
    average (fun M : (Matrix I I (ZMod 2))ˣ =>
      frameDeviation (matrixImageFrame u ψ M) ^ 2) ≤
        average (fun x => average (fun y => (∑ j, u j x y ^ 2) ^ 2)) /
          ((Fintype.card (NonzeroBinary I) : ℝ) - 1) := by
  have hvar := matrix_coordinate_variance hI (Finset.univ : Finset (J × J)) ψ
    (fun jk x y => u jk.1 x y * u jk.2 x y)
  have hleft (M : (Matrix I I (ZMod 2))ˣ) :
      frameDeviation (matrixImageFrame u ψ M) ^ 2 =
        ∑ jk : J × J,
          (average (fun x => u jk.1 x (matrixUnitNonzeroApply (ψ M) x) *
            u jk.2 x (matrixUnitNonzeroApply (ψ M) x)) -
            average (fun x => average (fun y => u jk.1 x y * u jk.2 x y))) ^ 2 := by
    rw [frameDeviation, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)))]
    simp only [frameGram, matrixImageFrame, Fintype.sum_prod_type, horth]
  have henergy (x y : NonzeroBinary I) :
      (∑ jk : J × J, (u jk.1 x y * u jk.2 x y) ^ 2) = (∑ j, u j x y ^ 2) ^ 2 := by
    rw [Fintype.sum_prod_type, pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    _ = average (fun M : (Matrix I I (ZMod 2))ˣ => ∑ jk : J × J,
        (average (fun x => u jk.1 x (matrixUnitNonzeroApply (ψ M) x) *
          u jk.2 x (matrixUnitNonzeroApply (ψ M) x)) -
          average (fun x => average (fun y => u jk.1 x y * u jk.2 x y))) ^ 2) :=
      average_congr hleft
    _ ≤ average (fun x => average (fun y =>
        ∑ jk : J × J, (u jk.1 x y * u jk.2 x y) ^ 2)) /
          ((Fintype.card (NonzeroBinary I) : ℝ) - 1) := hvar
    _ = _ := by simp_rw [henergy]

/-- Pointwise frame-energy control and orthonormality give the precise dimension/beta dependence needed for the nuclear bootstrap. -/
theorem matrix_frame_deviation_sq_le_of_energy [Fintype ((Matrix I I (ZMod 2))ˣ)]
    [Nonempty (NonzeroBinary I)] (hI : 2 ≤ Fintype.card (NonzeroBinary I))
    (u : J → NonzeroBinary I → NonzeroBinary I → ℝ)
    (ψ : (Matrix I I (ZMod 2))ˣ ≃ (Matrix I I (ZMod 2))ˣ)
    (horth : ∀ j k, average (fun x => average (fun y => u j x y * u k x y)) =
      if j = k then 1 else 0) {c : ℝ}
    (henergy : ∀ x y, (∑ j, u j x y ^ 2) ≤ c) :
    average (fun M : (Matrix I I (ZMod 2))ˣ =>
      frameDeviation (matrixImageFrame u ψ M) ^ 2) ≤
        c * (Fintype.card J : ℝ) / ((Fintype.card (NonzeroBinary I) : ℝ) - 1) := by
  have hnorm (j : J) : average (fun x => average (fun y => u j x y ^ 2)) = 1 := by
    simpa only [pow_two, eq_self, ite_true] using horth j j
  have hmean : average (fun x => average (fun y => ∑ j, u j x y ^ 2)) =
      (Fintype.card J : ℝ) := by
    simp_rw [average_sum, hnorm]
    simp
  have hmoment : average (fun x => average (fun y => (∑ j, u j x y ^ 2) ^ 2)) ≤
      c * (Fintype.card J : ℝ) := by
    calc
      _ ≤ average (fun x => average (fun y => c * ∑ j, u j x y ^ 2)) := by
        apply average_mono
        intro x
        apply average_mono
        intro y
        simpa only [pow_two] using mul_le_mul_of_nonneg_right (henergy x y)
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      _ = _ := by simp only [average_smul, hmean]
  have hden : 0 ≤ (Fintype.card (NonzeroBinary I) : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Fintype.card (NonzeroBinary I) := by exact_mod_cast hI
    linarith
  exact (matrix_frame_deviation_sq_le hI u ψ horth).trans
    (div_le_div_of_nonneg_right hmoment hden)

/-- Cauchy–Schwarz for the average of a scalar against the constant function. -/
theorem average_le_sqrt_average_sq {M : Type*} [Fintype M] [Nonempty M] (f : M → ℝ) :
    average f ≤ Real.sqrt (average (fun m => f m ^ 2)) := by
  have h := average_cauchy_schwarz f (fun _ => 1)
  simp only [mul_one, one_pow, RefreshingProof.average_const] at h
  have hs := Real.sq_sqrt (average_nonneg (fun m => sq_nonneg (f m)))
  have hp := Real.sqrt_nonneg (average (fun m => f m ^ 2))
  nlinarith

/-- Averaging the actual fixed-matrix mask-coefficient bound only requires a second-moment bound on the Gram deviation. -/
theorem average_mask_coefficients_le {M X J : Type*}
    [Fintype M] [Nonempty M] [Fintype X] [Fintype J] [DecidableEq J]
    (u : M → J → X → ℝ) (f : M → X → ℝ)
    (hf : ∀ m, average (fun x => f m x ^ 2) ≤ 1) {B : ℝ}
    (hB : average (fun m => frameDeviation (u m) ^ 2) ≤ B) :
    average (fun m => ∑ j, frameCoefficient (u m) (f m) j ^ 2) ≤
      1 + Real.sqrt B := by
  have hroot : average (fun m => frameDeviation (u m)) ≤ Real.sqrt B :=
    (average_le_sqrt_average_sq _).trans (Real.sqrt_le_sqrt hB)
  calc
    _ ≤ average (fun m => 1 + frameDeviation (u m)) :=
      average_mono (fun m => mask_coefficient_sq_le (u m) (f m) (hf m))
    _ = 1 + average (fun m => frameDeviation (u m)) := by
      rw [average_add, RefreshingProof.average_const]
    _ ≤ _ := add_le_add le_rfl hroot

/-- Cauchy–Schwarz with the normalized matrix average and the ordinary sum over factor indices. This does not normalize or require nonempty factor indices. -/
theorem average_inner_le {M J : Type*} [Fintype M] [Fintype J]
    (c d : M → J → ℝ) :
    average (fun m => ∑ j, c m j * d m j) ≤
      Real.sqrt (average (fun m => ∑ j, c m j ^ 2)) *
        Real.sqrt (average (fun m => ∑ j, d m j ^ 2)) := by
  have hcs := weighted_cauchy_schwarz
    (fun _ : M × J => (Fintype.card M : ℝ)⁻¹)
    (fun p : M × J => c p.1 p.2) (fun p : M × J => d p.1 p.2)
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  calc
    _ ≤ average (fun m => ∑ j, |c m j * d m j|) := by
      apply average_mono
      intro m
      exact Finset.sum_le_sum (fun j _ => le_abs_self _)
    _ ≤ _ := by
      simpa only [weightedMean, average, Fintype.sum_prod_type, Finset.mul_sum] using hcs

/-- If two coefficient families each have mean squared energy at most D, their mean inner product is at most D. -/
theorem average_inner_le_common_bound {M J : Type*} [Fintype M] [Fintype J]
    (c d : M → J → ℝ) {D : ℝ}
    (hc : average (fun m => ∑ j, c m j ^ 2) ≤ D)
    (hd : average (fun m => ∑ j, d m j ^ 2) ≤ D) :
    average (fun m => ∑ j, c m j * d m j) ≤ D := by
  have hD : 0 ≤ D := (average_nonneg (fun _ =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans hc
  calc
    _ ≤ Real.sqrt (average (fun m => ∑ j, c m j ^ 2)) *
        Real.sqrt (average (fun m => ∑ j, d m j ^ 2)) := average_inner_le c d
    _ ≤ Real.sqrt D * Real.sqrt D :=
      mul_le_mul (Real.sqrt_le_sqrt hc) (Real.sqrt_le_sqrt hd)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = D := Real.mul_self_sqrt hD

/-- The paired mask correlation averaged over shared refresh coins. The two frames may be arbitrarily correlated through those coins. -/
theorem average_mask_pairing_le {M X Y J : Type*}
    [Fintype M] [Nonempty M] [Fintype X] [Fintype Y] [Fintype J] [DecidableEq J]
    (u : M → J → X → ℝ) (v : M → J → Y → ℝ)
    (f : M → X → ℝ) (g : M → Y → ℝ)
    (hf : ∀ m, average (fun x => f m x ^ 2) ≤ 1)
    (hg : ∀ m, average (fun y => g m y ^ 2) ≤ 1) {B : ℝ}
    (hu : average (fun m => frameDeviation (u m) ^ 2) ≤ B)
    (hv : average (fun m => frameDeviation (v m) ^ 2) ≤ B) :
    average (fun m => ∑ j,
      frameCoefficient (u m) (f m) j * frameCoefficient (v m) (g m) j) ≤
        1 + Real.sqrt B :=
  average_inner_le_common_bound _ _
    (average_mask_coefficients_le u f hf hu) (average_mask_coefficients_le v g hg hv)

end RefreshingProof.Local
