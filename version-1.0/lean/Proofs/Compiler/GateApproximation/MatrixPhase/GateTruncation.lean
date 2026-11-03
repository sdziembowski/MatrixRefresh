import Proofs.Compiler.GateApproximation.MatrixPhase.GateDensity
import Proofs.Compiler.GateApproximation.MatrixPhase.JointSchur



/-!
# Row trimming and entry capping for the joint dual test

All averages here use normalized uniform measure. The complex phase of a capped entry is preserved, and a zero entry remains zero.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.GateTruncation

open Refresh MatrixRefresh WithLp

noncomputable section

variable {I Z : Type*} [Fintype I] [DecidableEq I] [Fintype Z]

/-
Mathematical definition (normal notation): For A ∈ ℂ^(I × I); i ∈ I, define

rowEnergy(A, i) := 𝔼ⱼ [(‖ A(i, j)‖)²].
-/
def rowEnergy (A : Matrix I I ℂ) (i : I) : ℝ := uavg (fun j => ‖A i j‖ ^ 2)

/-
Mathematical definition (normal notation): For A ∈ ℂ^(I × I); j ∈ I, define

columnEnergy(A, j) := 𝔼ᵢ [(‖ A(i, j)‖)²].
-/
def columnEnergy (A : Matrix I I ℂ) (j : I) : ℝ := uavg (fun i => ‖A i j‖ ^ 2)

/-
Mathematical definition (normal notation): For A ∈ ℂ^(I × I), define

energy(A) := 𝔼ᵤ [rowEnergy(A, u)].
-/
def energy (A : Matrix I I ℂ) : ℝ := uavg (rowEnergy A)

/-
Mathematical definition (normal notation): For A ∈ ℂ^(I × I), define

opNorm(A) := ‖ A‖ / |I|.
-/
def opNorm (A : Matrix I I ℂ) : ℝ := ‖A‖ / Fintype.card I

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); i ∈ I, we have

0 ≤ rowEnergy(A, i).
-/
theorem rowEnergy_nonneg (A : Matrix I I ℂ) (i : I) : 0 ≤ rowEnergy A i :=
  uavg_nonneg (fun _ => sq_nonneg _)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); j ∈ I, we have

0 ≤ columnEnergy(A, j).
-/
theorem columnEnergy_nonneg (A : Matrix I I ℂ) (j : I) : 0 ≤ columnEnergy A j :=
  uavg_nonneg (fun _ => sq_nonneg _)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I), we have

𝔼ᵤ [columnEnergy(A, u)] = energy(A).
-/
theorem columnEnergy_mean (A : Matrix I I ℂ) : uavg (columnEnergy A) = energy A :=
  uavg_comm _

/- Mathematical definition (normal notation): Given row and column predicates r,c, define the masked matrix by A'ᵢⱼ = Aᵢⱼ if both r(i) and c(j) hold, and A'ᵢⱼ = 0 otherwise. -/
def mask (A : Matrix I I ℂ) (r c : I → Prop) : Matrix I I ℂ := by
  classical
  exact fun i j => if r i ∧ c j then A i j else 0

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); r, c ∈ I → Prop; i, j ∈ I, we have

(‖ mask(A, r, c, i, j)‖)² ≤ (‖ A(i, j)‖)².
-/
theorem mask_energy_pointwise (A : Matrix I I ℂ) (r c : I → Prop) (i j : I) :
    ‖mask A r c i j‖ ^ 2 ≤ ‖A i j‖ ^ 2 := by
  classical
  unfold mask
  split_ifs
  · rfl
  · simpa using sq_nonneg ‖A i j‖

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); r, c ∈ I → Prop, we have

‖ mask(A, r, c)‖ ≤ ‖ A‖.
-/
theorem mask_norm_le (A : Matrix I I ℂ) (r c : I → Prop) :
    ‖mask A r c‖ ≤ ‖A‖ := by
  classical
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  let y : I → ℂ := fun j => if c j then x j else 0
  have hy : (∑ j, ‖y j‖ ^ 2) ≤ ∑ j, ‖x j‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    dsimp [y]
    split_ifs
    · rfl
    · simpa using sq_nonneg ‖x j‖
  have he (i : I) : ((mask A r c) *ᵥ x) i =
      if r i then (A *ᵥ y) i else 0 := by
    unfold Matrix.mulVec dotProduct mask y
    by_cases hr : r i <;> simp [hr, ite_and, mul_ite]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  change ‖(toLp 2 ((mask A r c) *ᵥ x) : EuclideanSpace ℂ I)‖ ^ 2 ≤ _
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ i, ‖(A *ᵥ y) i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      change ‖((mask A r c) *ᵥ x) i‖ ^ 2 ≤ _
      rw [he]
      split_ifs
      · rfl
      · simpa using sq_nonneg ‖(A *ᵥ y) i‖
    _ ≤ ‖A‖ ^ 2 * ∑ j, ‖y j‖ ^ 2 := complex_sum_sq_matrix_action_le A y
    _ ≤ _ := mul_le_mul_of_nonneg_left hy (sq_nonneg ‖A‖)

/-
Mathematical definition (normal notation): For A ∈ ℂ^(I × I); R ∈ ℝ, define

trim(A, R) := mask(A, ((i ↦ rowEnergy(A, i) ≤ R²)), ((j ↦ columnEnergy(A, j) ≤ R²))).
-/
def trim (A : Matrix I I ℂ) (R : ℝ) : Matrix I I ℂ :=
  mask A (fun i => rowEnergy A i ≤ R ^ 2) (fun j => columnEnergy A j ≤ R ^ 2)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); R ∈ ℝ, we have

opNorm(trim(A, R)) ≤ opNorm(A).
-/
theorem trim_opNorm_le (A : Matrix I I ℂ) (R : ℝ) : opNorm (trim A R) ≤ opNorm A :=
  div_le_div_of_nonneg_right (mask_norm_le _ _ _) (Nat.cast_nonneg _)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); R ∈ ℝ; i ∈ I, we have

rowEnergy(trim(A, R), i) ≤ R².
-/
theorem trim_rowEnergy_le (A : Matrix I I ℂ) (R : ℝ) (i : I) :
    rowEnergy (trim A R) i ≤ R ^ 2 := by
  by_cases hi : rowEnergy A i ≤ R ^ 2
  · exact (uavg_mono (mask_energy_pointwise A _ _ i)).trans hi
  · change (uavg fun j => ‖trim A R i j‖ ^ 2) ≤ R ^ 2
    simpa [trim, mask, hi] using sq_nonneg R

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); R ∈ ℝ; j ∈ I, we have

columnEnergy(trim(A, R), j) ≤ R².
-/
theorem trim_columnEnergy_le (A : Matrix I I ℂ) (R : ℝ) (j : I) :
    columnEnergy (trim A R) j ≤ R ^ 2 := by
  by_cases hj : columnEnergy A j ≤ R ^ 2
  · exact (uavg_mono (fun i => mask_energy_pointwise A _ _ i j)).trans hj
  · change (uavg fun i => ‖trim A R i j‖ ^ 2) ≤ R ^ 2
    simpa [trim, mask, hj] using sq_nonneg R

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); R ∈ ℝ, we have

energy(trim(A, R)) ≤ energy(A).
-/
theorem trim_energy_le (A : Matrix I I ℂ) (R : ℝ) : energy (trim A R) ≤ energy A :=
  uavg_mono (fun i => uavg_mono (mask_energy_pointwise A _ _ i))

/-- Preserve phase and cap only the modulus. -/
/-
Mathematical definition (normal notation): For L ∈ ℝ; z ∈ ℂ, define

cap(L, z) := { z if ‖ z‖ ≤ L,; L / ‖ z‖ · z otherwise }.
-/
def cap (L : ℝ) (z : ℂ) : ℂ := if ‖z‖ ≤ L then z else (L / ‖z‖ : ℝ) • z

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): Radial truncation of a complex number to radius L ≥ 0 has magnitude |cap_L(z)| = min(|z|,L). -/
theorem cap_norm (L : ℝ) (hL : 0 ≤ L) (z : ℂ) : ‖cap L z‖ = min ‖z‖ L := by
  unfold cap
  split_ifs with h
  · exact (min_eq_left h).symm
  · have hz : 0 < ‖z‖ := lt_of_le_of_lt hL (lt_of_not_ge h)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hL hz.le),
      div_mul_cancel₀ _ hz.ne', min_eq_right (le_of_not_ge h)]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For L ∈ ℝ; z ∈ ℂ, assume 0 ≤ L. Then

‖ cap(L, z)‖ ≤ ‖ z‖.
-/
theorem cap_norm_le (L : ℝ) (hL : 0 ≤ L) (z : ℂ) : ‖cap L z‖ ≤ ‖z‖ := by
  rw [cap_norm L hL]
  exact min_le_left _ _

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For L ∈ ℝ; z ∈ ℂ, assume 0 ≤ L. Then

‖ cap(L, z)‖ ≤ L.
-/
theorem cap_norm_le_level (L : ℝ) (hL : 0 ≤ L) (z : ℂ) : ‖cap L z‖ ≤ L := by
  rw [cap_norm L hL]
  exact min_le_right _ _

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For L ∈ ℝ, we have

cap(L, 0) = 0.
-/
@[simp] theorem cap_zero (L : ℝ) : cap L 0 = 0 := by
  simp [cap]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For L ∈ ℝ; z ∈ ℂ, assume 0 < L. Then

‖ z - cap(L, z)‖ ≤ (‖ z‖)² / L.
-/
theorem cap_error_le (L : ℝ) (hL : 0 < L) (z : ℂ) :
    ‖z - cap L z‖ ≤ ‖z‖ ^ 2 / L := by
  unfold cap
  split_ifs with h
  · simp only [sub_self, norm_zero]
    positivity
  · have hz : 0 < ‖z‖ := lt_trans hL (lt_of_not_ge h)
    have hfrac : L / ‖z‖ ≤ 1 := (div_le_one hz).2 (le_of_not_ge h)
    have he : z - (L / ‖z‖ : ℝ) • z = (1 - L / ‖z‖ : ℝ) • z := by
      rw [sub_smul, one_smul]
    rw [he, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hfrac)]
    apply (le_div_iff₀ hL).2
    have hcancel : (L / ‖z‖) * ‖z‖ = L := div_mul_cancel₀ _ hz.ne'
    nlinarith

/-
Mathematical definition (normal notation): For A ∈ ℂ^(I × I); R, L ∈ ℝ, define

capped(A, R, L) := (i, j ↦ cap(L, trim(A, R, i, j))).
-/
def capped (A : Matrix I I ℂ) (R L : ℝ) : Matrix I I ℂ := fun i j => cap L (trim A R i j)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); R, L ∈ ℝ; i ∈ I, assume 0 ≤ L. Then

rowEnergy(capped(A, R, L), i) ≤ R².
-/
theorem capped_rowEnergy_le (A : Matrix I I ℂ) (R L : ℝ) (hL : 0 ≤ L) (i : I) :
    rowEnergy (capped A R L) i ≤ R ^ 2 := by
  refine (uavg_mono (fun j => ?_)).trans (trim_rowEnergy_le A R i)
  exact pow_le_pow_left₀ (norm_nonneg _) (cap_norm_le L hL _) 2

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); R, L ∈ ℝ; j ∈ I, assume 0 ≤ L. Then

columnEnergy(capped(A, R, L), j) ≤ R².
-/
theorem capped_columnEnergy_le (A : Matrix I I ℂ) (R L : ℝ) (hL : 0 ≤ L) (j : I) :
    columnEnergy (capped A R L) j ≤ R ^ 2 := by
  refine (uavg_mono (fun i => ?_)).trans (trim_columnEnergy_le A R j)
  exact pow_le_pow_left₀ (norm_nonneg _) (cap_norm_le L hL _) 2

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); R, L ∈ ℝ, assume 0 ≤ L. Then

energy(capped(A, R, L)) ≤ energy(A).
-/
theorem capped_energy_le (A : Matrix I I ℂ) (R L : ℝ) (hL : 0 ≤ L) :
    energy (capped A R L) ≤ energy A := by
  refine (uavg_mono (fun i => uavg_mono (fun j => ?_))).trans (trim_energy_le A R)
  exact pow_le_pow_left₀ (norm_nonneg _) (cap_norm_le L hL _) 2

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); R, L ∈ ℝ; i, j ∈ I, assume 0 ≤ L. Then

‖ capped(A, R, L, i, j)‖ ≤ L.
-/
theorem capped_entry_le (A : Matrix I I ℂ) (R L : ℝ) (hL : 0 ≤ L) (i j : I) :
    ‖capped A R L i j‖ ≤ L :=
  cap_norm_le_level L hL _

/-- The complex Schur test with a common row and column absolute-sum bound. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); B ∈ ℝ, assume 0 ≤ B; ∀ i, (∑ⱼ (‖ A(i, j)‖)) ≤ B; ∀ j, (∑ᵢ (‖ A(i, j)‖)) ≤ B. Then

‖ A‖ ≤ B.
-/
theorem norm_le_row_column_sum (A : Matrix I I ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i, (∑ j, ‖A i j‖) ≤ B) (hcol : ∀ j, (∑ i, ‖A i j‖) ≤ B) :
    ‖A‖ ≤ B := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro x
  have hpoint (i : I) : ‖(A *ᵥ x) i‖ ^ 2 ≤ B * ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 := by
    have hsum : ‖(A *ᵥ x) i‖ ≤ ∑ j, ‖A i j‖ * ‖x j‖ := by
      simpa only [Matrix.mulVec, dotProduct, norm_mul] using
        norm_sum_le Finset.univ (fun j => A i j * x j)
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.univ : Finset I)
      (r := fun j => ‖A i j‖ * ‖x j‖)
      (f := fun j => ‖A i j‖) (g := fun j => ‖A i j‖ * ‖x j‖ ^ 2)
      (fun j _ => norm_nonneg _) (fun j _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
      (by intro j _; ring)
    exact (pow_le_pow_left₀ (norm_nonneg _) hsum 2).trans
      (hcs.trans (mul_le_mul_of_nonneg_right (hrow i)
        (Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)))))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg x))).mp
  change ‖(toLp 2 (A *ᵥ x) : EuclideanSpace ℂ I)‖ ^ 2 ≤ _
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2]
  simp only [ofLp_toLp]
  calc
    _ ≤ ∑ i, B * ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = B * ∑ j, (∑ i, ‖A i j‖) * ‖x j‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ B * ∑ j, B * ‖x j‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _))
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The same test in the uniform-table normalization used in the paper. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); B ∈ ℝ, assume I ≠ ∅; 0 ≤ B; ∀ i, 𝔼ⱼ [‖ A(i, j)‖] ≤ B; ∀ j, 𝔼ᵢ [‖ A(i, j)‖] ≤ B. Then

opNorm(A) ≤ B.
-/
theorem opNorm_le_row_column_average [Nonempty I] (A : Matrix I I ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i, uavg (fun j => ‖A i j‖) ≤ B)
    (hcol : ∀ j, uavg (fun i => ‖A i j‖) ≤ B) : opNorm A ≤ B := by
  have hd : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hd).2
  apply norm_le_row_column_sum A _ (mul_nonneg hB hd.le)
  · intro i
    apply (div_le_iff₀ hd).mp
    simpa [uavg, div_eq_mul_inv, mul_comm] using hrow i
  · intro j
    apply (div_le_iff₀ hd).mp
    simpa [uavg, div_eq_mul_inv, mul_comm] using hcol j

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); R, L ∈ ℝ; i ∈ I, assume 0 < L. Then

𝔼ⱼ [‖ trim(A, R, i, j) - capped(A, R, L, i, j)‖] ≤ R² / L.
-/
theorem cap_error_row_average (A : Matrix I I ℂ) (R L : ℝ) (hL : 0 < L) (i : I) :
    uavg (fun j => ‖trim A R i j - capped A R L i j‖) ≤ R ^ 2 / L := by
  calc
    _ ≤ uavg (fun j => ‖trim A R i j‖ ^ 2 / L) := uavg_mono (fun j => cap_error_le L hL _)
    _ = rowEnergy (trim A R) i / L := by
      simp only [rowEnergy, div_eq_mul_inv, uavg_mul_const]
    _ ≤ _ := div_le_div_of_nonneg_right (trim_rowEnergy_le A R i) hL.le

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); R, L ∈ ℝ; j ∈ I, assume 0 < L. Then

𝔼ᵢ [‖ trim(A, R, i, j) - capped(A, R, L, i, j)‖] ≤ R² / L.
-/
theorem cap_error_column_average (A : Matrix I I ℂ) (R L : ℝ) (hL : 0 < L) (j : I) :
    uavg (fun i => ‖trim A R i j - capped A R L i j‖) ≤ R ^ 2 / L := by
  calc
    _ ≤ uavg (fun i => ‖trim A R i j‖ ^ 2 / L) := uavg_mono (fun i => cap_error_le L hL _)
    _ = columnEnergy (trim A R) j / L := by
      simp only [columnEnergy, div_eq_mul_inv, uavg_mul_const]
    _ ≤ _ := div_le_div_of_nonneg_right (trim_columnEnergy_le A R j) hL.le

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); R, L ∈ ℝ, assume I ≠ ∅; 0 < L. Then

opNorm((trim(A, R) - capped(A, R, L))) ≤ R² / L.
-/
theorem cap_error_opNorm_le [Nonempty I] (A : Matrix I I ℂ) (R L : ℝ) (hL : 0 < L) :
    opNorm (trim A R - capped A R L) ≤ R ^ 2 / L :=
  opNorm_le_row_column_average _ _ (div_nonneg (sq_nonneg _) hL.le)
    (cap_error_row_average A R L hL) (cap_error_column_average A R L hL)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); R, L ∈ ℝ, assume I ≠ ∅; 0 < L. Then

opNorm(capped(A, R, L)) ≤ opNorm(A) + R² / L.
-/
theorem capped_opNorm_le [Nonempty I] (A : Matrix I I ℂ) (R L : ℝ) (hL : 0 < L) :
    opNorm (capped A R L) ≤ opNorm A + R ^ 2 / L := by
  have he : trim A R - (trim A R - capped A R L) = capped A R L := by abel
  have h := norm_sub_le (trim A R) (trim A R - capped A R L)
  rw [he] at h
  have h' := div_le_div_of_nonneg_right h (Nat.cast_nonneg (Fintype.card I) :
    (0 : ℝ) ≤ Fintype.card I)
  rw [add_div] at h'
  exact h'.trans (add_le_add (trim_opNorm_le A R) (cap_error_opNorm_le A R L hL))

/-
Mathematical definition (normal notation): For A ∈ ℂ^(I × I); R ∈ ℝ; i ∈ I, define

deletedRow(A, R, i) := { 0 if rowEnergy(A, i) ≤ R²,; 1 otherwise }.
-/
def deletedRow (A : Matrix I I ℂ) (R : ℝ) (i : I) : ℝ :=
  if rowEnergy A i ≤ R ^ 2 then 0 else 1

/-
Mathematical definition (normal notation): For A ∈ ℂ^(I × I); R ∈ ℝ; j ∈ I, define

deletedColumn(A, R, j) := { 0 if columnEnergy(A, j) ≤ R²,; 1 otherwise }.
-/
def deletedColumn (A : Matrix I I ℂ) (R : ℝ) (j : I) : ℝ :=
  if columnEnergy A j ≤ R ^ 2 then 0 else 1

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ I → ℝ; B ∈ ℝ, assume ∀ i, 0 ≤ f(i); 0 < B. Then

𝔼ᵢ [{ 0 if f(i) ≤ B,; 1 otherwise }] ≤ 𝔼ᵤ [f(u)] / B.
-/
private theorem markov_average (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) (B : ℝ) (hB : 0 < B) :
    uavg (fun i => if f i ≤ B then (0 : ℝ) else 1) ≤ uavg f / B := by
  calc
    _ ≤ uavg (fun i => f i / B) := by
      apply uavg_mono
      intro i
      split_ifs with h
      · exact div_nonneg (hf i) hB.le
      · exact (one_le_div hB).2 (le_of_not_ge h)
    _ = _ := by simp only [div_eq_mul_inv, uavg_mul_const]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); R ∈ ℝ, assume 0 < R. Then

𝔼ᵤ [deletedRow(A, R, u)] ≤ energy(A) / R².
-/
theorem deletedRow_average_le (A : Matrix I I ℂ) (R : ℝ) (hR : 0 < R) :
    uavg (deletedRow A R) ≤ energy A / R ^ 2 :=
  markov_average _ (rowEnergy_nonneg A) _ (sq_pos_of_pos hR)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); R ∈ ℝ, assume 0 < R. Then

𝔼ᵤ [deletedColumn(A, R, u)] ≤ energy(A) / R².
-/
theorem deletedColumn_average_le (A : Matrix I I ℂ) (R : ℝ) (hR : 0 < R) :
    uavg (deletedColumn A R) ≤ energy A / R ^ 2 := by
  change uavg (fun j => if columnEnergy A j ≤ R ^ 2 then 0 else 1) ≤ energy A / R ^ 2
  simpa only [columnEnergy_mean] using
    markov_average _ (columnEnergy_nonneg A) _ (sq_pos_of_pos hR)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V ∈ Z → ℂ^(I × I); R, H ∈ ℝ, assume 0 < R; (∑_z (energy(V(z)))) ≤ H. Then

(∑_z ((𝔼ᵤ [deletedRow(V(z), R, u)] + 𝔼ᵥ [deletedColumn(V(z), R, v)]))) ≤ 2 · H / R².
-/
theorem deleted_mass_le (V : Z → Matrix I I ℂ) (R H : ℝ) (hR : 0 < R)
    (henergy : (∑ z, energy (V z)) ≤ H) :
    (∑ z, (uavg (deletedRow (V z) R) + uavg (deletedColumn (V z) R))) ≤
      2 * H / R ^ 2 := by
  calc
    _ ≤ ∑ z, (energy (V z) / R ^ 2 + energy (V z) / R ^ 2) :=
      Finset.sum_le_sum (fun z _ => add_le_add
        (deletedRow_average_le (V z) R hR) (deletedColumn_average_le (V z) R hR))
    _ = 2 * (∑ z, energy (V z)) / R ^ 2 := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_div]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left henergy (by norm_num)) (sq_nonneg R)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); R, L ∈ ℝ, assume 0 < L. Then

𝔼ᵢ [𝔼ⱼ [‖ trim(A, R, i, j) - capped(A, R, L, i, j)‖]] ≤ energy(A) / L.
-/
theorem cap_error_mean_le (A : Matrix I I ℂ) (R L : ℝ) (hL : 0 < L) :
    uavg (fun i => uavg (fun j => ‖trim A R i j - capped A R L i j‖)) ≤ energy A / L := by
  calc
    _ ≤ uavg (fun i => uavg (fun j => ‖trim A R i j‖ ^ 2 / L)) :=
      uavg_mono (fun i => uavg_mono (fun j => cap_error_le L hL _))
    _ = energy (trim A R) / L := by
      simp only [energy, rowEnergy, div_eq_mul_inv, uavg_mul_const]
      rfl
    _ ≤ _ := div_le_div_of_nonneg_right (trim_energy_le A R) hL.le

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V ∈ Z → ℂ^(I × I); R, L, H ∈ ℝ, assume 0 ≤ L; (∑_z (energy(V(z)))) ≤ H. Then

(∑_z (energy(capped(V(z), R, L)))) ≤ H.
-/
theorem capped_family_energy_le (V : Z → Matrix I I ℂ) (R L H : ℝ) (hL : 0 ≤ L)
    (henergy : (∑ z, energy (V z)) ≤ H) :
    (∑ z, energy (capped (V z) R L)) ≤ H :=
  (Finset.sum_le_sum (fun z _ => capped_energy_le (V z) R L hL)).trans henergy

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V ∈ Z → ℂ^(I × I); R, L, H ∈ ℝ, assume 0 < L; (∑_z (energy(V(z)))) ≤ H. Then

(∑_z (𝔼ᵢ [𝔼ⱼ [‖ trim(V(z), R, i, j) - capped(V(z), R, L, i, j)‖]])) ≤ H / L.
-/
theorem cap_error_family_mean_le (V : Z → Matrix I I ℂ) (R L H : ℝ) (hL : 0 < L)
    (henergy : (∑ z, energy (V z)) ≤ H) :
    (∑ z, uavg (fun i => uavg (fun j =>
      ‖trim (V z) R i j - capped (V z) R L i j‖))) ≤ H / L := by
  calc
    _ ≤ ∑ z, energy (V z) / L := Finset.sum_le_sum (fun z _ => cap_error_mean_le _ _ _ hL)
    _ = (∑ z, energy (V z)) / L := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right henergy hL.le

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); R, L ∈ ℝ; i, j ∈ I, assume A(i, j) = 0. Then

capped(A, R, L, i, j) = 0.
-/
theorem capped_preserves_zero (A : Matrix I I ℂ) (R L : ℝ) (i j : I) (h : A i j = 0) :
    capped A R L i j = 0 := by
  simp [capped, trim, mask, h]

/-
Mathematical definition (normal notation): For A ∈ ℂ^(I × I); R ∈ ℝ; xy ∈ I × I, define

deleted(A, R, xy) := { 0 if rowEnergy(A, (xy)₁) ≤ R² ∧ columnEnergy(A, (xy)₂) ≤ R²,; 1 otherwise }.
-/
def deleted (A : Matrix I I ℂ) (R : ℝ) (xy : I × I) : ℝ :=
  if rowEnergy A xy.1 ≤ R ^ 2 ∧ columnEnergy A xy.2 ≤ R ^ 2 then 0 else 1

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); R ∈ ℝ; xy ∈ I × I, we have

deleted(A, R, xy) ≤ deletedRow(A, R, (xy)₁) + deletedColumn(A, R, (xy)₂).
-/
theorem deleted_le_sum (A : Matrix I I ℂ) (R : ℝ) (xy : I × I) :
    deleted A R xy ≤ deletedRow A R xy.1 + deletedColumn A R xy.2 := by
  unfold deleted deletedRow deletedColumn
  split_ifs <;> norm_num <;> tauto

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟((I × I)); A ∈ ℂ^(I × I); R ∈ ℝ, assume I ≠ ∅; ((Prod)₁_*P) = FiniteDistribution.uniform; ((Prod)₂_*P) = FiniteDistribution.uniform. Then

𝔼_(u ← P) [deleted(A, R, u)] ≤ 𝔼ᵥ [deletedRow(A, R, v)] + 𝔼_w [deletedColumn(A, R, w)].
-/
theorem deleted_expect_le [Nonempty I] (P : FiniteDistribution (I × I))
    (hleft : P.map Prod.fst = FiniteDistribution.uniform) (hright : P.map Prod.snd = FiniteDistribution.uniform)
    (A : Matrix I I ℂ) (R : ℝ) :
    P.expect (deleted A R) ≤ uavg (deletedRow A R) + uavg (deletedColumn A R) := by
  refine (P.expect_mono (deleted_le_sum A R)).trans_eq ?_
  rw [expect_add]
  rw [← expect_map P Prod.fst, ← expect_map P Prod.snd, hleft, hright]
  rw [← uavg_eq_expect_uniform, ← uavg_eq_expect_uniform]

/-- Row/column trimming costs the square root of the deleted marginal mass for any normalized dual test and every answer weight in `[0,1]`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟((I × I)); V, W ∈ Z → ℂ^(I × I); k ∈ Z → I × I → ℝ; R, H ∈ ℝ, assume I ≠ ∅; ((Prod)₁_*P) = FiniteDistribution.uniform; ((Prod)₂_*P) = FiniteDistribution.uniform; ∀ z, xy, 0 ≤ k(z, xy) ∧ k(z, xy) ≤ 1; 0 < R; 0 ≤ H; (∑_z (energy(V(z)))) ≤ H; 𝔼_(xy ← P) [∑_z ((‖ W(z, (xy)₁, (xy)₂)‖)²)] ≤ 1. Then

(∑_z (𝔼_(xy ← P) [‖ W(z, (xy)₁, (xy)₂)‖ · (k(z, xy) · deleted(V(z), R, xy))])) ≤ √(2 · H) / R.
-/
theorem trim_pairing_cost [Nonempty I] (P : FiniteDistribution (I × I))
    (hleft : P.map Prod.fst = FiniteDistribution.uniform) (hright : P.map Prod.snd = FiniteDistribution.uniform)
    (V W : Z → Matrix I I ℂ) (k : Z → I × I → ℝ)
    (hk : ∀ z xy, 0 ≤ k z xy ∧ k z xy ≤ 1)
    (R H : ℝ) (hR : 0 < R) (hH : 0 ≤ H)
    (henergy : (∑ z, energy (V z)) ≤ H)
    (hW : P.expect (fun xy => ∑ z, ‖W z xy.1 xy.2‖ ^ 2) ≤ 1) :
    (∑ z, P.expect (fun xy => ‖W z xy.1 xy.2‖ *
      (k z xy * deleted (V z) R xy))) ≤ Real.sqrt (2 * H) / R := by
  let f : Z → I × I → ℝ := fun z xy => ‖W z xy.1 xy.2‖
  let g : Z → I × I → ℝ := fun z xy => k z xy * deleted (V z) R xy
  have hgb (z : Z) (xy : I × I) : g z xy ^ 2 ≤ deleted (V z) R xy := by
    dsimp [g, deleted]
    split_ifs
    · norm_num
    · have h := hk z xy; nlinarith
  have hg : P.expect (fun xy => ∑ z, g z xy ^ 2) ≤ 2 * H / R ^ 2 := by
    rw [expect_sum]
    calc
      _ ≤ ∑ z, P.expect (deleted (V z) R) :=
        Finset.sum_le_sum (fun z _ => P.expect_mono (hgb z))
      _ ≤ ∑ z, (uavg (deletedRow (V z) R) + uavg (deletedColumn (V z) R)) :=
        Finset.sum_le_sum (fun z _ => deleted_expect_le P hleft hright (V z) R)
      _ ≤ _ := deleted_mass_le V R H hR henergy
  have hf : familyRms P f ≤ 1 := by
    apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1)).2
    simpa [f] using hW
  have hg' : familyRms P g ≤ Real.sqrt (2 * H) / R := by
    have h := Real.sqrt_le_sqrt hg
    rw [Real.sqrt_div (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hH), Real.sqrt_sq hR.le] at h
    exact h
  have h := abs_sum_expect_mul_le_familyRms_mul_familyRms P f g
  have hproduct := mul_le_mul hf hg' (familyRms_nonneg P g) (by norm_num : (0 : ℝ) ≤ 1)
  have hno : 0 ≤ ∑ z, P.expect (fun xy => f z xy * g z xy) := by
    apply Finset.sum_nonneg
    intro z _
    apply P.expect_nonneg
    intro xy
    apply mul_nonneg (norm_nonneg _)
    apply mul_nonneg (hk z xy).1
    unfold deleted
    split_ifs <;> norm_num
  rw [abs_of_nonneg hno] at h
  exact h.trans (by simpa using hproduct)

end

end CircuitCompiler.GateTruncation
