import Proofs.Compiler.Foundations.MatrixRefreshing.Analysis.FourthRootProduct
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Discrepancy
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Transitivity
import Proofs.Compiler.Foundations.LinearAlgebra.GramMixing
import Proofs.Compiler.Foundations.LinearAlgebra.PairOrbits



/-!
# Random-matrix mixing on nonzero finite-field vectors

The covariance table of a uniformly sampled general linear matrix is constant on independent ordered vector pairs. Its row mean is zero for a centered input. This leaves only the regular projective relation, whose row size is `(fieldCard F) - 1`.
-/

set_option autoImplicit false

open scoped BigOperators

noncomputable section

namespace TableAnalysis

open Refresh MatrixRefresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- Multiplication by a fixed invertible matrix permutes the nonzero rows. -/
/- Mathematical definition (normal notation): For invertible M, the row map ℓ ↦ ℓ · M is a bijection of U, with inverse ℓ ↦ ℓ · M⁻¹. -/
def rowEquiv (M : Refresh.«GL» F n) : U F n ≃ U F n where
  toFun l := rowRefresh l M
  invFun l := rowRefresh l M⁻¹
  left_inv l := by change rowRefresh (rowRefresh l M) M⁻¹ = l; rw [rowRefresh_mul]; simp
  right_inv l := by change rowRefresh (rowRefresh l M⁻¹) M = l; rw [rowRefresh_mul]; simp

/-- Fixed invertible matrices preserve the uniform nonzero-vector average. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For M ∈ GLₙ(F); f ∈ U(F, n) → ℝ, we have

𝔼ₗ [f(rowRefresh(l, M))] = 𝔼ᵤ [f(u)].
-/
theorem uavg_rowRefresh (M : Refresh.«GL» F n) (f : U F n → ℝ) :
    uavg (fun l => f (rowRefresh l M)) = uavg f :=
  uavg_equiv (rowEquiv M) f

/-- Left multiplication preserves the uniform group average. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ GLₙ(F); f ∈ GLₙ(F) → ℝ, we have

𝔼_M [f((A · M))] = 𝔼ᵤ [f(u)].
-/
theorem uavg_mulLeft (A : Refresh.«GL» F n) (f : Refresh.«GL» F n → ℝ) :
    uavg (fun M => f (A * M)) = uavg f :=
  uavg_equiv (Equiv.mulLeft A) f

/-- A fixed row becomes uniform after sampling an independent uniform matrix. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For l ∈ U(F, n); f ∈ U(F, n) → ℝ, we have

𝔼_(M ∈ GLₙ(F)) [f(rowRefresh(l, M))] = 𝔼ᵤ [f(u)].
-/
theorem uavg_random_rowRefresh (l : U F n) (f : U F n → ℝ) :
    uavg (fun M : Refresh.«GL» F n => f (rowRefresh l M)) = uavg f := by
  letI : Nonempty (U F n) := ⟨l⟩
  have hc (k : U F n) :
      uavg (fun M : Refresh.«GL» F n => f (rowRefresh k M)) =
        uavg (fun M : Refresh.«GL» F n => f (rowRefresh l M)) := by
    obtain ⟨A, hA⟩ := exists_rowRefresh_eq l k
    rw [← hA]
    simp_rw [rowRefresh_mul]
    exact uavg_mulLeft A (fun M => f (rowRefresh l M))
  calc
    _ = uavg (fun k : U F n =>
        uavg (fun M : Refresh.«GL» F n => f (rowRefresh k M))) := by
      simp_rw [hc]
      exact (uavg_const _).symm
    _ = uavg (fun M : Refresh.«GL» F n =>
        uavg (fun k : U F n => f (rowRefresh k M))) := uavg_comm _
    _ = uavg f := by simp_rw [uavg_rowRefresh]; exact uavg_const _

/-- The covariance table of the random row action. -/
/-
Mathematical definition (normal notation): For b ∈ U(F, n) → ℝ; l, k ∈ U(F, n), define

rowCovariance(b, l, k) := 𝔼_(M ∈ GLₙ(F)) [b(rowRefresh(l, M)) · b(rowRefresh(k, M))].
-/
def rowCovariance (b : U F n → ℝ) (l k : U F n) : ℝ :=
  uavg (fun M : Refresh.«GL» F n => b (rowRefresh l M) * b (rowRefresh k M))

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For b ∈ U(F, n) → ℝ; l, k ∈ U(F, n), we have

rowCovariance(b, l, k) = rowCovariance(b, k, l) .
-/
theorem rowCovariance_symm (b : U F n → ℝ) (l k : U F n) :
    rowCovariance b l k = rowCovariance b k l := by
  unfold rowCovariance
  apply uavg_congr
  intro M
  ring

/-- Simultaneously changing both input rows preserves their covariance. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For b ∈ U(F, n) → ℝ; l, k ∈ U(F, n); A ∈ GLₙ(F), we have

rowCovariance(b, rowRefresh(l, A), rowRefresh(k, A)) = rowCovariance(b, l, k) .
-/
theorem rowCovariance_refresh (b : U F n → ℝ) (l k : U F n) (A : Refresh.«GL» F n) :
    rowCovariance b (rowRefresh l A) (rowRefresh k A) = rowCovariance b l k := by
  unfold rowCovariance
  simp_rw [rowRefresh_mul]
  exact uavg_mulLeft A (fun M => b (rowRefresh l M) * b (rowRefresh k M))

/-- A centered function gives a covariance table with zero row mean. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For b ∈ U(F, n) → ℝ; l ∈ U(F, n), assume 𝔼ᵤ [b(u)] = 0. Then

𝔼ₖ [rowCovariance(b, l, k)] = 0.
-/
theorem rowCovariance_row_mean_zero (b : U F n → ℝ) (hb : uavg b = 0) (l : U F n) :
    uavg (fun k => rowCovariance b l k) = 0 := by
  unfold rowCovariance
  rw [uavg_comm]
  simp_rw [uavg_const_mul, uavg_rowRefresh, hb, mul_zero]
  exact uavg_zero

/-- Cauchy-Schwarz bounds every covariance entry by the uniform mean square. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For b ∈ U(F, n) → ℝ; l, k ∈ U(F, n), we have

|rowCovariance(b, l, k)| ≤ 𝔼ᵥ [(b(v))²].
-/
theorem abs_rowCovariance_le (b : U F n → ℝ) (l k : U F n) :
    |rowCovariance b l k| ≤ uavg (fun v => b v ^ 2) := by
  have h := uavg_mul_sq_le
    (fun M : Refresh.«GL» F n => b (rowRefresh l M))
    (fun M : Refresh.«GL» F n => b (rowRefresh k M))
  rw [uavg_random_rowRefresh l (fun v => b v ^ 2),
    uavg_random_rowRefresh k (fun v => b v ^ 2)] at h
  exact (sq_le_sq₀ (abs_nonneg _) (uavg_nonneg fun v => sq_nonneg (b v))).mp
    (by simpa only [rowCovariance, sq_abs, ← sq] using h)

/-- Expanding a squared random correlation gives the covariance quadratic form. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ U(F, n) → ℝ, we have

𝔼_(M ∈ GLₙ(F)) [(𝔼ₗ [a(l) · b(rowRefresh(l, M))])²] = 𝔼ₗ [𝔼ₖ [a(l) · a(k) · rowCovariance(b, l, k)]].
-/
theorem random_correlation_square_eq (a b : U F n → ℝ) :
    uavg (fun M : Refresh.«GL» F n =>
      (uavg (fun l => a l * b (rowRefresh l M))) ^ 2) =
    uavg (fun l => uavg (fun k => a l * a k * rowCovariance b l k)) := by
  have hp (M : Refresh.«GL» F n) :
      (uavg (fun l => a l * b (rowRefresh l M))) ^ 2 =
      uavg (fun l => uavg (fun k =>
        a l * a k * (b (rowRefresh l M) * b (rowRefresh k M)))) := by
    rw [sq, uavg_mul_uavg]
    apply uavg_congr
    intro l
    apply uavg_congr
    intro k
    ring
  simp_rw [hp]
  rw [uavg_comm]
  apply uavg_congr
  intro l
  rw [uavg_comm]
  simp_rw [uavg_const_mul]
  rfl

section RegularTables

variable {X : Type*} [Fintype X]

/-- A table dominated by a regular symmetric nonnegative table has a quadratic bound with that table's row mass. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P, K ∈ X → X → ℝ; r, C ∈ ℝ; a ∈ X → ℝ, assume ∀ i, j, 0 ≤ P(i, j); ∀ i, j, P(i, j) = P(j, i); ∀ i, ∑ⱼ (P(i, j)) = r; 0 ≤ C; ∀ i, j, |K(i, j)| ≤ C · P(i, j). Then

|∑ᵢ (∑ⱼ (K(i, j) · a(i) · a(j)))| ≤ C · r · ∑ᵢ ((a(i))²) .
-/
theorem sparse_table_quadratic_bound (P K : X → X → ℝ) (r C : ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hsym : ∀ i j, P i j = P j i)
    (hrow : ∀ i, ∑ j, P i j = r) (hC : 0 ≤ C)
    (hK : ∀ i j, |K i j| ≤ C * P i j) (a : X → ℝ) :
    |∑ i, ∑ j, K i j * a i * a j| ≤ C * r * ∑ i, a i ^ 2 := by
  have hquad := regular_table_quadratic_abs_le P r hP hsym hrow (fun i => |a i|)
  have hnonneg : 0 ≤ ∑ i, ∑ j, P i j * |a i| * |a j| := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (mul_nonneg (hP i j) (abs_nonneg _)) (abs_nonneg _)
  rw [abs_of_nonneg hnonneg] at hquad
  simp only [sq_abs] at hquad
  calc
    _ ≤ ∑ i, |∑ j, K i j * a i * a j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |K i j * a i * a j| :=
      Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, C * (P i j * |a i| * |a j|) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul]
      have h := mul_le_mul_of_nonneg_right (hK i j)
        (mul_nonneg (abs_nonneg (a i)) (abs_nonneg (a j)))
      nlinarith
    _ = C * (∑ i, ∑ j, P i j * |a i| * |a j|) := by simp [Finset.mul_sum]
    _ ≤ C * (r * ∑ i, a i ^ 2) := mul_le_mul_of_nonneg_left hquad hC
    _ = _ := by ring

variable [Nonempty X]

/-- The value of a zero-row-sum table outside a regular relation is small when every entry of the table is bounded. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For R ∈ X → X → Prop; K ∈ X → X → ℝ; r, B, t ∈ ℝ, assume DecidableRel(R); ∀ i, ∑ⱼ (({ 1 if R(i, j),; 0 otherwise })) = r; ∀ i, ∑ⱼ (K(i, j)) = 0; ∀ i, j, |K(i, j)| ≤ B; ∀ i, j, ¬ (R(i, j)) → K(i, j) = t; 0 < |X| - r. Then

|t| ≤ r · B / (|X| - r).
-/
theorem constant_off_relation_bound (R : X → X → Prop) [DecidableRel R]
    (K : X → X → ℝ) (r B t : ℝ)
    (hrow : ∀ i, ∑ j, (if R i j then (1 : ℝ) else 0) = r)
    (hzero : ∀ i, ∑ j, K i j = 0) (hK : ∀ i j, |K i j| ≤ B)
    (hoff : ∀ i j, ¬ R i j → K i j = t)
    (hD : 0 < (Fintype.card X : ℝ) - r) :
    |t| ≤ r * B / ((Fintype.card X : ℝ) - r) := by
  let i : X := Classical.choice inferInstance
  let P : X → X → ℝ := fun x y => if R x y then 1 else 0
  have hp : ∑ j, P i j = r := hrow i
  have hdecomp : ∑ j, K i j = (∑ j, P i j * K i j) +
      t * ((Fintype.card X : ℝ) - r) := by
    calc
      _ = ∑ j, (P i j * K i j + t * (1 - P i j)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : R i j
        · simp [P, h]
        · simp [P, h, hoff i j h]
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hp]
        simp
  have hdep : |∑ j, P i j * K i j| ≤ r * B := by
    calc
      _ ≤ ∑ j, |P i j * K i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, P i j * B := by
        apply Finset.sum_le_sum
        intro j _
        by_cases h : R i j
        · simpa [P, h] using hK i j
        · simp [P, h]
      _ = r * B := by rw [← Finset.sum_mul, hp]
  rw [hzero i] at hdecomp
  have he : (∑ j, P i j * K i j) = -t * ((Fintype.card X : ℝ) - r) := by
    linarith
  rw [he, abs_mul, abs_neg, abs_of_pos hD] at hdep
  exact (le_div_iff₀ hD).mpr hdep

/-- Centering removes a constant table. Combining that fact with a regular relation gives the sharp two-orbit quadratic estimate. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For R ∈ X → X → Prop; K ∈ X → X → ℝ; r, B, t ∈ ℝ; a ∈ X → ℝ, assume DecidableRel(R); ∀ i, j, R(i, j) ⇔ R(j, i); ∀ i, ∑ⱼ (({ 1 if R(i, j),; 0 otherwise })) = r; 0 ≤ r; 0 ≤ B; ∀ i, ∑ⱼ (K(i, j)) = 0; ∀ i, j, |K(i, j)| ≤ B; ∀ i, j, ¬ (R(i, j)) → K(i, j) = t; 0 < |X| - r; 𝔼ᵤ [a(u)] = 0. Then

|𝔼ᵢ [𝔼ⱼ [K(i, j) · a(i) · a(j)]]| ≤ r / (|X| - r) · 𝔼ᵢ [(a(i))²] · B.
-/
theorem two_orbit_quadratic_bound (R : X → X → Prop) [DecidableRel R]
    (K : X → X → ℝ) (r B t : ℝ)
    (hsym : ∀ i j, R i j ↔ R j i)
    (hrow : ∀ i, ∑ j, (if R i j then (1 : ℝ) else 0) = r)
    (hr : 0 ≤ r) (hB : 0 ≤ B)
    (hzero : ∀ i, ∑ j, K i j = 0) (hK : ∀ i j, |K i j| ≤ B)
    (hoff : ∀ i j, ¬ R i j → K i j = t)
    (hD : 0 < (Fintype.card X : ℝ) - r)
    (a : X → ℝ) (ha : uavg a = 0) :
    |uavg (fun i => uavg (fun j => K i j * a i * a j))| ≤
      r / ((Fintype.card X : ℝ) - r) * uavg (fun i => a i ^ 2) * B := by
  let d : ℝ := Fintype.card X
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card X)
  have ht := constant_off_relation_bound R K r B t hrow hzero hK hoff hD
  let C : ℝ := B + r * B / (d - r)
  have hC : 0 ≤ C := by dsimp [C, d]; positivity
  let P : X → X → ℝ := fun i j => if R i j then 1 else 0
  have hsparse : ∀ i j, |K i j - t| ≤ C * P i j := by
    intro i j
    by_cases h : R i j
    · simp only [P, if_pos h, mul_one]
      exact (abs_sub _ _).trans (add_le_add (hK i j) ht)
    · simp [P, h, hoff i j h]
  have hpSym : ∀ i j, P i j = P j i := by
    intro i j
    simp only [P, hsym i j]
  have hquad := sparse_table_quadratic_bound P (fun i j => K i j - t) r C
    (by intro i j; dsimp [P]; split_ifs <;> norm_num) hpSym hrow hC hsparse a
  have haSum : ∑ i, a i = 0 := by
    unfold uavg at ha
    exact (mul_eq_zero.mp ha).resolve_left (inv_ne_zero (ne_of_gt hd))
  have he : (∑ i, ∑ j, (K i j - t) * a i * a j) =
      ∑ i, ∑ j, K i j * a i * a j := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    simp [← Finset.mul_sum, haSum]
  rw [he] at hquad
  unfold uavg
  simp only [← Finset.mul_sum]
  change |d⁻¹ * (d⁻¹ * (∑ i, ∑ j, K i j * a i * a j))| ≤
    r / (d - r) * (d⁻¹ * ∑ i, a i ^ 2) * B
  rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hd)]
  calc
    _ ≤ d⁻¹ * (d⁻¹ * (C * r * ∑ i, a i ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hquad (inv_nonneg.mpr hd.le)) (inv_nonneg.mpr hd.le)
    _ = _ := by
      dsimp [C]
      have hDn : d - r ≠ 0 := ne_of_gt hD
      field_simp
      ring

end RegularTables

/-- The spectral coefficient from the nonzero-vector two-orbit calculation. -/
/-
Mathematical definition (normal notation): For F a set; n ∈ ℕ, assume F is finite. define

mixingCoefficient(n) := (|F| - 1) / (|F|ⁿ - |F|).
-/
def mixingCoefficient (F : Type*) [Fintype F] (n : ℕ) : ℝ :=
  ((fieldCard F : ℝ) - 1) / ((vectorCard F n : ℝ) - (fieldCard F : ℝ))

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

0 ≤ mixingCoefficient(F, n).
-/
theorem mixingCoefficient_nonneg (hn : 2 ≤ n) : 0 ≤ mixingCoefficient F n := by
  unfold mixingCoefficient
  have hq := fieldCard_cast_ge_two (F := F)
  exact div_nonneg (by linarith) (zeroFiber_denominator_pos hn).le

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

0 < mixingCoefficient(F, n).
-/
theorem mixingCoefficient_pos (hn : 2 ≤ n) : 0 < mixingCoefficient F n := by
  unfold mixingCoefficient
  have hq := fieldCard_cast_ge_two (F := F)
  exact div_pos (by linarith) (zeroFiber_denominator_pos hn)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

mixingCoefficient(F, n) ≤ 1.
-/
theorem mixingCoefficient_le_one (hn : 2 ≤ n) : mixingCoefficient F n ≤ 1 := by
  unfold mixingCoefficient
  apply (div_le_one (zeroFiber_denominator_pos hn)).mpr
  have hN := vectorCard_real_ge_two_mul_fieldCard (F := F) hn
  linarith

/-- Every independent ordered pair has the same covariance. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For b ∈ U(F, n) → ℝ; l, k, l', k' ∈ U(F, n), assume ¬ (projectiveRel(l, k)); ¬ (projectiveRel(l', k')). Then

rowCovariance(b, l, k) = rowCovariance(b, l', k').
-/
theorem rowCovariance_independent_eq (b : U F n → ℝ)
    (l k l' k' : U F n) (h : ¬ projectiveRel l k) (h' : ¬ projectiveRel l' k') :
    rowCovariance b l k = rowCovariance b l' k' := by
  obtain ⟨M, hl, hk⟩ := exists_rowRefresh_pair_eq l k l' k'
    (pair_independent_of_not_projectiveRel l k h)
    (pair_independent_of_not_projectiveRel l' k' h')
  simpa only [hl, hk] using (rowCovariance_refresh b l k M).symm

/-- There is an independent row pair in dimension at least two. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

∃ l, k ∈ U(F, n), ¬ (projectiveRel(l, k)).
-/
theorem exists_nonprojective_pair (hn : 2 ≤ n) :
    ∃ l k : U F n, ¬ projectiveRel l k := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  let l : U F n := Classical.choice inferInstance
  have hex : ∃ k : U F n, ¬ projectiveRel l k := by
    by_contra h
    have hall : ∀ k : U F n, projectiveRel l k := by
      intro k
      by_contra hk
      exact h ⟨k, hk⟩
    have hr := projectiveIndicator_row_sum l
    simp only [projectiveIndicator, hall, if_true, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] at hr
    rw [card_U_real] at hr
    have hD := zeroFiber_denominator_pos (F := F) hn
    linarith
  obtain ⟨k, hk⟩ := hex
  exact ⟨l, k, hk⟩

/-- The random-GL mixing estimate for centered real row functions. All three averages are uniform, including the matrix average. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ U(F, n) → ℝ, assume 2 ≤ n; 𝔼ᵤ [a(u)] = 0; 𝔼ᵥ [b(v)] = 0. Then

𝔼_(M ∈ GLₙ(F)) [(𝔼ₗ [a(l) · b(rowRefresh(l, M))])²] ≤ mixingCoefficient(F, n) · 𝔼ₗ [(a(l))²] · 𝔼ₗ [(b(l))²].
-/
theorem row_mixing_centered (hn : 2 ≤ n) (a b : U F n → ℝ)
    (ha : uavg a = 0) (hb : uavg b = 0) :
    uavg (fun M : Refresh.«GL» F n =>
      (uavg (fun l => a l * b (rowRefresh l M))) ^ 2) ≤
      mixingCoefficient F n * uavg (fun l => a l ^ 2) * uavg (fun l => b l ^ 2) := by
  classical
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  obtain ⟨l₀, k₀, h₀⟩ := exists_nonprojective_pair (F := F) hn
  have hrow (l : U F n) : ∑ k : U F n, rowCovariance b l k = 0 := by
    have h := rowCovariance_row_mean_zero b hb l
    unfold uavg at h
    exact (mul_eq_zero.mp h).resolve_left
      (inv_ne_zero (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card (U F n) ≠ 0)))
  have hD : 0 < (Fintype.card (U F n) : ℝ) - ((fieldCard F : ℝ) - 1) := by
    rw [card_U_real]
    have h := zeroFiber_denominator_pos (F := F) hn
    linarith
  have hq := fieldCard_cast_ge_two (F := F)
  have hquad := two_orbit_quadratic_bound projectiveRel (rowCovariance b)
    ((fieldCard F : ℝ) - 1) (uavg (fun l => b l ^ 2)) (rowCovariance b l₀ k₀)
    (fun l k => projectiveRel_symm l k)
    (fun l => projectiveIndicator_row_sum l)
    (by linarith) (uavg_nonneg fun l => sq_nonneg (b l)) hrow
    (fun l k => abs_rowCovariance_le b l k)
    (fun l k h => rowCovariance_independent_eq b l k l₀ k₀ h h₀)
    hD a ha
  have he : (Fintype.card (U F n) : ℝ) - ((fieldCard F : ℝ) - 1) =
      (vectorCard F n : ℝ) - (fieldCard F : ℝ) := by rw [card_U_real]; ring
  rw [he] at hquad
  rw [random_correlation_square_eq]
  have hreorder :
      uavg (fun l => uavg (fun k => a l * a k * rowCovariance b l k)) =
      uavg (fun l => uavg (fun k => rowCovariance b l k * a l * a k)) := by
    apply uavg_congr
    intro l
    apply uavg_congr
    intro k
    ring
  rw [hreorder]
  apply (le_abs_self _).trans
  exact hquad

section Centering

variable {X : Type*} [Fintype X] [Nonempty X]

/-- Subtract the uniform mean of a real finite function. -/
/-
Mathematical definition (normal notation): For f ∈ X → ℝ; x ∈ X, define

centered(f, x) := f(x) - 𝔼ᵤ [f(u)].
-/
def centered (f : X → ℝ) (x : X) : ℝ := f x - uavg f

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ X → ℝ, we have

𝔼ᵤ [centered(f, u)] = 0.
-/
theorem centered_mean_zero (f : X → ℝ) : uavg (centered f) = 0 := by
  change uavg (fun x => f x - uavg f) = 0
  rw [uavg_sub, uavg_const, sub_self]

/-- Centering can only decrease the uniform mean square. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ X → ℝ, we have

𝔼ₓ [(centered(f, x))²] ≤ 𝔼ₓ [(f(x))²].
-/
theorem centered_square_le (f : X → ℝ) :
    uavg (fun x => centered f x ^ 2) ≤ uavg (fun x => f x ^ 2) := by
  have he (x : X) : centered f x ^ 2 =
      f x ^ 2 - 2 * uavg f * f x + (uavg f) ^ 2 := by
    unfold centered
    ring
  simp_rw [he, uavg_add, uavg_sub, uavg_const_mul, uavg_const]
  nlinarith [sq_nonneg (uavg f)]

end Centering

/-- The arbitrary-function variance version of random-GL row mixing. The right-hand side may use the original, uncentered mean squares. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ U(F, n) → ℝ, assume 2 ≤ n. Then

𝔼_(M ∈ GLₙ(F)) [(𝔼ₗ [a(l) · b(rowRefresh(l, M))] - 𝔼_w [a(w)] · 𝔼ₓ [b(x)])²] ≤ mixingCoefficient(F, n) · 𝔼ₗ [(a(l))²] · 𝔼ₗ [(b(l))²].
-/
theorem row_mixing_variance (hn : 2 ≤ n) (a b : U F n → ℝ) :
    uavg (fun M : Refresh.«GL» F n =>
      (uavg (fun l => a l * b (rowRefresh l M)) - uavg a * uavg b) ^ 2) ≤
      mixingCoefficient F n * uavg (fun l => a l ^ 2) * uavg (fun l => b l ^ 2) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  have he (M : Refresh.«GL» F n) :
      uavg (fun l => centered a l * centered b (rowRefresh l M)) =
        uavg (fun l => a l * b (rowRefresh l M)) - uavg a * uavg b := by
    unfold centered
    simp only [sub_mul, mul_sub, uavg_sub, uavg_mul_const, uavg_const_mul, uavg_const,
      uavg_rowRefresh]
    ring
  have h := row_mixing_centered hn (centered a) (centered b)
    (centered_mean_zero a) (centered_mean_zero b)
  simp_rw [he] at h
  apply h.trans
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (centered_square_le a) (mixingCoefficient_nonneg hn))
    (centered_square_le b)
    (uavg_nonneg fun l => sq_nonneg (centered b l))
    (mul_nonneg (mixingCoefficient_nonneg hn) (uavg_nonneg fun l => sq_nonneg (a l)))

/-- The actual row refresh discharges the generic point-uniformity interface. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

UniformOnPoints(((M ∈ GLₙ(F) ↦ rowEquiv(M)))).
-/
theorem row_uniformOnPoints : UniformOnPoints (fun M : Refresh.«GL» F n => rowEquiv M) := by
  intro l f
  exact uavg_random_rowRefresh l f

/-- The actual row refresh discharges the generic mixing interface. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

VarianceMixing(((M ∈ GLₙ(F) ↦ rowEquiv(M))), mixingCoefficient(F, n)).
-/
theorem row_varianceMixing (hn : 2 ≤ n) :
    VarianceMixing (fun M : Refresh.«GL» F n => rowEquiv M) (mixingCoefficient F n) := by
  intro a b
  exact row_mixing_variance hn a b

/-- Inversion preserves the uniform matrix distribution. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ GLₙ(F) → ℝ, we have

𝔼_(M ∈ GLₙ(F)) [f((M)⁻¹)] = 𝔼ᵤ [f(u)].
-/
theorem uavg_inv (f : Refresh.«GL» F n → ℝ) :
    uavg (fun M : Refresh.«GL» F n => f M⁻¹) = uavg f :=
  uavg_equiv (Equiv.inv (Refresh.«GL» F n)) f

/-- Transpose an invertible matrix, retaining its checked inverse. -/
/- Mathematical definition (normal notation): Transpose an invertible matrix M and equip Mᵀ with inverse (M⁻¹)ᵀ. -/
def transposeUnit (M : Refresh.«GL» F n) : Refresh.«GL» F n where
  val := M.val.transpose
  inv := (M⁻¹).val.transpose
  val_inv := by rw [← Matrix.transpose_mul]; simp
  inv_val := by rw [← Matrix.transpose_mul]; simp

/-- Matrix transposition is an involutive permutation of the general linear group. -/
/- Mathematical definition (normal notation): Transposition M ↦ Mᵀ is a self-inverse bijection of GLₙ(𝔽). -/
def transposeEquiv : Refresh.«GL» F n ≃ Refresh.«GL» F n where
  toFun := transposeUnit
  invFun := transposeUnit
  left_inv M := by apply Units.ext; simp [transposeUnit]
  right_inv M := by apply Units.ext; simp [transposeUnit]

/-- Inverse transpose also permutes the general linear group. -/
/-
Mathematical definition (normal notation): Define

inverseTransposeEquiv := trans(Equiv.inv(GLₙ(F)))(transposeEquiv) .
-/
def inverseTransposeEquiv : Refresh.«GL» F n ≃ Refresh.«GL» F n :=
  (Equiv.inv (Refresh.«GL» F n)).trans transposeEquiv

omit [Fintype F] [DecidableEq F] in
/-- The column action is the row action of the inverse transpose. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ U(F, n); M ∈ GLₙ(F), we have

columnRefresh(r, M) = rowRefresh(r, inverseTransposeEquiv(M)).
-/
theorem columnRefresh_eq_rowRefresh (r : U F n) (M : Refresh.«GL» F n) :
    columnRefresh r M = rowRefresh r (inverseTransposeEquiv M) := by
  apply Subtype.ext
  change Matrix.mulVec (M⁻¹).val r.val = Matrix.vecMul r.val (M⁻¹).val.transpose
  exact (Matrix.vecMul_transpose _ _).symm

/-- Multiplication by the inverse of a fixed invertible matrix permutes columns. -/
/- Mathematical definition (normal notation): For invertible M, the column map r ↦ M⁻¹ · r is a bijection of U, with inverse r ↦ M · r. -/
def columnEquiv (M : Refresh.«GL» F n) : U F n ≃ U F n where
  toFun r := columnRefresh r M
  invFun r := columnRefresh r M⁻¹
  left_inv r := by
    change columnRefresh (columnRefresh r M) M⁻¹ = r
    rw [columnRefresh_mul]
    simp
  right_inv r := by
    change columnRefresh (columnRefresh r M⁻¹) M = r
    rw [columnRefresh_mul]
    simp

/-- Each fixed column becomes uniform under a random matrix. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ U(F, n); f ∈ U(F, n) → ℝ, we have

𝔼_(M ∈ GLₙ(F)) [f(columnRefresh(r, M))] = 𝔼ᵤ [f(u)].
-/
theorem uavg_random_columnRefresh (r : U F n) (f : U F n → ℝ) :
    uavg (fun M : Refresh.«GL» F n => f (columnRefresh r M)) = uavg f := by
  simp_rw [columnRefresh_eq_rowRefresh]
  rw [uavg_equiv inverseTransposeEquiv (fun M => f (rowRefresh r M))]
  exact uavg_random_rowRefresh r f

/-- The arbitrary-function variance estimate for the actual column action. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ U(F, n) → ℝ, assume 2 ≤ n. Then

𝔼_(M ∈ GLₙ(F)) [(𝔼ᵣ [a(r) · b(columnRefresh(r, M))] - 𝔼_w [a(w)] · 𝔼ₓ [b(x)])²] ≤ mixingCoefficient(F, n) · 𝔼ᵣ [(a(r))²] · 𝔼ᵣ [(b(r))²].
-/
theorem column_mixing_variance (hn : 2 ≤ n) (a b : U F n → ℝ) :
    uavg (fun M : Refresh.«GL» F n =>
      (uavg (fun r => a r * b (columnRefresh r M)) - uavg a * uavg b) ^ 2) ≤
      mixingCoefficient F n * uavg (fun r => a r ^ 2) * uavg (fun r => b r ^ 2) := by
  simp_rw [columnRefresh_eq_rowRefresh]
  rw [uavg_equiv inverseTransposeEquiv (fun M =>
    (uavg (fun r => a r * b (rowRefresh r M)) - uavg a * uavg b) ^ 2)]
  exact row_mixing_variance hn a b

/-- The actual column refresh discharges the generic point-uniformity interface. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

UniformOnPoints(((M ∈ GLₙ(F) ↦ columnEquiv(M)))).
-/
theorem column_uniformOnPoints :
    UniformOnPoints (fun M : Refresh.«GL» F n => columnEquiv M) := by
  intro r f
  exact uavg_random_columnRefresh r f

/-- The actual column refresh discharges the generic mixing interface. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

VarianceMixing(((M ∈ GLₙ(F) ↦ columnEquiv(M))), mixingCoefficient(F, n)).
-/
theorem column_varianceMixing (hn : 2 ≤ n) :
    VarianceMixing (fun M : Refresh.«GL» F n => columnEquiv M) (mixingCoefficient F n) := by
  intro a b
  exact column_mixing_variance hn a b

/-- Sampling the inverse row action also sends every point to uniform measure. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

UniformOnPoints(((M ∈ GLₙ(F) ↦ (rowEquiv(M))⁻¹))).
-/
theorem row_inverse_uniformOnPoints :
    UniformOnPoints (fun M : Refresh.«GL» F n => (rowEquiv M).symm) := by
  intro l f
  change uavg (fun M : Refresh.«GL» F n => f (rowRefresh l M⁻¹)) = uavg f
  rw [uavg_inv (fun M => f (rowRefresh l M))]
  exact uavg_random_rowRefresh l f

/-- Sampling inverse matrices gives the same row mixing coefficient. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

VarianceMixing(((M ∈ GLₙ(F) ↦ (rowEquiv(M))⁻¹)), mixingCoefficient(F, n)).
-/
theorem row_inverse_varianceMixing (hn : 2 ≤ n) :
    VarianceMixing (fun M : Refresh.«GL» F n => (rowEquiv M).symm)
      (mixingCoefficient F n) := by
  intro a b
  change uavg (fun M : Refresh.«GL» F n =>
    (uavg (fun l => a l * b (rowRefresh l M⁻¹)) - uavg a * uavg b) ^ 2) ≤ _
  rw [uavg_inv (fun M =>
    (uavg (fun l => a l * b (rowRefresh l M)) - uavg a * uavg b) ^ 2)]
  exact row_mixing_variance hn a b

/-- The inverse column action has the same pointwise uniformity. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

UniformOnPoints(((M ∈ GLₙ(F) ↦ (columnEquiv(M))⁻¹))).
-/
theorem column_inverse_uniformOnPoints :
    UniformOnPoints (fun M : Refresh.«GL» F n => (columnEquiv M).symm) := by
  intro r f
  change uavg (fun M : Refresh.«GL» F n => f (columnRefresh r M⁻¹)) = uavg f
  rw [uavg_inv (fun M => f (columnRefresh r M))]
  exact uavg_random_columnRefresh r f

/-- The inverse column action has the same variance mixing coefficient. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

VarianceMixing(((M ∈ GLₙ(F) ↦ (columnEquiv(M))⁻¹)), mixingCoefficient(F, n)).
-/
theorem column_inverse_varianceMixing (hn : 2 ≤ n) :
    VarianceMixing (fun M : Refresh.«GL» F n => (columnEquiv M).symm)
      (mixingCoefficient F n) := by
  intro a b
  change uavg (fun M : Refresh.«GL» F n =>
    (uavg (fun r => a r * b (columnRefresh r M⁻¹)) - uavg a * uavg b) ^ 2) ≤ _
  rw [uavg_inv (fun M =>
    (uavg (fun r => a r * b (columnRefresh r M)) - uavg a * uavg b) ^ 2)]
  exact column_mixing_variance hn a b

end TableAnalysis
