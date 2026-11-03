import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Proofs.Refreshing.LocalTables
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Proofs.Refreshing.DoubleTransitivity

/-!
# Centered off-diagonal sums

The exact cancellation in the paper's off-diagonal covariance calculation. The distributional assertion that a random invertible matrix gives uniform distinct images must be supplied by the separate group-action argument.
-/

open scoped BigOperators

namespace RefreshingProof

/-- Finite expectation commutes with the actual PMF pushforward. -/
theorem pmf_expectation_map {X Y : Type*} [Fintype X] [Fintype Y]
    (P : PMF X) (f : X → Y) (g : Y → ℝ) :
    (∑ y, ((P.map f) y).toReal * g y) = ∑ x, (P x).toReal * g (f x) := by
  classical
  have hmass (y : Y) : ((P.map f) y).toReal =
      ∑ x, if y = f x then (P x).toReal else 0 := by
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    · intro x _
      split_ifs
      · exact P.apply_ne_top x
      · exact ENNReal.zero_ne_top
  simp_rw [hmass, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul]

/-- The explicit uniform PMF agrees with the paper's normalized finite mean. -/
theorem uniformPMF_expectation {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) :
    (∑ x, (Refreshing.uniformPMF X x).toReal * f x) = Local.average f := by
  simp [Refreshing.uniformPMF_apply, ENNReal.toReal_inv, Local.average, Finset.mul_sum]

/-- A uniform-image distribution transports all finite real averages, including the second moments used in the Gram calculation. -/
theorem average_comp_of_uniform_map {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X → Y)
    (hf : (Refreshing.uniformPMF X).map f = Refreshing.uniformPMF Y) (g : Y → ℝ) :
    Local.average (fun x => g (f x)) = Local.average g := by
  rw [← uniformPMF_expectation, ← pmf_expectation_map, hf, uniformPMF_expectation]

/-- Removing the diagonal from the product of two centered finite sums leaves the negative diagonal pairing. -/
theorem centered_offDiagonal_sum {X : Type*} [Fintype X] [DecidableEq X]
    (f g : X → ℝ) (hg : ∑ x, g x = 0) :
    (∑ x, ∑ y, if x = y then 0 else f x * g y) = -∑ x, f x * g x := by
  have hpoint (x y : X) :
      (if x = y then 0 else f x * g y) =
        f x * g y - if x = y then f x * g x else 0 := by
    by_cases h : x = y
    · subst y
      simp
    · simp [h]
  simp_rw [hpoint]
  simp [Finset.sum_sub_distrib, ← Finset.mul_sum, hg]

/-- The covariance of uniform ordered distinct samples, in unnormalized sums. This is the numerator in the paper's off-diagonal covariance formula. -/
theorem centered_distinct_pairing {X : Type*} [Fintype X] [DecidableEq X]
    (f g : X → ℝ) (hg : ∑ x, g x = 0) :
    (∑ p : X × X, if p.1 ≠ p.2 then f p.1 * g p.2 else 0) =
      -∑ x, f x * g x := by
  rw [Fintype.sum_prod_type]
  simp only [ite_not]
  exact centered_offDiagonal_sum f g hg

/-- The finite carrier of ordered pairs with distinct entries. -/
abbrev OrderedDistinct (X : Type*) := {p : X × X // p.1 ≠ p.2}

/-- Identify equal-coordinate pairs with their common coordinate. -/
def diagonalEquiv (X : Type*) : {p : X × X // p.1 = p.2} ≃ X where
  toFun p := p.val.1
  invFun x := ⟨(x, x), rfl⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl p.property
  right_inv _ := rfl

/-- A finite set of size N has N(N − 1) ordered pairs of distinct elements. -/
theorem card_orderedDistinct (X : Type*) [Fintype X] [DecidableEq X] :
    Fintype.card (OrderedDistinct X) = Fintype.card X * (Fintype.card X - 1) := by
  rw [show Fintype.card (OrderedDistinct X) =
      Fintype.card (X × X) - Fintype.card {p : X × X // p.1 = p.2} from
    Fintype.card_subtype_compl (fun p : X × X => p.1 = p.2)]
  rw [Fintype.card_prod, Fintype.card_congr (diagonalEquiv X)]
  simp [Nat.mul_sub_left_distrib]

/-- Exact centered covariance for uniform sampling without replacement. -/
theorem average_orderedDistinct {X : Type*} [Fintype X] [DecidableEq X]
    (hX : 2 ≤ Fintype.card X) (f g : X → ℝ) (hg : ∑ x, g x = 0) :
    Local.average (fun p : OrderedDistinct X => f p.val.1 * g p.val.2) =
      -(Local.average (fun x => f x * g x)) / ((Fintype.card X : ℝ) - 1) := by
  classical
  have hsum : (∑ p : OrderedDistinct X, f p.val.1 * g p.val.2) =
      -∑ x, f x * g x := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun p : X × X => p.1 ≠ p.2))
      (by intro p; simp) (fun p => f p.1 * g p.2)]
    rw [Finset.sum_filter]
    exact centered_distinct_pairing f g hg
  have hq : (Fintype.card X : ℝ) ≠ 0 := by
    exact_mod_cast (show Fintype.card X ≠ 0 by omega)
  have hqm : (Fintype.card X : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ Fintype.card X := by exact_mod_cast hX
    linarith
  unfold Local.average
  rw [hsum, card_orderedDistinct]
  have hsub : ((Fintype.card X - 1 : ℕ) : ℝ) = (Fintype.card X : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card X)]
    norm_num
  push_cast
  rw [hsub]
  field_simp

/-- Sum of the diagonal/off-diagonal covariance cases. This is an algebraic identity, before the negative Gram term is discarded. -/
theorem average_covariance_cases {X : Type*} [Fintype X] [DecidableEq X]
    (hX : 2 ≤ Fintype.card X) (C : X → X → ℝ) :
    Local.average (fun x => Local.average (fun y =>
      if x = y then C x y else -C x y / ((Fintype.card X : ℝ) - 1))) =
      (Local.average (fun x => C x x) -
        Local.average (fun x => Local.average (fun y => C x y))) /
          ((Fintype.card X : ℝ) - 1) := by
  let q : ℝ := Fintype.card X
  have hq : q ≠ 0 := by
    dsimp [q]
    exact_mod_cast (show Fintype.card X ≠ 0 by omega)
  have hqm : q - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ q := by dsimp [q]; exact_mod_cast hX
    linarith
  have hpoint (x y : X) :
      (if x = y then C x y else -C x y / (q - 1)) =
        (q / (q - 1)) * (if x = y then C x y else 0) -
          (q - 1)⁻¹ * C x y := by
    by_cases h : x = y
    · subst y
      simp only [eq_self, ite_true]
      field_simp [hqm]
    · simp [h, div_eq_mul_inv, mul_comm]
  have hdiag (x : X) :
      Local.average (fun y => if x = y then C x y else 0) = q⁻¹ * C x x := by
    simp [Local.average, q]
  change Local.average (fun x => Local.average (fun y =>
      if x = y then C x y else -C x y / (q - 1))) = _
  simp_rw [hpoint, Local.average_sub, Local.average_smul, hdiag]
  simp only [Local.average_smul]
  change q / (q - 1) * (q⁻¹ * Local.average (fun x => C x x)) -
    (q - 1)⁻¹ * Local.average (fun x => Local.average (fun y => C x y)) = _
  change _ = (Local.average (fun x => C x x) -
    Local.average (fun x => Local.average (fun y => C x y))) / (q - 1)
  field_simp

/-- The subtracted term in the variance identity is nonnegative because it is the mean square of the sum of centered columns. No entrywise positivity is used. -/
theorem average_gram_nonneg {X U : Type*} [Fintype X] [Fintype U]
    (Z : X → U → ℝ) :
    0 ≤ Local.average (fun x => Local.average (fun y =>
      Local.average (fun u => Z x u * Z y u))) := by
  rw [Local.average_comm]
  have heq : Local.average (fun y => Local.average (fun x =>
      Local.average (fun u => Z x u * Z y u))) =
      Local.average (fun u => (Local.average (fun x => Z x u)) ^ 2) := by
    simp_rw [Local.average_comm (fun x u => Z x u * Z _ u)]
    rw [Local.average_comm]
    apply Local.average_congr
    intro u
    simpa only [pow_two, mul_comm] using
      (Local.average_mul_average (fun x => Z x u) (fun y => Z y u)).symm
  rw [heq]
  exact Local.average_nonneg (fun _ => sq_nonneg _)

/-- Summing the exact pair covariances bounds the mean square of the empirical mean. The negative Gram term is discarded only after it is a complete square. -/
theorem empirical_variance_of_covariances {X M U : Type*}
    [Fintype X] [DecidableEq X] [Fintype M] [Fintype U]
    (hX : 2 ≤ Fintype.card X) (z : M → X → ℝ) (Z : X → U → ℝ)
    (hcov : ∀ x y,
      Local.average (fun m => z m x * z m y) =
        if x = y then Local.average (fun u => Z x u * Z y u)
        else -Local.average (fun u => Z x u * Z y u) /
          ((Fintype.card X : ℝ) - 1)) :
    Local.average (fun m => (Local.average (z m)) ^ 2) ≤
      Local.average (fun x => Local.average (fun u => Z x u ^ 2)) /
        ((Fintype.card X : ℝ) - 1) := by
  have hexpand : Local.average (fun m => (Local.average (z m)) ^ 2) =
      Local.average (fun x => Local.average (fun y =>
        Local.average (fun m => z m x * z m y))) := by
    calc
      _ = Local.average (fun m => Local.average (fun x =>
          Local.average (fun y => z m x * z m y))) := by
        simp_rw [pow_two, Local.average_mul_average]
      _ = Local.average (fun x => Local.average (fun m =>
          Local.average (fun y => z m x * z m y))) := Local.average_comm _
      _ = _ := by
        apply Local.average_congr
        intro x
        exact Local.average_comm _
  rw [hexpand]
  simp_rw [hcov]
  rw [average_covariance_cases hX]
  have hnonneg := average_gram_nonneg Z
  have hden : 0 ≤ (Fintype.card X : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Fintype.card X := by exact_mod_cast hX
    linarith
  simpa only [pow_two] using
    div_le_div_of_nonneg_right (sub_le_self _ hnonneg) hden

/-- A finite action with exact uniform one- and two-point image distributions has the paper's variance bound for every centered table. -/
theorem empirical_variance_of_uniform_images {X M : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X] [Fintype M] [Nonempty M]
    [Nonempty (OrderedDistinct X)] (hX : 2 ≤ Fintype.card X)
    (e : M → Equiv.Perm X)
    (hsingle : ∀ x, (Refreshing.uniformPMF M).map (fun m => e m x) =
      Refreshing.uniformPMF X)
    (hpair : ∀ p : OrderedDistinct X,
      (Refreshing.uniformPMF M).map (fun m =>
        (⟨(e m p.val.1, e m p.val.2), fun h => p.property ((e m).injective h)⟩ :
          OrderedDistinct X)) = Refreshing.uniformPMF (OrderedDistinct X))
    (Z : X → X → ℝ) (hcenter : ∀ x, ∑ u, Z x u = 0) :
    Local.average (fun m => (Local.average (fun x => Z x (e m x))) ^ 2) ≤
      Local.average (fun x => Local.average (fun u => Z x u ^ 2)) /
        ((Fintype.card X : ℝ) - 1) := by
  apply empirical_variance_of_covariances hX _ Z
  intro x y
  by_cases hxy : x = y
  · subst y
    simpa only [eq_self, ite_true] using
      average_comp_of_uniform_map (fun m => e m x) (hsingle x)
        (fun u => Z x u * Z x u)
  · simp only [hxy, ite_false]
    let p : OrderedDistinct X := ⟨(x, y), hxy⟩
    have hp := average_comp_of_uniform_map
      (fun m => (⟨(e m p.val.1, e m p.val.2),
        fun h => p.property ((e m).injective h)⟩ : OrderedDistinct X)) (hpair p)
      (fun p : OrderedDistinct X => Z x p.val.1 * Z y p.val.2)
    exact hp.trans (average_orderedDistinct hX (Z x) (Z y) (hcenter y))

/-- Actual centered scalar Gram variance for a uniform binary invertible matrix. There is no assumed independence or pair-uniformity hypothesis. -/
theorem matrix_centered_variance {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype ((Matrix I I (ZMod 2))ˣ)] [Nonempty (NonzeroBinary I)]
    (hI : 2 ≤ Fintype.card (NonzeroBinary I)) (Z : NonzeroBinary I → NonzeroBinary I → ℝ)
    (hcenter : ∀ x, ∑ u, Z x u = 0) :
    Local.average (fun M : (Matrix I I (ZMod 2))ˣ =>
      (Local.average (fun x => Z x (matrixUnitNonzeroApply M x))) ^ 2) ≤
      Local.average (fun x => Local.average (fun u => Z x u ^ 2)) /
        ((Fintype.card (NonzeroBinary I) : ℝ) - 1) := by
  classical
  letI : Nontrivial (NonzeroBinary I) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Nonempty (OrderedDistinct (NonzeroBinary I)) := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (NonzeroBinary I)
    exact ⟨⟨(x, y), hxy⟩⟩
  apply empirical_variance_of_uniform_images hI matrixUnitNonzeroEquiv
  · intro x
    exact uniform_matrixUnit_nonzero x
  · intro p
    exact uniform_distinct_binary_pair p
  · exact hcenter

/-- The uniform average of a constant on a nonempty finite carrier equals that constant. -/
@[simp] theorem average_const {X : Type*} [Fintype X] [Nonempty X] (c : ℝ) :
    Local.average (fun _ : X => c) = c := by
  have hq : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [Local.average, Finset.sum_const, nsmul_eq_mul, hq]

/-- Subtracting a function’s uniform average gives a function whose coordinate sum is zero. -/
theorem centered_sum_zero {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) :
    ∑ x, (f x - Local.average f) = 0 := by
  have hq : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Local.average]
  field_simp
  ring

/-- Pointwise inequalities are preserved by the uniform finite average. -/
theorem uniform_average_mono {X : Type*} [Fintype X] {f g : X → ℝ}
    (h : ∀ x, f x ≤ g x) : Local.average f ≤ Local.average g := by
  unfold Local.average
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => h x))
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- Uniform averaging commutes with a finite sum of functions. -/
theorem uniform_average_sum {X J : Type*} [Fintype X] (s : Finset J)
    (f : J → X → ℝ) :
    Local.average (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, Local.average (f j) := by
  simp only [Local.average, Finset.mul_sum]
  exact Finset.sum_comm

/-- Subtracting the uniform mean decreases the second moment. -/
theorem average_centered_sq_le {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) :
    Local.average (fun x => (f x - Local.average f) ^ 2) ≤
      Local.average (fun x => f x ^ 2) := by
  have heq (x : X) : (f x - Local.average f) ^ 2 =
      f x ^ 2 - 2 * Local.average f * f x + (Local.average f) ^ 2 := by ring
  simp_rw [heq, Local.average_add, Local.average_sub, Local.average_smul, average_const]
  nlinarith [sq_nonneg (Local.average f)]

/-- The mean of the random empirical average is its full product average. -/
theorem matrix_average_image {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype ((Matrix I I (ZMod 2))ˣ)] [Nonempty (NonzeroBinary I)]
    (Z : NonzeroBinary I → NonzeroBinary I → ℝ) :
    Local.average (fun M : (Matrix I I (ZMod 2))ˣ =>
      Local.average (fun x => Z x (matrixUnitNonzeroApply M x))) =
        Local.average (fun x => Local.average (Z x)) := by
  rw [Local.average_comm]
  apply Local.average_congr
  intro x
  exact average_comp_of_uniform_map (fun M => matrixUnitNonzeroApply M x)
    (uniform_matrixUnit_nonzero x) (Z x)

/-- The actual scalar version of the paper's GL Gram-variance bound, for arbitrary input tables. Centering is performed here and is not an assumption. -/
theorem matrix_variance {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype ((Matrix I I (ZMod 2))ˣ)] [Nonempty (NonzeroBinary I)]
    (hI : 2 ≤ Fintype.card (NonzeroBinary I)) (Z : NonzeroBinary I → NonzeroBinary I → ℝ) :
    Local.average (fun M : (Matrix I I (ZMod 2))ˣ =>
      (Local.average (fun x => Z x (matrixUnitNonzeroApply M x)) -
        Local.average (fun x => Local.average (Z x))) ^ 2) ≤
      Local.average (fun x => Local.average (fun u => Z x u ^ 2)) /
        ((Fintype.card (NonzeroBinary I) : ℝ) - 1) := by
  have h := matrix_centered_variance hI
    (fun x u => Z x u - Local.average (Z x)) (fun x => centered_sum_zero (Z x))
  have hden : 0 ≤ (Fintype.card (NonzeroBinary I) : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Fintype.card (NonzeroBinary I) := by exact_mod_cast hI
    linarith
  have hmono :
      Local.average (fun x => Local.average (fun u => (Z x u - Local.average (Z x)) ^ 2)) ≤
      Local.average (fun x => Local.average (fun u => Z x u ^ 2)) :=
    uniform_average_mono (fun x => average_centered_sq_le (Z x))
  simpa only [Local.average_sub] using
    h.trans (div_le_div_of_nonneg_right hmono hden)

/-- The same bound holds after any bijective reindexing of the uniform coins, in particular inversion and matrix transposition. -/
theorem matrix_variance_reindexed {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype ((Matrix I I (ZMod 2))ˣ)] [Nonempty (NonzeroBinary I)]
    (hI : 2 ≤ Fintype.card (NonzeroBinary I))
    (ψ : (Matrix I I (ZMod 2))ˣ ≃ (Matrix I I (ZMod 2))ˣ)
    (Z : NonzeroBinary I → NonzeroBinary I → ℝ) :
    Local.average (fun M : (Matrix I I (ZMod 2))ˣ =>
      (Local.average (fun x => Z x (matrixUnitNonzeroApply (ψ M) x)) -
        Local.average (fun x => Local.average (Z x))) ^ 2) ≤
      Local.average (fun x => Local.average (fun u => Z x u ^ 2)) /
        ((Fintype.card (NonzeroBinary I) : ℝ) - 1) := by
  calc
    _ = Local.average (fun M : (Matrix I I (ZMod 2))ˣ =>
        (Local.average (fun x => Z x (matrixUnitNonzeroApply M x)) -
          Local.average (fun x => Local.average (Z x))) ^ 2) :=
      average_comp_of_uniform_map ψ (uniformPMF_map_equiv ψ) _
    _ ≤ _ := matrix_variance hI Z

/-- Finite-dimensional (coordinate/Frobenius) form of the actual GL variance bound. The coordinate index can in particular be a pair of singular indices. -/
theorem matrix_coordinate_variance {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype ((Matrix I I (ZMod 2))ˣ)] [Nonempty (NonzeroBinary I)]
    (hI : 2 ≤ Fintype.card (NonzeroBinary I)) (s : Finset J)
    (ψ : (Matrix I I (ZMod 2))ˣ ≃ (Matrix I I (ZMod 2))ˣ)
    (Z : J → NonzeroBinary I → NonzeroBinary I → ℝ) :
    Local.average (fun M : (Matrix I I (ZMod 2))ˣ => ∑ j ∈ s,
      (Local.average (fun x => Z j x (matrixUnitNonzeroApply (ψ M) x)) -
        Local.average (fun x => Local.average (Z j x))) ^ 2) ≤
      Local.average (fun x => Local.average (fun u => ∑ j ∈ s, Z j x u ^ 2)) /
        ((Fintype.card (NonzeroBinary I) : ℝ) - 1) := by
  rw [uniform_average_sum]
  calc
    _ ≤ ∑ j ∈ s, Local.average (fun x => Local.average (fun u => Z j x u ^ 2)) /
        ((Fintype.card (NonzeroBinary I) : ℝ) - 1) := by
      apply Finset.sum_le_sum
      intro j _
      exact matrix_variance_reindexed hI ψ (Z j)
    _ = _ := by
      simp_rw [uniform_average_sum]
      rw [Finset.sum_div]

end RefreshingProof
