import Proofs.Refreshing.BinaryCharacters
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity

/-!
# Walsh pairing bounds from binary character orthogonality

The estimates here derive from the actual binary sign transform. No spectral or Gram bound is assumed. The normalization is by counting measure, as indicated by the explicit sums.
-/

noncomputable section
open scoped BigOperators Matrix

namespace RefreshingProof.Binary

/-- The unnormalized pairing with the full binary inner-product sign matrix. -/
def walshPairing {n : ℕ} (f g : Vec n → ℝ) : ℝ :=
  ∑ x : Vec n, ∑ y : Vec n, f x * sign (x ⬝ᵥ y) * g y

/-- Cauchy–Schwarz and exact Parseval give the squared sign-matrix bound. -/
theorem walshPairing_sq_le {n : ℕ} (f g : Vec n → ℝ) :
    walshPairing f g ^ 2 ≤
      (2 : ℝ) ^ n * (∑ x : Vec n, f x ^ 2) * ∑ y : Vec n, g y ^ 2 := by
  have hp : walshPairing f g =
      ∑ x : Vec n, f x * ∑ y : Vec n, sign (x ⬝ᵥ y) * g y := by
    unfold walshPairing
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hp]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f
    (fun x : Vec n => ∑ y : Vec n, sign (x ⬝ᵥ y) * g y)
  rw [character_parseval] at hcs
  nlinarith [hcs]

/-- The full Walsh matrix has operator norm at most √(2^n) under counting L₂. -/
theorem walshPairing_abs_le {n : ℕ} (f g : Vec n → ℝ) :
    |walshPairing f g| ≤
      Real.sqrt ((2 : ℝ) ^ n) *
        Real.sqrt (∑ x : Vec n, f x ^ 2) * Real.sqrt (∑ y : Vec n, g y ^ 2) := by
  calc
    |walshPairing f g| ≤
        Real.sqrt ((2 : ℝ) ^ n * (∑ x : Vec n, f x ^ 2) * ∑ y : Vec n, g y ^ 2) :=
      Real.abs_le_sqrt (walshPairing_sq_le f g)
    _ = _ := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ) ^ n * ∑ x : Vec n, f x ^ 2),
        Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ) ^ n)]

/-- Restricting both coordinate sets cannot increase the counting-L₂ sign bound. This is obtained by zero-extending the two functions to the full binary space. -/
theorem walshPairing_subset_abs_le {n : ℕ} (A B : Finset (Vec n))
    (f g : Vec n → ℝ) :
    |∑ x ∈ A, ∑ y ∈ B, f x * sign (x ⬝ᵥ y) * g y| ≤
      Real.sqrt ((2 : ℝ) ^ n) *
        Real.sqrt (∑ x ∈ A, f x ^ 2) * Real.sqrt (∑ y ∈ B, g y ^ 2) := by
  classical
  have hp := walshPairing_abs_le (fun x => if x ∈ A then f x else 0)
    (fun y => if y ∈ B then g y else 0)
  simpa only [walshPairing, ite_mul, mul_ite, zero_mul, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_mem,
    Finset.univ_inter, ite_pow, zero_pow (by norm_num : 2 ≠ 0)] using hp

/-- The character of two independent binary inner products. -/
def pairSign {n : ℕ} (a v : Vec n × Vec n) : ℝ :=
  sign (a.1 ⬝ᵥ v.1 + a.2 ⬝ᵥ v.2)

/-- The tensor sign transform satisfies exact Parseval with factor (2^n)². -/
theorem pair_character_parseval {n : ℕ} (f : (Vec n × Vec n) → ℝ) :
    (∑ a : Vec n × Vec n, (∑ v : Vec n × Vec n, pairSign a v * f v) ^ 2) =
      ((2 : ℝ) ^ n) ^ 2 * ∑ v : Vec n × Vec n, f v ^ 2 := by
  classical
  have htransform (a b : Vec n) :
      (∑ v : Vec n × Vec n, pairSign (a, b) v * f v) =
        ∑ v : Vec n, sign (a ⬝ᵥ v) *
          ∑ w : Vec n, sign (b ⬝ᵥ w) * f (v, w) := by
    simp only [Fintype.sum_prod_type, pairSign, sign_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    ring
  calc
    _ = ∑ b : Vec n, ∑ a : Vec n,
        (∑ v : Vec n, sign (a ⬝ᵥ v) *
          ∑ w : Vec n, sign (b ⬝ᵥ w) * f (v, w)) ^ 2 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      rw [htransform]
    _ = ∑ b : Vec n, (2 : ℝ) ^ n *
        ∑ v : Vec n, (∑ w : Vec n, sign (b ⬝ᵥ w) * f (v, w)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro b _
      exact character_parseval _
    _ = (2 : ℝ) ^ n * ∑ v : Vec n, ∑ b : Vec n,
        (∑ w : Vec n, sign (b ⬝ᵥ w) * f (v, w)) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = (2 : ℝ) ^ n * ∑ v : Vec n, (2 : ℝ) ^ n * ∑ w : Vec n, f (v, w) ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro v _
      exact character_parseval _
    _ = _ := by
      rw [← Finset.mul_sum, Fintype.sum_prod_type]
      ring

/-- Pairing against the tensor sign matrix on two-vector states. -/
def pairWalshPairing {n : ℕ} (f g : (Vec n × Vec n) → ℝ) : ℝ :=
  ∑ a : Vec n × Vec n, ∑ v : Vec n × Vec n, f a * pairSign a v * g v

/-- The tensor Walsh matrix has squared operator bound (2^n)². -/
theorem pairWalshPairing_sq_le {n : ℕ} (f g : (Vec n × Vec n) → ℝ) :
    pairWalshPairing f g ^ 2 ≤
      ((2 : ℝ) ^ n) ^ 2 * (∑ a : Vec n × Vec n, f a ^ 2) *
        ∑ v : Vec n × Vec n, g v ^ 2 := by
  have hp : pairWalshPairing f g =
      ∑ a : Vec n × Vec n, f a * ∑ v : Vec n × Vec n, pairSign a v * g v := by
    unfold pairWalshPairing
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hp]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f
    (fun a : Vec n × Vec n => ∑ v : Vec n × Vec n, pairSign a v * g v)
  rw [pair_character_parseval] at hcs
  nlinarith [hcs]

/-- The tensor sign matrix has counting-L₂ operator norm at most 2^n. -/
theorem pairWalshPairing_abs_le {n : ℕ} (f g : (Vec n × Vec n) → ℝ) :
    |pairWalshPairing f g| ≤
      (2 : ℝ) ^ n * Real.sqrt (∑ a : Vec n × Vec n, f a ^ 2) *
        Real.sqrt (∑ v : Vec n × Vec n, g v ^ 2) := by
  calc
    |pairWalshPairing f g| ≤ Real.sqrt
        (((2 : ℝ) ^ n) ^ 2 * (∑ a : Vec n × Vec n, f a ^ 2) *
          ∑ v : Vec n × Vec n, g v ^ 2) :=
      Real.abs_le_sqrt (pairWalshPairing_sq_le f g)
    _ = _ := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ ((2 : ℝ) ^ n) ^ 2 *
        ∑ a : Vec n × Vec n, f a ^ 2),
        Real.sqrt_mul (by positivity : 0 ≤ ((2 : ℝ) ^ n) ^ 2),
        Real.sqrt_sq (by positivity : 0 ≤ (2 : ℝ) ^ n)]

/-- Zero extension gives the same tensor bound for arbitrary finite subsets. -/
theorem pairWalshPairing_subset_abs_le {n : ℕ} (A B : Finset (Vec n × Vec n))
    (f g : (Vec n × Vec n) → ℝ) :
    |∑ a ∈ A, ∑ v ∈ B, f a * pairSign a v * g v| ≤
      (2 : ℝ) ^ n * Real.sqrt (∑ a ∈ A, f a ^ 2) *
        Real.sqrt (∑ v ∈ B, g v ^ 2) := by
  classical
  have hp := pairWalshPairing_abs_le (fun a => if a ∈ A then f a else 0)
    (fun v => if v ∈ B then g v else 0)
  simpa only [pairWalshPairing, ite_mul, mul_ite, zero_mul, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_mem,
    Finset.univ_inter, ite_pow, zero_pow (by norm_num : 2 ≠ 0)] using hp

end RefreshingProof.Binary
