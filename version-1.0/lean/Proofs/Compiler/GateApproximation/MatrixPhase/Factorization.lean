import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.InitialDiscrepancy
import Proofs.Compiler.Foundations.MatrixRefreshing.Probability.FiniteDistribution



/-!
# Explicit bounded factorizations

The composition proof needs finite witnesses for a bound on the factorization norm. Keeping the factors themselves avoids infima and supplies certificates that are preserved by restriction and multiplication.
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler

open Refresh

/-- A chosen bounded finite factorization: both squared factor norms are at most `B`. It certifies the manuscript's bound `γ₂(table) ≤ B`. -/
/- Mathematical definition (normal notation): A chosen bounded product representation of F:X × Y → ℝ consists of finitely many functions aⱼ,bⱼ with F(x,y) = ∑ⱼ aⱼ(x)bⱼ(y), ∑ⱼ aⱼ(x)² ≤ B for every x, and ∑ⱼ bⱼ(y)² ≤ B for every y. No orthogonality or minimum-cost property is required. -/
structure BoundedFactorization {X Y : Type*} (table : X → Y → ℝ) (B : ℝ) where
  rank : ℕ
  left : X → Fin rank → ℝ
  right : Y → Fin rank → ℝ
  reconstruct : ∀ x y, table x y = ∑ i, left x i * right y i
  left_bound : ∀ x, (∑ i, left x i ^ 2) ≤ B
  right_bound : ∀ y, (∑ i, right y i ^ 2) ≤ B

namespace BoundedFactorization

variable {X Y X' Y' : Type*} {f g : X → Y → ℝ} {B C : ℝ}

/-- Fixing other port coordinates restricts the same features. -/
/- Mathematical definition (normal notation): Precompose the left factors with l and right factors with r, obtaining a representation of f(l(x),r(y)) with the same pointwise energy bound. -/
def restrict (factor : BoundedFactorization f B) (l : X' → X) (r : Y' → Y) :
    BoundedFactorization (fun x y => f (l x) (r y)) B where
  rank := factor.rank
  left := fun x => factor.left (l x)
  right := fun y => factor.right (r y)
  reconstruct x y := factor.reconstruct (l x) (r y)
  left_bound x := factor.left_bound (l x)
  right_bound y := factor.right_bound (r y)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For factor ∈ BoundedFactorization(f, B); x ∈ X; y ∈ Y, assume 0 ≤ B. Then

|f(x, y)| ≤ B.
-/
theorem abs_le (factor : BoundedFactorization f B) (hB : 0 ≤ B) (x : X) (y : Y) :
    |f x y| ≤ B := by
  rw [factor.reconstruct]
  exact (Refresh.abs_sum_mul_le _ _).trans (by
    calc
      _ ≤ Real.sqrt B * Real.sqrt B :=
        mul_le_mul (Real.sqrt_le_sqrt (factor.left_bound x))
          (Real.sqrt_le_sqrt (factor.right_bound y)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = B := Real.mul_self_sqrt hB)

/-- Multiplication tensors the two feature vectors. -/
/- Mathematical definition (normal notation): If f = ∑ᵢ aᵢ bᵢᵀ and g = ∑ⱼ cⱼ dⱼᵀ have pointwise factor-energy bounds B and C, construct the product representation fg = ∑_(i,j) (aᵢ cⱼ)(bᵢ dⱼ)ᵀ, where products are entrywise. Both resulting energy bounds are at most BC under the stated nonnegativity assumptions. -/
def mul (a : BoundedFactorization f B) (b : BoundedFactorization g C)
    (hB : 0 ≤ B) : BoundedFactorization (fun x y => f x y * g x y) (B * C) where
  rank := a.rank * b.rank
  left x i := a.left x (finProdFinEquiv.symm i).1 * b.left x (finProdFinEquiv.symm i).2
  right y i := a.right y (finProdFinEquiv.symm i).1 * b.right y (finProdFinEquiv.symm i).2
  reconstruct x y := by
    rw [a.reconstruct, b.reconstruct, ← Equiv.sum_comp finProdFinEquiv]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  left_bound x := by
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, mul_pow]
    rw [← Finset.sum_mul_sum]
    exact mul_le_mul (a.left_bound x) (b.left_bound x) (Finset.sum_nonneg (by intros; positivity)) hB
  right_bound y := by
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, mul_pow]
    rw [← Finset.sum_mul_sum]
    exact mul_le_mul (a.right_bound y) (b.right_bound y) (Finset.sum_nonneg (by intros; positivity)) hB

/-- The empty product has a one-dimensional constant factorization. -/
/- Mathematical definition (normal notation): Represent the constant-one table by a single constant left factor and right factor, each equal to one. Its pointwise energy bound is one. -/
def one : BoundedFactorization (fun (_ : X) (_ : Y) => 1) 1 where
  rank := 1
  left _ _ := 1
  right _ _ := 1
  reconstruct _ _ := by simp
  left_bound _ := by simp
  right_bound _ := by simp

section Expectations

variable [Fintype X] [Fintype Y]

/-- A scalar product discrepancy estimate extends to every bounded factorization. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For factor ∈ BoundedFactorization(f, B); P, Q ∈ 𝒟((X × Y)); L ∈ 𝒟(X); R ∈ 𝒟(Y); δ ∈ ℝ, assume 0 ≤ B; 0 ≤ δ; ∀ a ∈ X → ℝ, ∀ b ∈ Y → ℝ, |𝔼_(xy ← P) [a((xy)₁) · b((xy)₂)] - 𝔼_(xy ← Q) [a((xy)₁) · b((xy)₂)]| ≤ δ · √(𝔼_(x ← L) [(a(x))²]) · √(𝔼_(y ← R) [(b(y))²]). Then

|𝔼_(xy ← P) [f((xy)₁, (xy)₂)] - 𝔼_(xy ← Q) [f((xy)₁, (xy)₂)]| ≤ δ · B.
-/
theorem discrepancy (factor : BoundedFactorization f B) (hB : 0 ≤ B)
    (P Q : FiniteDistribution (X × Y)) (L : FiniteDistribution X) (R : FiniteDistribution Y)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : ∀ a : X → ℝ, ∀ b : Y → ℝ,
      |P.expect (fun xy => a xy.1 * b xy.2) - Q.expect (fun xy => a xy.1 * b xy.2)| ≤
        δ * Real.sqrt (L.expect (fun x => a x ^ 2)) * Real.sqrt (R.expect (fun y => b y ^ 2))) :
    |P.expect (fun xy => f xy.1 xy.2) - Q.expect (fun xy => f xy.1 xy.2)| ≤ δ * B := by
  let A := fun i => L.expect (fun x => factor.left x i ^ 2)
  let C := fun i => R.expect (fun y => factor.right y i ^ 2)
  have hA (i) : 0 ≤ A i := L.expect_nonneg _ (by intro x; positivity)
  have hC (i) : 0 ≤ C i := R.expect_nonneg _ (by intro y; positivity)
  have hleft : (∑ i, A i) ≤ B := by
    have he : (∑ i, A i) = L.expect (fun x => ∑ i, factor.left x i ^ 2) := by
      simp only [A, FiniteDistribution.expect, Finset.mul_sum]
      exact Finset.sum_comm
    rw [he]
    exact L.expect_le_const factor.left_bound
  have hright : (∑ i, C i) ≤ B := by
    have he : (∑ i, C i) = R.expect (fun y => ∑ i, factor.right y i ^ 2) := by
      simp only [C, FiniteDistribution.expect, Finset.mul_sum]
      exact Finset.sum_comm
    rw [he]
    exact R.expect_le_const factor.right_bound
  have hexpand (S : FiniteDistribution (X × Y)) :
      S.expect (fun xy => f xy.1 xy.2) =
        ∑ i, S.expect (fun xy => factor.left xy.1 i * factor.right xy.2 i) := by
    simp only [FiniteDistribution.expect, factor.reconstruct, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hexpand, hexpand, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |P.expect (fun xy => factor.left xy.1 i * factor.right xy.2 i) -
        Q.expect (fun xy => factor.left xy.1 i * factor.right xy.2 i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, δ * Real.sqrt (A i) * Real.sqrt (C i) :=
      Finset.sum_le_sum (fun i _ => hscalar (fun x => factor.left x i) (fun y => factor.right y i))
    _ = δ * ∑ i, Real.sqrt (A i) * Real.sqrt (C i) := by
      simp [Finset.mul_sum, mul_assoc]
    _ ≤ δ * (Real.sqrt (∑ i, A i) * Real.sqrt (∑ i, C i)) :=
      mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le _ hA hC) hδ
    _ ≤ δ * (Real.sqrt B * Real.sqrt B) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hδ
    _ = δ * B := by rw [Real.mul_self_sqrt hB]

end Expectations

end BoundedFactorization

/-- The concrete inner-product fiber distributions satisfy the scalar hypothesis used by the adaptive one-wire comparison. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For F a set; n ∈ ℕ; s, t ∈ F; a, b ∈ U(F, n) → ℝ, assume F is a field; F is finite; 2 ≤ n. Then

|𝔼_(xy ← (stateEquivProd(F, n)_*μₛ)) [a((xy)₁) · b((xy)₂)] - 𝔼_(xy ← (stateEquivProd(F, n)_*μₜ)) [a((xy)₁) · b((xy)₂)]| ≤ zeta(F, n) · √(𝔼_(x ← uniformShare(F, n)) [(a(x))²]) · √(𝔼_(y ← uniformShare(F, n)) [(b(y))²]).
-/
theorem wire_scalar_discrepancy
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (hn : 2 ≤ n) (s t : F) (a b : U F n → ℝ) :
    |((mu F n hn s).map (stateEquivProd F n)).expect (fun xy => a xy.1 * b xy.2) -
      ((mu F n hn t).map (stateEquivProd F n)).expect (fun xy => a xy.1 * b xy.2)| ≤
      zeta F n * Real.sqrt ((uniformShare F n hn).expect (fun x => a x ^ 2)) *
        Real.sqrt ((uniformShare F n hn).expect (fun y => b y ^ 2)) := by
  simpa! only [MatrixRefresh.expect_map, stateEquivProd, Equiv.coe_fn_mk,
    ← shareL2_eq_sqrt_expect hn] using innerProduct_discrepancy hn s t a b

/-- The explicit factorization certificate gives the actual wire-label bound with `δ_n = 2q / sqrt(q^n)`, including zero plaintexts. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For F a set; n ∈ ℕ; s, t ∈ F; f ∈ U(F, n) → U(F, n) → ℝ; B ∈ ℝ; factor ∈ BoundedFactorization(f, B), assume F is a field; F is finite; 2 ≤ n; 0 ≤ B. Then

|𝔼_(x ← μₛ) [f(x.L, x.R)] - 𝔼_(x ← μₜ) [f(x.L, x.R)]| ≤ zeta(F, n) · B.
-/
theorem wire_factorization_discrepancy
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (hn : 2 ≤ n) (s t : F) (f : U F n → U F n → ℝ) {B : ℝ}
    (factor : BoundedFactorization f B) (hB : 0 ≤ B) :
    |(mu F n hn s).expect (fun x => f x.L x.R) -
      (mu F n hn t).expect (fun x => f x.L x.R)| ≤ zeta F n * B := by
  have h := factor.discrepancy hB
    ((mu F n hn s).map (stateEquivProd F n))
    ((mu F n hn t).map (stateEquivProd F n))
    (uniformShare F n hn) (uniformShare F n hn)
    (by unfold zeta; positivity) (wire_scalar_discrepancy hn s t)
  simpa! only [MatrixRefresh.expect_map, stateEquivProd, Equiv.coe_fn_mk] using h

end CircuitCompiler
