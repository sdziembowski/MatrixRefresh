import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Proofs.Compiler.Foundations.MatrixRefreshing.Probability.FiniteProbability



/-!
# Normalized finite table algebra

All averages in this file are normalized.  The row and column index types are kept separate, so the same results apply to local-pair tables and share tables. No positivity or symmetry of the entries of a table is assumed.

The first group of lemmas provides the finite-average algebra used throughout the proof. `fourCycle` is defined as a squared Gram average, which makes its nonnegativity immediate, and then expanded as the signed product of the four corners of a rectangle. `cubic` is its normalized cubic gradient: the derivative of four-cycle energy in direction `Ψ` is `4 * pairing (cubic Φ) Ψ`.

The row and column pairing identities supply nonnegative local energies for the variational approximation argument. The derivative and continuity results justify its optimization step. Every normalization is explicit in `uavg`, so changing from share tables to endpoint tables introduces no implicit matrix-size factors.
-/

set_option autoImplicit false

open scoped BigOperators

namespace MatrixRefresh

noncomputable section

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- The uniform normalized average of a real function on a finite type. It is also defined on the empty type, where it equals zero; lemmas saying that constants average to themselves therefore require `Nonempty`. -/
/-
Mathematical definition (normal notation): For a real function on a finite nonempty set X, define the uniform average

𝔼_(x ← X) [f(x)] := 1/(|X|)∑_(x ∈ X) f(x).

The formal auxiliary definition assigns the value 0 when X is empty.
-/
def uavg (f : α → ℝ) : ℝ := (Fintype.card α : ℝ)⁻¹ * ∑ a, f a

/-- On a nonempty finite type, the normalized average equals expectation under the uniform probability distribution. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ α → ℝ, assume α ≠ ∅. Then

𝔼ᵤ [f(u)] = 𝔼_(v ← 𝒰_α) [f(v)].
-/
theorem uavg_eq_expect_uniform [Nonempty α] (f : α → ℝ) :
    uavg f = (Refresh.FiniteDistribution.uniform : Refresh.FiniteDistribution α).expect f := by
  simp [uavg, Refresh.FiniteDistribution.expect, Refresh.FiniteDistribution.uniform, Finset.mul_sum]

/-- Pointwise equal functions have the same normalized finite average. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f, g ∈ α → ℝ, assume ∀ a, f(a) = g(a). Then

𝔼ᵤ [f(u)] = 𝔼ᵥ [g(v)].
-/
theorem uavg_congr {f g : α → ℝ} (h : ∀ a, f a = g a) : uavg f = uavg g := by
  unfold uavg
  congr 1
  exact Finset.sum_congr rfl (fun a _ => h a)

/-- The uniform normalized average of the zero function is zero, including on an empty type. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

𝔼_(x ∈ α) [0] = 0.
-/
@[simp] theorem uavg_zero : uavg (fun _ : α => (0 : ℝ)) = 0 := by
  simp [uavg]

/-- On a nonempty finite type, a constant averages to itself. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c ∈ ℝ, assume α ≠ ∅. Then

𝔼_(x ∈ α) [c] = c.
-/
@[simp] theorem uavg_const [Nonempty α] (c : ℝ) : uavg (fun _ : α => c) = c := by
  rw [uavg_eq_expect_uniform, Refresh.FiniteDistribution.expect_const]

/-- A pointwise nonnegative real function has a nonnegative normalized finite average. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ α → ℝ, assume ∀ a, 0 ≤ f(a). Then

0 ≤ 𝔼ᵤ [f(u)].
-/
theorem uavg_nonneg {f : α → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ uavg f :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun a _ => h a))

/-- A pointwise inequality is preserved by uniform normalized averaging. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f, g ∈ α → ℝ, assume ∀ a, f(a) ≤ g(a). Then

𝔼ᵤ [f(u)] ≤ 𝔼ᵥ [g(v)].
-/
theorem uavg_mono {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : uavg f ≤ uavg g :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => h a))
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- Uniform normalized averaging distributes over addition of real functions. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f, g ∈ α → ℝ, we have

𝔼ₐ [f(a) + g(a)] = 𝔼ᵤ [f(u)] + 𝔼ᵥ [g(v)].
-/
theorem uavg_add (f g : α → ℝ) :
    uavg (fun a => f a + g a) = uavg f + uavg g := by
  simp [uavg, Finset.sum_add_distrib, mul_add]

/-- Uniform normalized averaging distributes over subtraction of real functions. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f, g ∈ α → ℝ, we have

𝔼ₐ [f(a) - g(a)] = 𝔼ᵤ [f(u)] - 𝔼ᵥ [g(v)].
-/
theorem uavg_sub (f g : α → ℝ) :
    uavg (fun a => f a - g a) = uavg f - uavg g := by
  simp [uavg, Finset.sum_sub_distrib, mul_sub]

/-- A fixed real factor on the right can be taken outside a normalized finite average. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ α → ℝ; c ∈ ℝ, we have

𝔼ₐ [f(a) · c] = 𝔼ᵤ [f(u)] · c.
-/
theorem uavg_mul_const (f : α → ℝ) (c : ℝ) :
    uavg (fun a => f a * c) = uavg f * c := by
  simp [uavg, Finset.sum_mul, mul_assoc]

/-- A fixed real factor on the left can be taken outside a normalized finite average. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c ∈ ℝ; f ∈ α → ℝ, we have

𝔼ₐ [c · f(a)] = c · 𝔼ᵤ [f(u)].
-/
theorem uavg_const_mul (c : ℝ) (f : α → ℝ) :
    uavg (fun a => c * f a) = c * uavg f := by
  simp [uavg, Finset.mul_sum, mul_left_comm]

/-- Two independent normalized finite averages may be taken in either order. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ α → β → ℝ, we have

𝔼ₐ [𝔼ᵥ [f(a, v)]] = 𝔼_b [𝔼ₐ [f(a, b)]].
-/
theorem uavg_comm (f : α → β → ℝ) :
    uavg (fun a => uavg (f a)) = uavg (fun b => uavg (fun a => f a b)) := by
  simp only [uavg, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

/-- The product of two separate uniform averages equals the double average of their separated product. -/

/-
Mathematical statement (normal notation): Independent uniform averages factor:

𝔼ₓ [f(x)] · 𝔼_y [g(y)] = 𝔼ₓ [𝔼_y [f(x) · g(y)]].
-/
theorem uavg_mul_uavg (f : α → ℝ) (g : β → ℝ) :
    uavg f * uavg g = uavg (fun a => uavg (fun b => f a * g b)) := by
  simp only [uavg_const_mul, uavg_mul_const]

/-- Bijections preserve both the finite sum and its cardinality normalization. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ α ≃ β; f ∈ β → ℝ, we have

𝔼ₐ [f(e(a))] = 𝔼ᵤ [f(u)].
-/
theorem uavg_equiv (e : α ≃ β) (f : β → ℝ) :
    uavg (fun a => f (e a)) = uavg f := by
  unfold uavg
  rw [Fintype.card_congr e, Equiv.sum_comp e]

/-- A uniform average on a product equals two independent uniform averages. This is the finite Fubini identity used when regrouping endpoint coordinates. -/

/-
Mathematical statement (normal notation): A uniform average on a finite product set equals iterated uniform averaging:

𝔼_((x,y) ← X × Y) [f(x,y)] = 𝔼_(x ← X) [𝔼_(y ← Y) [f(x,y)]].
-/
theorem uavg_prod (f : α × β → ℝ) :
    uavg f = uavg (fun a => uavg (fun b => f (a, b))) := by
  simp only [uavg, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

/-- The normalized bilinear pairing of two real tables. -/
/-
Mathematical definition (normal notation): The normalized pairing of two real tables is

⟨ F,G⟩ := 𝔼_(x ← X,y ← Y) [F(x,y) · G(x,y)].
-/
def pairing (Φ Ψ : α → β → ℝ) : ℝ :=
  uavg (fun x => uavg (fun y => Φ x y * Ψ x y))

/-- The normalized Gram product of two rows of a table. Off-diagonal values can have either sign; the diagonal is the mean square of a single row. -/
/-
Mathematical definition (normal notation): The normalized inner product of two rows of F is

𝔼_(y ← Y) [F(x,y) · F(x',y)].
-/
def rowProduct (Φ : α → β → ℝ) (x x' : α) : ℝ :=
  uavg (fun y => Φ x y * Φ x' y)

/-- The four-cycle energy, normalized over two independent rows. Defining it through squared Gram entries records nonnegativity before any four-corner expansion; the underlying table itself may be signed and rectangular. -/
/-
Mathematical definition (normal notation): The four-cycle energy is

𝔼_(x,x') [(𝔼_y [F(x,y) · F(x',y)])²] = 𝔼_(x,x',y,y') [F(x,y) · F(x',y) · F(x',y') · F(x,y')].

All four indices are sampled independently and uniformly.
-/
def fourCycle (Φ : α → β → ℝ) : ℝ :=
  uavg (fun x => uavg (fun x' => rowProduct Φ x x' ^ 2))

/-- The normalized cubic table `Φ Φᵀ Φ`. Both contracted indices are uniformly averaged, matching the normalizations in `pairing` and `fourCycle`. Its pairing with a perturbation gives one quarter of the energy derivative. -/
/-
Mathematical definition (normal notation): The normalized cubic table is

C_F(x,y) := 𝔼_(x',y') [F(x,y') · F(x',y') · F(x',y)].

Thus matrix multiplication is interpreted using averages over the two contracted indices.
-/
def cubic (Φ : α → β → ℝ) (x : α) (y : β) : ℝ :=
  uavg (fun ξ => rowProduct Φ x ξ * Φ ξ y)

/-- The normalized Gram product of two rows is symmetric in the row indices. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ ∈ α → β → ℝ; x, x' ∈ α, we have

rowProduct(Φ, x, x') = rowProduct(Φ, x', x).
-/
theorem rowProduct_comm (Φ : α → β → ℝ) (x x' : α) :
    rowProduct Φ x x' = rowProduct Φ x' x := by
  simp only [rowProduct, mul_comm]

/-- Every row Gram product of the zero table is zero. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For x, x' ∈ α, we have

rowProduct(((x ∈ α, x ∈ β ↦ 0)), x, x') = 0.
-/
@[simp] theorem rowProduct_zero (x x' : α) :
    rowProduct (fun (_ : α) (_ : β) => (0 : ℝ)) x x' = 0 := by
  simp [rowProduct]

/-- The zero table has zero normalized four-cycle energy. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

fourCycle(((x ∈ α, x ∈ β ↦ 0))) = 0 .
-/
@[simp] theorem fourCycle_zero : fourCycle (fun (_ : α) (_ : β) => (0 : ℝ)) = 0 := by
  simp [fourCycle]

/-- The four-cycle energy is nonnegative because it averages squared row Gram products, even when the original table has signed entries. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ ∈ α → β → ℝ, we have

0 ≤ fourCycle(Φ).
-/
theorem fourCycle_nonneg (Φ : α → β → ℝ) : 0 ≤ fourCycle Φ :=
  uavg_nonneg (fun _ => uavg_nonneg (fun _ => sq_nonneg _))

/-- Expansion into the four signed corner entries; no absolute values are inserted. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ ∈ α → β → ℝ, we have

fourCycle(Φ) = 𝔼ₓ [𝔼_(x') [𝔼_y [𝔼_(y') [Φ(x, y) · Φ(x', y) · Φ(x', y') · Φ(x, y')]]]].
-/
theorem fourCycle_expansion (Φ : α → β → ℝ) :
    fourCycle Φ = uavg (fun x => uavg (fun x' =>
      uavg (fun y => uavg (fun y' =>
        Φ x y * Φ x' y * Φ x' y' * Φ x y')))) := by
  unfold fourCycle rowProduct
  apply uavg_congr
  intro x
  apply uavg_congr
  intro x'
  -- Expand a square of a column average using two independent columns. Keep the signed corner entries; taking absolute values here would destroy the exact cancellation needed by the variational argument.
  rw [pow_two, uavg_mul_uavg]
  apply uavg_congr
  intro y
  apply uavg_congr
  intro y'
  ring

/-- Reindexing the columns by a bijection leaves each row Gram product unchanged. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ ∈ α → β → ℝ; e ∈ β ≃ β; x, x' ∈ α, we have

rowProduct(((a, b ↦ Φ(a, e(b)))), x, x') = rowProduct(Φ, x, x').
-/
theorem rowProduct_permute_columns (Φ : α → β → ℝ) (e : β ≃ β) (x x' : α) :
    rowProduct (fun a b => Φ a (e b)) x x' = rowProduct Φ x x' := by
  exact uavg_equiv e (fun y => Φ x y * Φ x' y)

/-- The four-cycle energy is invariant under any bijective relabeling of columns. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ ∈ α → β → ℝ; e ∈ β ≃ β, we have

fourCycle(((a, b ↦ Φ(a, e(b))))) = fourCycle(Φ).
-/
theorem fourCycle_permute_columns (Φ : α → β → ℝ) (e : β ≃ β) :
    fourCycle (fun a b => Φ a (e b)) = fourCycle Φ := by
  simp only [fourCycle, rowProduct_permute_columns]

/--
Pairing the cubic table with the original table along one row gives the uniform mean square of that row's Gram products.

Row energy identity used before the weighted-answer estimate.
-/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ ∈ α → β → ℝ; x ∈ α, we have

𝔼_y [cubic(Φ, x, y) · Φ(x, y)] = 𝔼_ξ [(rowProduct(Φ, x, ξ))²].
-/
theorem cubic_row_pairing (Φ : α → β → ℝ) (x : α) :
    uavg (fun y => cubic Φ x y * Φ x y) =
      uavg (fun ξ => rowProduct Φ x ξ ^ 2) := by
  simp only [cubic, ← uavg_mul_const]
  rw [uavg_comm]
  apply uavg_congr
  intro ξ
  calc
    uavg (fun y => rowProduct Φ x ξ * Φ ξ y * Φ x y) =
        rowProduct Φ x ξ * uavg (fun y => Φ x y * Φ ξ y) := by
      rw [← uavg_const_mul]
      apply uavg_congr
      intro y
      ring
    _ = rowProduct Φ x ξ ^ 2 := by rw [← rowProduct, pow_two]

/--
Pairing the cubic table with the original table along one column gives the uniform mean square of that column's Gram products.

Independent column energy identity; it does not assume a symmetric table.
-/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ ∈ α → β → ℝ; y ∈ β, we have

𝔼ₓ [cubic(Φ, x, y) · Φ(x, y)] = 𝔼_(y') [(𝔼ₓ [Φ(x, y) · Φ(x, y')])²].
-/
theorem cubic_column_pairing (Φ : α → β → ℝ) (y : β) :
    uavg (fun x => cubic Φ x y * Φ x y) =
      uavg (fun y' => (uavg (fun x => Φ x y * Φ x y')) ^ 2) := by
  simp only [cubic, rowProduct, ← uavg_mul_const]
  calc
    uavg (fun x => uavg (fun ξ => uavg (fun y' =>
        Φ x y' * Φ ξ y' * Φ ξ y * Φ x y))) =
        uavg (fun x => uavg (fun y' => uavg (fun ξ =>
          Φ x y' * Φ ξ y' * Φ ξ y * Φ x y))) := by
      apply uavg_congr
      intro x
      rw [uavg_comm]
    _ = uavg (fun y' => uavg (fun x => uavg (fun ξ =>
          Φ x y' * Φ ξ y' * Φ ξ y * Φ x y))) := uavg_comm _
    _ = uavg (fun y' => (uavg (fun x => Φ x y * Φ x y')) ^ 2) := by
      apply uavg_congr
      intro y'
      rw [pow_two, uavg_mul_uavg]
      apply uavg_congr
      intro x
      apply uavg_congr
      intro ξ
      ring

/-- For each column, the uniform pairing of the cubic table with the original table is nonnegative, by its column Gram-square representation. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ ∈ α → β → ℝ; y ∈ β, we have

0 ≤ 𝔼ₓ [cubic(Φ, x, y) · Φ(x, y)].
-/
theorem cubic_column_pairing_nonneg (Φ : α → β → ℝ) (y : β) :
    0 ≤ uavg (fun x => cubic Φ x y * Φ x y) := by
  rw [cubic_column_pairing]
  exact uavg_nonneg (fun _ => sq_nonneg _)

/-- Differentiation commutes with a normalized finite average. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ α → ℝ → ℝ; f' ∈ α → ℝ; t ∈ ℝ, assume ∀ a, HasDerivAt(f(a), f'(a), t). Then

HasDerivAt(((τ ↦ 𝔼ₐ [f(a, τ)])), 𝔼ᵤ [f'(u)], t).
-/
theorem hasDerivAt_uavg {f : α → ℝ → ℝ} {f' : α → ℝ} {t : ℝ}
    (h : ∀ a, HasDerivAt (f a) (f' a) t) :
    HasDerivAt (fun τ => uavg (fun a => f a τ)) (uavg f') t := by
  exact (HasDerivAt.fun_sum (fun a (_ : a ∈ Finset.univ) => h a)).const_mul _

/-- One of the four equal linear terms in the directional four-cycle derivative. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ, Ψ ∈ α → β → ℝ, we have

pairing(cubic(Φ), Ψ) = 𝔼ₓ [𝔼_ξ [rowProduct(Φ, x, ξ) · 𝔼_y [Ψ(x, y) · Φ(ξ, y)]]].
-/
theorem cubic_pairing_expansion (Φ Ψ : α → β → ℝ) :
    pairing (cubic Φ) Ψ = uavg (fun x => uavg (fun ξ =>
      rowProduct Φ x ξ * uavg (fun y => Ψ x y * Φ ξ y))) := by
  unfold pairing cubic
  apply uavg_congr
  intro x
  simp only [← uavg_mul_const]
  rw [uavg_comm]
  apply uavg_congr
  intro ξ
  rw [← uavg_const_mul]
  apply uavg_congr
  intro y
  ring

/-- Expand the pairing of the cubic table with a perturbation into a double row average of a row Gram product and a mixed row pairing. This orientation supplies one linear term in the four-cycle derivative. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ, Ψ ∈ α → β → ℝ, we have

pairing(cubic(Φ), Ψ) = 𝔼ₓ [𝔼_ξ [rowProduct(Φ, x, ξ) · 𝔼_y [Φ(x, y) · Ψ(ξ, y)]]].
-/
theorem cubic_pairing_expansion' (Φ Ψ : α → β → ℝ) :
    pairing (cubic Φ) Ψ = uavg (fun x => uavg (fun ξ =>
      rowProduct Φ x ξ * uavg (fun y => Φ x y * Ψ ξ y))) := by
  rw [uavg_comm, cubic_pairing_expansion]
  apply uavg_congr
  intro x
  apply uavg_congr
  intro ξ
  rw [rowProduct_comm Φ ξ x]
  congr 1
  apply uavg_congr
  intro y
  ring

/--
Along a perturbation direction `Ψ`, the derivative of four-cycle energy at zero step is four times the normalized pairing of the cubic table with `Ψ`.

The derivative is for the normalized cubic: no matrix-cardinality factor is missing.
-/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ, Ψ ∈ α → β → ℝ, we have

HasDerivAt(((τ ∈ ℝ ↦ fourCycle(((x, y ↦ Φ(x, y) + τ · Ψ(x, y)))))), (4 · pairing(cubic(Φ), Ψ)), 0).
-/
theorem hasDerivAt_fourCycle (Φ Ψ : α → β → ℝ) :
    HasDerivAt (fun τ : ℝ => fourCycle (fun x y => Φ x y + τ * Ψ x y))
      (4 * pairing (cubic Φ) Ψ) 0 := by
  -- Differentiate each affine entry, then each Gram product, then its square. Finite averages commute with each differentiation step.
  have hentry (x : α) (y : β) :
      HasDerivAt (fun τ : ℝ => Φ x y + τ * Ψ x y) (Ψ x y) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).mul_const (Ψ x y)).const_add (Φ x y) using 1 <;>
      simp
  have hrow (x ξ : α) :
      HasDerivAt (fun τ : ℝ => rowProduct (fun a b => Φ a b + τ * Ψ a b) x ξ)
        (uavg (fun y => Ψ x y * Φ ξ y + Φ x y * Ψ ξ y)) 0 := by
    apply hasDerivAt_uavg
    intro y
    convert! (hentry x y).mul (hentry ξ y) using 1 <;> simp
  have hsquare (x ξ : α) :
      HasDerivAt (fun τ : ℝ => rowProduct (fun a b => Φ a b + τ * Ψ a b) x ξ ^ 2)
        (2 * rowProduct Φ x ξ *
          uavg (fun y => Ψ x y * Φ ξ y + Φ x y * Ψ ξ y)) 0 := by
    simpa using (hrow x ξ).fun_pow 2
  have h := hasDerivAt_uavg (fun x => hasDerivAt_uavg (fun ξ => hsquare x ξ))
  change HasDerivAt _ _ 0 at h
  -- Differentiating the square contributes two; the two symmetric row variations give equal cubic pairings, producing the final factor four.
  have hcoef : uavg (fun x => uavg (fun ξ => 2 * rowProduct Φ x ξ *
        uavg (fun y => Ψ x y * Φ ξ y + Φ x y * Ψ ξ y))) =
      4 * pairing (cubic Φ) Ψ := by
    calc
      _ = uavg (fun x => uavg (fun ξ =>
          2 * (rowProduct Φ x ξ * uavg (fun y => Ψ x y * Φ ξ y)) +
          2 * (rowProduct Φ x ξ * uavg (fun y => Φ x y * Ψ ξ y)))) := by
        apply uavg_congr
        intro x
        apply uavg_congr
        intro ξ
        rw [uavg_add]
        ring
      _ = 2 * pairing (cubic Φ) Ψ + 2 * pairing (cubic Φ) Ψ := by
        simp only [uavg_add, uavg_const_mul]
        rw [← cubic_pairing_expansion, ← cubic_pairing_expansion']
      _ = _ := by ring
  rw [hcoef] at h
  exact h

/-- The variational objective is a polynomial in the finitely many table entries. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

Continuous(fourCycle).
-/
theorem continuous_fourCycle : Continuous (fourCycle : (α → β → ℝ) → ℝ) := by
  unfold fourCycle rowProduct uavg
  fun_prop

/-- With the first table fixed, the normalized bilinear pairing depends continuously on the second table's finitely many real entries. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ ∈ α → β → ℝ, we have

Continuous(((Ψ ∈ α → β → ℝ ↦ pairing(Φ, Ψ)))).
-/
theorem continuous_pairing_right (Φ : α → β → ℝ) :
    Continuous (fun Ψ : α → β → ℝ => pairing Φ Ψ) := by
  unfold pairing uavg
  fun_prop

end

end MatrixRefresh
