import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Notation



set_option autoImplicit false

/-!
# The finite-field pairing as a linear map

For a family `l : Fin k → V F n` of field-valued rows, `dotMap l` is the linear map sending a vector to its `k` pairings.  Linear independence of the family is exactly surjectivity of `dotMap l`, and each fibre of a surjective linear map between finite spaces has the same size, so the fibres of `dotMap l` have `fieldCard F ^ n / fieldCard F ^ k` elements.
-/

namespace Refresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open scoped BigOperators

/-- Pairing with a finite family of rows, as a linear map. -/
/- Mathematical definition (normal notation): For rows ℓ₁,…,ℓₖ, define the linear map x ↦ (ℓᵢ · x)ᵢ₌₁ᵏ from 𝔽ⁿ to 𝔽ᵏ. -/
def dotMap {n k : ℕ} (l : Fin k → V F n) : V F n →ₗ[F] (Fin k → F) where
  toFun x := fun i => dot (l i) x
  map_add' x y := by
    funext i
    simp [dot, dotProduct_add]
  map_smul' a x := by
    funext i
    simp [dot, dotProduct_smul]

/-- Each coordinate of the pairing map is the inner product with the corresponding row. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, k ∈ ℕ; l ∈ {0,…,k-1} → V(F, n); x ∈ V(F, n); i ∈ {0,…,k-1}, we have

dotMap(l, x, i) = (l(i) · x).
-/
@[simp] theorem dotMap_apply {n k : ℕ} (l : Fin k → V F n) (x : V F n) (i : Fin k) :
    dotMap l x i = dot (l i) x :=
  rfl

/-- The simultaneous pairing map is matrix multiplication by the matrix whose rows are the given vectors. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, k ∈ ℕ; l ∈ {0,…,k-1} → V(F, n), we have

dotMap(l) = Matrix.mulVecLin(Matrix.of(l)).
-/
theorem dotMap_eq_mulVecLin {n k : ℕ} (l : Fin k → V F n) :
    dotMap l = Matrix.mulVecLin (Matrix.of l) := by
  ext x i
  simp [dot, Matrix.mulVec, dotProduct]

/-- Linearly independent rows make every prescribed tuple of pairing values attainable. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, k ∈ ℕ; l ∈ {0,…,k-1} → V(F, n), assume LinearIndependent(F, l). Then

dotMap(l) is surjective.
-/
theorem dotMap_surjective {n k : ℕ} (l : Fin k → V F n) (h : LinearIndependent F l) :
    Function.Surjective (dotMap l) := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [dotMap_eq_mulVecLin]
  change (Matrix.of l).rank = Module.finrank F (Fin k → F)
  rw [Matrix.rank_eq_finrank_span_row]
  change Module.finrank F (Submodule.span F (Set.range l)) = _
  rw [finrank_span_eq_card h, Module.finrank_pi, Fintype.card_fin]

/-- For `k` independent rows, each prescribed pairing fiber has cardinality which, multiplied by `(fieldCard F)^k`, equals `(fieldCard F)^n`. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, k ∈ ℕ; l ∈ {0,…,k-1} → V(F, n); γ ∈ {0,…,k-1} → F, assume LinearIndependent(F, l). Then

|{v ∈ V(F, n) | dotMap(l, v) = γ}| · (|F|)ᵏ = (|F|)ⁿ.
-/
theorem card_fiber_mul {n k : ℕ} (l : Fin k → V F n) (h : LinearIndependent F l)
    (γ : Fin k → F) :
    Fintype.card {v : V F n // dotMap l v = γ} * fieldCard F ^ k = fieldCard F ^ n := by
  classical
  have hsurj := dotMap_surjective l h
  have hconst : ∀ δ : Fin k → F,
      Fintype.card {v : V F n // dotMap l v = δ} =
        Fintype.card {v : V F n // dotMap l v = γ} := by
    intro δ
    obtain ⟨x, hx⟩ := hsurj (δ - γ)
    refine Fintype.card_congr ⟨fun v => ⟨v.val - x, ?_⟩, fun v => ⟨v.val + x, ?_⟩, ?_, ?_⟩
    · have := v.property
      simp [map_sub, this, hx]
    · have := v.property
      simp [map_add, this, hx]
    · intro v; ext; simp
    · intro v; ext; simp
  have hsum : ∑ δ : Fin k → F, Fintype.card {v : V F n // dotMap l v = δ}
      = Fintype.card (V F n) := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv (fun v : V F n => dotMap l v))
  rw [Finset.sum_congr rfl (fun δ _ => hconst δ)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  simpa only [Fintype.card_fun, Fintype.card_fin, fieldCard, V, nsmul_eq_mul, mul_comm] using hsum

end Refresh
