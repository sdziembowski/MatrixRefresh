import Mathlib.LinearAlgebra.Basis.VectorSpace
import Proofs.Compiler.Construction.Parameters
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.DualPairing



set_option autoImplicit false

/-!
# Unrestricted matrix extensions

The two row constraints give fibers of size `(fieldCard F) ^ (n - 2)`. A basis extension turns the simultaneous row and column constraints into a product of `n - 2` such fibers. Thus compatible prescribed images have exactly `(fieldCard F) ^ ((n - 2) ^ 2)` matrices. Neither the matrix nor the prescribed outputs are required to be invertible or independent.

The proof changes representation twice. `matrixCompletionEquivLinearCompletion` replaces a matrix by its linear map; `completionEquivFreeImages` replaces that map by the images of the basis vectors outside the two prescribed columns. These are explicit equivalences, so the cardinality argument also proves existence for every compatible prescription. `completion_probability` then divides by the number of all matrices, giving the exact `(fieldCard F)^4 / (vectorCard F n)^4` coefficient used in `MatrixAverage.lean`.
-/

namespace MatrixRefresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open Refresh Module

open scoped Classical

/-- The four scalar equations forced by the two row and column actions. They express `l_i · (A rho_j) = (l_i A) · rho_j`. The counting theorem assumes independence of the input families `l` and `rho`, not of their prescribed outputs. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; l, rho, lout, rout ∈ {0,…,2-1} → V(F, n), define

ExtensionCompatible(l, rho, lout, rout) := ∀ i, j, (l(i) · rout(j)) = (lout(i) · rho(j)).
-/
def ExtensionCompatible {n : ℕ} (l rho lout rout : Fin 2 → V F n) : Prop :=
  ∀ i j, dot (l i) (rout j) = dot (lout i) (rho j)

/-- All unrestricted matrices realizing the two prescribed row images and two prescribed column images. The subtype includes singular matrices and does not assume the inputs or outputs are independent; those assumptions enter the counting theorems. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; l, rho, lout, rout ∈ {0,…,2-1} → V(F, n), define

MatrixCompletion(l, rho, lout, rout) := {A ∈ F^({0,…,n−1} × {0,…,n−1}) | (∀ i, Matrix.vecMul(l(i), A) = lout(i)) ∧ (∀ j, Matrix.mulVec(A, rho(j)) = rout(j))}.
-/
def MatrixCompletion {n : ℕ} (l rho lout rout : Fin 2 → V F n) :=
  {A : Matrix (Fin n) (Fin n) F //
    (∀ i, Matrix.vecMul (l i) A = lout i) ∧
    (∀ j, Matrix.mulVec A (rho j) = rout j)}

/-- Equip the matrices satisfying the prescribed row and column images with a finite enumeration, so their number can be expressed as a finite cardinality. -/
noncomputable instance {n : ℕ} (l rho lout rout : Fin 2 → V F n) :
    Fintype (MatrixCompletion l rho lout rout) := by
  classical
  unfold MatrixCompletion
  infer_instance

/-- Each pair of independent row equations has exactly `(fieldCard F) ^ (n - 2)` solutions. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; l ∈ {0,…,2-1} → V(F, n); gamma ∈ {0,…,2-1} → F, assume 2 ≤ n; LinearIndependent(F, l). Then

|{v ∈ V(F, n) | dotMap(l, v) = gamma}| = (|F|)^(n − 2).
-/
theorem card_dotMap_fiber {n : ℕ} (hn : 2 ≤ n) (l : Fin 2 → V F n)
    (hl : LinearIndependent F l) (gamma : Fin 2 → F) :
    Fintype.card {v : V F n // dotMap l v = gamma} = fieldCard F ^ (n - 2) := by
  have hcard := Refresh.card_fiber_mul l hl gamma
  -- Surjectivity of the two independent linear forms makes all fibers equipotent: `(fieldCard F)^n = |fiber| * (fieldCard F)^2`.
  have hpow : fieldCard F ^ n = fieldCard F ^ (n - 2) * fieldCard F ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hn]
  rw [hpow] at hcard
  exact Nat.eq_of_mul_eq_mul_right (pow_pos Fintype.card_pos 2) hcard

/-- The same prescribed-image problem for linear maps: composing with the two row forms gives the prescribed output forms, and the two column inputs have their prescribed images. It is equivalent to matrix completion in coordinates. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; l, rho, lout, rout ∈ {0,…,2-1} → V(F, n), define

LinearCompletion(l, rho, lout, rout) := {f ∈ V(F, n) —linear over F→ V(F, n) | comp(dotMap(l))(f) = dotMap(lout) ∧ ∀ j, f(rho(j)) = rout(j)}.
-/
def LinearCompletion {n : ℕ} (l rho lout rout : Fin 2 → V F n) :=
  {f : V F n →ₗ[F] V F n // (dotMap l).comp f = dotMap lout ∧ ∀ j, f (rho j) = rout j}

/-- The linear maps satisfying the prescribed images form a finite set, since the ambient vector space is finite. This supplies an enumeration for counting them. -/
noncomputable instance {n : ℕ} (l rho lout rout : Fin 2 → V F n) :
    Fintype (LinearCompletion l rho lout rout) := by
  classical
  letI : Fintype (V F n →ₗ[F] V F n) :=
    Fintype.ofInjective (fun f : V F n →ₗ[F] V F n => (f : V F n → V F n)) DFunLike.coe_injective
  unfold LinearCompletion
  infer_instance

/-- A completion is determined exactly by the images of the free basis vectors. The basis begins with `rho 0, rho 1`, whose images are already prescribed. Each remaining image may be chosen independently in the affine fiber imposed by the two row constraints. Compatibility validates the two prescribed images. -/
/- Mathematical definition (normal notation): Choose a basis whose first two vectors are the prescribed columns ρ₁,ρ₂. For compatible row and column prescriptions, a linear completion A is uniquely determined by its remaining basis images vⱼ := A(bⱼ). Each vⱼ may be chosen independently subject to ℓᵢ · vⱼ = ℓᵢ^out · bⱼ for i = 1,2. The bijection sends A to this family of free images; its inverse extends the prescribed basis images linearly. -/
noncomputable def completionEquivFreeImages {n : ℕ} {J : Type*}
    (l rho lout rout : Fin 2 → V F n) (b : Basis (Fin 2 ⊕ J) F (V F n))
    (hb : ∀ j, b (Sum.inl j) = rho j) (hc : ExtensionCompatible l rho lout rout) :
    LinearCompletion l rho lout rout ≃
      ((j : J) → {v : V F n // dotMap l v = dotMap lout (b (Sum.inr j))}) where
  toFun f j := ⟨f.val (b (Sum.inr j)), by
    exact DFunLike.congr_fun f.property.1 (b (Sum.inr j))⟩
  invFun g := ⟨b.constr F (Sum.elim rout (fun j => (g j).val)), by
    constructor
    -- Checking on the basis separates the prescribed columns (`inl`) from the freely chosen images (`inr`); no invertibility is required.
    · apply b.ext
      intro j
      cases j with
      | inl j =>
        ext i
        simp only [LinearMap.comp_apply, Basis.constr_basis, Sum.elim_inl,
          dotMap_apply]
        rw [hb]
        exact hc i j
      | inr j =>
        simpa only [LinearMap.comp_apply, Basis.constr_basis, Sum.elim_inr]
          using (g j).property
    · intro j
      rw [← hb j, Basis.constr_basis]
      rfl⟩
  left_inv f := by
    apply Subtype.ext
    apply b.ext
    intro j
    cases j with
    | inl j =>
      simp only [Basis.constr_basis, Sum.elim_inl]
      rw [hb]
      exact (f.property.2 j).symm
    | inr j => simp only [Basis.constr_basis, Sum.elim_inr]
  right_inv g := by
    funext j
    apply Subtype.ext
    simp only [Basis.constr_basis, Sum.elim_inr]

/-- Counting completions reduces to independent choices for the free images. There are `n - 2` free basis vectors and `(fieldCard F)^(n - 2)` choices for each image; the chosen images themselves need not be linearly independent. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; J a set; l, rho, lout, rout ∈ {0,…,2-1} → V(F, n); b ∈ Basis(({0,…,2-1} ⊕ J), F, V(F, n)), assume 2 ≤ n; J is finite; LinearIndependent(F, l); ∀ j, b(Sum.inl(j)) = rho(j); ExtensionCompatible(l, rho, lout, rout). Then

|LinearCompletion(l, rho, lout, rout)| = (|F|)^((n − 2)²).
-/
theorem card_linearCompletion_with_basis {n : ℕ} (hn : 2 ≤ n) {J : Type*} [Fintype J]
    (l rho lout rout : Fin 2 → V F n) (hl : LinearIndependent F l)
    (b : Basis (Fin 2 ⊕ J) F (V F n))
    (hb : ∀ j, b (Sum.inl j) = rho j) (hc : ExtensionCompatible l rho lout rout) :
    Fintype.card (LinearCompletion l rho lout rout) = fieldCard F ^ ((n - 2) ^ 2) := by
  classical
  have hJ : Fintype.card J = n - 2 := by
    have hd := Module.finrank_eq_card_basis b
    simp only [Module.finrank_pi, Fintype.card_fin, Fintype.card_sum] at hd
    omega
  rw [Fintype.card_congr (completionEquivFreeImages l rho lout rout b hb hc), Fintype.card_pi]
  simp_rw [card_dotMap_fiber hn l hl]
  simp only [Finset.prod_const, Finset.card_univ, hJ, ← pow_mul, pow_two]

/-- Extending an independent pair to a basis retains the original two columns. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; rho ∈ {0,…,2-1} → V(F, n); j ∈ {0,…,2-1}, assume LinearIndependent(F, rho). Then

Basis.sumExtend(Sum.inl(j)) = rho(j).
-/
theorem sumExtend_inl {n : ℕ} (rho : Fin 2 → V F n) (hrho : LinearIndependent F rho)
    (j : Fin 2) : Basis.sumExtend hrho (Sum.inl j) = rho j := by
  classical
  simp [Basis.sumExtend]
  rfl

/-- Two independent input rows and two independent input columns, with compatible prescribed images, admit exactly `(fieldCard F)^((n-2)^2)` linear-map completions. The outputs and the completing map need not be independent or invertible. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; l, rho, lout, rout ∈ {0,…,2-1} → V(F, n), assume 2 ≤ n; LinearIndependent(F, l); LinearIndependent(F, rho); ExtensionCompatible(l, rho, lout, rout). Then

|LinearCompletion(l, rho, lout, rout)| = (|F|)^((n − 2)²).
-/
theorem card_linearCompletion_of_compatible {n : ℕ} (hn : 2 ≤ n)
    (l rho lout rout : Fin 2 → V F n)
    (hl : LinearIndependent F l) (hrho : LinearIndependent F rho)
    (hc : ExtensionCompatible l rho lout rout) :
    Fintype.card (LinearCompletion l rho lout rout) = fieldCard F ^ ((n - 2) ^ 2) := by
  classical
  exact card_linearCompletion_with_basis hn l rho lout rout hl
    (Basis.sumExtend hrho) (sumExtend_inl rho hrho) hc

/-- Row action becomes composition of linear forms with the matrix's linear map. Testing on coordinate vectors recovers the original row equalities. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; l, lout ∈ {0,…,2-1} → V(F, n); A ∈ F^({0,…,n−1} × {0,…,n−1}), we have

(∀ i, Matrix.vecMul(l(i), A) = lout(i)) ⇔ comp(dotMap(l))(Matrix.toLin'(A)) = dotMap(lout).
-/
theorem matrix_row_constraints_iff {n : ℕ} (l lout : Fin 2 → V F n)
    (A : Matrix (Fin n) (Fin n) F) :
    (∀ i, Matrix.vecMul (l i) A = lout i) ↔
      (dotMap l).comp (Matrix.toLin' A) = dotMap lout := by
  constructor
  · intro h
    apply LinearMap.ext
    intro v
    funext i
    change dotProduct (l i) (Matrix.mulVec A v) = dotProduct (lout i) v
    rw [Matrix.dotProduct_mulVec, h i]
  · intro h i
    funext j
    have hi := congrFun (DFunLike.congr_fun h (Pi.single j 1)) i
    change dotProduct (l i) (Matrix.mulVec A (Pi.single j 1)) =
      dotProduct (lout i) (Pi.single j 1) at hi
    simpa only [Matrix.dotProduct_mulVec, dotProduct_single, mul_one] using hi

/-- The standard matrix/linear-map equivalence preserves both prescribed actions. -/
/- Mathematical definition (normal notation): Identify a matrix A with the linear map x ↦ A · x. This is a bijection between matrices satisfying the prescribed two row and two column equations and linear maps satisfying the same equations; the inverse takes coordinates in the standard basis. -/
noncomputable def matrixCompletionEquivLinearCompletion {n : ℕ}
    (l rho lout rout : Fin 2 → V F n) :
    MatrixCompletion l rho lout rout ≃ LinearCompletion l rho lout rout where
  toFun A := ⟨Matrix.toLin' A.val,
    (matrix_row_constraints_iff l lout A.val).mp A.property.1, A.property.2⟩
  invFun f := ⟨LinearMap.toMatrix' f.val, by
    constructor
    · apply (matrix_row_constraints_iff l lout _).mpr
      simpa only [Matrix.toLin'_toMatrix'] using f.property.1
    · intro j
      simpa only [LinearMap.toMatrix'_mulVec] using f.property.2 j⟩
  left_inv A := Subtype.ext (LinearMap.toMatrix'_toLin' A.val)
  right_inv f := Subtype.ext (Matrix.toLin'_toMatrix' f.val)

/-- In dimension at least two, independent input row and column pairs with compatible prescribed images have exactly `(fieldCard F)^((n-2)^2)` unrestricted matrix completions. Singular completions and dependent or zero outputs are included. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; l, rho, lout, rout ∈ {0,…,2-1} → V(F, n), assume 2 ≤ n; LinearIndependent(F, l); LinearIndependent(F, rho); ExtensionCompatible(l, rho, lout, rout). Then

|MatrixCompletion(l, rho, lout, rout)| = (|F|)^((n − 2)²).
-/
theorem card_matrixCompletion_of_compatible {n : ℕ} (hn : 2 ≤ n)
    (l rho lout rout : Fin 2 → V F n)
    (hl : LinearIndependent F l) (hrho : LinearIndependent F rho)
    (hc : ExtensionCompatible l rho lout rout) :
    Fintype.card (MatrixCompletion l rho lout rout) = fieldCard F ^ ((n - 2) ^ 2) := by
  rw [Fintype.card_congr (matrixCompletionEquivLinearCompletion l rho lout rout)]
  exact card_linearCompletion_of_compatible hn l rho lout rout hl hrho hc

/-- Each compatible output quadruple has mass `(fieldCard F)^4 / (vectorCard F n)^4` under a uniform matrix, where `(vectorCard F n) = (fieldCard F)^n`. The exponent identity over the integers is `(n - 2)^2 - n^2 = 4 - 4*n`; no estimate has been introduced here. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; l, rho, lout, rout ∈ {0,…,2-1} → V(F, n), assume 2 ≤ n; LinearIndependent(F, l); LinearIndependent(F, rho); ExtensionCompatible(l, rho, lout, rout). Then

|MatrixCompletion(l, rho, lout, rout)| / |F^({0,…,n−1} × {0,…,n−1})| = (|F|)⁴ / (|F|ⁿ)⁴.
-/
theorem completion_probability {n : ℕ} (hn : 2 ≤ n)
    (l rho lout rout : Fin 2 → V F n)
    (hl : LinearIndependent F l) (hrho : LinearIndependent F rho)
    (hc : ExtensionCompatible l rho lout rout) :
    (Fintype.card (MatrixCompletion l rho lout rout) : ℝ) /
        Fintype.card (Matrix (Fin n) (Fin n) F) = (fieldCard F : ℝ) ^ 4 / (vectorCard F n : ℝ) ^ 4 := by
  rw [card_matrixCompletion_of_compatible hn l rho lout rout hl hrho hc,
    card_all_matrices]
  simp only [Nat.cast_pow, vectorCard]
  have hexp : (n - 2) ^ 2 + n * 4 = 4 + n ^ 2 := by
    have hsub := Nat.sub_add_cancel hn
    nlinarith
  have hqpos : (0 : ℝ) < fieldCard F := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hp : (fieldCard F : ℝ) ^ ((n - 2) ^ 2) * ((fieldCard F : ℝ) ^ n) ^ 4 =
      (fieldCard F : ℝ) ^ 4 * (fieldCard F : ℝ) ^ (n ^ 2) := by
    rw [← pow_mul, ← pow_add, hexp, pow_add]
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  exact hp

end MatrixRefresh
