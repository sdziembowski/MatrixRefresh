import Proofs.Compiler.Foundations.MatrixRefreshing.Counting.LinearExtensions
import Proofs.Compiler.Foundations.MatrixRefreshing.Counting.MatrixAverage



/-!
# Prescribed row and column images for unrestricted matrices

The tensor operator four-cycle proof uses all four binary rank cases. For r independent input rows and s independent input columns, compatible prescribed outputs have exactly q^((n-r)*(n-s)) completions. Dividing by the number of all matrices gives q^(r*s)/Q^(r+s). Outputs may be zero or dependent; matrices need not be invertible. The construction extends the prescribed columns to a basis and independently chooses each remaining image in a fiber of the r row equations.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

namespace CircuitCompiler.RefreshAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open Refresh MatrixRefresh Module

open scoped Classical

/-
Mathematical definition (normal notation): The prescribed rows and columns are compatible if

ℓᵢ · ρ'ⱼ = ℓ'ᵢ · ρⱼ for every i,j.

This is necessary for a matrix satisfying ℓᵢ · A = ℓ'ᵢ and A · ρⱼ = ρ'ⱼ.
-/
def ExtensionCompatible {n r s : ℕ} (l : Fin r → V F n) (rho : Fin s → V F n)
    (lout : Fin r → V F n) (rout : Fin s → V F n) : Prop :=
  ∀ i j, dot (l i) (rout j) = dot (lout i) (rho j)

/-
Mathematical definition (normal notation): The completion set consists of all matrices A ∈ 𝔽^(n × n) satisfying every prescribed equation

ℓᵢ · A = ℓ'ᵢ, A · ρⱼ = ρ'ⱼ.

Invertibility is not imposed.
-/
def MatrixCompletion {n r s : ℕ} (l : Fin r → V F n) (rho : Fin s → V F n)
    (lout : Fin r → V F n) (rout : Fin s → V F n) :=
  {A : Matrix (Fin n) (Fin n) F //
    (∀ i, Matrix.vecMul (l i) A = lout i) ∧
    (∀ j, Matrix.mulVec A (rho j) = rout j)}

noncomputable instance {n r s : ℕ} (l : Fin r → V F n) (rho : Fin s → V F n)
    (lout : Fin r → V F n) (rout : Fin s → V F n) :
    Fintype (MatrixCompletion l rho lout rout) := by
  classical
  unfold MatrixCompletion
  infer_instance

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, r ∈ ℕ; l ∈ {0,…,r-1} → V(F, n); gamma ∈ {0,…,r-1} → F, assume r ≤ n; LinearIndependent(F, l). Then

|{v ∈ V(F, n) | dotMap(l, v) = gamma}| = (|F|)^(n − r).
-/
theorem card_dotMap_fiber {n r : ℕ} (hr : r ≤ n) (l : Fin r → V F n)
    (hl : LinearIndependent F l) (gamma : Fin r → F) :
    Fintype.card {v : V F n // dotMap l v = gamma} = fieldCard F ^ (n - r) := by
  have hcard := Refresh.card_fiber_mul l hl gamma
  have hpow : fieldCard F ^ n = fieldCard F ^ (n - r) * fieldCard F ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hr]
  rw [hpow] at hcard
  exact Nat.eq_of_mul_eq_mul_right (pow_pos Fintype.card_pos r) hcard

/-
Mathematical definition (normal notation): A linear completion is a linear map f:𝔽ⁿ → 𝔽ⁿ satisfying

ℓᵢ · f(v) = ℓ'ᵢ · v for every i,v, f(ρⱼ) = ρ'ⱼ for every j.

These are the prescribed matrix-completion constraints in linear-map form.
-/
def LinearCompletion {n r s : ℕ} (l : Fin r → V F n) (rho : Fin s → V F n)
    (lout : Fin r → V F n) (rout : Fin s → V F n) :=
  {f : V F n →ₗ[F] V F n // (dotMap l).comp f = dotMap lout ∧ ∀ j, f (rho j) = rout j}

noncomputable instance {n r s : ℕ} (l : Fin r → V F n) (rho : Fin s → V F n)
    (lout : Fin r → V F n) (rout : Fin s → V F n) :
    Fintype (LinearCompletion l rho lout rout) := by
  classical
  letI : Fintype (V F n →ₗ[F] V F n) :=
    Fintype.ofInjective (fun f : V F n →ₗ[F] V F n => (f : V F n → V F n)) DFunLike.coe_injective
  unfold LinearCompletion
  infer_instance

/-
Mathematical definition (normal notation): Extend the independent prescribed column inputs ρⱼ to a basis (ρⱼ) ∪ (bₖ)_(k ∈ J). Under the row/column compatibility equations, a linear completion is determined bijectively by the free images vₖ = f(bₖ), subject only to

ℓᵢ · vₖ = ℓ'ᵢ · bₖ for all i,k.

The inverse bijection assigns f(ρⱼ) = ρ'ⱼ, f(bₖ) = vₖ, and extends linearly.
-/
noncomputable def completionEquivFreeImages {n r s : ℕ} {J : Type*}
    (l : Fin r → V F n) (rho : Fin s → V F n)
    (lout : Fin r → V F n) (rout : Fin s → V F n) (b : Basis (Fin s ⊕ J) F (V F n))
    (hb : ∀ j, b (Sum.inl j) = rho j) (hc : ExtensionCompatible l rho lout rout) :
    LinearCompletion l rho lout rout ≃
      ((j : J) → {v : V F n // dotMap l v = dotMap lout (b (Sum.inr j))}) where
  toFun f j := ⟨f.val (b (Sum.inr j)), by
    exact DFunLike.congr_fun f.property.1 (b (Sum.inr j))⟩
  invFun g := ⟨b.constr F (Sum.elim rout (fun j => (g j).val)), by
    constructor
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

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, r, s ∈ ℕ; J a set; l ∈ {0,…,r-1} → V(F, n); rho ∈ {0,…,s-1} → V(F, n); lout ∈ {0,…,r-1} → V(F, n); rout ∈ {0,…,s-1} → V(F, n); b ∈ Basis(({0,…,s-1} ⊕ J), F, V(F, n)), assume r ≤ n; J is finite; LinearIndependent(F, l); ∀ j, b(Sum.inl(j)) = rho(j); ExtensionCompatible(l, rho, lout, rout). Then

|LinearCompletion(l, rho, lout, rout)| = (|F|)^((n − r) · (n − s)).
-/
theorem card_linearCompletion_with_basis {n r s : ℕ} (hr : r ≤ n) {J : Type*} [Fintype J]
    (l : Fin r → V F n) (rho : Fin s → V F n)
    (lout : Fin r → V F n) (rout : Fin s → V F n) (hl : LinearIndependent F l)
    (b : Basis (Fin s ⊕ J) F (V F n))
    (hb : ∀ j, b (Sum.inl j) = rho j) (hc : ExtensionCompatible l rho lout rout) :
    Fintype.card (LinearCompletion l rho lout rout) = fieldCard F ^ ((n - r) * (n - s)) := by
  classical
  have hJ : Fintype.card J = n - s := by
    have hd := Module.finrank_eq_card_basis b
    simp only [Module.finrank_pi, Fintype.card_fin, Fintype.card_sum] at hd
    omega
  rw [Fintype.card_congr (completionEquivFreeImages l rho lout rout b hb hc), Fintype.card_pi]
  simp_rw [card_dotMap_fiber hr l hl]
  simp only [Finset.prod_const, Finset.card_univ, hJ, ← pow_mul]

omit [Fintype F] [DecidableEq F] in
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, s ∈ ℕ; rho ∈ {0,…,s-1} → V(F, n); j ∈ {0,…,s-1}, assume LinearIndependent(F, rho). Then

Basis.sumExtend(Sum.inl(j)) = rho(j).
-/
theorem sumExtend_inl {n s : ℕ} (rho : Fin s → V F n) (hrho : LinearIndependent F rho)
    (j : Fin s) : Basis.sumExtend hrho (Sum.inl j) = rho j := by
  classical
  simp [Basis.sumExtend]
  rfl

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, r, s ∈ ℕ; l ∈ {0,…,r-1} → V(F, n); rho ∈ {0,…,s-1} → V(F, n); lout ∈ {0,…,r-1} → V(F, n); rout ∈ {0,…,s-1} → V(F, n), assume r ≤ n; s ≤ n; LinearIndependent(F, l); LinearIndependent(F, rho); ExtensionCompatible(l, rho, lout, rout). Then

|LinearCompletion(l, rho, lout, rout)| = (|F|)^((n − r) · (n − s)).
-/
theorem card_linearCompletion_of_compatible {n r s : ℕ} (hr : r ≤ n) (_hs : s ≤ n)
    (l : Fin r → V F n) (rho : Fin s → V F n)
    (lout : Fin r → V F n) (rout : Fin s → V F n)
    (hl : LinearIndependent F l) (hrho : LinearIndependent F rho)
    (hc : ExtensionCompatible l rho lout rout) :
    Fintype.card (LinearCompletion l rho lout rout) = fieldCard F ^ ((n - r) * (n - s)) := by
  classical
  exact card_linearCompletion_with_basis hr l rho lout rout hl
    (Basis.sumExtend hrho) (sumExtend_inl rho hrho) hc

omit [Fintype F] [DecidableEq F] in
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, r ∈ ℕ; l, lout ∈ {0,…,r-1} → V(F, n); A ∈ F^({0,…,n−1} × {0,…,n−1}), we have

(∀ i, Matrix.vecMul(l(i), A) = lout(i)) ⇔ comp(dotMap(l))(Matrix.toLin'(A)) = dotMap(lout).
-/
theorem matrix_row_constraints_iff {n r : ℕ} (l lout : Fin r → V F n)
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

/- Mathematical definition (normal notation): Sending a matrix A to the linear map v ↦ A · v gives a bijection between matrix completions of the prescribed row/column constraints and linear completions of the same constraints. The inverse takes the matrix of a linear map in the standard basis. -/
noncomputable def matrixCompletionEquivLinearCompletion {n r s : ℕ}
    (l : Fin r → V F n) (rho : Fin s → V F n)
    (lout : Fin r → V F n) (rout : Fin s → V F n) :
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

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, r, s ∈ ℕ; l ∈ {0,…,r-1} → V(F, n); rho ∈ {0,…,s-1} → V(F, n); lout ∈ {0,…,r-1} → V(F, n); rout ∈ {0,…,s-1} → V(F, n), assume r ≤ n; s ≤ n; LinearIndependent(F, l); LinearIndependent(F, rho); ExtensionCompatible(l, rho, lout, rout). Then

|MatrixCompletion(l, rho, lout, rout)| = (|F|)^((n − r) · (n − s)).
-/
theorem card_matrixCompletion_of_compatible {n r s : ℕ} (hr : r ≤ n) (hs : s ≤ n)
    (l : Fin r → V F n) (rho : Fin s → V F n)
    (lout : Fin r → V F n) (rout : Fin s → V F n)
    (hl : LinearIndependent F l) (hrho : LinearIndependent F rho)
    (hc : ExtensionCompatible l rho lout rout) :
    Fintype.card (MatrixCompletion l rho lout rout) = fieldCard F ^ ((n - r) * (n - s)) := by
  rw [Fintype.card_congr (matrixCompletionEquivLinearCompletion l rho lout rout)]
  exact card_linearCompletion_of_compatible hr hs l rho lout rout hl hrho hc

omit [Field F] [DecidableEq F] in
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, we have

|F^({0,…,n−1} × {0,…,n−1})| = (|F|)^(n²).
-/
theorem card_all_matrices (n : ℕ) :
    Fintype.card (Matrix (Fin n) (Fin n) F) = fieldCard F ^ (n ^ 2) := by
  simp [Matrix, fieldCard, pow_mul, pow_two]


/- Mathematical statement (normal notation): Let ℓ₁,…,ℓᵣ and ρ₁,…,ρₛ be linearly independent families in 𝔽ⁿ, with r,s ≤ n. Prescribe ℓᵢ · A = ℓ'ᵢ and A · ρⱼ = ρ'ⱼ. The compatibility conditions are ℓᵢ · ρ'ⱼ = ℓ'ᵢ · ρⱼ for every i,j. If the constraints are compatible, a uniformly random matrix A ∈ 𝔽^(n × n) meets them with probability |𝔽|ʳˢ/(|𝔽|ⁿ)ʳ⁺ˢ. The matrix need not be invertible. -/
theorem completion_probability {n r s : ℕ} (hr : r ≤ n) (hs : s ≤ n)
    (l : Fin r → V F n) (rho : Fin s → V F n)
    (lout : Fin r → V F n) (rout : Fin s → V F n)
    (hl : LinearIndependent F l) (hrho : LinearIndependent F rho)
    (hc : ExtensionCompatible l rho lout rout) :
    (Fintype.card (MatrixCompletion l rho lout rout) : ℝ) /
        Fintype.card (Matrix (Fin n) (Fin n) F) = (fieldCard F : ℝ) ^ (r*s) / (vectorCard F n : ℝ) ^ (r+s) := by
  rw [card_matrixCompletion_of_compatible hr hs l rho lout rout hl hrho hc,
    card_all_matrices]
  simp only [Nat.cast_pow, vectorCard]
  have hexp : (n - r) * (n - s) + n * (r + s) = r*s + n ^ 2 := by
    have hsubr := Nat.sub_add_cancel hr
    have hsubs := Nat.sub_add_cancel hs
    nlinarith
  have hqpos : (0 : ℝ) < fieldCard F := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hp : (fieldCard F : ℝ) ^ ((n - r) * (n - s)) * ((fieldCard F : ℝ) ^ n) ^ (r+s) =
      (fieldCard F : ℝ) ^ (r*s) * (fieldCard F : ℝ) ^ (n ^ 2) := by
    rw [← pow_mul, ← pow_add, hexp, pow_add]
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  exact hp

omit [Fintype F] [DecidableEq F] in
/-- Any simultaneous row/column prescription realized by a matrix is compatible. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, r, s ∈ ℕ; l ∈ {0,…,r-1} → V(F, n); rho ∈ {0,…,s-1} → V(F, n); lout ∈ {0,…,r-1} → V(F, n); rout ∈ {0,…,s-1} → V(F, n); A ∈ MatrixCompletion(l, rho, lout, rout), we have

ExtensionCompatible(l, rho, lout, rout).
-/
theorem completion_compatible {n r s : ℕ}
    (l : Fin r → V F n) (rho : Fin s → V F n)
    (lout : Fin r → V F n) (rout : Fin s → V F n)
    (A : MatrixCompletion l rho lout rout) : ExtensionCompatible l rho lout rout := by
  intro i j
  rw [← A.property.2 j, ← A.property.1 i]
  exact Matrix.dotProduct_mulVec (l i) A.val (rho j)

/-- Inconsistent prescriptions have probability zero, including singular maps. -/

/- Mathematical statement (normal notation): If some prescribed row/column constraints violate ℓᵢ · ρ'ⱼ = ℓ'ᵢ · ρⱼ, then no matrix satisfies them: the set of completions is empty. -/
theorem card_completion_eq_zero_of_incompatible {n r s : ℕ}
    (l : Fin r → V F n) (rho : Fin s → V F n)
    (lout : Fin r → V F n) (rout : Fin s → V F n)
    (hc : ¬ExtensionCompatible l rho lout rout) :
    Fintype.card (MatrixCompletion l rho lout rout) = 0 := by
  letI : IsEmpty (MatrixCompletion l rho lout rout) :=
    ⟨fun A => hc (completion_compatible l rho lout rout A)⟩
  exact Fintype.card_eq_zero

/-- Exact binary prescribed-entry probability. For ranks (2,2), (1,2), (2,1), and (1,1), the numerator is respectively 16, 4, 4, and 2. -/

/- Mathematical statement (normal notation): Let ℓ₁,…,ℓᵣ and ρ₁,…,ρₛ be linearly independent families in 𝔽ⁿ, with r,s ≤ n. Prescribe ℓᵢ · A = ℓ'ᵢ and A · ρⱼ = ρ'ⱼ. The compatibility conditions are ℓᵢ · ρ'ⱼ = ℓ'ᵢ · ρⱼ for every i,j. Over the binary field, a uniformly random matrix A ∈ 𝔽₂^(n × n) meets all constraints with probability 2ʳˢ/(2ⁿ)ʳ⁺ˢ when they are compatible, and with probability zero otherwise. -/
theorem binary_completion_probability (hq : fieldCard F = 2)
    {n r s : ℕ} (hr : r ≤ n) (hs : s ≤ n)
    (l : Fin r → V F n) (rho : Fin s → V F n)
    (lout : Fin r → V F n) (rout : Fin s → V F n)
    (hl : LinearIndependent F l) (hrho : LinearIndependent F rho) :
    (Fintype.card (MatrixCompletion l rho lout rout) : ℝ) /
        Fintype.card (Matrix (Fin n) (Fin n) F) =
      if ExtensionCompatible l rho lout rout then
        (2 : ℝ) ^ (r*s) / (vectorCard F n : ℝ) ^ (r+s) else 0 := by
  by_cases hc : ExtensionCompatible l rho lout rout
  · rw [if_pos hc, completion_probability hr hs l rho lout rout hl hrho hc, hq]
    norm_num
  · rw [if_neg hc, card_completion_eq_zero_of_incompatible l rho lout rout hc]
    norm_num

/-- The row and column outputs of an unrestricted matrix. -/
/-
Mathematical definition (normal notation): For n, r, s ∈ ℕ; l ∈ {0,…,r-1} → V(F, n); rho ∈ {0,…,s-1} → V(F, n); A ∈ F^({0,…,n−1} × {0,…,n−1}), define

matrixOutputs(l, rho, A) := ((i ↦ Matrix.vecMul(l(i), A)), (j ↦ Matrix.mulVec(A, rho(j)))).
-/
def matrixOutputs {n r s : ℕ} (l : Fin r → V F n) (rho : Fin s → V F n)
    (A : Matrix (Fin n) (Fin n) F) : (Fin r → V F n) × (Fin s → V F n) :=
  (fun i => Matrix.vecMul (l i) A, fun j => Matrix.mulVec A (rho j))

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, r, s ∈ ℕ; l ∈ {0,…,r-1} → V(F, n); rho ∈ {0,…,s-1} → V(F, n); w ∈ ({0,…,r-1} → V(F, n)) × ({0,…,s-1} → V(F, n)), we have

|{A ∈ F^({0,…,n−1} × {0,…,n−1}) | matrixOutputs(l, rho, A) = w}| = |MatrixCompletion(l, rho, (w)₁, (w)₂)|.
-/
theorem matrixOutputs_fiber_card {n r s : ℕ} (l : Fin r → V F n) (rho : Fin s → V F n)
    (w : (Fin r → V F n) × (Fin s → V F n)) :
    Fintype.card {A : Matrix (Fin n) (Fin n) F // matrixOutputs l rho A = w} =
      Fintype.card (MatrixCompletion l rho w.1 w.2) := by
  apply Fintype.card_congr
  refine ⟨fun A => ⟨A.val, ?_⟩, fun A => ⟨A.val, ?_⟩, fun _ => rfl, fun _ => rfl⟩ <;>
    simpa only [matrixOutputs, Prod.ext_iff, funext_iff] using A.property

/-- Signed test functions supported on compatibility have the exact prescribed- output factor. This keeps signs until the full four-cycle is formed. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, r, s ∈ ℕ; l ∈ {0,…,r-1} → V(F, n); rho ∈ {0,…,s-1} → V(F, n); f ∈ (({0,…,r-1} → V(F, n)) × ({0,…,s-1} → V(F, n))) → ℝ, assume r ≤ n; s ≤ n; LinearIndependent(F, l); LinearIndependent(F, rho); ∀ w, ¬ (ExtensionCompatible(l, rho, (w)₁, (w)₂)) → f(w) = 0. Then

𝔼_(A ∈ F^({0,…,n−1} × {0,…,n−1})) [f(matrixOutputs(l, rho, A))] = (|F|)^(r · s) · 𝔼ᵤ [f(u)].
-/
theorem uavg_matrixOutputs_eq {n r s : ℕ} (hr : r ≤ n) (hs : s ≤ n)
    (l : Fin r → V F n) (rho : Fin s → V F n)
    (hl : LinearIndependent F l) (hrho : LinearIndependent F rho)
    (f : ((Fin r → V F n) × (Fin s → V F n)) → ℝ)
    (hf : ∀ w, ¬ ExtensionCompatible l rho w.1 w.2 → f w = 0) :
    uavg (fun A : Matrix (Fin n) (Fin n) F => f (matrixOutputs l rho A)) =
      (fieldCard F : ℝ) ^ (r*s) * uavg f := by
  rw [uavg_comp_eq_sum_fibers (matrixOutputs l rho) f]
  have heach (w) :
      ((Fintype.card {A : Matrix (Fin n) (Fin n) F // matrixOutputs l rho A = w} : ℝ) /
          Fintype.card (Matrix (Fin n) (Fin n) F)) * f w =
        ((fieldCard F : ℝ) ^ (r*s) / (vectorCard F n : ℝ) ^ (r+s)) * f w := by
    by_cases hc : ExtensionCompatible l rho w.1 w.2
    · rw [matrixOutputs_fiber_card, completion_probability hr hs l rho w.1 w.2 hl hrho hc]
    · rw [hf w hc]; ring
  trans ∑ w, ((fieldCard F : ℝ) ^ (r*s) / (vectorCard F n : ℝ) ^ (r+s)) * f w
  · apply Finset.sum_congr rfl
    intro w _
    simpa only [← Nat.card_eq_fintype_card] using heach w
  rw [← Finset.mul_sum]
  unfold uavg
  have hcard : Fintype.card ((Fin r → V F n) × (Fin s → V F n)) = (vectorCard F n) ^ (r+s) := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, V, vectorCard, fieldCard, pow_add]
  rw [hcard, Nat.cast_pow]
  ring

/-- Independent row vectors have independent uniform images under an unrestricted random matrix. This includes the one-row and two-row cases. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): Let ℓ₁,…,ℓᵣ be linearly independent vectors in 𝔽ⁿ, with r ≤ n. For a uniformly random unrestricted matrix A, the tuple (ℓ₁ · A,…,ℓᵣ · A) is uniform over (𝔽ⁿ)ʳ. Consequently every real test function has the same average under these two descriptions. -/
theorem uavg_row_images {n r : ℕ} (hr : r ≤ n)
    (l : Fin r → V F n) (hl : LinearIndependent F l)
    (f : (Fin r → V F n) → ℝ) :
    uavg (fun A : Matrix (Fin n) (Fin n) F => f (fun i => Matrix.vecMul (l i) A)) =
      uavg f := by
  let rho : Fin 0 → V F n := fun i => Fin.elim0 i
  have h := uavg_matrixOutputs_eq hr (Nat.zero_le n) l rho hl
    (linearIndependent_empty_type (R := F) (v := rho)) (fun w => f w.1) (by
      intro w hw
      exact (hw (fun _ j => Fin.elim0 j)).elim)
  simpa only [matrixOutputs, mul_zero, pow_zero, one_mul, uavg_prod, uavg_const] using h

omit [DecidableEq F] in
/-- A field of cardinality two has exactly one nonzero scalar. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ F, assume |F| = 2; a ≠ 0. Then

a = 1.
-/
theorem binary_nonzero_eq_one (hq : fieldCard F = 2) (a : F) (ha : a ≠ 0) : a = 1 := by
  have hcard : Nat.card F = 2 := by simpa only [Nat.card_eq_fintype_card, fieldCard] using hq
  obtain ⟨x, _, hx⟩ := (Nat.card_eq_two_iff' (0 : F)).mp hcard
  exact (hx a ha).trans (hx 1 one_ne_zero).symm

/-- Distinct nonzero binary vectors are independent; therefore injective feature maps have independent pairs of distinct images. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; a, b ∈ U(F, n), assume |F| = 2; a ≠ b. Then

LinearIndependent(F, (a, b)).
-/
theorem binary_pair_independent (hq : fieldCard F = 2) {n : ℕ}
    (a b : U F n) (hab : a ≠ b) : LinearIndependent F ![a.val, b.val] := by
  rw [linearIndependent_fin2]
  refine ⟨b.property, ?_⟩
  intro c hc
  by_cases hc0 : c = 0
  · exact a.property (by simpa [hc0] using hc.symm)
  · have hc1 := binary_nonzero_eq_one hq c hc0
    apply hab
    apply Subtype.ext
    simpa [hc1] using hc.symm

end CircuitCompiler.RefreshAnalysis
