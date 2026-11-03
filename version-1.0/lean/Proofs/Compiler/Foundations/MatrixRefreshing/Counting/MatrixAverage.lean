import Proofs.Compiler.Foundations.MatrixRefreshing.Counting.InvertibilityCount
import Proofs.Compiler.Foundations.MatrixRefreshing.Counting.ReferenceCycle
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.EncodingBounds
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.MatrixAction
import Proofs.Compiler.Foundations.MatrixRefreshing.Probability.FiniteDistribution



set_option autoImplicit false

/-! Inverse-free matrix restriction and four-cycle identities. Changing the right input to its new share extends the table to arbitrary matrices. Nonnegative averaging pays a factor four for invertibility; `RankSplitMatrixAverage` supplies the exceptional-rank estimates. -/

namespace MatrixRefresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open Refresh

open scoped BigOperators Classical

noncomputable section

/-- Extend an endpoint table by zero when any of its four vectors is zero. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; Φ ∈ Endpoint(F, n) → Endpoint(F, n) → ℝ; l, l', r, r' ∈ V(F, n), define

zeroExtend(Φ, l, l', r, r') := { Φ(((l, (h)₁), (l', ((h)₂)₁)), ((r, (((h)₂)₂)₁), (r', (((h)₂)₂)₂))) if l ≠ 0 ∧ l' ≠ 0 ∧ r ≠ 0 ∧ r' ≠ 0,; 0 otherwise }.
-/
def zeroExtend {n : ℕ} (Φ : Endpoint F n → Endpoint F n → ℝ)
    (l l' r r' : V F n) : ℝ :=
  if h : l ≠ 0 ∧ l' ≠ 0 ∧ r ≠ 0 ∧ r' ≠ 0 then
    Φ ⟨⟨l, h.1⟩, ⟨l', h.2.1⟩⟩ ⟨⟨r, h.2.2.1⟩, ⟨r', h.2.2.2⟩⟩
  else 0

/-- When all four share vectors are nonzero, zero extension returns the original table entry at the corresponding left and right endpoints. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; Φ ∈ Endpoint(F, n) → Endpoint(F, n) → ℝ; l, l', r, r' ∈ U(F, n), we have

zeroExtend(Φ, l, l', r, r') = Φ((l, l'), (r, r')).
-/
@[simp] theorem zeroExtend_nonzero {n : ℕ} (Φ : Endpoint F n → Endpoint F n → ℝ)
    (l l' r r' : U F n) : zeroExtend Φ l.val l'.val r.val r'.val = Φ ⟨l, l'⟩ ⟨r, r'⟩ := by
  simp [zeroExtend, l.property, l'.property, r.property, r'.property]

/-- A nonnegative uniform bound on the endpoint table also bounds its zero extension, since any entry with a zero share is replaced by zero. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; Φ ∈ Endpoint(F, n) → Endpoint(F, n) → ℝ; B ∈ ℝ; l, l', r, r' ∈ V(F, n), assume 0 ≤ B; ∀ x, y, |Φ(x, y)| ≤ B. Then

|zeroExtend(Φ, l, l', r, r')| ≤ B.
-/
theorem zeroExtend_abs_le {n : ℕ} (Φ : Endpoint F n → Endpoint F n → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hΦ : ∀ x y, |Φ x y| ≤ B) (l l' r r' : V F n) :
    |zeroExtend Φ l l' r r'| ≤ B := by
  unfold zeroExtend
  split_ifs
  · exact hΦ _ _
  · simpa using hB

/-- If the table vanishes off the legal relation `D`, its zero extension vanishes whenever the old and new dot products differ. This also covers zero share vectors. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; Φ ∈ Endpoint(F, n) → Endpoint(F, n) → ℝ; l, l', r, r' ∈ V(F, n), assume ∀ x, y, ¬ (D(x, y)) → Φ(x, y) = 0; (l · r) ≠ (l' · r'). Then

zeroExtend(Φ, l, l', r, r') = 0.
-/
theorem zeroExtend_eq_zero_of_incompatible {n : ℕ} (Φ : Endpoint F n → Endpoint F n → ℝ)
    (hΦ : ∀ x y, ¬ D x y → Φ x y = 0) (l l' r r' : V F n)
    (h : dot l r ≠ dot l' r') : zeroExtend Φ l l' r r' = 0 := by
  unfold zeroExtend
  split_ifs
  · exact hΦ _ _ h
  · rfl

/-- The table obtained from the actual invertible refresh on single nonzero shares. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; Φ ∈ Endpoint(F, n) → Endpoint(F, n) → ℝ; M ∈ GLₙ(F); l, r ∈ U(F, n), define

graphRestriction(Φ, M, l, r) := Φ((l, rowRefresh(l, M)), (r, columnRefresh(r, M))).
-/
def graphRestriction {n : ℕ} (Φ : Endpoint F n → Endpoint F n → ℝ)
    (M : Refresh.«GL» F n) (l r : U F n) : ℝ :=
  Φ ⟨l, rowRefresh l M⟩ ⟨r, columnRefresh r M⟩

/-- Inverse-free restriction, defined for every matrix after zero extension. Its arguments are the left party's old share `l` and the right party's new share `rho`. The old right share is reconstructed as `A rho`, so no inverse or invertibility proof occurs. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; Φ ∈ Endpoint(F, n) → Endpoint(F, n) → ℝ; A ∈ F^({0,…,n−1} × {0,…,n−1}); l, rho ∈ U(F, n), define

matrixRestriction(Φ, A, l, rho) := zeroExtend(Φ, l, Matrix.vecMul(l, A), Matrix.mulVec(A, rho), rho).
-/
def matrixRestriction {n : ℕ} (Φ : Endpoint F n → Endpoint F n → ℝ)
    (A : Matrix (Fin n) (Fin n) F) (l rho : U F n) : ℝ :=
  zeroExtend Φ l.val (Matrix.vecMul l.val A) (Matrix.mulVec A rho.val) rho.val

/-- Multiplication by an invertible matrix `M` permutes nonzero columns: send the right party's new share `rho` to his old share `M rho`, with inverse given by the column refresh under `M`. This replaces the old-share graph index by a new-share index. -/
/- Mathematical definition (normal notation): For invertible M, the map ρ ↦ M · ρ is a bijection of the nonzero column shares, with inverse r ↦ M⁻¹ · r. -/
def columnForwardEquiv {n : ℕ} (M : Refresh.«GL» F n) : U F n ≃ U F n where
  toFun rho := columnRefresh rho M⁻¹
  invFun r := columnRefresh r M
  left_inv rho := by
    change columnRefresh (columnRefresh rho M⁻¹) M = rho
    rw [columnRefresh_mul, inv_mul_cancel, columnRefresh_one]
  right_inv r := by
    change columnRefresh (columnRefresh r M) M⁻¹ = r
    rw [columnRefresh_mul, mul_inv_cancel, columnRefresh_one]

/-- For an invertible matrix, reconstructing the right party's old share as `M rho` turns the inverse-free matrix restriction into the actual refresh graph restriction. The column permutation converts the new-share index `rho` into the old-share index. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; Φ ∈ Endpoint(F, n) → Endpoint(F, n) → ℝ; M ∈ GLₙ(F); l, rho ∈ U(F, n), we have

matrixRestriction(Φ, M, l, rho) = graphRestriction(Φ, M, l, columnForwardEquiv(M, rho)).
-/
theorem matrixRestriction_GL {n : ℕ} (Φ : Endpoint F n → Endpoint F n → ℝ)
    (M : Refresh.«GL» F n) (l rho : U F n) :
    matrixRestriction Φ M.val l rho = graphRestriction Φ M l (columnForwardEquiv M rho) := by
  have hc : Matrix.mulVec M.val rho.val = (columnRefresh rho M⁻¹).val := by simp
  rw [matrixRestriction, hc]
  change zeroExtend Φ l.val (rowRefresh l M).val (columnRefresh rho M⁻¹).val rho.val = _
  rw [zeroExtend_nonzero]
  simp [graphRestriction, columnForwardEquiv, columnRefresh_mul]

/-- On an invertible matrix, the auxiliary table differs from the actual graph table by a permutation of its column index. Uniform four-cycle energy is invariant under that permutation. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; Φ ∈ Endpoint(F, n) → Endpoint(F, n) → ℝ; M ∈ GLₙ(F), we have

fourCycle(matrixRestriction(Φ, M)) = fourCycle(graphRestriction(Φ, M)).
-/
theorem fourCycle_matrixRestriction_GL {n : ℕ} (Φ : Endpoint F n → Endpoint F n → ℝ)
    (M : Refresh.«GL» F n) :
    fourCycle (matrixRestriction Φ M.val) = fourCycle (graphRestriction Φ M) := by
  have heq : matrixRestriction Φ M.val =
      fun l rho => graphRestriction Φ M l (columnForwardEquiv M rho) := by
    funext l rho
    exact matrixRestriction_GL Φ M l rho
  rw [heq]
  exact fourCycle_permute_columns (graphRestriction Φ M) (columnForwardEquiv M)

/-- The mean actual refresh-graph four-cycle is at most four times the mean inverse-free unrestricted-matrix four-cycle. The complete four-cycle statistic is nonnegative even for signed tables, so conditioning on invertibility costs at most four after the column-index reindexing. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; Φ ∈ Endpoint(F, n) → Endpoint(F, n) → ℝ, we have

𝔼_(M ∈ GLₙ(F)) [fourCycle(graphRestriction(Φ, M))] ≤ 4 · 𝔼_(A ∈ F^({0,…,n−1} × {0,…,n−1})) [fourCycle(matrixRestriction(Φ, A))].
-/
theorem graph_fourCycle_le_four_matrix_fourCycle {n : ℕ}
    (Φ : Endpoint F n → Endpoint F n → ℝ) :
    uavg (fun M : Refresh.«GL» F n => fourCycle (graphRestriction Φ M)) ≤
      4 * uavg (fun A : Matrix (Fin n) (Fin n) F => fourCycle (matrixRestriction Φ A)) := by
  simpa only [fourCycle_matrixRestriction_GL] using
    uavg_GL_le_four_mul_uavg_matrices (fun A => fourCycle (matrixRestriction Φ A))
      (fun A => fourCycle_nonneg (matrixRestriction Φ A))

/-- Group a uniform average on a nonempty finite domain by the fibers of an arbitrary map. Each output receives exactly its fiber cardinality divided by the domain cardinality, and this identity allows arbitrary signed test functions. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α,β a set; g ∈ α → β; f ∈ β → ℝ, assume α is finite; α ≠ ∅; β is finite. Then

𝔼ₐ [f(g(a))] = ∑_b ((|{a ∈ α | g(a) = b}| / |α|) · f(b)).
-/
theorem uavg_comp_eq_sum_fibers {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    (g : α → β) (f : β → ℝ) :
    uavg (fun a => f (g a)) =
      ∑ b, ((Fintype.card {a : α // g a = b} : ℝ) / Fintype.card α) * f b := by
  rw [uavg_eq_expect_uniform, ← expect_map]
  simp only [FiniteDistribution.expect, FiniteDistribution.uniform_map_weight]

/-- The four unrestricted output vectors of a matrix on a fixed pair of rows and columns. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; l, rho ∈ {0,…,2-1} → V(F, n); A ∈ F^({0,…,n−1} × {0,…,n−1}), define

matrixOutputs(l, rho, A) := ((i ↦ Matrix.vecMul(l(i), A)), (j ↦ Matrix.mulVec(A, rho(j)))).
-/
def matrixOutputs {n : ℕ} (l rho : Fin 2 → V F n)
    (A : Matrix (Fin n) (Fin n) F) : (Fin 2 → V F n) × (Fin 2 → V F n) :=
  (fun i => Matrix.vecMul (l i) A, fun j => Matrix.mulVec A (rho j))

/-- The fiber over a specified output quadruple has exactly as many elements as the matrix-completion subtype imposing those four row and column actions. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; l, rho ∈ {0,…,2-1} → V(F, n); w ∈ ({0,…,2-1} → V(F, n)) × ({0,…,2-1} → V(F, n)), we have

|{A ∈ F^({0,…,n−1} × {0,…,n−1}) | matrixOutputs(l, rho, A) = w}| = |MatrixCompletion(l, rho, (w)₁, (w)₂)|.
-/
theorem matrixOutputs_fiber_card {n : ℕ} (l rho : Fin 2 → V F n)
    (w : (Fin 2 → V F n) × (Fin 2 → V F n)) :
    Fintype.card {A : Matrix (Fin n) (Fin n) F // matrixOutputs l rho A = w} =
      Fintype.card (MatrixCompletion l rho w.1 w.2) := by
  apply Fintype.card_congr
  refine ⟨fun A => ⟨A.val, ?_⟩, fun A => ⟨A.val, ?_⟩, fun _ => rfl, fun _ => rfl⟩
  · simpa only [matrixOutputs, Prod.ext_iff, funext_iff] using A.property
  · simpa only [matrixOutputs, Prod.ext_iff, funext_iff] using A.property

/-- Four unrestricted vector outputs have `(vectorCard F n)^4` possible values, where `(vectorCard F n) = (fieldCard F)^n`; no compatibility condition is imposed in this reference carrier. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, we have

|(({0,…,2-1} → V(F, n)) × ({0,…,2-1} → V(F, n)))| = (|F|ⁿ)⁴.
-/
theorem card_output_quadruples (n : ℕ) :
    Fintype.card ((Fin 2 → V F n) × (Fin 2 → V F n)) = (vectorCard F n) ^ 4 := by
  simp [V, fieldCard, vectorCard, ← pow_add]

/-- Exact factor `(fieldCard F)^4` for signed weightings supported on the compatibility equations. A uniform output quadruple has mass `1/(vectorCard F n)^4`; a compatible matrix output has mass `(fieldCard F)^4/(vectorCard F n)^4`. The weighting vanishes on incompatible outputs, so the two averages differ by exactly this factor. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; l, rho ∈ {0,…,2-1} → V(F, n); f ∈ (({0,…,2-1} → V(F, n)) × ({0,…,2-1} → V(F, n))) → ℝ, assume 2 ≤ n; LinearIndependent(F, l); LinearIndependent(F, rho); ∀ w, ¬ (ExtensionCompatible(l, rho, (w)₁, (w)₂)) → f(w) = 0. Then

𝔼_(A ∈ F^({0,…,n−1} × {0,…,n−1})) [f(matrixOutputs(l, rho, A))] = (|F|)⁴ · 𝔼ᵤ [f(u)].
-/
theorem uavg_matrixOutputs_eq_q_four {n : ℕ} (hn : 2 ≤ n) (l rho : Fin 2 → V F n)
    (hl : LinearIndependent F l) (hrho : LinearIndependent F rho)
    (f : ((Fin 2 → V F n) × (Fin 2 → V F n)) → ℝ)
    (hf : ∀ w, ¬ ExtensionCompatible l rho w.1 w.2 → f w = 0) :
    uavg (fun A : Matrix (Fin n) (Fin n) F => f (matrixOutputs l rho A)) =
      (fieldCard F : ℝ) ^ 4 * uavg f := by
  rw [uavg_comp_eq_sum_fibers (matrixOutputs l rho) f]
  -- Compare output masses pointwise before summing; this preserves signed weightings and does not replace the common matrix by independent matrices.
  have heach : ∀ w,
      ((Fintype.card {A : Matrix (Fin n) (Fin n) F // matrixOutputs l rho A = w} : ℝ) /
          Fintype.card (Matrix (Fin n) (Fin n) F)) * f w =
        ((fieldCard F : ℝ) ^ 4 / (vectorCard F n : ℝ) ^ 4) * f w := by
    intro w
    by_cases hc : ExtensionCompatible l rho w.1 w.2
    · rw [matrixOutputs_fiber_card, completion_probability hn l rho w.1 w.2 hl hrho hc]
    · rw [hf w hc]
      ring
  trans ∑ w, ((fieldCard F : ℝ) ^ 4 / (vectorCard F n : ℝ) ^ 4) * f w
  · apply Finset.sum_congr rfl
    intro w _
    simpa only [← Nat.card_eq_fintype_card] using heach w
  rw [← Finset.mul_sum]
  unfold uavg
  rw [card_output_quadruples, Nat.cast_pow]
  ring

/-- The signed product of the four corner entries for fixed inputs and unrestricted outputs. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; Φ ∈ Endpoint(F, n) → Endpoint(F, n) → ℝ; l, rho ∈ {0,…,2-1} → V(F, n); w ∈ ({0,…,2-1} → V(F, n)) × ({0,…,2-1} → V(F, n)), define

outputCornerProduct(Φ, l, rho, w) := zeroExtend(Φ, l(0), (w)₁(0), (w)₂(0), rho(0)) · zeroExtend(Φ, l(1), (w)₁(1), (w)₂(0), rho(0)) · zeroExtend(Φ, l(1), (w)₁(1), (w)₂(1), rho(1)) · zeroExtend(Φ, l(0), (w)₁(0), (w)₂(1), rho(1)).
-/
def outputCornerProduct {n : ℕ} (Φ : Endpoint F n → Endpoint F n → ℝ)
    (l rho : Fin 2 → V F n) (w : (Fin 2 → V F n) × (Fin 2 → V F n)) : ℝ :=
  zeroExtend Φ (l 0) (w.1 0) (w.2 0) (rho 0) *
  zeroExtend Φ (l 1) (w.1 1) (w.2 0) (rho 0) *
  zeroExtend Φ (l 1) (w.1 1) (w.2 1) (rho 1) *
  zeroExtend Φ (l 0) (w.1 0) (w.2 1) (rho 1)

/-- Failure of any one of the four compatibility equations forces the corresponding corner entry to vanish by the table's support condition. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; Φ ∈ Endpoint(F, n) → Endpoint(F, n) → ℝ; l, rho ∈ {0,…,2-1} → V(F, n); w ∈ ({0,…,2-1} → V(F, n)) × ({0,…,2-1} → V(F, n)), assume ∀ x, y, ¬ (D(x, y)) → Φ(x, y) = 0; ¬ (ExtensionCompatible(l, rho, (w)₁, (w)₂)). Then

outputCornerProduct(Φ, l, rho, w) = 0.
-/
theorem outputCornerProduct_eq_zero_of_incompatible {n : ℕ}
    (Φ : Endpoint F n → Endpoint F n → ℝ) (hΦ : ∀ x y, ¬ D x y → Φ x y = 0)
    (l rho : Fin 2 → V F n) (w : (Fin 2 → V F n) × (Fin 2 → V F n))
    (h : ¬ ExtensionCompatible l rho w.1 w.2) : outputCornerProduct Φ l rho w = 0 := by
  have hh : ∃ i j, dot (l i) (w.2 j) ≠ dot (w.1 i) (rho j) := by
    simpa only [ExtensionCompatible, not_forall] using h
  obtain ⟨i, j, hij⟩ := hh
  have hz := zeroExtend_eq_zero_of_incompatible Φ hΦ (l i) (w.1 i) (w.2 j) (rho j) hij
  fin_cases i <;> fin_cases j <;> dsimp at hz <;> simp [outputCornerProduct, hz]

/-- For independent input row and column pairs in dimension at least two, the matrix average of the signed corner product is `(fieldCard F)^4` times its independent-output average. Support on `D` makes every incompatible output product vanish. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; Φ ∈ Endpoint(F, n) → Endpoint(F, n) → ℝ; l, rho ∈ {0,…,2-1} → V(F, n), assume 2 ≤ n; ∀ x, y, ¬ (D(x, y)) → Φ(x, y) = 0; LinearIndependent(F, l); LinearIndependent(F, rho). Then

𝔼_(A ∈ F^({0,…,n−1} × {0,…,n−1})) [outputCornerProduct(Φ, l, rho, matrixOutputs(l, rho, A))] = (|F|)⁴ · 𝔼ᵤ [outputCornerProduct(Φ, l, rho, u)].
-/
theorem uavg_matrix_corner_eq_q_four {n : ℕ} (hn : 2 ≤ n)
    (Φ : Endpoint F n → Endpoint F n → ℝ) (hΦ : ∀ x y, ¬ D x y → Φ x y = 0)
    (l rho : Fin 2 → V F n) (hl : LinearIndependent F l) (hrho : LinearIndependent F rho) :
    uavg (fun A : Matrix (Fin n) (Fin n) F =>
      outputCornerProduct Φ l rho (matrixOutputs l rho A)) =
      (fieldCard F : ℝ) ^ 4 * uavg (outputCornerProduct Φ l rho) :=
  uavg_matrixOutputs_eq_q_four hn l rho hl hrho _
    (outputCornerProduct_eq_zero_of_incompatible Φ hΦ l rho)

/-- The absolute value of a uniform finite average is bounded by the uniform average of the absolute values, including the empty-carrier convention. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α a set; f ∈ α → ℝ, assume α is finite. Then

|𝔼ᵤ [f(u)]| ≤ 𝔼ₐ [|f(a)|].
-/
theorem abs_uavg_le_uavg_abs {α : Type*} [Fintype α] (f : α → ℝ) :
    |uavg f| ≤ uavg (fun a => |f a|) := by
  unfold uavg
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Fintype.card α : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs f Finset.univ) (by positivity)

/-- The nonzero points of a one-dimensional span, without multiplicity. -/
/- Mathematical definition (normal notation): For a fixed nonzero vector v, the map a ↦ a · v embeds the nonzero field scalars into the nonzero vectors. -/
def nonzeroScalarEmbedding {n : ℕ} (v : U F n) : Fˣ ↪ U F n where
  toFun a := ⟨(a : F) • v.val, smul_ne_zero a.ne_zero v.property⟩
  inj' a b hab := Units.ext (smul_left_injective F v.property (congrArg Subtype.val hab))

/-- For nonzero vectors, linear dependence is exactly membership in the nonzero scalar orbit. Over a general field this is broader than equality. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; u, v ∈ U(F, n), we have

¬ (LinearIndependent(F, (u, v))) ⇔ u ∈ Set.range(nonzeroScalarEmbedding(v)).
-/
theorem dependent_iff_scalar_range {n : ℕ} (u v : U F n) :
    ¬ LinearIndependent F ![u.val, v.val] ↔ u ∈ Set.range (nonzeroScalarEmbedding v) := by
  rw [linearIndependent_fin2]
  change ¬ (v.val ≠ 0 ∧ ∀ a : F, a • v.val ≠ u.val) ↔ _
  constructor
  · intro h
    have hex : ∃ a : F, a • v.val = u.val := by
      by_contra hh
      exact h ⟨v.property, fun a ha => hh ⟨a, ha⟩⟩
    obtain ⟨a, ha⟩ := hex
    have ha0 : a ≠ 0 := by
      intro hz
      apply u.property
      simpa [hz] using ha.symm
    exact ⟨Units.mk0 a ha0, Subtype.ext ha⟩
  · rintro ⟨a, ha⟩ h
    exact h.2 a.val (congrArg Subtype.val ha)

/-- Both the left row pair and the right new-column pair are independent. There is no independence requirement between the row pair and column pair. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; w ∈ (U(F, n) × U(F, n)) × (U(F, n) × U(F, n)), define

goodInputPairs(w) := LinearIndependent(F, (((w)₁)₁, ((w)₁)₂)) ∧ LinearIndependent(F, (((w)₂)₁, ((w)₂)₂)).
-/
def goodInputPairs {n : ℕ} (w : (U F n × U F n) × (U F n × U F n)) : Prop :=
  LinearIndependent F ![w.1.1.val, w.1.2.val] ∧
    LinearIndependent F ![w.2.1.val, w.2.2.val]

/-- The signed average for fixed input pairs in the unrestricted-matrix experiment. -/
/-
Mathematical definition (normal notation): Fix nonzero rows ℓ₀,ℓ₁ and nonzero columns ρ₀,ρ₁. Average

∏_(i,j ∈ {0,1}) F̃((ℓᵢ,ℓᵢ · A),(A · ρⱼ,ρⱼ))

over all n × n field matrices A, sampled uniformly. Here F̃ extends the endpoint table by zero whenever a share is zero. This average includes singular A.
-/
def matrixInputMoment {n : ℕ} (Φ : Endpoint F n → Endpoint F n → ℝ)
    (w : (U F n × U F n) × (U F n × U F n)) : ℝ :=
  let l := ![w.1.1.val, w.1.2.val]
  let rho := ![w.2.1.val, w.2.2.val]
  uavg (fun A : Matrix (Fin n) (Fin n) F =>
    outputCornerProduct Φ l rho (matrixOutputs l rho A))

/-- The signed average when all four output vectors are sampled independently. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; Φ ∈ Endpoint(F, n) → Endpoint(F, n) → ℝ; w ∈ (U(F, n) × U(F, n)) × (U(F, n) × U(F, n)), define

referenceInputMoment(Φ, w) := 𝔼ᵤ [outputCornerProduct(Φ, (((w)₁)₁, ((w)₁)₂), (((w)₂)₁, ((w)₂)₂), u)].
-/
def referenceInputMoment {n : ℕ} (Φ : Endpoint F n → Endpoint F n → ℝ)
    (w : (U F n × U F n) × (U F n × U F n)) : ℝ :=
  uavg (outputCornerProduct Φ ![w.1.1.val, w.1.2.val] ![w.2.1.val, w.2.2.val])

/-- On an input quadruple whose row pair and column pair are both independent, legal support gives the exact identity: the common-matrix moment is `(fieldCard F)^4` times the independently sampled output moment. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; Φ ∈ Endpoint(F, n) → Endpoint(F, n) → ℝ; w ∈ (U(F, n) × U(F, n)) × (U(F, n) × U(F, n)), assume 2 ≤ n; ∀ x, y, ¬ (D(x, y)) → Φ(x, y) = 0; goodInputPairs(w). Then

matrixInputMoment(Φ, w) = (|F|)⁴ · referenceInputMoment(Φ, w).
-/
theorem matrixInputMoment_eq_q_four_of_good {n : ℕ} (hn : 2 ≤ n)
    (Φ : Endpoint F n → Endpoint F n → ℝ) (hΦ : ∀ x y, ¬ D x y → Φ x y = 0)
    (w : (U F n × U F n) × (U F n × U F n)) (hw : goodInputPairs w) :
    matrixInputMoment Φ w = (fieldCard F : ℝ) ^ 4 * referenceInputMoment Φ w :=
  uavg_matrix_corner_eq_q_four hn Φ hΦ _ _ hw.1 hw.2

/-- Expanding the four-cycle and commuting finite averages identifies the mean unrestricted-matrix four-cycle with the average of the fixed-input matrix moments. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; Φ ∈ Endpoint(F, n) → Endpoint(F, n) → ℝ, we have

𝔼_(A ∈ F^({0,…,n−1} × {0,…,n−1})) [fourCycle(matrixRestriction(Φ, A))] = 𝔼ᵤ [matrixInputMoment(Φ, u)].
-/
theorem matrix_fourCycle_eq_inputMoment {n : ℕ} (Φ : Endpoint F n → Endpoint F n → ℝ) :
    uavg (fun A : Matrix (Fin n) (Fin n) F => fourCycle (matrixRestriction Φ A)) =
      uavg (matrixInputMoment Φ) := by
  unfold matrixInputMoment
  simp only [uavg_prod, fourCycle_expansion]
  rw [uavg_comm]
  apply uavg_congr
  intro l
  rw [uavg_comm]
  apply uavg_congr
  intro l'
  rw [uavg_comm]
  apply uavg_congr
  intro rho
  rw [uavg_comm]
  apply uavg_congr
  intro rho'
  apply uavg_congr
  intro A
  rfl

/-- Passing from a supported finite function to its embedded carrier changes only normalization: its unnormalized sum is unchanged, and its average gains the ratio of carrier cardinalities. This also applies to signed functions. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α,β a set; e ∈ α ↪ β; f ∈ β → ℝ, assume α is finite; α ≠ ∅; β is finite; β ≠ ∅; ∀ b, (b ∉ Set.range(e)) ⇒ f(b) = 0. Then

𝔼ᵤ [f(u)] = |α| / |β| · 𝔼ₐ [f(e(a))].
-/
theorem uavg_eq_card_ratio_of_embedding {α β : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ↪ β) (f : β → ℝ) (hf : ∀ b, b ∉ Set.range e → f b = 0) :
    uavg f = (Fintype.card α : ℝ) / Fintype.card β * uavg (fun a => f (e a)) := by
  have hsum : (∑ b, f b) = ∑ a, f (e a) := by
    symm
    calc
      (∑ a, f (e a)) = ∑ b ∈ Finset.univ.image e, f b := by
        rw [Finset.sum_image]
        exact fun a _ b _ h => e.injective h
      _ = ∑ b, f b := Finset.sum_subset (Finset.subset_univ _) (by
        intro b _ hb
        apply hf b
        rintro ⟨a, rfl⟩
        exact hb (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩))
  unfold uavg
  rw [hsum]
  have ha : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := α)
  have hb : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := β)
  field_simp

/-- Forget the four nonzero proofs while retaining every output coordinate. This embeds the reference experiment's nonzero outputs into all vector outputs. -/
/- Mathematical definition (normal notation): Forget the nonzero certificates in two pairs of nonzero vectors. The map (u₁,u₂,v₁,v₂) ↦ (u₁,u₂,v₁,v₂) into the unrestricted vector space is injective. -/
def nonzeroOutputEmbedding (n : ℕ) :
    ((Fin 2 → U F n) × (Fin 2 → U F n)) ↪ ((Fin 2 → V F n) × (Fin 2 → V F n)) where
  toFun w := (fun i => (w.1 i).val, fun j => (w.2 j).val)
  inj' := by
    intro a b h
    apply Prod.ext
    · funext i
      apply Subtype.ext
      exact congrFun (congrArg Prod.fst h) i
    · funext j
      apply Subtype.ext
      exact congrFun (congrArg Prod.snd h) j

/-- The zero-extended corner product vanishes outside the embedded carrier of four nonzero outputs: any missing nonzero witness means some output is zero. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; Φ ∈ Endpoint(F, n) → Endpoint(F, n) → ℝ; l, rho ∈ {0,…,2-1} → V(F, n); w ∈ ({0,…,2-1} → V(F, n)) × ({0,…,2-1} → V(F, n)), assume w ∉ Set.range(nonzeroOutputEmbedding(n)). Then

outputCornerProduct(Φ, l, rho, w) = 0.
-/
theorem outputCornerProduct_supported_nonzero {n : ℕ} (Φ : Endpoint F n → Endpoint F n → ℝ)
    (l rho : Fin 2 → V F n) (w : (Fin 2 → V F n) × (Fin 2 → V F n))
    (hw : w ∉ Set.range (nonzeroOutputEmbedding n)) : outputCornerProduct Φ l rho w = 0 := by
  have hz : ¬ ((∀ i, w.1 i ≠ 0) ∧ ∀ j, w.2 j ≠ 0) := by
    intro hh
    exact hw ⟨(fun i => ⟨w.1 i, hh.1 i⟩, fun j => ⟨w.2 j, hh.2 j⟩), rfl⟩
  have hh : w.1 0 = 0 ∨ w.1 1 = 0 ∨ w.2 0 = 0 ∨ w.2 1 = 0 := by
    simpa only [Fin.forall_fin_two, not_and_or, not_not, or_assoc] using hz
  rcases hh with h | h | h | h <;> simp [outputCornerProduct, zeroExtend, h]

/-- Four nonzero vector outputs have `(shareCard F n)^4` possible values, with `(shareCard F n) = (vectorCard F n) - 1`; this is the carrier size used to normalize the reference experiment. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, we have

|(({0,…,2-1} → U(F, n)) × ({0,…,2-1} → U(F, n)))| = (|F|ⁿ-1)⁴.
-/
theorem card_nonzero_output_quadruples (n : ℕ) :
    Fintype.card ((Fin 2 → U F n) × (Fin 2 → U F n)) = (shareCard F n) ^ 4 := by
  simp [← pow_add, shareCard, vectorCard, fieldCard]

/-- Normalizing the four output-vector carriers contributes precisely `((shareCard F n)/(vectorCard F n))^4`. The input vectors were already sampled from the nonzero carrier, so there are four density factors here, not eight. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; Φ ∈ Endpoint(F, n) → Endpoint(F, n) → ℝ; w ∈ (U(F, n) × U(F, n)) × (U(F, n) × U(F, n)), assume 2 ≤ n. Then

referenceInputMoment(Φ, w) = ((|F|ⁿ-1) / |F|ⁿ)⁴ · 𝔼_(o ∈ ({0,…,2−1} → U(F, n)) × ({0,…,2−1} → U(F, n))) [outputCornerProduct(Φ, (((w)₁)₁, ((w)₁)₂), (((w)₂)₁, ((w)₂)₂), nonzeroOutputEmbedding(n, o))].
-/
theorem referenceInputMoment_nonzero_outputs {n : ℕ} (hn : 2 ≤ n)
    (Φ : Endpoint F n → Endpoint F n → ℝ) (w : (U F n × U F n) × (U F n × U F n)) :
    referenceInputMoment Φ w = ((shareCard F n : ℝ) / vectorCard F n) ^ 4 *
      uavg (fun o : (Fin 2 → U F n) × (Fin 2 → U F n) =>
        outputCornerProduct Φ ![w.1.1.val, w.1.2.val] ![w.2.1.val, w.2.2.val]
          (nonzeroOutputEmbedding n o)) := by
  letI : Nonempty (U F n) := Fintype.card_pos_iff.mp (by
    rw [nonzero_vector_card]
    have hN := four_le_pow (F := F) hn
    omega)
  unfold referenceInputMoment
  rw [uavg_eq_card_ratio_of_embedding (nonzeroOutputEmbedding n) _
    (outputCornerProduct_supported_nonzero Φ _ _)]
  rw [card_nonzero_output_quadruples, card_output_quadruples, Nat.cast_pow, Nat.cast_pow, div_pow]

/-- On the embedded nonzero output carrier, the four zero-extended entries become exactly the four endpoint entries, with the right party's old and new coordinates in the order required by the inverse-free experiment. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; Φ ∈ Endpoint(F, n) → Endpoint(F, n) → ℝ; w ∈ (U(F, n) × U(F, n)) × (U(F, n) × U(F, n)); o ∈ ({0,…,2-1} → U(F, n)) × ({0,…,2-1} → U(F, n)), we have

outputCornerProduct(Φ, (((w)₁)₁, ((w)₁)₂), (((w)₂)₁, ((w)₂)₂), nonzeroOutputEmbedding(n, o)) = Φ((((w)₁)₁, (o)₁(0)), ((o)₂(0), ((w)₂)₁)) · Φ((((w)₁)₂, (o)₁(1)), ((o)₂(0), ((w)₂)₁)) · Φ((((w)₁)₂, (o)₁(1)), ((o)₂(1), ((w)₂)₂)) · Φ((((w)₁)₁, (o)₁(0)), ((o)₂(1), ((w)₂)₂)).
-/
theorem nonzero_output_product {n : ℕ} (Φ : Endpoint F n → Endpoint F n → ℝ)
    (w : (U F n × U F n) × (U F n × U F n)) (o : (Fin 2 → U F n) × (Fin 2 → U F n)) :
    outputCornerProduct Φ ![w.1.1.val, w.1.2.val] ![w.2.1.val, w.2.2.val]
        (nonzeroOutputEmbedding n o) =
      Φ ⟨w.1.1, o.1 0⟩ ⟨o.2 0, w.2.1⟩ *
      Φ ⟨w.1.2, o.1 1⟩ ⟨o.2 0, w.2.1⟩ *
      Φ ⟨w.1.2, o.1 1⟩ ⟨o.2 1, w.2.2⟩ *
      Φ ⟨w.1.1, o.1 0⟩ ⟨o.2 1, w.2.2⟩ := by
  change zeroExtend Φ w.1.1.val (o.1 0).val (o.2 0).val w.2.1.val *
      zeroExtend Φ w.1.2.val (o.1 1).val (o.2 0).val w.2.1.val *
      zeroExtend Φ w.1.2.val (o.1 1).val (o.2 1).val w.2.2.val *
      zeroExtend Φ w.1.1.val (o.1 0).val (o.2 1).val w.2.2.val = _
  simp only [zeroExtend_nonzero]

/-- The four-output nonzero density `((shareCard F n)/(vectorCard F n))^4` is at most one. This permits dropping that factor in an upper bound for a nonnegative four-cycle. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, assume 2 ≤ n. Then

((|F|ⁿ-1) / |F|ⁿ)⁴ ≤ 1.
-/
theorem reference_density_le_one {n : ℕ} (hn : 2 ≤ n) :
    ((shareCard F n : ℝ) / vectorCard F n) ^ 4 ≤ 1 := by
  have hqpos : (0 : ℝ) < fieldCard F := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hN : (0 : ℝ) < vectorCard F n := by
    simpa only [vectorCard, Nat.cast_pow] using pow_pos hqpos n
  have hd := nonzeroCard_real_pos (F := F) hn
  apply pow_le_one₀ (div_nonneg hd.le hN.le)
  apply (div_le_one hN).mpr
  rw [shareCard_cast_real]
  linarith

/-- Averaging the complete independent-output experiment gives exactly `((shareCard F n)/(vectorCard F n))^4` times the ambient signed four-cycle. The four density factors restrict only the outputs to nonzero vectors; regrouping the eight vectors then forms four endpoints. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; Φ ∈ Endpoint(F, n) → Endpoint(F, n) → ℝ, assume 2 ≤ n. Then

𝔼ᵤ [referenceInputMoment(Φ, u)] = ((|F|ⁿ-1) / |F|ⁿ)⁴ · fourCycle(Φ).
-/
theorem referenceMoment_eq_fourCycle {n : ℕ} (hn : 2 ≤ n)
    (Φ : Endpoint F n → Endpoint F n → ℝ) :
    uavg (referenceInputMoment Φ) = ((shareCard F n : ℝ) / vectorCard F n) ^ 4 * fourCycle Φ := by
  change uavg (fun w => referenceInputMoment Φ w) = _
  simp_rw [referenceInputMoment_nonzero_outputs hn Φ, nonzero_output_product]
  rw [uavg_const_mul, nonzeroReference_eq_fourCycle]

end

end MatrixRefresh
