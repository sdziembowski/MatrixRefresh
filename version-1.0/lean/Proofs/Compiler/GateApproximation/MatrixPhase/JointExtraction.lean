import Proofs.Compiler.GateApproximation.MatrixPhase.JointSchur



/-!
# Grouped feature blocks of the actual simultaneous extraction

Retained terms are grouped by their phase tag. Each block has an explicit finite complex feature factorization whose pointwise energy is bounded by the all-term energy certificate from the greedy extraction.
-/

set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler

noncomputable section

variable {I C : Type*} [Fintype I] [DecidableEq I] [DecidableEq C]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A,M a set; ts ∈ A*; f ∈ A → M, assume AddCommMonoid(M). Then

sum((f_*ts)) = ∑_(j ∈ {0,…,|ts|−1}) (f(ts.get(j))).
-/
lemma list_sum_map_eq_sum_get {A M : Type*} [AddCommMonoid M] (ts : List A) (f : A → M) :
    (ts.map f).sum = ∑ j : Fin ts.length, f (ts.get j) := by
  calc
    _ = (List.ofFn (fun j : Fin ts.length => f (ts.get j))).sum := by
      change (ts.map f).sum = (List.ofFn (f ∘ ts.get)).sum
      rw [← List.map_ofFn, List.ofFn_get]
    _ = _ := List.sum_ofFn

/-- The untwisted singular product associated to a retained term. -/
/-
Mathematical definition (normal notation): For t ∈ TwistedTerm(I, C), define

TwistedTerm.productTable(t) := singularProduct(t.magnitude, t.left, t.right).
-/
def TwistedTerm.productTable (t : TwistedTerm I C) : Matrix I I ℂ :=
  singularProduct t.magnitude t.left t.right

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For t ∈ TwistedTerm(I, C); i, j ∈ I, assume 0 ≤ t.magnitude. Then

t.productTable(i, j) = t.leftFeature(i) · star(t.rightFeature(j)).
-/
lemma TwistedTerm.productTable_eq_factors (t : TwistedTerm I C) (ht : 0 ≤ t.magnitude) (i j : I) :
    t.productTable i j = t.leftFeature i * star (t.rightFeature j) := by
  have hs : (Real.sqrt t.magnitude : ℂ) ^ 2 = (t.magnitude : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt ht]
  simp only [TwistedTerm.productTable, singularProduct, TwistedTerm.leftFeature,
    TwistedTerm.rightFeature, star_mul, Complex.star_def, Complex.conj_ofReal]
  linear_combination -t.left i * (starRingEnd ℂ) (t.right j) * hs

/-- All extracted singular products with a fixed twist label. -/
/-
Mathematical definition (normal notation): For ts ∈ TwistedTerm(I, C)*; c ∈ C, define

extractedBlock(ts, c) := sum((((t ↦ { t.productTable if t.tag = c,; 0 otherwise }))_*ts)).
-/
def extractedBlock (ts : List (TwistedTerm I C)) (c : C) : Matrix I I ℂ :=
  (ts.map (fun t => if t.tag = c then t.productTable else 0)).sum

/-- Finite left feature vector for a fixed extracted block. -/
/-
Mathematical definition (normal notation): For ts ∈ TwistedTerm(I, C)*; c ∈ C; i ∈ I, define

extractedLeftFeatures(ts, c, i) := WithLp.toLp(2, ((j ↦ { leftFeature(ts.get(j))(i) if tag(ts.get(j)) = c,; 0 otherwise }))).
-/
def extractedLeftFeatures (ts : List (TwistedTerm I C)) (c : C) (i : I) :
    EuclideanSpace ℂ (Fin ts.length) :=
  WithLp.toLp 2 (fun j => if (ts.get j).tag = c then (ts.get j).leftFeature i else 0)

/-- Finite right feature vector for the same extracted block. -/
/-
Mathematical definition (normal notation): For ts ∈ TwistedTerm(I, C)*; c ∈ C; i ∈ I, define

extractedRightFeatures(ts, c, i) := WithLp.toLp(2, ((j ↦ { rightFeature(ts.get(j))(i) if tag(ts.get(j)) = c,; 0 otherwise }))).
-/
def extractedRightFeatures (ts : List (TwistedTerm I C)) (c : C) (i : I) :
    EuclideanSpace ℂ (Fin ts.length) :=
  WithLp.toLp 2 (fun j => if (ts.get j).tag = c then (ts.get j).rightFeature i else 0)

/-- Grouping retains an exact feature factorization, without orthogonality. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ts ∈ TwistedTerm(I, C)*; c ∈ C, assume ∀ t ∈ ts, 0 ≤ t.magnitude. Then

extractedBlock(ts, c) = complexProductTable(extractedLeftFeatures(ts, c), extractedRightFeatures(ts, c)).
-/
theorem extractedBlock_eq_features (ts : List (TwistedTerm I C))
    (ht : ∀ t ∈ ts, 0 ≤ t.magnitude) (c : C) :
    extractedBlock ts c = complexProductTable (extractedLeftFeatures ts c) (extractedRightFeatures ts c) := by
  rw [extractedBlock, list_sum_map_eq_sum_get]
  ext i j
  simp only [Matrix.sum_apply, complexProductTable, extractedLeftFeatures,
    extractedRightFeatures, PiLp.toLp_apply]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : (ts.get k).tag = c
  · simp only [h, if_true]
    exact (ts.get k).productTable_eq_factors (ht _ (List.get_mem _ _)) i j
  · simp only [h, if_false, Matrix.zero_apply, star_zero, mul_zero]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ts ∈ TwistedTerm(I, C)*; c ∈ C; i ∈ I, we have

(‖ extractedLeftFeatures(ts, c, i)‖)² ≤ sum((((t ↦ (‖ t.leftFeature(i)‖)²))_*ts)) .
-/
lemma extractedLeftFeatures_norm_sq_le (ts : List (TwistedTerm I C)) (c : C) (i : I) :
    ‖extractedLeftFeatures ts c i‖ ^ 2 ≤ (ts.map (fun t => ‖t.leftFeature i‖ ^ 2)).sum := by
  rw [list_sum_map_eq_sum_get, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro k _
  change ‖if (ts.get k).tag = c then (ts.get k).leftFeature i else 0‖ ^ 2 ≤ _
  by_cases h : (ts.get k).tag = c
  · simp only [h, if_true, le_refl]
  · simp only [h, if_false, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ts ∈ TwistedTerm(I, C)*; c ∈ C; i ∈ I, we have

(‖ extractedRightFeatures(ts, c, i)‖)² ≤ sum((((t ↦ (‖ t.rightFeature(i)‖)²))_*ts)) .
-/
lemma extractedRightFeatures_norm_sq_le (ts : List (TwistedTerm I C)) (c : C) (i : I) :
    ‖extractedRightFeatures ts c i‖ ^ 2 ≤ (ts.map (fun t => ‖t.rightFeature i‖ ^ 2)).sum := by
  rw [list_sum_map_eq_sum_get, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro k _
  change ‖if (ts.get k).tag = c then (ts.get k).rightFeature i else 0‖ ^ 2 ≤ _
  by_cases h : (ts.get k).tag = c
  · simp only [h, if_true, le_refl]
  · simp only [h, if_false, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _

/-- Grouping by phase preserves the exact matrix decomposition. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For χ ∈ C → ℂ^(I × I); ts ∈ TwistedTerm(I, C)*, assume C is finite. Then

sum((TwistedTerm.value(χ)_*ts)) = ∑_c (inversePhase(χ(c)) ⊙ extractedBlock(ts, c)).
-/
theorem extractedBlock_decomposition [Fintype C] (χ : C → Matrix I I ℂ)
    (ts : List (TwistedTerm I C)) :
    (ts.map (TwistedTerm.value χ)).sum = ∑ c, inversePhase (χ c) ⊙ extractedBlock ts c := by
  induction ts with
  | nil => simp [extractedBlock]
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, extractedBlock, Matrix.hadamard_add,
      Finset.sum_add_distrib]
    change t.value χ + (ts.map (TwistedTerm.value χ)).sum =
      (∑ c, inversePhase (χ c) ⊙ (if t.tag = c then t.productTable else 0)) + _
    rw [ih]
    congr 1
    have h : (∑ c, inversePhase (χ c) ⊙ (if t.tag = c then t.productTable else 0)) =
        inversePhase (χ t.tag) ⊙ t.productTable := by
      simp only [apply_ite, Matrix.hadamard_zero]
      simp
    exact h.symm

/-- A block inherits the total extracted feature-energy Schur multiplier bound. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ts ∈ TwistedTerm(I, C)*; c ∈ C; B ∈ ℂ^(I × I); H ∈ ℝ, assume ∀ t ∈ ts, 0 ≤ t.magnitude; 0 ≤ H; ∀ i, sum((((t ↦ (‖ t.leftFeature(i)‖)²))_*ts)) ≤ H; ∀ j, sum((((t ↦ (‖ t.rightFeature(j)‖)²))_*ts)) ≤ H. Then

‖ B ⊙ extractedBlock(ts, c)‖ ≤ ‖ B‖ · H.
-/
theorem extractedBlock_schur_bound (ts : List (TwistedTerm I C))
    (ht : ∀ t ∈ ts, 0 ≤ t.magnitude) (c : C) (B : Matrix I I ℂ) (H : ℝ) (hH : 0 ≤ H)
    (hleft : ∀ i, (ts.map (fun t => ‖t.leftFeature i‖ ^ 2)).sum ≤ H)
    (hright : ∀ j, (ts.map (fun t => ‖t.rightFeature j‖ ^ 2)).sum ≤ H) :
    ‖B ⊙ extractedBlock ts c‖ ≤ ‖B‖ * H := by
  rw [extractedBlock_eq_features ts ht]
  have hleft' (i : I) : ‖extractedLeftFeatures ts c i‖ ≤ Real.sqrt H := by
    have h := (extractedLeftFeatures_norm_sq_le ts c i).trans (hleft i)
    simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt h
  have hright' (j : I) : ‖extractedRightFeatures ts c j‖ ≤ Real.sqrt H := by
    have h := (extractedRightFeatures_norm_sq_le ts c j).trans (hright j)
    simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt h
  have h := complex_feature_schur_bound (extractedLeftFeatures ts c)
    (extractedRightFeatures ts c) B (Real.sqrt H) (Real.sqrt H)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hleft' hright'
  simpa only [mul_assoc, ← pow_two, Real.sq_sqrt hH] using h

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ts ∈ TwistedTerm(I, C)*; c ∈ C, assume ∀ t ∈ ts, 0 ≤ t.magnitude ∧ ‖ t.left‖ = 1. Then

(∑ᵢ ((‖ extractedLeftFeatures(ts, c, i)‖)²)) ≤ sum((TwistedTerm.magnitude_*ts)) .
-/
lemma extractedLeftFeatures_total_le (ts : List (TwistedTerm I C))
    (ht : ∀ t ∈ ts, 0 ≤ t.magnitude ∧ ‖t.left‖ = 1) (c : C) :
    (∑ i, ‖extractedLeftFeatures ts c i‖ ^ 2) ≤ (ts.map TwistedTerm.magnitude).sum := by
  calc
    _ ≤ ∑ i, (ts.map (fun t => ‖t.leftFeature i‖ ^ 2)).sum :=
      Finset.sum_le_sum (fun i _ => extractedLeftFeatures_norm_sq_le ts c i)
    _ = _ := by
      simp_rw [list_sum_map_eq_sum_get]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      have hk := ht (ts.get k) (List.get_mem _ _)
      simp_rw [TwistedTerm.leftFeature_norm_sq _ hk.1]
      rw [← Finset.mul_sum, ← PiLp.norm_sq_eq_of_L2, hk.2]
      ring

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ts ∈ TwistedTerm(I, C)*; c ∈ C, assume ∀ t ∈ ts, 0 ≤ t.magnitude ∧ ‖ t.right‖ = 1. Then

(∑ᵢ ((‖ extractedRightFeatures(ts, c, i)‖)²)) ≤ sum((TwistedTerm.magnitude_*ts)) .
-/
lemma extractedRightFeatures_total_le (ts : List (TwistedTerm I C))
    (ht : ∀ t ∈ ts, 0 ≤ t.magnitude ∧ ‖t.right‖ = 1) (c : C) :
    (∑ i, ‖extractedRightFeatures ts c i‖ ^ 2) ≤ (ts.map TwistedTerm.magnitude).sum := by
  calc
    _ ≤ ∑ i, (ts.map (fun t => ‖t.rightFeature i‖ ^ 2)).sum :=
      Finset.sum_le_sum (fun i _ => extractedRightFeatures_norm_sq_le ts c i)
    _ = _ := by
      simp_rw [list_sum_map_eq_sum_get]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      have hk := ht (ts.get k) (List.get_mem _ _)
      simp_rw [TwistedTerm.rightFeature_norm_sq _ hk.1]
      rw [← Finset.mul_sum, ← PiLp.norm_sq_eq_of_L2, hk.2]
      ring

/-- Pointwise feature budgets also control the entrywise size of the residual. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For χ ∈ C → ℂ^(I × I); ts ∈ TwistedTerm(I, C)*; A, E ∈ ℂ^(I × I); L, H ∈ ℝ, assume ∀ c, i, j, ‖ χ(c, i, j)‖ = 1; ∀ t ∈ ts, 0 ≤ t.magnitude; A = sum((TwistedTerm.value(χ)_*ts)) + E; ∀ i, j, ‖ A(i, j)‖ ≤ L; ∀ i, sum((((t ↦ (‖ t.leftFeature(i)‖)²))_*ts)) ≤ H; ∀ j, sum((((t ↦ (‖ t.rightFeature(j)‖)²))_*ts)) ≤ H. Then

∀ i, j, ‖ E(i, j)‖ ≤ L + H.
-/
theorem extracted_residual_entry_le (χ : C → Matrix I I ℂ)
    (hχ : ∀ c i j, ‖χ c i j‖ = 1) (ts : List (TwistedTerm I C))
    (ht : ∀ t ∈ ts, 0 ≤ t.magnitude) (A E : Matrix I I ℂ)
    (hd : A = (ts.map (TwistedTerm.value χ)).sum + E) (L H : ℝ)
    (hA : ∀ i j, ‖A i j‖ ≤ L)
    (hleft : ∀ i, (ts.map (fun t => ‖t.leftFeature i‖ ^ 2)).sum ≤ H)
    (hright : ∀ j, (ts.map (fun t => ‖t.rightFeature j‖ ^ 2)).sum ≤ H) :
    ∀ i j, ‖E i j‖ ≤ L + H := by
  intro i j
  have he : E i j = A i j - ((ts.map (TwistedTerm.value χ)).sum) i j := by
    have h := congrArg (fun B : Matrix I I ℂ => B i j) hd
    change A i j = ((ts.map (TwistedTerm.value χ)).sum) i j + E i j at h
    rw [h, add_sub_cancel_left]
  rw [he]
  apply (norm_sub_le _ _).trans
  apply add_le_add (hA i j)
  rw [list_sum_map_eq_sum_get, Matrix.sum_apply]
  apply (norm_sum_le _ _).trans
  have hb (k : Fin ts.length) : ‖(ts.get k).value χ i j‖ ≤
      (‖(ts.get k).leftFeature i‖ ^ 2 + ‖(ts.get k).rightFeature j‖ ^ 2) / 2 := by
    have hk := (ts.get k).productTable_eq_factors (ht _ (List.get_mem _ _)) i j
    have hv : (ts.get k).value χ i j = inversePhase (χ (ts.get k).tag) i j *
        (ts.get k).productTable i j := rfl
    rw [hv, norm_mul, inversePhase_unit _ (hχ _) i j, one_mul, hk, norm_mul, norm_star]
    nlinarith [sq_nonneg (‖(ts.get k).leftFeature i‖ - ‖(ts.get k).rightFeature j‖)]
  calc
    _ ≤ ∑ k : Fin ts.length,
        (‖(ts.get k).leftFeature i‖ ^ 2 + ‖(ts.get k).rightFeature j‖ ^ 2) / 2 :=
      Finset.sum_le_sum (fun k _ => hb k)
    _ = ((ts.map (fun t => ‖t.leftFeature i‖ ^ 2)).sum +
        (ts.map (fun t => ‖t.rightFeature j‖ ^ 2)).sum) / 2 := by
      simp_rw [list_sum_map_eq_sum_get]
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ H := by linarith [hleft i, hright j]

/-- Support on the character constraint lets us isolate each individual block. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For χ ∈ C → ℂ^(I × I); ts ∈ TwistedTerm(I, C)*; A, E ∈ ℂ^(I × I); c ∈ C, assume C is finite; ∀ c, i, j, ‖ χ(c, i, j)‖ = 1; A = sum((TwistedTerm.value(χ)_*ts)) + E; ∀ c, χ(c) ⊙ A = A. Then

extractedBlock(ts, c) = A - χ(c) ⊙ E - ∑_(d ∈ Finset.univ.erase(c)) ((χ(c) ⊙ inversePhase(χ(d))) ⊙ extractedBlock(ts, d)).
-/
theorem extractedBlock_isolation [Fintype C] (χ : C → Matrix I I ℂ)
    (hχ : ∀ c i j, ‖χ c i j‖ = 1) (ts : List (TwistedTerm I C))
    (A E : Matrix I I ℂ) (hd : A = (ts.map (TwistedTerm.value χ)).sum + E)
    (hsupport : ∀ c, χ c ⊙ A = A) (c : C) :
    extractedBlock ts c = A - χ c ⊙ E -
      ∑ d ∈ Finset.univ.erase c, (χ c ⊙ inversePhase (χ d)) ⊙ extractedBlock ts d := by
  rw [extractedBlock_decomposition] at hd
  have he : χ c ⊙ A = (∑ d, (χ c ⊙ inversePhase (χ d)) ⊙ extractedBlock ts d) + χ c ⊙ E := by
    rw [hd]
    ext i j
    simp only [Matrix.hadamard_apply, Matrix.add_apply, Matrix.sum_apply, mul_add,
      Finset.mul_sum, mul_assoc]
  rw [hsupport] at he
  have hz (i j : I) : χ c i j ≠ 0 := by
    intro h
    simpa only [h, norm_zero, zero_ne_one] using hχ c i j
  have hself : (χ c ⊙ inversePhase (χ c)) ⊙ extractedBlock ts c = extractedBlock ts c := by
    ext i j
    simp [Matrix.hadamard_apply, inversePhase, hz]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ c), hself] at he
  rw [he]
  abel

/-- The isolated block is small because every unequal phase quotient is mixing. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For χ ∈ C → ℂ^(I × I); ts ∈ TwistedTerm(I, C)*; A, E ∈ ℂ^(I × I); β, δ, H ∈ ℝ; c ∈ C, assume C is finite; ∀ c, i, j, ‖ χ(c, i, j)‖ = 1; ∀ t ∈ ts, 0 ≤ t.magnitude; A = sum((TwistedTerm.value(χ)_*ts)) + E; ∀ c, χ(c) ⊙ A = A; 0 ≤ δ; 0 ≤ H; ∀ c, ‖ χ(c) ⊙ E‖ ≤ β; ∀ c, d, (c ≠ d) ⇒ ‖ χ(c) ⊙ inversePhase(χ(d))‖ ≤ δ; ∀ i, sum((((t ↦ (‖ t.leftFeature(i)‖)²))_*ts)) ≤ H; ∀ j, sum((((t ↦ (‖ t.rightFeature(j)‖)²))_*ts)) ≤ H. Then

‖ extractedBlock(ts, c)‖ ≤ ‖ A‖ + β + |C| · δ · H.
-/
theorem extractedBlock_norm_le [Fintype C] (χ : C → Matrix I I ℂ)
    (hχ : ∀ c i j, ‖χ c i j‖ = 1) (ts : List (TwistedTerm I C))
    (ht : ∀ t ∈ ts, 0 ≤ t.magnitude) (A E : Matrix I I ℂ)
    (hd : A = (ts.map (TwistedTerm.value χ)).sum + E)
    (hsupport : ∀ c, χ c ⊙ A = A) (β δ H : ℝ) (hδ : 0 ≤ δ) (hH : 0 ≤ H)
    (hE : ∀ c, ‖χ c ⊙ E‖ ≤ β)
    (hcross : ∀ c d, c ≠ d → ‖χ c ⊙ inversePhase (χ d)‖ ≤ δ)
    (hleft : ∀ i, (ts.map (fun t => ‖t.leftFeature i‖ ^ 2)).sum ≤ H)
    (hright : ∀ j, (ts.map (fun t => ‖t.rightFeature j‖ ^ 2)).sum ≤ H) (c : C) :
    ‖extractedBlock ts c‖ ≤ ‖A‖ + β + Fintype.card C * δ * H := by
  rw [extractedBlock_isolation χ hχ ts A E hd hsupport c]
  apply (norm_sub_le _ _).trans
  have hfirst : ‖A - χ c ⊙ E‖ ≤ ‖A‖ + β :=
    (norm_sub_le _ _).trans (add_le_add le_rfl (hE c))
  apply add_le_add hfirst
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ d ∈ Finset.univ.erase c, δ * H := by
      apply Finset.sum_le_sum
      intro d hd
      exact (extractedBlock_schur_bound ts ht d _ H hH hleft hright).trans
        (mul_le_mul_of_nonneg_right (hcross c d (Ne.symm (Finset.mem_erase.mp hd).1)) hH)
    _ ≤ ∑ _d : C, δ * H := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset _ _) (fun _ _ _ => mul_nonneg hδ hH)
    _ = _ := by simp [mul_assoc]

end

end CircuitCompiler
