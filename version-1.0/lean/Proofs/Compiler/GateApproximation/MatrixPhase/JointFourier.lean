import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.LegendreSymbol.Complex
import Mathlib.Tactic
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Counts



/-!
# Finite-field Fourier orthogonality for the joint-port twists

A primitive complex additive character exists over every finite field. The full dot-product character matrix has operator norm exactly `sqrt(q^n)`. This is the spectral estimate underlying the nonzero-twist error term.
-/

set_option autoImplicit false

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler

open Refresh

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A fixed primitive additive character, over an arbitrary finite field. -/
/-
Mathematical definition (normal notation): For F a set, assume F is a field; F is finite. define

fieldCharacter := AddChar.FiniteField.primitiveChar_to_Complex(F).
-/
def fieldCharacter (F : Type*) [Field F] [Fintype F] : AddChar F ℂ :=
  AddChar.FiniteField.primitiveChar_to_Complex F

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

IsPrimitive(fieldCharacter(F)).
-/
theorem fieldCharacter_primitive : (fieldCharacter F).IsPrimitive :=
  AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F

/-- Pairing with a fixed row followed by an additive character. -/
/-
Mathematical definition (normal notation): From an additive character ψ:𝔽 → ℂ and a vector a ∈ 𝔽ⁿ, form the additive character on vectors

χₐ(v) := ψ(a · v).
-/
def dotCharacter {n : ℕ} (ψ : AddChar F ℂ) (a : V F n) : AddChar (V F n) ℂ :=
  ψ.compAddMonoidHom
    { toFun := fun v => dot a v
      map_zero' := dot_zero_right a
      map_add' := fun v w => dot_add_right a v w }

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; ψ ∈ AddChar(F, ℂ); a, v ∈ V(F, n), we have

dotCharacter(ψ, a, v) = ψ((a · v)).
-/
@[simp] theorem dotCharacter_apply {n : ℕ} (ψ : AddChar F ℂ) (a v : V F n) :
    dotCharacter ψ a v = ψ (dot a v) :=
  rfl

/-- Orthogonality of a nontrivial character on each nonzero vector functional. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; ψ ∈ AddChar(F, ℂ); a ∈ V(F, n), assume ψ.IsPrimitive. Then

(∑_(v ∈ V(F, n)) (ψ((a · v)))) = { (|F|)ⁿ if a = 0,; 0 otherwise }.
-/
theorem sum_dotCharacter {n : ℕ} (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (a : V F n) :
    (∑ v : V F n, ψ (dot a v)) = if a = 0 then (fieldCard F ^ n : ℕ) else 0 := by
  by_cases ha : a = 0
  · simp [ha, fieldCard]
  · rw [if_neg ha]
    have hn : ψ ≠ 1 := by
      have h := hψ (a := 1) one_ne_zero
      simpa using h
    obtain ⟨t, ht⟩ := AddChar.ne_one_iff.1 hn
    obtain ⟨v, hv⟩ := exists_dot_one (⟨a, ha⟩ : U F n)
    have hdot : dotCharacter ψ a ≠ 1 := by
      intro h
      have he := congrArg (fun χ : AddChar (V F n) ℂ => χ (t • v)) h
      exact ht (by simpa [dot_smul_right, hv] using he)
    simpa using AddChar.sum_eq_zero_of_ne_one hdot

/-- Fourier matrix of the field dot product, with counting-measure entries. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; ψ ∈ AddChar(F, ℂ), define

dotFourierMatrix(n, ψ) := (a, b ↦ ψ((a · b))).
-/
def dotFourierMatrix (n : ℕ) (ψ : AddChar F ℂ) : Matrix (V F n) (V F n) ℂ :=
  fun a b => ψ (dot a b)

/-- Exact Gram identity before any restriction to nonzero shares. -/

/-
Mathematical statement (normal notation): Let ψ be a primitive additive character of a finite field 𝔽, and define H_(x,y) = ψ(x · y) for x,y ∈ 𝔽ⁿ. Then

H* · H = |𝔽|ⁿ · I.

The star denotes conjugate transpose; matrix multiplication here uses ordinary sums.
-/
theorem dotFourierMatrix_gram (n : ℕ) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    (dotFourierMatrix n ψ)ᴴ * dotFourierMatrix n ψ =
      ((fieldCard F ^ n : ℕ) : ℂ) • (1 : Matrix (V F n) (V F n) ℂ) := by
  ext a b
  change (∑ v, star (ψ (dot v a)) * ψ (dot v b)) = _
  have hp (v : V F n) : star (ψ (dot v a)) * ψ (dot v b) = ψ (dot (b - a) v) := by
    rw [dot_comm (b - a) v, dot_sub_right, ψ.map_sub_eq_div, div_eq_mul_inv,
      Complex.inv_eq_conj (ψ.norm_apply _)]
    simp only [starRingEnd_apply, mul_comm]
  simp_rw [hp]
  rw [sum_dotCharacter ψ hψ]
  by_cases h : a = b
  · subst b; simp
  · have hab : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    simp [h, hab, Matrix.one_apply]

/-- Counting-measure Fourier operator norm squared. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; ψ ∈ AddChar(F, ℂ), assume ψ.IsPrimitive. Then

(‖ dotFourierMatrix(n, ψ)‖)² = (|F|)ⁿ.
-/
theorem dotFourierMatrix_norm_sq (n : ℕ) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖dotFourierMatrix n ψ‖ ^ 2 = (fieldCard F ^ n : ℕ) := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (dotFourierMatrix n ψ)
  rw [dotFourierMatrix_gram n ψ hψ, norm_smul, norm_one, mul_one] at h
  simpa [pow_two] using h.symm

/-- The exact square-root Fourier bound, for every finite extension field. -/

/-
Mathematical statement (normal notation): For the character matrix H_(x,y) = ψ(x · y), where ψ is primitive and x,y ∈ 𝔽ⁿ, the usual Euclidean operator norm is

‖H‖_(op,Euclidean) = √(|𝔽|ⁿ).

This is the unnormalized matrix norm.
-/
theorem dotFourierMatrix_norm (n : ℕ) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖dotFourierMatrix n ψ‖ = Real.sqrt (fieldCard F ^ n : ℕ) := by
  rw [← dotFourierMatrix_norm_sq n ψ hψ, Real.sqrt_sq (norm_nonneg _)]

section Restriction

variable {I : Type*} [Fintype I] [DecidableEq I] (P : I → Prop) [DecidablePred P]

/-- Zero extension from a subset of the coordinate indices. -/
/-
Mathematical definition (normal notation): For x ∈ EuclideanSpace(ℂ, {i | P(i)}), define

extendCoordinates(x) := WithLp.toLp(2, ((i ↦ { x((i, h)) if P(i),; 0 otherwise }))).
-/
def extendCoordinates (x : EuclideanSpace ℂ {i // P i}) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun i => if h : P i then x ⟨i, h⟩ else 0)

/-- Restriction to a subset of coordinates. -/
/-
Mathematical definition (normal notation): For x ∈ EuclideanSpace(ℂ, I), define

restrictCoordinates(x) := WithLp.toLp(2, ((i ↦ x(i)))).
-/
def restrictCoordinates (x : EuclideanSpace ℂ I) : EuclideanSpace ℂ {i // P i} :=
  WithLp.toLp 2 (fun i => x i.val)

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For x ∈ EuclideanSpace(ℂ, {i | P(i)}), we have

‖ extendCoordinates(P, x)‖ = ‖ x‖.
-/
theorem extendCoordinates_norm (x : EuclideanSpace ℂ {i // P i}) :
    ‖extendCoordinates P x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  have h := Fintype.sum_subtype_add_sum_subtype P
    (fun i => ‖extendCoordinates P x i‖ ^ 2)
  have hp (i : {i // P i}) : extendCoordinates P x i.val = x i := by
    simp [extendCoordinates, i.property]
  have hn (i : {i // ¬ P i}) : extendCoordinates P x i.val = 0 := by
    simp [extendCoordinates, i.property]
  simpa only [hp, hn, norm_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, add_zero] using h.symm

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For x ∈ EuclideanSpace(ℂ, I), we have

‖ restrictCoordinates(P, x)‖ ≤ ‖ x‖.
-/
theorem restrictCoordinates_norm_le (x : EuclideanSpace ℂ I) :
    ‖restrictCoordinates P x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  have h := Fintype.sum_subtype_add_sum_subtype P (fun i => ‖x i‖ ^ 2)
  have hn : 0 ≤ ∑ i : {i // ¬ P i}, ‖x i.val‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change (∑ i : {i // P i}, ‖x i.val‖ ^ 2) ≤ _
  linarith

/-- A principal submatrix is compression by zero extension and restriction. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); x ∈ EuclideanSpace(ℂ, {i | P(i)}), we have

toEuclideanLin(A.submatrix(Subtype, Subtype))(x) = restrictCoordinates(P, A.toEuclideanLin(extendCoordinates(P, x))) .
-/
theorem subtypeMatrix_apply (A : Matrix I I ℂ) (x : EuclideanSpace ℂ {i // P i}) :
    (A.submatrix Subtype.val Subtype.val).toEuclideanLin x =
      restrictCoordinates P (A.toEuclideanLin (extendCoordinates P x)) := by
  ext i
  change (∑ j : {i // P i}, A i.val j.val * x j) =
    ∑ j : I, A i.val j * extendCoordinates P x j
  have h := Fintype.sum_subtype_add_sum_subtype P
    (fun j => A i.val j * extendCoordinates P x j)
  have hp (j : {i // P i}) : extendCoordinates P x j.val = x j := by
    simp [extendCoordinates, j.property]
  have hn (j : {i // ¬ P i}) : extendCoordinates P x j.val = 0 := by
    simp [extendCoordinates, j.property]
  simpa only [hp, hn, mul_zero, Finset.sum_const_zero, add_zero] using h

/-- Restricting a matrix to a principal subset cannot increase its operator norm. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I), we have

‖ A.submatrix(((i ∈ {i | P(i)} ↦ i)), ((i ∈ {i | P(i)} ↦ i)))‖ ≤ ‖ A‖.
-/
theorem subtypeMatrix_norm_le (A : Matrix I I ℂ) :
    ‖A.submatrix (fun i : {i // P i} => i.val) (fun i : {i // P i} => i.val)‖ ≤ ‖A‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖(A.submatrix Subtype.val Subtype.val).toEuclideanLin x‖ ≤ ‖A‖ * ‖x‖
  rw [subtypeMatrix_apply]
  calc
    _ ≤ ‖A.toEuclideanLin (extendCoordinates P x)‖ := restrictCoordinates_norm_le P _
    _ ≤ ‖A‖ * ‖extendCoordinates P x‖ := A.l2_opNorm_mulVec _
    _ = ‖A‖ * ‖x‖ := by rw [extendCoordinates_norm]

end Restriction

/-- The character table on the manuscript's nonzero share space. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; ψ ∈ AddChar(F, ℂ), define

nonzeroDotFourierMatrix(n, ψ) := submatrix(dotFourierMatrix(n, ψ))(Subtype, Subtype).
-/
def nonzeroDotFourierMatrix (n : ℕ) (ψ : AddChar F ℂ) : Matrix (U F n) (U F n) ℂ :=
  (dotFourierMatrix n ψ).submatrix Subtype.val Subtype.val

/-- Restriction to nonzero vectors gives the exact normalization in the paper: `sqrt(Q)/(Q-1)` for the operator under uniform measure on nonzero vectors. -/

/-
Mathematical statement (normal notation): Restrict the character matrix H_(x,y) = ψ(x · y) to nonzero rows and columns, obtaining H₀. Its normalized operator norm obeys

(‖H₀‖_(op,Euclidean))/(|𝔽|ⁿ-1) ≤ (√(|𝔽|ⁿ))/(|𝔽|ⁿ-1).

Here ψ is a primitive additive character; the formal statement also uses Lean's totalized division when the carrier is empty.
-/
theorem nonzeroDotFourierMatrix_uniform_norm_le (n : ℕ) (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) :
    ‖nonzeroDotFourierMatrix n ψ‖ / Fintype.card (U F n) ≤
      Real.sqrt (fieldCard F ^ n : ℕ) / ((fieldCard F ^ n - 1 : ℕ) : ℝ) := by
  have h := subtypeMatrix_norm_le (fun v : V F n => v ≠ 0) (dotFourierMatrix n ψ)
  rw [dotFourierMatrix_norm n ψ hψ] at h
  change ‖(dotFourierMatrix n ψ).submatrix Subtype.val Subtype.val‖ / _ ≤ _
  rw [nonzero_vector_card]
  exact div_le_div_of_nonneg_right h (Nat.cast_nonneg _)

end

end CircuitCompiler
