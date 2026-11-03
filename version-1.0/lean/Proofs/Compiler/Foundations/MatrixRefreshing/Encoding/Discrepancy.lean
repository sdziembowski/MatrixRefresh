import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.DualPairing
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.EncodingBounds



set_option autoImplicit false

open scoped BigOperators

/-! Real incidence-matrix estimates for scalar products over finite fields. The proof uses counts of simultaneous linear equations and finite sums. -/

namespace Refresh

attribute [local instance] Classical.propDecidable

section FiniteSums

variable {α : Type*} [Fintype α]

/-- Cauchy–Schwarz for unnormalized finite real sums. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f, g ∈ α → ℝ, we have

|∑ᵢ (f(i) · g(i))| ≤ √(∑ᵢ ((f(i))²)) · √(∑ᵢ ((g(i))²)).
-/
theorem abs_sum_mul_le (f g : α → ℝ) :
    |∑ i, f i * g i| ≤ Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, g i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt h

/-- A symmetric nonnegative table of constant row mass bounds its quadratic form. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ α → α → ℝ; c ∈ ℝ; b ∈ α → ℝ, assume ∀ i, j, 0 ≤ P(i, j); ∀ i, j, P(i, j) = P(j, i); ∀ i, ∑ⱼ (P(i, j)) = c. Then

|∑ᵢ (∑ⱼ (P(i, j) · b(i) · b(j)))| ≤ c · ∑ᵢ ((b(i))²).
-/
theorem regular_table_quadratic_abs_le (P : α → α → ℝ) (c : ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hsym : ∀ i j, P i j = P j i)
    (hrow : ∀ i, ∑ j, P i j = c) (b : α → ℝ) :
    |∑ i, ∑ j, P i j * b i * b j| ≤ c * ∑ i, b i ^ 2 := by
  have hpair (i j : α) : |P i j * b i * b j| ≤
      P i j * (b i ^ 2 + b j ^ 2) / 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (hP i j)]
    have hab : 2 * (|b i| * |b j|) ≤ b i ^ 2 + b j ^ 2 := by
      nlinarith [sq_nonneg (|b i| - |b j|), sq_abs (b i), sq_abs (b j)]
    have hh := mul_le_mul_of_nonneg_left hab (hP i j)
    nlinarith
  have hcol (j : α) : ∑ i, P i j = c := by
    simp_rw [hsym _ j]
    exact hrow j
  calc
    _ ≤ ∑ i, |∑ j, P i j * b i * b j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |P i j * b i * b j| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, P i j * (b i ^ 2 + b j ^ 2) / 2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpair i j))
    _ = c * ∑ i, b i ^ 2 := by
      simp_rw [mul_add, add_div, Finset.sum_add_distrib]
      have hleft : (∑ i, ∑ j, P i j * b i ^ 2 / 2) =
          (c / 2) * ∑ i, b i ^ 2 := by
        simp_rw [← Finset.sum_div, ← Finset.sum_mul, hrow]
        simp [div_eq_mul_inv, ← Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
      have hright : (∑ i, ∑ j, P i j * b j ^ 2 / 2) =
          (c / 2) * ∑ j, b j ^ 2 := by
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_div, ← Finset.sum_mul, hcol]
        simp [div_eq_mul_inv, ← Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
      rw [hleft, hright]
      ring

/-- Expanding a squared matrix action produces the Gram quadratic form. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ α → α → ℝ; b ∈ α → ℝ, we have

∑ᵢ ((∑ⱼ (A(i, j) · b(j)))²) = ∑ⱼ (∑ₖ ((∑ᵢ (A(i, j) · A(i, k))) · b(j) · b(k))).
-/
theorem gram_quadratic_identity (A : α → α → ℝ) (b : α → ℝ) :
    ∑ i, (∑ j, A i j * b j) ^ 2 =
      ∑ j, ∑ k, (∑ i, A i j * A i k) * b j * b k := by
  simp only [sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A table consisting of a diagonal term, a multiple of `P`, and a constant term has the corresponding sum of square, table, and total-mass quadratic forms. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ α → α → ℝ; b ∈ α → ℝ; a, c, e ∈ ℝ, we have

(∑ᵢ (∑ⱼ ((({ a if i = j,; 0 otherwise }) + c · P(i, j) - e) · b(i) · b(j)))) = a · ∑ᵢ ((b(i))² + c · (∑ᵢ (∑ⱼ (P(i, j) · b(i) · b(j)))) - e · (∑ᵢ (b(i)))²).
-/
theorem quadratic_gram_formula [DecidableEq α] (P : α → α → ℝ) (b : α → ℝ) (a c e : ℝ) :
    (∑ i, ∑ j, ((if i = j then a else 0) + c * P i j - e) * b i * b j) =
      a * ∑ i, b i ^ 2 + c * (∑ i, ∑ j, P i j * b i * b j) - e * (∑ i, b i) ^ 2 := by
  classical
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hdiag : (∑ i, ∑ j, (if i = j then a else 0) * b i * b j) = a * ∑ i, b i ^ 2 := by
    simp [ite_mul, Finset.mul_sum, sq, mul_assoc]
  have hP : (∑ i, ∑ j, c * P i j * b i * b j) = c * (∑ i, ∑ j, P i j * b i * b j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hone : (∑ i, ∑ j, e * b i * b j) = e * (∑ i, b i) ^ 2 := by
    calc
      _ = (∑ i, e * b i) * (∑ j, b j) := by rw [Finset.sum_mul_sum]
      _ = _ := by rw [← Finset.mul_sum]; ring
  rw [hdiag, hP, hone]

/-- A squared Euclidean norm bound for a matrix action implies a bilinear bound with the same nonnegative operator coefficient. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ α → α → ℝ; S ∈ ℝ; a, b ∈ α → ℝ, assume 0 ≤ S; ∀ b ∈ α → ℝ, ∑ᵢ ((∑ⱼ (A(i, j) · b(j)))²) ≤ S² · ∑ⱼ ((b(j))²). Then

|∑ᵢ (∑ⱼ (A(i, j) · a(i) · b(j)))| ≤ S · √(∑ᵢ ((a(i))²)) · √(∑ⱼ ((b(j))²)).
-/
theorem bilinear_bound_of_quadratic (A : α → α → ℝ) (S : ℝ) (hS : 0 ≤ S)
    (hquad : ∀ b : α → ℝ, ∑ i, (∑ j, A i j * b j) ^ 2 ≤ S ^ 2 * ∑ j, b j ^ 2)
    (a b : α → ℝ) :
    |∑ i, ∑ j, A i j * a i * b j| ≤
      S * Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ j, b j ^ 2) := by
  let g := fun i => ∑ j, A i j * b j
  have he : (∑ i, ∑ j, A i j * a i * b j) = ∑ i, a i * g i := by
    simp only [g, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hq := Real.sqrt_le_sqrt (hquad b)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg hS] at hq
  rw [he]
  exact (abs_sum_mul_le a g).trans (by
    have hh := mul_le_mul_of_nonneg_left hq (Real.sqrt_nonneg (∑ i, a i ^ 2))
    simpa only [g, mul_assoc, mul_comm, mul_left_comm] using hh)

/-- A common positive averaging factor can be pulled out of the product of two square-root second moments. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For d, A, B ∈ ℝ, assume 0 < d. Then

√((1 / d) · A) · √((1 / d) · B) = (1 / d) · (√A · √B).
-/
theorem sqrt_product_normalization (d A B : ℝ) (hd : 0 < d) :
    Real.sqrt ((1 / d) * A) * Real.sqrt ((1 / d) * B) =
      (1 / d) * (Real.sqrt A * Real.sqrt B) := by
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  calc
    _ = (Real.sqrt (1 / d) * Real.sqrt (1 / d)) * (Real.sqrt A * Real.sqrt B) := by ring
    _ = _ := by rw [Real.mul_self_sqrt (by positivity)]

end FiniteSums

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- A sum over nonzero vectors is the sum over all vectors with the zero-vector contribution removed. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ V(F, n) → ℝ, we have

∑_(r ∈ U(F, n)) (f(r)) = (∑_(r ∈ V(F, n)) (f(r))) - f(0).
-/
theorem sum_U_eq (f : V F n → ℝ) :
    ∑ r : U F n, f r.val = (∑ r : V F n, f r) - f 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.erase (0 : V F n)) (by intro x; simp) f]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]

/-- The nonzero-vector carrier has exactly `(fieldCard F)^n - 1` elements. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For F a set; n ∈ ℕ, assume F is a field; F is finite. Then

|U(F, n)| = (|F|)ⁿ - 1.
-/
theorem card_U (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) :
    Fintype.card (U F n) = fieldCard F ^ n - 1 := by
  simp [U, V, fieldCard, Fintype.card_subtype_compl]

/-- As a real number, the nonzero-vector count is `(vectorCard F n) - 1`. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For F a set; n ∈ ℕ, assume F is a field; F is finite. Then

|U(F, n)| = |F|ⁿ - 1.
-/
theorem card_U_real (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) :
    (Fintype.card (U F n) : ℝ) = (vectorCard F n : ℝ) - 1 := by
  rw [card_U]
  have hq : 1 ≤ fieldCard F := Fintype.card_pos
  have hp : 1 ≤ fieldCard F ^ n := Nat.one_le_pow _ _ hq
  push_cast [Nat.cast_sub hp]
  simp [vectorCard]

/-- Nonzero vectors on the same one-dimensional subspace. -/
/-
Mathematical definition (normal notation): For l, k ∈ U(F, n), define

projectiveRel(l, k) := ∃ c ∈ F, k = c · l.
-/
def projectiveRel (l k : U F n) : Prop := ∃ c : F, k.val = c • l.val

/-- Being on the same one-dimensional subspace is symmetric for nonzero vectors. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For l, k ∈ U(F, n), we have

projectiveRel(l, k) ⇔ projectiveRel(k, l).
-/
theorem projectiveRel_symm (l k : U F n) : projectiveRel l k ↔ projectiveRel k l := by
  suffices ∀ l k : U F n, projectiveRel l k → projectiveRel k l from
    ⟨this l k, this k l⟩
  intro l k ⟨c, hc⟩
  have hc0 : c ≠ 0 := by
    intro hz
    exact k.property (by simpa [hz] using hc)
  refine ⟨c⁻¹, ?_⟩
  rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]

/-- Every nonzero vector lies in its own projective class. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For l ∈ U(F, n), we have

projectiveRel(l, l).
-/
theorem projectiveRel_self (l : U F n) : projectiveRel l l :=
  ⟨1, by simp⟩

/-- The nonzero scalar multiples of a nonzero vector are in bijection with its projective class. -/
/- Mathematical definition (normal notation): For a nonzero vector ℓ, multiplication c ↦ c · ℓ bijects the nonzero field scalars with the nonzero vectors proportional to ℓ. -/
noncomputable def projectiveClassEquiv (l : U F n) :
    {c : F // c ≠ 0} ≃ {k : U F n // projectiveRel l k} :=
  Equiv.ofBijective (fun c => ⟨⟨c.val • l.val, smul_ne_zero c.property l.property⟩, c.val, rfl⟩)
    (by
      constructor
      · intro a b hab
        apply Subtype.ext
        exact smul_left_injective F l.property (congrArg (fun k => k.val.val) hab)
      · rintro ⟨k, c, hc⟩
        have hc0 : c ≠ 0 := by
          intro hz
          exact k.property (by simpa [hz] using hc)
        refine ⟨⟨c, hc0⟩, ?_⟩
        apply Subtype.ext
        exact Subtype.ext hc.symm)

/-- Each projective class contains exactly `(fieldCard F) - 1` nonzero vectors. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For l ∈ U(F, n), we have

|{k ∈ U(F, n) | projectiveRel(l, k)}| = |F| - 1.
-/
theorem projectiveRel_card (l : U F n) :
    Fintype.card {k : U F n // projectiveRel l k} = fieldCard F - 1 := by
  classical
  rw [← Fintype.card_congr (projectiveClassEquiv l)]
  simp [fieldCard, Fintype.card_subtype_compl]

/-- Two nonzero vectors on different one-dimensional subspaces are linearly independent. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For l, k ∈ U(F, n), assume ¬ (projectiveRel(l, k)). Then

LinearIndependent(F, (l, k)).
-/
theorem pair_independent_of_not_projectiveRel (l k : U F n)
    (h : ¬ projectiveRel l k) : LinearIndependent F ![l.val, k.val] := by
  apply (LinearIndependent.pair_iff' l.property).mpr
  intro c hc
  exact h ⟨c, hc.symm⟩

/-- The manuscript's partner count `m_s`, expressed in real arithmetic: `(vectorCard F n)/(fieldCard F) - 1` for secret zero and `(vectorCard F n)/(fieldCard F)` otherwise. It is the number of nonzero partners of each fixed nonzero row, whenever such a row exists. -/
/-
Mathematical definition (normal notation): For F a set; n ∈ ℕ; s ∈ F, assume F is a field; F is finite. define

incidenceDegree(n, s) := |F|ⁿ / |F| - { 1 if s = 0,; 0 otherwise }.
-/
noncomputable def incidenceDegree (F : Type*) [Field F] [Fintype F]
    (n : ℕ) (s : F) : ℝ :=
  (vectorCard F n : ℝ) / (fieldCard F : ℝ) - if s = 0 then 1 else 0

/-- The real-valued indicator that two nonzero vectors have inner product `s`. -/
/-
Mathematical definition (normal notation): For s ∈ F; l, r ∈ U(F, n), define

incidence(s, l, r) := { 1 if (l · r) = s,; 0 otherwise }.
-/
noncomputable def incidence (s : F) (l r : U F n) : ℝ :=
  if dot l.val r.val = s then 1 else 0

/-- Scalar-product incidence is symmetric in its two nonzero-vector arguments. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F; l, r ∈ U(F, n), we have

incidence(s, l, r) = incidence(s, r, l).
-/
theorem incidence_symm (s : F) (l r : U F n) : incidence s l r = incidence s r l := by
  unfold incidence dot
  rw [dotProduct_comm l.val r.val]

/-- For `k` linearly independent pairing constraints, the number of simultaneous solutions is `(vectorCard F n) / (fieldCard F)^k`, expressed in real arithmetic. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For k ∈ ℕ; l ∈ {0,…,k-1} → V(F, n); s ∈ {0,…,k-1} → F, assume LinearIndependent(F, l). Then

|{v ∈ V(F, n) | dotMap(l, v) = s}| = |F|ⁿ / (|F|)ᵏ.
-/
theorem dotMap_fiber_card_real {k : ℕ} (l : Fin k → V F n)
    (h : LinearIndependent F l) (s : Fin k → F) :
    (Fintype.card {v : V F n // dotMap l v = s} : ℝ) =
      (vectorCard F n : ℝ) / (fieldCard F : ℝ) ^ k := by
  have hq : (0 : ℝ) < fieldCard F := by exact_mod_cast Fintype.card_pos (α := F)
  apply (eq_div_iff (pow_ne_zero k (ne_of_gt hq))).mpr
  exact_mod_cast card_fiber_mul l h s

/-- A single prescribed pairing with a nonzero row has `(vectorCard F n) / (fieldCard F)` solutions in the full vector space. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For l ∈ U(F, n); s ∈ F, we have

(∑_(r ∈ V(F, n)) ({ 1 if (l · r) = s,; 0 otherwise })) = |F|ⁿ / |F|.
-/
theorem full_incidence_row_sum (l : U F n) (s : F) :
    (∑ r : V F n, if dot l.val r = s then (1 : ℝ) else 0) =
      (vectorCard F n : ℝ) / (fieldCard F : ℝ) := by
  have hi : LinearIndependent F (fun _ : Fin 1 => l.val) :=
    LinearIndependent.of_subsingleton 0 l.property
  have hc := dotMap_fiber_card_real (fun _ : Fin 1 => l.val) hi (fun _ => s)
  have he : {v : V F n // dotMap (fun _ : Fin 1 => l.val) v = (fun _ => s)} ≃
      {v : V F n // dot l.val v = s} :=
    Equiv.subtypeEquivRight (fun v => by simp [dotMap, funext_iff])
  rw [Fintype.card_congr he, pow_one] at hc
  simpa [Fintype.card_subtype, Finset.sum_boole, Nat.cast_ite] using hc

/-- The row sum of the incidence matrix is its degree, with the zero partner removed exactly when the prescribed secret is zero. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For l ∈ U(F, n); s ∈ F, we have

∑_(r ∈ U(F, n)) (incidence(s, l, r)) = incidenceDegree(F, n, s).
-/
theorem incidence_row_sum (l : U F n) (s : F) :
    ∑ r : U F n, incidence s l r = incidenceDegree F n s := by
  rw [incidenceDegree]
  have h := sum_U_eq (fun r : V F n => if dot l.val r = s then (1 : ℝ) else 0)
  rw [full_incidence_row_sum] at h
  by_cases hs : s = 0 <;> simpa [incidence, dot, hs, eq_comm] using h

/-- Two independent rows and arbitrary prescribed pairing values have `(vectorCard F n) / (fieldCard F)²` simultaneous solutions in the full vector space. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For l, k ∈ U(F, n); s, t ∈ F, assume LinearIndependent(F, (l, k)). Then

(∑_(r ∈ V(F, n)) ({ 1 if (l · r) = s ∧ (k · r) = t,; 0 otherwise })) = |F|ⁿ / (|F|)².
-/
theorem full_incidence_pair_sum (l k : U F n) (s t : F)
    (hi : LinearIndependent F ![l.val, k.val]) :
    (∑ r : V F n, if dot l.val r = s ∧ dot k.val r = t then (1 : ℝ) else 0) =
      (vectorCard F n : ℝ) / (fieldCard F : ℝ) ^ 2 := by
  have hc := dotMap_fiber_card_real ![l.val, k.val] hi ![s, t]
  have he : {v : V F n // dotMap ![l.val, k.val] v = ![s, t]} ≃
      {v : V F n // dot l.val v = s ∧ dot k.val v = t} :=
    Equiv.subtypeEquivRight (fun v => by simp [dotMap, funext_iff, Fin.forall_fin_two])
  rw [Fintype.card_congr he] at hc
  simpa [Fintype.card_subtype, Finset.sum_boole, Nat.cast_ite] using hc

/-- For nonproportional rows, the common-neighbor count is `(vectorCard F n) / (fieldCard F)²`, reduced by one when both prescribed pairings are zero. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For l, k ∈ U(F, n); s ∈ F, assume ¬ (projectiveRel(l, k)). Then

∑_(r ∈ U(F, n)) (incidence(s, l, r) · incidence(s, k, r)) = |F|ⁿ / (|F|)² - { 1 if s = 0,; 0 otherwise }.
-/
theorem incidence_pair_sum_of_not_projectiveRel (l k : U F n) (s : F)
    (h : ¬ projectiveRel l k) :
    ∑ r : U F n, incidence s l r * incidence s k r =
      (vectorCard F n : ℝ) / (fieldCard F : ℝ) ^ 2 - if s = 0 then 1 else 0 := by
  have hi := pair_independent_of_not_projectiveRel l k h
  have hz := sum_U_eq (fun r : V F n =>
    if dot l.val r = s ∧ dot k.val r = s then (1 : ℝ) else 0)
  rw [full_incidence_pair_sum l k s s hi] at hz
  have he (r : U F n) : incidence s l r * incidence s k r =
      if dot l.val r.val = s ∧ dot k.val r.val = s then (1 : ℝ) else 0 := by
    by_cases hl : dot l.val r.val = s <;> by_cases hk : dot k.val r.val = s <;>
      simp [incidence, hl, hk]
  simp_rw [he]
  simpa [dot, eq_comm] using hz

/-- The squared incidence row has the same sum as the row itself, because its entries are indicators. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For l ∈ U(F, n); s ∈ F, we have

∑_(r ∈ U(F, n)) (incidence(s, l, r) · incidence(s, l, r)) = incidenceDegree(F, n, s).
-/
theorem incidence_pair_sum_self (l : U F n) (s : F) :
    ∑ r : U F n, incidence s l r * incidence s l r = incidenceDegree F n s := by
  have he (r : U F n) : incidence s l r * incidence s l r = incidence s l r := by
    unfold incidence
    split <;> norm_num
  simp_rw [he]
  exact incidence_row_sum l s

/-- Proportional nonzero rows have identical zero-pairing neighbors, so their common-neighbor count is the zero-secret degree. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For l, k ∈ U(F, n), assume projectiveRel(l, k). Then

∑_(r ∈ U(F, n)) (incidence(0, l, r) · incidence(0, k, r)) = incidenceDegree(F, n, 0).
-/
theorem incidence_zero_pair_sum_of_projectiveRel (l k : U F n)
    (h : projectiveRel l k) :
    ∑ r : U F n, incidence 0 l r * incidence 0 k r = incidenceDegree F n 0 := by
  rcases h with ⟨c, hc⟩
  rw [← incidence_row_sum l 0]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hl : dot l.val r.val = 0
  · have hk : dot k.val r.val = 0 := by
      rw [hc]
      simpa [dot, smul_dotProduct, smul_eq_mul] using congrArg (fun z : F => c * z) hl
    simp [incidence, hl, hk]
  · simp [incidence, hl]

/-- Distinct proportional rows cannot both pair to the same nonzero secret with one column, so their common-neighbor count is zero. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For l, k ∈ U(F, n); s ∈ F, assume s ≠ 0; projectiveRel(l, k); l ≠ k. Then

∑_(r ∈ U(F, n)) (incidence(s, l, r) · incidence(s, k, r)) = 0.
-/
theorem incidence_nonzero_pair_sum_of_projectiveRel (l k : U F n) (s : F) (hs : s ≠ 0)
    (h : projectiveRel l k) (hne : l ≠ k) :
    ∑ r : U F n, incidence s l r * incidence s k r = 0 := by
  rcases h with ⟨c, hc⟩
  apply Finset.sum_eq_zero
  intro r _
  by_cases hl : dot l.val r.val = s
  · by_cases hk : dot k.val r.val = s
    · have hcs : c * s = s := by
        have he : dot k.val r.val = c * dot l.val r.val := by
          simp [hc, dot, smul_dotProduct, smul_eq_mul]
        rw [hl, hk] at he
        exact he.symm
      have hc1 : c = 1 := mul_right_cancel₀ hs (by simpa using hcs)
      exact (hne (Subtype.ext (by simpa [hc1] using hc.symm))).elim
    · simp [incidence, hk]
  · simp [incidence, hl]

/-- The real-valued indicator that two nonzero vectors belong to the same projective class. -/
/-
Mathematical definition (normal notation): For l, k ∈ U(F, n), define

projectiveIndicator(l, k) := { 1 if projectiveRel(l, k),; 0 otherwise }.
-/
noncomputable def projectiveIndicator (l k : U F n) : ℝ := if projectiveRel l k then 1 else 0

/-- Every entry of the projective-class indicator table is nonnegative. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For l, k ∈ U(F, n), we have

0 ≤ projectiveIndicator(l, k).
-/
theorem projectiveIndicator_nonneg (l k : U F n) : 0 ≤ projectiveIndicator l k := by
  unfold projectiveIndicator
  split <;> norm_num

/-- The projective-class table is symmetric in its two arguments. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For l, k ∈ U(F, n), we have

projectiveIndicator(l, k) = projectiveIndicator(k, l).
-/
theorem projectiveIndicator_symm (l k : U F n) : projectiveIndicator l k = projectiveIndicator k l := by
  unfold projectiveIndicator
  rw [projectiveRel_symm]

/-- Each row of the projective-class table has mass `(fieldCard F) - 1`, the number of vectors in that class. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For l ∈ U(F, n), we have

∑_(k ∈ U(F, n)) (projectiveIndicator(l, k)) = |F| - 1.
-/
theorem projectiveIndicator_row_sum (l : U F n) :
    ∑ k : U F n, projectiveIndicator l k = (fieldCard F : ℝ) - 1 := by
  have hcard := projectiveRel_card l
  have hq : 1 ≤ fieldCard F := Fintype.card_pos
  have hc : (Fintype.card {k : U F n // projectiveRel l k} : ℝ) = (fieldCard F : ℝ) - 1 := by
    rw [hcard, Nat.cast_sub hq]
    norm_num
  simpa [projectiveIndicator, Fintype.card_subtype, Finset.sum_boole] using hc

/-- The zero-secret incidence Gram matrix is a constant matrix plus a specified multiple of the projective-class table. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For l, k ∈ U(F, n), we have

∑_(r ∈ U(F, n)) (incidence(0, l, r) · incidence(0, k, r)) = |F|ⁿ / (|F|)² - 1 + (|F|ⁿ · (|F| - 1) / (|F|)²) · projectiveIndicator(l, k).
-/
theorem incidence_zero_gram (l k : U F n) :
    ∑ r : U F n, incidence 0 l r * incidence 0 k r =
      (vectorCard F n : ℝ) / (fieldCard F : ℝ) ^ 2 - 1 +
        ((vectorCard F n : ℝ) * ((fieldCard F : ℝ) - 1) / (fieldCard F : ℝ) ^ 2) * projectiveIndicator l k := by
  have hq : (fieldCard F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := F)
  by_cases h : projectiveRel l k
  · rw [incidence_zero_pair_sum_of_projectiveRel l k h]
    simp only [incidenceDegree, projectiveIndicator, if_pos h, mul_one]
    simp
    field_simp
    ring
  · rw [incidence_pair_sum_of_not_projectiveRel l k 0 h]
    simp [projectiveIndicator, h]

/-- For a nonzero secret, the incidence Gram matrix separates equal rows, distinct proportional rows, and nonproportional rows. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For l, k ∈ U(F, n); s ∈ F, assume s ≠ 0. Then

∑_(r ∈ U(F, n)) (incidence(s, l, r) · incidence(s, k, r)) = (|F|ⁿ / |F|) · ({ 1 if l = k,; 0 otherwise }) + (|F|ⁿ / (|F|)²) · (1 - projectiveIndicator(l, k)).
-/
theorem incidence_nonzero_gram (l k : U F n) (s : F) (hs : s ≠ 0) :
    ∑ r : U F n, incidence s l r * incidence s k r =
      ((vectorCard F n : ℝ) / (fieldCard F : ℝ)) * (if l = k then 1 else 0) +
        ((vectorCard F n : ℝ) / (fieldCard F : ℝ) ^ 2) * (1 - projectiveIndicator l k) := by
  by_cases he : l = k
  · subst k
    rw [incidence_pair_sum_self]
    simp [incidenceDegree, hs, projectiveIndicator, projectiveRel_self]
  · by_cases h : projectiveRel l k
    · rw [incidence_nonzero_pair_sum_of_projectiveRel l k s hs h he]
      simp [projectiveIndicator, h, he]
    · rw [incidence_pair_sum_of_not_projectiveRel l k s h]
      simp [projectiveIndicator, h, he, hs]

/-- Subtract the uniform row average from scalar-product incidence, producing a centered incidence matrix. -/
/-
Mathematical definition (normal notation): For s ∈ F; l, r ∈ U(F, n), define

centeredIncidence(s, l, r) := incidence(s, l, r) - incidenceDegree(F, n, s) / (|F|ⁿ - 1).
-/
noncomputable def centeredIncidence (s : F) (l r : U F n) : ℝ :=
  incidence s l r - incidenceDegree F n s / ((vectorCard F n : ℝ) - 1)

/-- Centering incidence subtracts the squared degree divided by the nonzero-vector count from every Gram-matrix entry. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F; l, k ∈ U(F, n), we have

∑_(r ∈ U(F, n)) (centeredIncidence(s, r, l) · centeredIncidence(s, r, k)) = (∑_(r ∈ U(F, n)) (incidence(s, l, r) · incidence(s, k, r))) - (incidenceDegree(F, n, s))² / (|F|ⁿ - 1).
-/
theorem centeredIncidence_gram (s : F) (l k : U F n) :
    ∑ r : U F n, centeredIncidence s r l * centeredIncidence s r k =
      (∑ r : U F n, incidence s l r * incidence s k r) -
        incidenceDegree F n s ^ 2 / ((vectorCard F n : ℝ) - 1) := by
  letI : Nonempty (U F n) := ⟨l⟩
  have hd : (vectorCard F n : ℝ) - 1 ≠ 0 := by
    rw [← card_U_real]
    exact_mod_cast Fintype.card_ne_zero (α := U F n)
  have he (r : U F n) : centeredIncidence s r l * centeredIncidence s r k =
      incidence s l r * incidence s k r -
        (incidenceDegree F n s / ((vectorCard F n : ℝ) - 1)) * incidence s l r -
        (incidenceDegree F n s / ((vectorCard F n : ℝ) - 1)) * incidence s k r +
        (incidenceDegree F n s / ((vectorCard F n : ℝ) - 1)) ^ 2 := by
    unfold centeredIncidence
    rw [incidence_symm s r l, incidence_symm s r k]
    ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    incidence_row_sum]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, card_U_real]
  field_simp
  ring

/-- The centered zero-secret Gram matrix is a projective-class term minus a constant term. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For l, k ∈ U(F, n), we have

∑_(r ∈ U(F, n)) (centeredIncidence(0, r, l) · centeredIncidence(0, r, k)) = (|F|ⁿ · (|F| - 1) / (|F|)²) · projectiveIndicator(l, k) - (|F|ⁿ · (|F| - 1)² / ((|F|)² · (|F|ⁿ - 1))).
-/
theorem centeredIncidence_zero_gram (l k : U F n) :
    ∑ r : U F n, centeredIncidence 0 r l * centeredIncidence 0 r k =
      ((vectorCard F n : ℝ) * ((fieldCard F : ℝ) - 1) / (fieldCard F : ℝ) ^ 2) * projectiveIndicator l k -
        ((vectorCard F n : ℝ) * ((fieldCard F : ℝ) - 1) ^ 2 / ((fieldCard F : ℝ) ^ 2 * ((vectorCard F n : ℝ) - 1))) := by
  letI : Nonempty (U F n) := ⟨l⟩
  have hq : (fieldCard F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := F)
  have hd : (vectorCard F n : ℝ) - 1 ≠ 0 := by
    rw [← card_U_real]
    exact_mod_cast Fintype.card_ne_zero (α := U F n)
  rw [centeredIncidence_gram, incidence_zero_gram]
  simp [incidenceDegree]
  field_simp
  ring

/-- The centered nonzero-secret Gram matrix is a diagonal term minus a projective-class term and a constant term. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For l, k ∈ U(F, n); s ∈ F, assume s ≠ 0. Then

∑_(r ∈ U(F, n)) (centeredIncidence(s, r, l) · centeredIncidence(s, r, k)) = ({ |F|ⁿ / |F| if l = k,; 0 otherwise }) + (-(|F|ⁿ) / (|F|)²) · projectiveIndicator(l, k) - (|F|ⁿ / ((|F|)² · (|F|ⁿ - 1))).
-/
theorem centeredIncidence_nonzero_gram (l k : U F n) (s : F) (hs : s ≠ 0) :
    ∑ r : U F n, centeredIncidence s r l * centeredIncidence s r k =
      (if l = k then (vectorCard F n : ℝ) / (fieldCard F : ℝ) else 0) +
        (-(vectorCard F n : ℝ) / (fieldCard F : ℝ) ^ 2) * projectiveIndicator l k -
        ((vectorCard F n : ℝ) / ((fieldCard F : ℝ) ^ 2 * ((vectorCard F n : ℝ) - 1))) := by
  letI : Nonempty (U F n) := ⟨l⟩
  have hq : (fieldCard F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := F)
  have hd : (vectorCard F n : ℝ) - 1 ≠ 0 := by
    rw [← card_U_real]
    exact_mod_cast Fintype.card_ne_zero (α := U F n)
  rw [centeredIncidence_gram, incidence_nonzero_gram l k s hs]
  simp only [incidenceDegree, if_neg hs, sub_zero]
  by_cases he : l = k <;> simp only [he, if_true, if_false] <;> field_simp <;> ring

/-- In dimension at least two, the squared Euclidean norm of the centered zero-secret incidence action is at most `(vectorCard F n) * ((fieldCard F) - 1)² / (fieldCard F)²` times the input squared norm. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For b ∈ U(F, n) → ℝ, assume 2 ≤ n. Then

∑ₗ ((∑ᵣ (centeredIncidence(0, l, r) · b(r)))²) ≤ (|F|ⁿ · (|F| - 1)² / (|F|)²) · ∑ᵣ ((b(r))²).
-/
theorem centeredIncidence_zero_quadratic (hn : 2 ≤ n) (b : U F n → ℝ) :
    ∑ l, (∑ r, centeredIncidence 0 l r * b r) ^ 2 ≤
      ((vectorCard F n : ℝ) * ((fieldCard F : ℝ) - 1) ^ 2 / (fieldCard F : ℝ) ^ 2) * ∑ r, b r ^ 2 := by
  have hq := fieldCard_cast_ge_two (F := F)
  have hN := vectorCard_real_ge_fieldCard_sq (F := F) hn
  have hD : 0 < (vectorCard F n : ℝ) - 1 := by nlinarith
  have hqm : 0 ≤ (fieldCard F : ℝ) - 1 := by linarith
  have hC : 0 ≤ (vectorCard F n : ℝ) * ((fieldCard F : ℝ) - 1) / (fieldCard F : ℝ) ^ 2 := by positivity
  have hE : 0 ≤ (vectorCard F n : ℝ) * ((fieldCard F : ℝ) - 1) ^ 2 /
      ((fieldCard F : ℝ) ^ 2 * ((vectorCard F n : ℝ) - 1)) := by positivity
  have hP := (abs_le.mp (regular_table_quadratic_abs_le projectiveIndicator
    ((fieldCard F : ℝ) - 1) projectiveIndicator_nonneg projectiveIndicator_symm projectiveIndicator_row_sum b)).2
  rw [gram_quadratic_identity]
  simp_rw [centeredIncidence_zero_gram]
  have he := quadratic_gram_formula projectiveIndicator b 0
    ((vectorCard F n : ℝ) * ((fieldCard F : ℝ) - 1) / (fieldCard F : ℝ) ^ 2)
    ((vectorCard F n : ℝ) * ((fieldCard F : ℝ) - 1) ^ 2 / ((fieldCard F : ℝ) ^ 2 * ((vectorCard F n : ℝ) - 1)))
  simp only [ite_self, zero_add, zero_mul] at he
  rw [he]
  have hp := mul_le_mul_of_nonneg_left hP hC
  have hnz := mul_nonneg hE (sq_nonneg (∑ r, b r))
  calc
    _ ≤ ((vectorCard F n : ℝ) * ((fieldCard F : ℝ) - 1) / (fieldCard F : ℝ) ^ 2) *
        (((fieldCard F : ℝ) - 1) * ∑ r, b r ^ 2) := by linarith
    _ = _ := by ring

/-- In dimension at least two, the centered incidence action for a nonzero secret has squared norm at most `(vectorCard F n)` times the input squared norm. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F; b ∈ U(F, n) → ℝ, assume 2 ≤ n; s ≠ 0. Then

∑ₗ ((∑ᵣ (centeredIncidence(s, l, r) · b(r)))²) ≤ |F|ⁿ · ∑ᵣ ((b(r))²).
-/
theorem centeredIncidence_nonzero_quadratic (hn : 2 ≤ n) (s : F) (hs : s ≠ 0)
    (b : U F n → ℝ) :
    ∑ l, (∑ r, centeredIncidence s l r * b r) ^ 2 ≤ (vectorCard F n : ℝ) * ∑ r, b r ^ 2 := by
  have hq := fieldCard_cast_ge_two (F := F)
  have hN := vectorCard_real_ge_fieldCard_sq (F := F) hn
  have hD : 0 < (vectorCard F n : ℝ) - 1 := by nlinarith
  have hq0 : 0 < (fieldCard F : ℝ) := by linarith
  have hE : 0 ≤ (vectorCard F n : ℝ) / ((fieldCard F : ℝ) ^ 2 * ((vectorCard F n : ℝ) - 1)) := by positivity
  have hC : 0 ≤ (vectorCard F n : ℝ) / (fieldCard F : ℝ) ^ 2 := by positivity
  have hP := (abs_le.mp (regular_table_quadratic_abs_le projectiveIndicator
    ((fieldCard F : ℝ) - 1) projectiveIndicator_nonneg projectiveIndicator_symm projectiveIndicator_row_sum b)).1
  rw [gram_quadratic_identity]
  simp_rw [centeredIncidence_nonzero_gram _ _ s hs]
  rw [quadratic_gram_formula]
  have hp := mul_le_mul_of_nonneg_left hP hC
  have hnz := mul_nonneg hE (sq_nonneg (∑ r, b r))
  have hcoef : (vectorCard F n : ℝ) / (fieldCard F : ℝ) +
      (vectorCard F n : ℝ) / (fieldCard F : ℝ) ^ 2 * ((fieldCard F : ℝ) - 1) ≤ (vectorCard F n : ℝ) := by
    have he : ((vectorCard F n : ℝ) / (fieldCard F : ℝ) +
        (vectorCard F n : ℝ) / (fieldCard F : ℝ) ^ 2 * ((fieldCard F : ℝ) - 1)) =
        ((vectorCard F n : ℝ) * (2 * (fieldCard F : ℝ) - 1)) / (fieldCard F : ℝ) ^ 2 := by field_simp; ring
    rw [he]
    apply (div_le_iff₀ (pow_pos hq0 2)).mpr
    have hmul := mul_nonneg (show 0 ≤ (vectorCard F n : ℝ) by positivity) (sq_nonneg ((fieldCard F : ℝ) - 1))
    nlinarith
  have hsum : 0 ≤ ∑ r, b r ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hbound := mul_le_mul_of_nonneg_right hcoef hsum
  simp only [neg_div] at *
  nlinarith

/-- The centered-incidence operator bound proved below in dimension at least two: `((fieldCard F) - 1)√(vectorCard F n) / (fieldCard F)` for secret zero and `√(vectorCard F n)` otherwise. -/
/-
Mathematical definition (normal notation): For F a set; n ∈ ℕ; s ∈ F, assume F is a field; F is finite. define

incidenceSpectralRadius(n, s) := { ((|F| - 1) / |F|) · √(|F|ⁿ) if s = 0,; √(|F|ⁿ) otherwise }.
-/
noncomputable def incidenceSpectralRadius (F : Type*) [Field F] [Fintype F]
    (n : ℕ) (s : F) : ℝ :=
  if s = 0 then (((fieldCard F : ℝ) - 1) / (fieldCard F : ℝ)) * Real.sqrt (vectorCard F n : ℝ)
  else Real.sqrt (vectorCard F n : ℝ)

/-- The chosen centered-incidence operator bound is nonnegative for every secret. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F, we have

0 ≤ incidenceSpectralRadius(F, n, s).
-/
theorem incidenceSpectralRadius_nonneg (s : F) :
    0 ≤ incidenceSpectralRadius F n s := by
  have hq := fieldCard_cast_ge_two (F := F)
  have hqm : 0 ≤ (fieldCard F : ℝ) - 1 := by linarith
  unfold incidenceSpectralRadius
  split <;> positivity

/-- The centered incidence matrix satisfies the squared norm bound given by `incidenceSpectralRadius` in dimension at least two. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F; b ∈ U(F, n) → ℝ, assume 2 ≤ n. Then

∑ₗ ((∑ᵣ (centeredIncidence(s, l, r) · b(r)))²) ≤ (incidenceSpectralRadius(F, n, s))² · ∑ᵣ ((b(r))²).
-/
theorem centeredIncidence_quadratic (hn : 2 ≤ n) (s : F) (b : U F n → ℝ) :
    ∑ l, (∑ r, centeredIncidence s l r * b r) ^ 2 ≤
      incidenceSpectralRadius F n s ^ 2 * ∑ r, b r ^ 2 := by
  by_cases hs : s = 0
  · subst s
    have he : incidenceSpectralRadius F n (0 : F) ^ 2 =
        (vectorCard F n : ℝ) * ((fieldCard F : ℝ) - 1) ^ 2 / (fieldCard F : ℝ) ^ 2 := by
      simp [incidenceSpectralRadius, mul_pow, div_pow,
        Real.sq_sqrt (Nat.cast_nonneg _)]
      ring
    rw [he]
    exact centeredIncidence_zero_quadratic hn b
  · simpa only [incidenceSpectralRadius, if_neg hs, Real.sq_sqrt (Nat.cast_nonneg _)] using
      centeredIncidence_nonzero_quadratic hn s hs b

/-- Every incidence row has positive degree for every secret when the dimension is at least two. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F, assume 2 ≤ n. Then

0 < incidenceDegree(F, n, s).
-/
theorem incidenceDegree_pos (hn : 2 ≤ n) (s : F) : 0 < incidenceDegree F n s := by
  have hq := fieldCard_cast_ge_two (F := F)
  have hN := vectorCard_real_ge_fieldCard_sq (F := F) hn
  have hq0 : 0 < (fieldCard F : ℝ) := by linarith
  have hNq : (fieldCard F : ℝ) < (vectorCard F n : ℝ) := by nlinarith
  have hone : 1 < (vectorCard F n : ℝ) / (fieldCard F : ℝ) :=
    (lt_div_iff₀ hq0).mpr (by linarith)
  unfold incidenceDegree
  split <;> linarith

/-- In dimension at least two, the centered-incidence operator bound divided by the degree is at most `(fieldCard F) / √(vectorCard F n)`. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F, assume 2 ≤ n. Then

incidenceSpectralRadius(F, n, s) / incidenceDegree(F, n, s) ≤ |F| / √(|F|ⁿ).
-/
theorem incidence_radius_div_degree_le (hn : 2 ≤ n) (s : F) :
    incidenceSpectralRadius F n s / incidenceDegree F n s ≤
      (fieldCard F : ℝ) / Real.sqrt (vectorCard F n : ℝ) := by
  have hq := fieldCard_cast_ge_two (F := F)
  have hN := vectorCard_real_ge_fieldCard_sq (F := F) hn
  have hq0 : 0 < (fieldCard F : ℝ) := by linarith
  have hqne : (fieldCard F : ℝ) ≠ 0 := ne_of_gt hq0
  have hN0 : 0 < (vectorCard F n : ℝ) := by nlinarith
  have hNne := ne_of_gt hN0
  have hNq : 0 < (vectorCard F n : ℝ) - (fieldCard F : ℝ) := by nlinarith
  have hNqne := ne_of_gt hNq
  have hS : 0 < Real.sqrt (vectorCard F n : ℝ) := Real.sqrt_pos.mpr hN0
  have hSne := ne_of_gt hS
  have hsq := Real.mul_self_sqrt hN0.le
  by_cases hs : s = 0
  · subst s
    have he : incidenceSpectralRadius F n (0 : F) / incidenceDegree F n 0 =
        (((fieldCard F : ℝ) - 1) * Real.sqrt (vectorCard F n : ℝ)) / ((vectorCard F n : ℝ) - (fieldCard F : ℝ)) := by
      simp [incidenceSpectralRadius, incidenceDegree]
      field_simp
    rw [he]
    apply (div_le_div_iff₀ hNq hS).mpr
    nlinarith [mul_assoc ((fieldCard F : ℝ) - 1) (Real.sqrt (vectorCard F n : ℝ)) (Real.sqrt (vectorCard F n : ℝ))]
  · have he : incidenceSpectralRadius F n s / incidenceDegree F n s =
        (fieldCard F : ℝ) / Real.sqrt (vectorCard F n : ℝ) := by
      simp only [incidenceSpectralRadius, incidenceDegree, if_neg hs, sub_zero]
      field_simp
      nlinarith
    exact he.le

/-- The normalized average of `a(l)b(r)` over nonzero share pairs with prescribed inner product; in dimension at least two this is the uniform encoding expectation. -/
/-
Mathematical definition (normal notation): For s ∈ F; a, b ∈ U(F, n) → ℝ, define

incidenceMean(s, a, b) := (1 / ((|F|ⁿ - 1) · incidenceDegree(F, n, s))) · ∑ₗ (∑ᵣ (incidence(s, l, r) · a(l) · b(r))).
-/
noncomputable def incidenceMean (s : F) (a b : U F n → ℝ) : ℝ :=
  (1 / (((vectorCard F n : ℝ) - 1) * incidenceDegree F n s)) *
    ∑ l, ∑ r, incidence s l r * a l * b r

/-- The normalized product sum of `a(l)b(r)` over nonzero shares; when that carrier is nonempty, it is the expectation under independent uniform shares. -/
/-
Mathematical definition (normal notation): For a, b ∈ U(F, n) → ℝ, define

incidenceIndependentMean(a, b) := (1 / (|F|ⁿ - 1)²) · ∑ₗ (∑ᵣ (a(l) · b(r))).
-/
noncomputable def incidenceIndependentMean (a b : U F n → ℝ) : ℝ :=
  (1 / ((vectorCard F n : ℝ) - 1) ^ 2) * ∑ l, ∑ r, a l * b r

/-- The square root of the normalized square sum over nonzero vectors, equal to the uniform root mean square when this carrier is nonempty. -/
/-
Mathematical definition (normal notation): For a ∈ U(F, n) → ℝ, define

incidenceRms(a) := √((1 / (|F|ⁿ - 1)) · ∑ₗ ((a(l))²)).
-/
noncomputable def incidenceRms (a : U F n → ℝ) : ℝ :=
  Real.sqrt ((1 / ((vectorCard F n : ℝ) - 1)) * ∑ l, a l ^ 2)

/-- The difference between the constrained-pairing average and the independent average is the appropriately normalized centered-incidence bilinear form. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F; a, b ∈ U(F, n) → ℝ, assume 2 ≤ n. Then

incidenceMean(s, a, b) - incidenceIndependentMean(a, b) = (1 / ((|F|ⁿ - 1) · incidenceDegree(F, n, s))) · ∑ₗ (∑ᵣ (centeredIncidence(s, l, r) · a(l) · b(r))).
-/
theorem incidenceMean_sub_independent (hn : 2 ≤ n) (s : F) (a b : U F n → ℝ) :
    incidenceMean s a b - incidenceIndependentMean a b =
      (1 / (((vectorCard F n : ℝ) - 1) * incidenceDegree F n s)) *
        ∑ l, ∑ r, centeredIncidence s l r * a l * b r := by
  have hq := fieldCard_cast_ge_two (F := F)
  have hN := vectorCard_real_ge_fieldCard_sq (F := F) hn
  have hd : (vectorCard F n : ℝ) - 1 ≠ 0 := by nlinarith
  have hm := ne_of_gt (incidenceDegree_pos hn s)
  unfold incidenceMean incidenceIndependentMean
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro r _
  unfold centeredIncidence
  field_simp

/-- In dimension at least two, a prescribed pairing changes a product expectation from the independent-share value by at most `(fieldCard F) / √(vectorCard F n)` times the two uniform root mean squares. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F; a, b ∈ U(F, n) → ℝ, assume 2 ≤ n. Then

|incidenceMean(s, a, b) - incidenceIndependentMean(a, b)| ≤ (|F| / √(|F|ⁿ)) · incidenceRms(a) · incidenceRms(b).
-/
theorem incidenceMean_centered_bound (hn : 2 ≤ n) (s : F) (a b : U F n → ℝ) :
    |incidenceMean s a b - incidenceIndependentMean a b| ≤
      ((fieldCard F : ℝ) / Real.sqrt (vectorCard F n : ℝ)) * incidenceRms a * incidenceRms b := by
  have hq := fieldCard_cast_ge_two (F := F)
  have hN := vectorCard_real_ge_fieldCard_sq (F := F) hn
  have hd : 0 < (vectorCard F n : ℝ) - 1 := by nlinarith
  have hm := incidenceDegree_pos hn s
  have hr := bilinear_bound_of_quadratic (centeredIncidence s) (incidenceSpectralRadius F n s)
    (incidenceSpectralRadius_nonneg s) (centeredIncidence_quadratic hn s) a b
  rw [incidenceMean_sub_independent hn s a b, abs_mul, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (1 / (((vectorCard F n : ℝ) - 1) * incidenceDegree F n s)) *
        (incidenceSpectralRadius F n s * Real.sqrt (∑ l, a l ^ 2) * Real.sqrt (∑ r, b r ^ 2)) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = (incidenceSpectralRadius F n s / incidenceDegree F n s) * incidenceRms a * incidenceRms b := by
      rw [mul_assoc (incidenceSpectralRadius F n s / incidenceDegree F n s),
        incidenceRms, incidenceRms, sqrt_product_normalization _ _ _ hd]
      field_simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_right (incidence_radius_div_degree_le hn s) (Real.sqrt_nonneg _)

/-- Scalar-product discrepancy for any two field values and arbitrary signed factors. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s, t ∈ F; a, b ∈ U(F, n) → ℝ, assume 2 ≤ n. Then

|incidenceMean(s, a, b) - incidenceMean(t, a, b)| ≤ (2 · |F| / √(|F|ⁿ)) · incidenceRms(a) · incidenceRms(b).
-/
theorem discrepancy_bound (hn : 2 ≤ n) (s t : F) (a b : U F n → ℝ) :
    |incidenceMean s a b - incidenceMean t a b| ≤
      (2 * (fieldCard F : ℝ) / Real.sqrt (vectorCard F n : ℝ)) * incidenceRms a * incidenceRms b := by
  have hs := incidenceMean_centered_bound hn s a b
  have ht := incidenceMean_centered_bound hn t a b
  have htri := abs_sub_le (incidenceMean s a b) (incidenceIndependentMean a b) (incidenceMean t a b)
  rw [abs_sub_comm (incidenceIndependentMean a b)] at htri
  calc
    _ ≤ _ := htri
    _ ≤ ((fieldCard F : ℝ) / Real.sqrt (vectorCard F n : ℝ)) * incidenceRms a * incidenceRms b +
        ((fieldCard F : ℝ) / Real.sqrt (vectorCard F n : ℝ)) * incidenceRms a * incidenceRms b := add_le_add hs ht
    _ = _ := by ring

end FiniteField

end Refresh
