import Proofs.Compiler.GateApproximation.MatrixPhase.JointTwisted



/-!
# Complex mixed four-cycle estimates

The four character-twisted factors in the joint-port moment need not be equal. This file proves the operator/Hilbert--Schmidt bound for their exact expanded cycle, and the fourth-power operator bound supplied by an ordinary cycle.
-/

set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I), we have

complexMatrixL2Sq(Aᴴ) = complexMatrixL2Sq(A).
-/
lemma complexMatrixL2Sq_conjTranspose (A : Matrix I I ℂ) :
    complexMatrixL2Sq Aᴴ = complexMatrixL2Sq A := by
  simp only [complexMatrixL2Sq, Matrix.conjTranspose_apply, norm_star]
  rw [Finset.sum_comm]

/-- Multiplication by a bounded operator contracts every column energy. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B ∈ ℂ^(I × I), we have

complexMatrixL2Sq((A · B)) ≤ (‖ A‖)² · complexMatrixL2Sq(B).
-/
theorem complexMatrixL2Sq_mul_le (A B : Matrix I I ℂ) :
    complexMatrixL2Sq (A * B) ≤ ‖A‖ ^ 2 * complexMatrixL2Sq B := by
  rw [complexMatrixL2Sq_eq_basis, complexMatrixL2Sq_eq_basis, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have h := A.l2_opNorm_mulVec (B.toEuclideanLin (EuclideanSpace.basisFun I ℂ j))
  change ‖A.toEuclideanLin (B.toEuclideanLin (EuclideanSpace.basisFun I ℂ j))‖ ≤
    ‖A‖ * ‖B.toEuclideanLin (EuclideanSpace.basisFun I ℂ j)‖ at h
  have hp := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [Matrix.toLpLin_mul_same, LinearMap.comp_apply, mul_pow] using hp

/-- The corresponding Hilbert--Schmidt bound for right multiplication. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B ∈ ℂ^(I × I), we have

complexMatrixL2Sq((A · B)) ≤ complexMatrixL2Sq(A) · (‖ B‖)².
-/
theorem complexMatrixL2Sq_mul_le_right (A B : Matrix I I ℂ) :
    complexMatrixL2Sq (A * B) ≤ complexMatrixL2Sq A * ‖B‖ ^ 2 := by
  have h := complexMatrixL2Sq_mul_le Bᴴ Aᴴ
  rw [← Matrix.conjTranspose_mul, complexMatrixL2Sq_conjTranspose,
    complexMatrixL2Sq_conjTranspose, Matrix.l2_opNorm_conjTranspose] at h
  simpa only [mul_comm] using h

/-- Entries regarded as a single Euclidean vector. -/
/-
Mathematical definition (normal notation): For A ∈ ℂ^(I × I), define

complexMatrixEntries(A) := WithLp.toLp(2, ((p ↦ A((p)₁, (p)₂)))).
-/
def complexMatrixEntries (A : Matrix I I ℂ) : EuclideanSpace ℂ (I × I) :=
  WithLp.toLp 2 (fun p => A p.1 p.2)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I), we have

(‖ complexMatrixEntries(A)‖)² = complexMatrixL2Sq(A).
-/
lemma complexMatrixEntries_norm_sq (A : Matrix I I ℂ) :
    ‖complexMatrixEntries A‖ ^ 2 = complexMatrixL2Sq A := by
  simp only [complexMatrixEntries, PiLp.norm_sq_eq_of_L2, PiLp.toLp_apply,
    Fintype.sum_prod_type, complexMatrixL2Sq]
  rw [Finset.sum_comm]

/-- Counting-measure pairing with conjugation in the second table. -/
/-
Mathematical definition (normal notation): For A, B ∈ ℂ^(I × I), define

complexMatrixPair(A, B) := ∑ᵢ (∑ⱼ (A(i, j) · star(B(i, j)))).
-/
def complexMatrixPair (A B : Matrix I I ℂ) : ℂ := ∑ i, ∑ j, A i j * star (B i j)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B ∈ ℂ^(I × I), we have

complexMatrixPair(A, B) = inner(ℂ, complexMatrixEntries(B), complexMatrixEntries(A)).
-/
lemma complexMatrixPair_eq_inner (A B : Matrix I I ℂ) :
    complexMatrixPair A B = inner ℂ (complexMatrixEntries B) (complexMatrixEntries A) := by
  simp [complexMatrixPair, complexMatrixEntries, PiLp.inner_apply, RCLike.inner_apply,
    Fintype.sum_prod_type, mul_comm]

/-- Hilbert--Schmidt Cauchy--Schwarz, retaining all complex phases. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B ∈ ℂ^(I × I), we have

(‖ complexMatrixPair(A, B)‖)² ≤ complexMatrixL2Sq(A) · complexMatrixL2Sq(B) .
-/
theorem complexMatrixPair_sq_le (A B : Matrix I I ℂ) :
    ‖complexMatrixPair A B‖ ^ 2 ≤ complexMatrixL2Sq A * complexMatrixL2Sq B := by
  rw [complexMatrixPair_eq_inner]
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (norm_inner_le_norm (𝕜 := ℂ) (complexMatrixEntries B) (complexMatrixEntries A)) 2
  simpa only [mul_pow, complexMatrixEntries_norm_sq, mul_comm] using h

/-- Adjoint identity for the counting L2 pairing under matrix multiplication. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B, C ∈ ℂ^(I × I), we have

complexMatrixPair((A · B), C) = complexMatrixPair(B, (Aᴴ · C)).
-/
lemma complexMatrixPair_mul_left (A B C : Matrix I I ℂ) :
    complexMatrixPair (A * B) C = complexMatrixPair B (Aᴴ * C) := by
  unfold complexMatrixPair
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_sum, star_mul,
    star_star, Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I), we have

complexMatrixPair(A, A) = complexMatrixL2Sq(A).
-/
lemma complexMatrixPair_self (A : Matrix I I ℂ) :
    complexMatrixPair A A = (complexMatrixL2Sq A : ℂ) := by
  simp only [complexMatrixPair, complexMatrixL2Sq, Complex.ofReal_sum,
    Complex.ofReal_pow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact (Complex.mul_conj (A i j)).trans (by rw [Complex.normSq_eq_norm_sq, Complex.ofReal_pow])

/-- A mixed four-cycle with the alternating conjugations of the singular fourth-moment expansion. -/
/-
Mathematical definition (normal notation): For A, B, C, D ∈ ℂ^(I × I), define

complexMixedFourCycle(A, B, C, D) := ∑ᵢ (∑ⱼ (∑ₖ (∑ₗ (A(i, j) · star(B(k, j)) · C(k, l) · star(D(i, l)))))).
-/
def complexMixedFourCycle (A B C D : Matrix I I ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, A i j * star (B k j) * C k l * star (D i l)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B, C, D ∈ ℂ^(I × I), we have

complexMixedFourCycle(A, B, C, D) = complexMatrixPair((A · Bᴴ · C), D).
-/
lemma complexMixedFourCycle_eq_pair (A B C D : Matrix I I ℂ) :
    complexMixedFourCycle A B C D = complexMatrixPair (A * Bᴴ * C) D := by
  unfold complexMixedFourCycle complexMatrixPair
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext k
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

/-- An ordinary cycle is exactly the Gram matrix's squared counting L2 norm. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I), we have

complexMixedFourCycle(A, A, A, A) = complexMatrixL2Sq((Aᴴ · A)).
-/
lemma complexMixedFourCycle_self (A : Matrix I I ℂ) :
    complexMixedFourCycle A A A A = (complexMatrixL2Sq (Aᴴ * A) : ℂ) := by
  rw [complexMixedFourCycle_eq_pair, Matrix.mul_assoc, complexMatrixPair_mul_left,
    complexMatrixPair_self]

/-- Two operator bounds and two `L₂` bounds control every mixed cycle. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B, C, D ∈ ℂ^(I × I), we have

(‖ complexMixedFourCycle(A, B, C, D)‖)² ≤ (‖ A‖)² · (‖ C‖)² · complexMatrixL2Sq(B) · complexMatrixL2Sq(D) .
-/
theorem complexMixedFourCycle_sq_le (A B C D : Matrix I I ℂ) :
    ‖complexMixedFourCycle A B C D‖ ^ 2 ≤
      ‖A‖ ^ 2 * ‖C‖ ^ 2 * complexMatrixL2Sq B * complexMatrixL2Sq D := by
  rw [complexMixedFourCycle_eq_pair]
  have h₁ := complexMatrixPair_sq_le (A * Bᴴ * C) D
  have h₂ := complexMatrixL2Sq_mul_le_right (A * Bᴴ) C
  have h₃ := complexMatrixL2Sq_mul_le A Bᴴ
  rw [complexMatrixL2Sq_conjTranspose] at h₃
  have h₄ := mul_le_mul_of_nonneg_right h₃ (sq_nonneg ‖C‖)
  have h₅ := mul_le_mul_of_nonneg_right (h₂.trans h₄) (complexMatrixL2Sq_nonneg D)
  convert h₁.trans h₅ using 1 <;> ring

/-- The exact uniform twist estimate used for each of the `q⁴` character terms. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B, C, D ∈ ℂ^(I × I); β, H ∈ ℝ, assume 0 ≤ β; 0 ≤ H; ‖ A‖ ≤ β; ‖ C‖ ≤ β; complexMatrixL2Sq(B) ≤ H; complexMatrixL2Sq(D) ≤ H. Then

‖ complexMixedFourCycle(A, B, C, D)‖ ≤ β² · H.
-/
theorem complexMixedFourCycle_le (A B C D : Matrix I I ℂ) (β H : ℝ)
    (hβ : 0 ≤ β) (hH : 0 ≤ H) (hA : ‖A‖ ≤ β) (hC : ‖C‖ ≤ β)
    (hB : complexMatrixL2Sq B ≤ H) (hD : complexMatrixL2Sq D ≤ H) :
    ‖complexMixedFourCycle A B C D‖ ≤ β ^ 2 * H := by
  have h := complexMixedFourCycle_sq_le A B C D
  have hAC : ‖A‖ ^ 2 * ‖C‖ ^ 2 ≤ β ^ 2 * β ^ 2 :=
    mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hA 2)
      (pow_le_pow_left₀ (norm_nonneg _) hC 2) (sq_nonneg _) (sq_nonneg _)
  have hBD : complexMatrixL2Sq B * complexMatrixL2Sq D ≤ H * H :=
    mul_le_mul hB hD (complexMatrixL2Sq_nonneg D) hH
  have hprod := mul_le_mul hAC hBD
    (mul_nonneg (complexMatrixL2Sq_nonneg B) (complexMatrixL2Sq_nonneg D))
    (mul_nonneg (sq_nonneg β) (sq_nonneg β))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sq_nonneg _) hH)).1
  nlinarith

/-- Operator norm squared is bounded by squared Hilbert--Schmidt norm. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I), we have

(‖ A‖)² ≤ complexMatrixL2Sq(A).
-/
theorem complexMatrix_norm_sq_le_L2Sq (A : Matrix I I ℂ) :
    ‖A‖ ^ 2 ≤ complexMatrixL2Sq A := by
  have he : complexMatrixL2Sq A = ∑ k, (complexMatrixSVD A).sigma k ^ 2 := by
    rw [complexMatrixL2Sq_eq_basis]
    exact (complexMatrixSVD A).l2_sq (EuclideanSpace.basisFun I ℂ)
  have hnorm : ‖A‖ = ‖(complexMatrixSVD A).sigma‖ := by
    rw [Matrix.l2_opNorm_def]
    exact (complexMatrixSVD A).operator_norm
  have hle : ‖(complexMatrixSVD A).sigma‖ ≤ Real.sqrt (complexMatrixL2Sq A) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro k
    have hk : (complexMatrixSVD A).sigma k ^ 2 ≤ complexMatrixL2Sq A := by
      rw [he]
      exact Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
    have hn := (complexMatrixSVD A).nonneg k
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact (sq_le_sq₀ hn (Real.sqrt_nonneg _)).1 (by
      rw [Real.sq_sqrt (complexMatrixL2Sq_nonneg A)]
      exact hk)
  rw [hnorm]
  exact (pow_le_pow_left₀ (norm_nonneg _) hle 2).trans_eq
    (Real.sq_sqrt (complexMatrixL2Sq_nonneg A))

/-- The Schatten fourth moment bounds the fourth power of the operator norm. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I), we have

(‖ A‖)⁴ ≤ complexMatrixL2Sq((Aᴴ · A)).
-/
theorem complexMatrix_norm_four_le_gram_energy (A : Matrix I I ℂ) :
    ‖A‖ ^ 4 ≤ complexMatrixL2Sq (Aᴴ * A) := by
  have h := complexMatrix_norm_sq_le_L2Sq (Aᴴ * A)
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at h
  nlinarith

/-- The expanded ordinary four-cycle is real and nonnegative. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I), we have

0 ≤ re(complexMixedFourCycle(A, A, A, A)).
-/
theorem complexMixedFourCycle_self_nonneg (A : Matrix I I ℂ) :
    0 ≤ (complexMixedFourCycle A A A A).re := by
  rw [complexMixedFourCycle_self, Complex.ofReal_re]
  exact complexMatrixL2Sq_nonneg _

/-- Fourth powers of operator norms are controlled by actual four-cycles. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I), we have

(‖ A‖)⁴ ≤ re(complexMixedFourCycle(A, A, A, A)).
-/
theorem complexMatrix_norm_four_le_fourCycle (A : Matrix I I ℂ) :
    ‖A‖ ^ 4 ≤ (complexMixedFourCycle A A A A).re := by
  rw [complexMixedFourCycle_self, Complex.ofReal_re]
  exact complexMatrix_norm_four_le_gram_energy A

end

end CircuitCompiler
