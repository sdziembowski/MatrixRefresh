import Proofs.Compiler.Foundations.MatrixRefreshing.Probability.FiniteDistribution



/-! EnergyCompression fourth-root estimates with finite real probability distributions. -/

set_option autoImplicit false

namespace MatrixRefresh

noncomputable section

/-- The nonnegative fourth root; the proof development uses real powers only at its boundary. -/
/-
Mathematical definition (normal notation): For a ∈ ℝ, define

fourthRoot(a) := √(√a).
-/
def fourthRoot (a : ℝ) : ℝ := Real.sqrt (Real.sqrt a)

/-- The iterated real square root is nonnegative for every real input. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ ℝ, we have

0 ≤ fourthRoot(a).
-/
theorem fourthRoot_nonneg (a : ℝ) : 0 ≤ fourthRoot a :=
  Real.sqrt_nonneg _

/-- The nonnegative fourth-root function preserves the order of real inputs. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ ℝ, assume a ≤ b. Then

fourthRoot(a) ≤ fourthRoot(b).
-/
theorem fourthRoot_mono {a b : ℝ} (h : a ≤ b) : fourthRoot a ≤ fourthRoot b :=
  Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h)

/-- Squaring the nonnegative fourth root gives the real square root, including the totalized behavior on negative inputs. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ ℝ, we have

(fourthRoot(a))² = √a.
-/
theorem fourthRoot_sq (a : ℝ) : fourthRoot a ^ 2 = Real.sqrt a :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

/-- For a nonnegative input, raising its fourth root to the fourth power recovers the input. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ ℝ, assume 0 ≤ a. Then

(fourthRoot(a))⁴ = a.
-/
theorem fourthRoot_pow_four {a : ℝ} (ha : 0 ≤ a) : fourthRoot a ^ 4 = a := by
  rw [show 4 = 2 * 2 by rfl, pow_mul, fourthRoot_sq, Real.sq_sqrt ha]

/-- The fourth root of a product factors into the product of fourth roots when the first factor is nonnegative; real square roots are totalized at zero on negative inputs. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ ℝ, assume 0 ≤ a. Then

fourthRoot((a · b)) = fourthRoot(a) · fourthRoot(b).
-/
theorem fourthRoot_mul {a b : ℝ} (ha : 0 ≤ a) :
    fourthRoot (a * b) = fourthRoot a * fourthRoot b := by
  simp only [fourthRoot, Real.sqrt_mul ha, Real.sqrt_mul (Real.sqrt_nonneg a)]

/-- Taking the fourth root of the fourth power of a nonnegative number recovers that number. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ ℝ, assume 0 ≤ a. Then

fourthRoot((a⁴)) = a.
-/
theorem fourthRoot_pow_four_of_nonneg {a : ℝ} (ha : 0 ≤ a) :
    fourthRoot (a ^ 4) = a := by
  rw [fourthRoot, show 4 = 2 * 2 by rfl, pow_mul,
    Real.sqrt_sq (sq_nonneg a), Real.sqrt_sq ha]

/--
For nonnegative inputs, the fourth root of their sum is at most the sum of their fourth roots.

Subadditivity is proved on nonnegative inputs, as used in the matrix-average bound.
-/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ ℝ, assume 0 ≤ a; 0 ≤ b. Then

fourthRoot((a + b)) ≤ fourthRoot(a) + fourthRoot(b).
-/
theorem fourthRoot_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    fourthRoot (a + b) ≤ fourthRoot a + fourthRoot b := by
  have hra := fourthRoot_nonneg a
  have hrb := fourthRoot_nonneg b
  apply le_of_pow_le_pow_left₀ (n := 4) (by decide) (add_nonneg hra hrb)
  rw [fourthRoot_pow_four (add_nonneg ha hb)]
  have hea := fourthRoot_pow_four ha
  have heb := fourthRoot_pow_four hb
  nlinarith [mul_nonneg (pow_nonneg hra 3) hrb,
    mul_nonneg (sq_nonneg (fourthRoot a)) (sq_nonneg (fourthRoot b)),
    mul_nonneg hra (pow_nonneg hrb 3)]

/--
The expected fourth root of a nonnegative function is at most the fourth root of its expected value under any finite probability distribution.

Fourth-root Jensen inequality, proved by two finite Cauchy--Schwarz applications.
-/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α a set; P ∈ 𝒟(α); F ∈ α → ℝ, assume α is finite; ∀ a, 0 ≤ F(a). Then

𝔼_(a ← P) [fourthRoot(F(a))] ≤ fourthRoot(𝔼_(v ← P) [F(v)]).
-/
theorem expect_fourthRoot_le {α : Type*} [Fintype α] (P : Refresh.FiniteDistribution α)
    (F : α → ℝ) (hF : ∀ a, 0 ≤ F a) :
    P.expect (fun a => fourthRoot (F a)) ≤ fourthRoot (P.expect F) := by
  have h₁ := expect_mul_sq_le P (fun a => fourthRoot (F a)) (fun _ => 1)
  have h₂ := expect_mul_sq_le P (fun a => Real.sqrt (F a)) (fun _ => 1)
  simp only [mul_one, one_pow, Refresh.FiniteDistribution.expect_one, fourthRoot_sq,
    Real.sq_sqrt (hF _)] at h₁ h₂
  apply le_of_pow_le_pow_left₀ (n := 4) (by decide) (fourthRoot_nonneg _)
  rw [fourthRoot_pow_four (P.expect_nonneg F hF)]
  calc
    _ = (P.expect (fun a => fourthRoot (F a)) ^ 2) ^ 2 := by ring
    _ ≤ P.expect (fun a => Real.sqrt (F a)) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) h₁ 2
    _ ≤ P.expect F := h₂

end

end MatrixRefresh
