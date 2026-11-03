import Proofs.Compiler.GateApproximation.Shortening.ShorteningEmbeddings
import Proofs.Compiler.GateApproximation.Shortening.ShorteningRectangles
import Proofs.Compiler.Foundations.LinearAlgebra.TableGeometry



/-!
# Nuclear transport for each fixed shortening message

The nuclear norm is the repository's actual dual operator norm. A proved rank-one bound converts the rectangle factor calculation into a nuclear bound; no nuclear-norm inequality is assumed as a certificate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.Shortening

open Refresh MatrixRefresh TableAnalysis

variable {X D B : Type*} [Fintype X] [DecidableEq X] [Fintype D] [Fintype B]

/-- The genuine dual nuclear norm of a rank-one matrix has the usual upper bound by the product of counting-measure Euclidean norms. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → ℝ, we have

‖ ((x, y ↦ a(x) · b(y)))‖_(*,count) ≤ √(∑ₓ ((a(x))²)) · √(∑_y ((b(y))²)).
-/
theorem rankOne_nuclearNorm_le (a b : X → ℝ) :
    nuclearNorm (fun x y => a x * b y) ≤
      Real.sqrt (∑ x, a x ^ 2) * Real.sqrt (∑ y, b y ^ 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro W
  rw [countingPairingDual_apply, Real.norm_eq_abs]
  have hpair : countingPairing (fun x y => a x * b y) W =
      ∑ x, a x * ∑ y, W x y * b y := by
    simp only [countingPairing, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hpair]
  calc
    _ ≤ Real.sqrt (∑ x, a x ^ 2) *
        Real.sqrt (∑ x, (∑ y, W x y * b y) ^ 2) := abs_sum_mul_le _ _
    _ ≤ Real.sqrt (∑ x, a x ^ 2) * Real.sqrt (‖W‖ ^ 2 * ∑ y, b y ^ 2) :=
      mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (sum_sq_matrix_action_le W b)) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
      ring

/-- The two normalizations cancel to a single matrix-size denominator. -/

/- Mathematical statement (normal notation): For real functions a,b:X → ℝ, with X ≠ ∅, ‖a‖₂ · ‖b‖₂ = |X|⁻¹√(∑ₓ a(x)²)√(∑_y b(y)²). Thus the two uniform-average normalizations together contribute 1/|X|. -/
theorem uniform_rms_product [Nonempty X] (a b : X → ℝ) :
    rms (FiniteDistribution.uniform : FiniteDistribution X) a * rms (FiniteDistribution.uniform : FiniteDistribution X) b =
      (Real.sqrt (∑ x, a x ^ 2) * Real.sqrt (∑ y, b y ^ 2)) / Fintype.card X := by
  have hc : (0 : ℝ) ≤ (Fintype.card X : ℝ)⁻¹ := by positivity
  simp only [rms, FiniteDistribution.expect, FiniteDistribution.uniform, ← Finset.mul_sum, Real.sqrt_mul hc]
  calc
    _ = (Real.sqrt (Fintype.card X : ℝ)⁻¹ * Real.sqrt (Fintype.card X : ℝ)⁻¹) *
        (Real.sqrt (∑ x, a x ^ 2) * Real.sqrt (∑ y, b y ^ 2)) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hc]; ring

/-- Rank-one bound in the manuscript's uniform-table normalization. -/

/- Mathematical statement (normal notation): For real functions a,b on a nonempty finite set, the product table F(x,y) = a(x) · b(y) satisfies ‖F‖_* ≤ ‖a‖₂ · ‖b‖₂. All norms use uniform averages over the indicated finite sets. -/
theorem rankOne_tableNuclearNorm_le [Nonempty X] (a b : X → ℝ) :
    tableNuclearNorm (fun x y => a x * b y) ≤
      rms (FiniteDistribution.uniform : FiniteDistribution X) a * rms (FiniteDistribution.uniform : FiniteDistribution X) b := by
  rw [uniform_rms_product]
  exact div_le_div_of_nonneg_right (rankOne_nuclearNorm_le a b) (Nat.cast_nonneg _)

/-- The nuclear norm is subadditive over any finite matrix family. -/

/- Mathematical statement (normal notation): The nuclear norm is subadditive for every finite family of real tables: ‖∑ᵢ Fᵢ‖_* ≤ ∑ᵢ ‖Fᵢ‖_*. -/
theorem tableNuclearNorm_sum_le {I : Type*} [Fintype I] (T : I → Matrix X X ℝ) :
    tableNuclearNorm (∑ i, T i) ≤ ∑ i, tableNuclearNorm (T i) := by
  classical
  have h (s : Finset I) : tableNuclearNorm (∑ i ∈ s, T i) ≤ ∑ i ∈ s, tableNuclearNorm (T i) := by
    induction s using Finset.induction_on with
    | empty => simp [tableNuclearNorm]
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (tableNuclearNorm_add_le _ _).trans (add_le_add (le_refl _) ih)
  exact h Finset.univ

/-- Finite probabilistic mixtures do not increase the average nuclear cost. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For I a set; P ∈ 𝒟(I); T ∈ I → ℝ^(X × X), assume I is finite. Then

‖ ((x, y ↦ 𝔼_(i ← P) [T(i, x, y)]))‖_* ≤ 𝔼_(i ← P) [‖ T(i)‖_*].
-/
theorem tableNuclearNorm_expect_le {I : Type*} [Fintype I] (P : FiniteDistribution I)
    (T : I → Matrix X X ℝ) :
    tableNuclearNorm (fun x y => P.expect (fun i => T i x y)) ≤
      P.expect (fun i => tableNuclearNorm (T i)) := by
  have heq : (fun x y => P.expect (fun i => T i x y)) =
      ∑ i, P.weight i • T i := by
    ext x y
    simp [FiniteDistribution.expect, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [heq]
  refine (tableNuclearNorm_sum_le _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  simp only [tableNuclearNorm, nuclearNorm_smul, abs_of_nonneg (P.nonneg i)]
  change P.weight i * nuclearNorm (T i) / _ ≤ P.weight i * (nuclearNorm (T i) / _)
  ring_nf
  rfl

/-- The manuscript's fixed-message rank-one nuclear estimate, proved for a real rectangle partition and the actual normalized nuclear norm. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ RectanglePartition(B, X, (X × D)); R ∈ 𝒟(D); a ∈ X → ℝ; b ∈ X × D → ℝ, assume X ≠ ∅. Then

(∑ᵦ (‖ ((x, y ↦ ({ a(x) if r.left(β, x),; 0 otherwise }) · 𝔼_(d ← R) [{ b((y, d)) if r.right(β, (y, d)),; 0 otherwise }]))‖_*)) ≤ √(|B|) · ‖ a‖_(2,𝒰_X) · ‖ b‖_(2,(𝒰_X ⊗ R)).
-/
theorem rectangle_nuclear_budget [Nonempty X]
    (r : RectanglePartition B X (X × D)) (R : FiniteDistribution D)
    (a : X → ℝ) (b : X × D → ℝ) :
    (∑ β, tableNuclearNorm (fun x y =>
      (if r.left β x then a x else 0) *
        R.expect (fun d => if r.right β (y, d) then b (y, d) else 0))) ≤
      Real.sqrt (Fintype.card B) * rms (FiniteDistribution.uniform : FiniteDistribution X) a *
        rms ((FiniteDistribution.uniform : FiniteDistribution X).prod R) b := by
  refine le_trans ?_ (rectangle_factor_budget r FiniteDistribution.uniform FiniteDistribution.uniform R a b)
  apply Finset.sum_le_sum
  intro β _
  exact rankOne_tableNuclearNorm_le _ _

/-- Averaging nonnegative square-root energies across a finite message index costs the square root of the index count and the averaged total energy. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For I,J a set; P ∈ 𝒟(I); E ∈ I → J → ℝ, assume I is finite; J is finite; ∀ i, j, 0 ≤ E(i, j). Then

𝔼_(i ← P) [∑ⱼ (√(E(i, j)))] ≤ √(|J|) · √(𝔼_(i ← P) [∑ⱼ (E(i, j))]).
-/
theorem averaged_sqrt_sum_le {I J : Type*} [Fintype I] [Fintype J]
    (P : FiniteDistribution I) (E : I → J → ℝ) (hE : ∀ i j, 0 ≤ E i j) :
    P.expect (fun i => ∑ j, Real.sqrt (E i j)) ≤
      Real.sqrt (Fintype.card J) * Real.sqrt (P.expect (fun i => ∑ j, E i j)) := by
  have hpoint (i : I) : (∑ j, Real.sqrt (E i j)) ≤
      Real.sqrt (Fintype.card J) * Real.sqrt (∑ j, E i j) := by
    have h := abs_sum_mul_le (fun _ : J => (1 : ℝ)) (fun j => Real.sqrt (E i j))
    simpa only [one_mul, one_pow, Real.sq_sqrt (hE i _), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one,
      abs_of_nonneg (Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg (E i j)))] using h
  have hJ : P.expect (fun i => Real.sqrt (∑ j, E i j)) ≤
      Real.sqrt (P.expect (fun i => ∑ j, E i j)) := by
    have h := abs_expect_le_rms P (fun i => Real.sqrt (∑ j, E i j))
    simpa only [rms, Real.sq_sqrt (Finset.sum_nonneg (fun j _ => hE _ j)),
      abs_of_nonneg (P.expect_nonneg _ (fun _ => Real.sqrt_nonneg _))] using h
  calc
    _ ≤ P.expect (fun i => Real.sqrt (Fintype.card J) * Real.sqrt (∑ j, E i j)) :=
      P.expect_mono hpoint
    _ = Real.sqrt (Fintype.card J) * P.expect (fun i => Real.sqrt (∑ j, E i j)) :=
      expect_smul _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hJ (Real.sqrt_nonneg _)

/-- Assemble the tail and pivot averages after the concrete pullback energies have been established. Every `T i j β` is an actual matrix, and its output is an explicitly specified finite average. `C` is the fixed-message leaf loss. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For I,J a set; P ∈ 𝒟(I); T ∈ I → J → B → ℝ^(X × X); u, v ∈ I → J → ℝ; ρ, A, C ∈ ℝ, assume I is finite; J is finite; 0 ≤ ρ; 0 ≤ A; 0 ≤ C; ∀ i, j, 0 ≤ u(i, j); ∀ i, j, 0 ≤ v(i, j); 𝔼_(i ← P) [∑ⱼ ((u(i, j))²)] ≤ ρ · A²; ∀ i, j, v(i, j) ≤ C; ∀ i, j, (∑ᵦ (‖ T(i, j, β)‖_*)) ≤ u(i, j) · v(i, j). Then

(∑ᵦ (‖ ((x, y ↦ 𝔼_(i ← P) [∑ⱼ (T(i, j, β, x, y))]))‖_*)) ≤ √(|J|) · √ρ · A · C.
-/
theorem averaged_nuclear_budget {I J : Type*} [Fintype I] [Fintype J]
    (P : FiniteDistribution I) (T : I → J → B → Matrix X X ℝ)
    (u v : I → J → ℝ) (ρ A C : ℝ)
    (hρ : 0 ≤ ρ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hu : ∀ i j, 0 ≤ u i j) (hv : ∀ i j, 0 ≤ v i j)
    (hleft : P.expect (fun i => ∑ j, u i j ^ 2) ≤ ρ * A ^ 2)
    (hright : ∀ i j, v i j ≤ C)
    (hlocal : ∀ i j, (∑ β, tableNuclearNorm (T i j β)) ≤ u i j * v i j) :
    (∑ β, tableNuclearNorm (fun x y => P.expect (fun i => ∑ j, T i j β x y))) ≤
      Real.sqrt (Fintype.card J) * Real.sqrt ρ * A * C := by
  have havg : P.expect (fun i => ∑ j, u i j) ≤
      Real.sqrt (Fintype.card J) * Real.sqrt ρ * A := by
    have h := averaged_sqrt_sum_le P (fun i j => u i j ^ 2) (fun _ _ => sq_nonneg _)
    simp only [Real.sqrt_sq_eq_abs, abs_of_nonneg (hu _ _)] at h
    refine h.trans ?_
    calc
      _ ≤ Real.sqrt (Fintype.card J) * Real.sqrt (ρ * A ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hleft) (Real.sqrt_nonneg _)
      _ = _ := by rw [Real.sqrt_mul hρ, Real.sqrt_sq_eq_abs, abs_of_nonneg hA]; ring
  calc
    _ ≤ ∑ β, P.expect (fun i => ∑ j, tableNuclearNorm (T i j β)) := by
      apply Finset.sum_le_sum
      intro β _
      have h := tableNuclearNorm_expect_le P (fun i => ∑ j, T i j β)
      simp only [Matrix.sum_apply] at h
      refine h.trans ?_
      apply P.expect_mono
      intro i
      exact tableNuclearNorm_sum_le _
    _ = P.expect (fun i => ∑ j, ∑ β, tableNuclearNorm (T i j β)) := by
      rw [← expect_sum]
      apply congrArg P.expect
      funext i
      exact Finset.sum_comm
    _ ≤ P.expect (fun i => ∑ j, u i j * v i j) := by
      apply P.expect_mono
      intro i
      exact Finset.sum_le_sum (fun j _ => hlocal i j)
    _ ≤ P.expect (fun i => ∑ j, u i j * C) := by
      apply P.expect_mono
      intro i
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hright i j) (hu i j))
    _ = P.expect (fun i => ∑ j, u i j) * C := by
      simp only [← Finset.sum_mul, expect_mul_const]
    _ ≤ _ := mul_le_mul_of_nonneg_right havg hC

end CircuitCompiler.Shortening
