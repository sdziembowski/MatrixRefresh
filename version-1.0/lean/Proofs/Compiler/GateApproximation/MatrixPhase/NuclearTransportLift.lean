import Proofs.Compiler.GateApproximation.Shortening.ShorteningNuclear
import Proofs.Compiler.Foundations.LinearAlgebra.NuclearIdentification



/-!
# Lifting a rank-one transport bound by a genuine SVD

A linear family of table operators with a rank-one `L₂ × L₂` bound has the corresponding nuclear-norm bound for every input table. The decomposition and its exact nuclear cost are proved using the repository's genuine real SVD.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.Shortening

open Refresh MatrixRefresh TableAnalysis

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
  [Fintype Y] [DecidableEq Y] [Fintype Z]

/-- An arbitrary finite square table has a rank-one decomposition whose exact sum of normalized `L₂` costs is its genuine normalized nuclear norm. -/

/-
Mathematical statement (normal notation): Every real square table G on a finite nonempty set X admits |X| pairs of real factors (zero factors are allowed) such that

G = ∑ⱼ₌₁ ^(|X|)aⱼ · bⱼᵀ, ∑ⱼ₌₁ ^(|X|)‖aⱼ‖₂ · ‖bⱼ‖₂ = ‖G‖_*.

The vector norms and nuclear norm use the paper's uniform normalization.
-/
theorem exists_nuclear_rankOne_decomposition (G : Matrix X X ℝ) :
    ∃ (a b : Fin (Fintype.card X) → X → ℝ),
      (G = ∑ i, (fun x y => a i x * b i y)) ∧
      (∑ i, rms (FiniteDistribution.uniform : FiniteDistribution X) (a i) *
        rms (FiniteDistribution.uniform : FiniteDistribution X) (b i)) = tableNuclearNorm G := by
  let s : RealSVD G.toEuclideanLin (Fintype.card X) :=
    Classical.choice (exists_realSVD G.toEuclideanLin finrank_euclideanSpace)
  let a := fun i x => s.sigma i * s.left i x
  let b := fun i x => s.right i x
  refine ⟨a, b, ?_, ?_⟩
  · ext x y
    simpa only [Finset.sum_apply, a, b] using s.matrix_entry x y
  · have hterm (i : Fin (Fintype.card X)) :
        rms (FiniteDistribution.uniform : FiniteDistribution X) (a i) *
          rms (FiniteDistribution.uniform : FiniteDistribution X) (b i) = s.sigma i / Fintype.card X := by
      have hl : (∑ x, s.left i x ^ 2) = 1 := by
        have h := congrArg (fun z : ℝ => z ^ 2) (s.left.norm_eq_one i)
        simpa only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, one_pow] using h
      have hr : (∑ x, s.right i x ^ 2) = 1 := by
        have h := congrArg (fun z : ℝ => z ^ 2) (s.right.norm_eq_one i)
        simpa only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, one_pow] using h
      rw [uniform_rms_product]
      simp only [a, b, mul_pow, ← Finset.mul_sum, hl, hr, mul_one,
        Real.sqrt_one, Real.sqrt_sq_eq_abs, abs_of_nonneg (s.nonneg i)]
    simp_rw [hterm]
    rw [← Finset.sum_div, ← s.nuclearNorm_eq_sum_sigma]
    rfl

/-- Rank-one control implies the full nuclear bound for a concrete linear transport operator; no decomposition premise remains in this theorem. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For T ∈ ℝ^(X × X) —linear over ℝ→ (Z → ℝ^(Y × Y)); C ∈ ℝ; G ∈ ℝ^(X × X), assume ∀ a, b ∈ X → ℝ, (∑_z (‖ T(((x, y ↦ a(x) · b(y))), z)‖_*)) ≤ C · ‖ a‖_(2,𝒰_X) · ‖ b‖_(2,𝒰_X). Then

(∑_z (‖ T(G, z)‖_*)) ≤ C · ‖ G‖_*.
-/
theorem linear_transport_nuclear_bound
    (T : Matrix X X ℝ →ₗ[ℝ] (Z → Matrix Y Y ℝ)) (C : ℝ)
    (hrank : ∀ a b : X → ℝ,
      (∑ z, tableNuclearNorm (T (fun x y => a x * b y) z)) ≤
        C * rms (FiniteDistribution.uniform : FiniteDistribution X) a * rms (FiniteDistribution.uniform : FiniteDistribution X) b)
    (G : Matrix X X ℝ) :
    (∑ z, tableNuclearNorm (T G z)) ≤ C * tableNuclearNorm G := by
  obtain ⟨a, b, hG, hcost⟩ := exists_nuclear_rankOne_decomposition G
  have hT (z : Z) : T G z = ∑ i, T (fun x y => a i x * b i y) z := by
    rw [hG, map_sum]
    simp only [Finset.sum_apply]
  simp_rw [hT]
  calc
    _ ≤ ∑ z, ∑ i, tableNuclearNorm (T (fun x y => a i x * b i y) z) :=
      Finset.sum_le_sum (fun z _ => tableNuclearNorm_sum_le _)
    _ = ∑ i, ∑ z, tableNuclearNorm (T (fun x y => a i x * b i y) z) := Finset.sum_comm
    _ ≤ ∑ i, C * rms (FiniteDistribution.uniform : FiniteDistribution X) (a i) *
        rms (FiniteDistribution.uniform : FiniteDistribution X) (b i) :=
      Finset.sum_le_sum (fun i _ => hrank (a i) (b i))
    _ = C * tableNuclearNorm G := by
      simp only [mul_assoc, ← Finset.mul_sum, hcost]

end CircuitCompiler.Shortening
