import Proofs.Compiler.GateApproximation.MatrixPhase.JointOrbitAverage
import Proofs.Compiler.GateApproximation.MatrixPhase.JointRankExceptions



/-!
# Comparing the actual shared-matrix orbit with four pairing constraints

This is the signed test-function form of the orbit calculation. It removes both output rank restrictions and the small nonuniformity of the finite orbit, leaving exactly the four pairing equations for Fourier expansion.
-/
set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators Classical

namespace CircuitCompiler

open Refresh MatrixRefresh TableAnalysis

noncomputable section

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X a set; f ∈ X → ℝ, assume X is finite. Then

|𝔼ᵤ [f(u)]| ≤ 𝔼ₓ [|f(x)|].
-/
lemma abs_uavg_le_uavg_abs {X : Type*} [Fintype X] (f : X → ℝ) :
    |uavg f| ≤ uavg (fun x => |f x|) := by
  unfold uavg
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X a set; f ∈ X → ℝ; B ∈ ℝ, assume X is finite; X ≠ ∅; ∀ x, |f(x)| ≤ B. Then

|𝔼ᵤ [f(u)]| ≤ B.
-/
lemma abs_uavg_le_bound {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (B : ℝ) (hf : ∀ x, |f x| ≤ B) : |uavg f| ≤ B := by
  exact (abs_uavg_le_uavg_abs f).trans ((uavg_mono hf).trans_eq (uavg_const B))

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; p ∈ AmbientQuadruple(F, m), we have

quadrupleIndependent(p) ⇔ ¬ (projectiveRel(((p)₁)₁, ((p)₁)₂)) ∧ ¬ (projectiveRel(((p)₂)₁, ((p)₂)₂)).
-/
theorem quadrupleIndependent_iff {m : ℕ} (p : AmbientQuadruple F m) :
    quadrupleIndependent p ↔ ¬projectiveRel p.1.1 p.1.2 ∧ ¬projectiveRel p.2.1 p.2.2 := by
  unfold quadrupleIndependent
  rw [LinearIndependent.pair_iff' p.1.1.property, LinearIndependent.pair_iff' p.2.1.property]
  simp only [projectiveRel, not_exists, ne_eq, eq_comm]

/-- Removing both rank restrictions costs exactly the previously counted proportional-output exceptional fraction. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; S ∈ F^({0,…,2−1} × {0,…,2−1}); f ∈ AmbientQuadruple(F, m) → ℝ; B ∈ ℝ, assume U(F, m) ≠ ∅; 0 ≤ B; ∀ p, |f(p)| ≤ B. Then

|𝔼ₚ [{ f(p) if quadrupleAdmissible(S, p),; 0 otherwise }] - 𝔼ₚ [{ f(p) if quadruplePairings(p) = S,; 0 otherwise }]| ≤ (2 · (|F| - 1) / |U(F, m)|) · B.
-/
theorem orbit_rank_mask_error {m : ℕ} [Nonempty (U F m)]
    (S : Matrix (Fin 2) (Fin 2) F) (f : AmbientQuadruple F m → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ p, |f p| ≤ B) :
    |uavg (fun p => if quadrupleAdmissible S p then f p else 0) -
      uavg (fun p => if quadruplePairings p = S then f p else 0)| ≤
        (2 * ((fieldCard F : ℝ) - 1) / Fintype.card (U F m)) * B := by
  rw [← uavg_sub]
  refine (abs_uavg_le_uavg_abs _).trans ?_
  calc
    _ ≤ uavg (fun p : AmbientQuadruple F m =>
        if projectiveRel p.1.1 p.1.2 ∨ projectiveRel p.2.1 p.2.2 then |f p| else 0) := by
      apply uavg_mono
      intro p
      by_cases hp : projectiveRel p.1.1 p.1.2 <;>
        by_cases hq : projectiveRel p.2.1 p.2.2 <;> by_cases hs : quadruplePairings p = S <;>
        simp [quadrupleAdmissible, quadrupleIndependent_iff, hp, hq, hs, abs_nonneg]
    _ ≤ _ := by
      simp_rw [uavg_prod]
      exact output_rank_exception_le B hB (fun u u' v v' => f ((u, u'), (v, v')))
        (fun u u' v v' => hf ((u, u'), (v, v')))

/-
Mathematical definition (normal notation): For F a set, assume F is a field; F is finite. define

jointOrbitComparisonConstant := jointOrbitDensityConstant(F) + 4 · (|F|)⁴ · (|F| - 1).
-/
def jointOrbitComparisonConstant (F : Type*) [Field F] [Fintype F] : ℝ :=
  jointOrbitDensityConstant F + 4 * (fieldCard F : ℝ) ^ 4 * ((fieldCard F : ℝ) - 1)

/-- The rank-exception coefficient in the simpler `constant/Q` form. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ, assume 1 ≤ m. Then

2 · (|F| - 1) / |U(F, m)| ≤ 4 · (|F| - 1) / (|F|)ᵐ.
-/
theorem output_rank_coefficient_le {m : ℕ} (hm : 1 ≤ m) :
    2 * ((fieldCard F : ℝ) - 1) / Fintype.card (U F m) ≤
      4 * ((fieldCard F : ℝ) - 1) / (fieldCard F : ℝ) ^ m := by
  have hq : (2 : ℝ) ≤ fieldCard F := by exact_mod_cast fieldCard_ge_two (F := F)
  have hQN : 2 ≤ fieldCard F ^ m := (fieldCard_ge_two (F := F)).trans (by
    simpa using Nat.pow_le_pow_right (show 1 ≤ fieldCard F by have := fieldCard_ge_two (F := F); omega) hm)
  have hQ : (2 : ℝ) ≤ (fieldCard F : ℝ) ^ m := by exact_mod_cast hQN
  have hQ1 : 1 ≤ fieldCard F ^ m := by omega
  rw [nonzero_vector_card, Nat.cast_sub hQ1, Nat.cast_pow, Nat.cast_one]
  apply (div_le_div_iff₀ (by linarith : 0 < (fieldCard F : ℝ) ^ m - 1) (by linarith)).2
  nlinarith

/-- Actual simultaneous matrix refresh is approximated by `q⁴` times the four-equation mask. The error is uniform over every bounded signed test function and every prescribed pairing matrix. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): Let m ≥ 4, Q = |F|, and fix an independent row-pair/column-pair quadruple whose cross-pairing matrix is S. For every real test |f| ≤ B, its average after a uniform invertible refresh differs by at most C_F B/Qᵐ from Q⁴ times its unrestricted uniform average restricted to quadruples with cross-pairing matrix S. Here C_F is the defined field-dependent orbit-comparison constant, and B ≥ 0. -/
theorem shared_quadruple_approximation {m : ℕ} (hm : 4 ≤ m)
    {S : Matrix (Fin 2) (Fin 2) F} (p : CompatibleQuadruples (m := m) S)
    (f : AmbientQuadruple F m → ℝ) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ a, |f a| ≤ B) :
    |uavg (fun M : Refresh.«GL» F m => f (quadrupleEmbedding S (quadrupleRefresh p M))) -
      (fieldCard F : ℝ) ^ 4 * uavg (fun a => if quadruplePairings a = S then f a else 0)| ≤
      (jointOrbitComparisonConstant F / (fieldCard F : ℝ) ^ m) * B := by
  letI : Nonempty (U F m) := ⟨p.1.val.1⟩
  rw [uavg_shared_quadruple (by omega)]
  let g := uavg (fun a => if quadrupleAdmissible S a then f a else 0)
  let h := uavg (fun a => if quadruplePairings a = S then f a else 0)
  have hg : |g| ≤ B := abs_uavg_le_bound _ B (fun a => by
    split_ifs
    · exact hf a
    · simpa using hB)
  have hdiff := orbit_rank_mask_error S f B hB hf
  change |g - h| ≤ _ at hdiff
  have hdensity := jointOrbitDensity_error hm S
  have hq0 : 0 ≤ (fieldCard F : ℝ) ^ 4 := by positivity
  have hdc : 0 ≤ jointOrbitDensityConstant F / (fieldCard F : ℝ) ^ m := by
    unfold jointOrbitDensityConstant
    positivity
  have hexpand : jointOrbitDensity m S * g - (fieldCard F : ℝ) ^ 4 * h =
      (jointOrbitDensity m S - (fieldCard F : ℝ) ^ 4) * g + (fieldCard F : ℝ) ^ 4 * (g - h) := by ring
  change |jointOrbitDensity m S * g - (fieldCard F : ℝ) ^ 4 * h| ≤ _
  rw [hexpand]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hq0]
  have hfirst := mul_le_mul hdensity hg (abs_nonneg _) hdc
  have hsecond := mul_le_mul_of_nonneg_left hdiff hq0
  have hcoef := mul_le_mul_of_nonneg_right (output_rank_coefficient_le (F := F) (m := m) (by omega)) hB
  have hsecond' := hsecond.trans (mul_le_mul_of_nonneg_left hcoef hq0)
  refine (add_le_add hfirst hsecond').trans_eq ?_
  unfold jointOrbitComparisonConstant
  ring

end

end CircuitCompiler
