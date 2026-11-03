import Proofs.Compiler.GateApproximation.Interfaces.NuclearDirections



/-!
# Random-refresh control of the strict polar witness

The variance estimate keeps the mean feature energy (the retained rank), instead of replacing it by the pointwise factorEnergy bound. That trace budget is what permits the nuclear-norm bootstrap at the cube-root threshold.
-/

set_option autoImplicit false

set_option maxHeartbeats 1800000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.TruncatedAnswerNorm

open Refresh MatrixRefresh TableAnalysis GateTruncation RefreshAnalysis SingularTruncation

noncomputable section

variable {F X P : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype X] [DecidableEq X] [Nonempty X] [Fintype P] [DecidableEq P] {m : ℕ}

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); ξ, ζ ∈ X → U(F, m) → P → ℂ; θ, L, R ∈ ℝ, assume |F| = 2; 2 ≤ m; a is injective; b is injective; 0 ≤ L; ‖ featureMeanGram(ξ)‖ ≤ θ; ‖ featureMeanGram(ζ)‖ ≤ θ; ∀ x, u, featureEnergy(ξ, x, u) ≤ L; ∀ x, u, featureEnergy(ζ, x, u) ≤ L; 𝔼ₓ [𝔼ᵤ [featureEnergy(ξ, x, u)]] ≤ R; 𝔼ₓ [𝔼ᵤ [featureEnergy(ζ, x, u)]] ≤ R. Then

𝔼_(M ∈ GLₘ(F)) [opNorm(graphRestriction(a, b, featureFactorTable(ξ, ζ), M))] ≤ θ + √(featureVarianceCoefficient(F, X, m) · L · R).
-/
theorem feature_large_part_mean_trace (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (ξ ζ : X → U F m → P → ℂ) (θ L R : ℝ) (hL : 0 ≤ L)
    (hξ : ‖featureMeanGram ξ‖ ≤ θ) (hζ : ‖featureMeanGram ζ‖ ≤ θ)
    (hξpoint : ∀ x u, featureEnergy ξ x u ≤ L)
    (hζpoint : ∀ x u, featureEnergy ζ x u ≤ L)
    (hξtrace : uavg (fun x => uavg (fun u => featureEnergy ξ x u)) ≤ R)
    (hζtrace : uavg (fun x => uavg (fun u => featureEnergy ζ x u)) ≤ R) :
    uavg (fun M : Refresh.«GL» F m =>
      opNorm (graphRestriction a b (featureFactorTable ξ ζ) M)) ≤
        θ + Real.sqrt (featureVarianceCoefficient F X m * L * R) := by
  letI : Nonempty (U F m) := ⟨unitShare ⟨0, by omega⟩⟩
  have hκ := featureVarianceCoefficient_nonneg (F := F) (X := X) hm
  have hξvar := (feature_row_Gram_variance_le_energy hq hm a ha ξ L hξpoint).trans
    (mul_le_mul_of_nonneg_left hξtrace (mul_nonneg hκ hL))
  have hζvar := (feature_column_Gram_variance_le_energy hq hm b hb ζ L hζpoint).trans
    (mul_le_mul_of_nonneg_left hζtrace (mul_nonneg hκ hL))
  let u := fun M : Refresh.«GL» F m => Real.sqrt (featureRowGramDeviationSq a ξ M)
  let v := fun M : Refresh.«GL» F m => Real.sqrt
    (∑ p, ∑ q, ‖featureColumnGram b ζ M p q - featureMeanGram ζ p q‖ ^ 2)
  have hu : uavg (fun M => u M ^ 2) ≤ featureVarianceCoefficient F X m * L * R := by
    have hu0 (M : Refresh.«GL» F m) : 0 ≤ featureRowGramDeviationSq a ξ M := by
      unfold featureRowGramDeviationSq
      positivity
    simpa only [u, Real.sq_sqrt (hu0 _)] using hξvar
  have hv : uavg (fun M => v M ^ 2) ≤ featureVarianceCoefficient F X m * L * R := by
    simpa only [v, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
      (fun _ _ => sq_nonneg _)))] using hζvar
  have h := gram_mean_of_second_moments (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F m))
    (fun M => opNorm (graphRestriction a b (featureFactorTable ξ ζ) M))
    u v θ _ _ (feature_large_part_pointwise a b ξ ζ θ hξ hζ)
    (by simpa only [uavg_eq_expect_uniform] using hu)
    (by simpa only [uavg_eq_expect_uniform] using hv)
  rw [← uavg_eq_expect_uniform] at h
  linarith

/-- The polar test of the actual strict SVD cutoff has bounded average operator norm after an injective-feature refresh. All Gram and factorEnergy hypotheses are discharged by its concrete singular directions. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); A ∈ ℝ^((X × U(F, m)) × (X × U(F, m))); β ∈ ℝ, assume |F| = 2; 2 ≤ m; a is injective; b is injective; 0 < β; ∀ i, j, |A(i, j)| ≤ 1. Then

𝔼_(M ∈ GLₘ(F)) [‖ refreshTable(a, b, strictPolar(A, β), M)‖ₒₚ] ≤ 1 + √(featureVarianceCoefficient(F, X, m) · (1 / β²) · strictRank(A, β)).
-/
theorem strictPolar_graph_mean (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (A : Matrix (X × U F m) (X × U F m) ℝ)
    (β : ℝ) (hβ : 0 < β) (hA : ∀ i j, |A i j| ≤ 1) :
    uavg (fun M : Refresh.«GL» F m => largestSingularCoefficient (refreshTable a b (strictPolar A β) M)) ≤
      1 + Real.sqrt (featureVarianceCoefficient F X m * (1 / β ^ 2) * strictRank A β) := by
  letI : Nonempty (U F m) := ⟨unitShare ⟨0, by omega⟩⟩
  let ξ := fun (x : X) (u : U F m) (p : Fin (Fintype.card (X × U F m))) =>
    (strictUnitLeft A β (x,u) p : ℂ)
  let ζ := fun (x : X) (u : U F m) (p : Fin (Fintype.card (X × U F m))) =>
    (strictUnitRight A β (x,u) p : ℂ)
  have hξ : ‖featureMeanGram ξ‖ ≤ 1 := by
    rw [show ξ = (fun x u p => (strictUnitLeft A β (x,u) p : ℂ)) by rfl,
      featureMeanGram_ofReal (fun i p => strictUnitLeft A β i p), complexMatrix_ofReal_norm]
    exact strictUnitLeft_gram_norm A β
  have hζ : ‖featureMeanGram ζ‖ ≤ 1 := by
    rw [show ζ = (fun x u p => (strictUnitRight A β (x,u) p : ℂ)) by rfl,
      featureMeanGram_ofReal (fun i p => strictUnitRight A β i p), complexMatrix_ofReal_norm]
    exact strictUnitRight_gram_norm A β
  have hξenergy (x : X) (u : U F m) :
      featureEnergy ξ x u = ‖strictUnitLeft A β (x,u)‖ ^ 2 := by
    simp only [featureEnergy, ξ, Complex.norm_real, PiLp.norm_sq_eq_of_L2]
  have hζenergy (x : X) (u : U F m) :
      featureEnergy ζ x u = ‖strictUnitRight A β (x,u)‖ ^ 2 := by
    simp only [featureEnergy, ζ, Complex.norm_real, PiLp.norm_sq_eq_of_L2]
  have hξpoint : ∀ x u, featureEnergy ξ x u ≤ 1 / β ^ 2 := by
    intro x u
    rw [hξenergy]
    exact strictUnitLeft_energy A β hβ hA (x,u)
  have hζpoint : ∀ x u, featureEnergy ζ x u ≤ 1 / β ^ 2 := by
    intro x u
    rw [hζenergy]
    exact strictUnitRight_energy A β hβ hA (x,u)
  have hξtrace : uavg (fun x => uavg (fun u => featureEnergy ξ x u)) = strictRank A β := by
    simp_rw [hξenergy]
    exact (uavg_prod (fun i : X × U F m => ‖strictUnitLeft A β i‖ ^ 2)).symm.trans
      (strictUnitLeft_mean_energy A β)
  have hζtrace : uavg (fun x => uavg (fun u => featureEnergy ζ x u)) = strictRank A β := by
    simp_rw [hζenergy]
    exact (uavg_prod (fun i : X × U F m => ‖strictUnitRight A β i‖ ^ 2)).symm.trans
      (strictUnitRight_mean_energy A β)
  have htable : featureFactorTable ξ ζ = (strictPolar A β).map Complex.ofReal := by
    ext x y
    simp only [featureFactorTable, ξ, ζ, Matrix.map_apply, strictPolar_factorization,
      PiLp.inner_apply, RCLike.inner_apply, Complex.star_def, Complex.conj_ofReal,
      ← Complex.ofReal_mul, ← Complex.ofReal_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    simp only [starRingEnd_apply, star_trivial]
    ring
  have h := feature_large_part_mean_trace hq hm a b ha hb ξ ζ 1 (1 / β ^ 2)
    (strictRank A β) (by positivity) hξ hζ hξpoint hζpoint hξtrace.le hζtrace.le
  rw [htable] at h
  simpa only [refreshTable_op_complex] using h

end

end CircuitCompiler.TruncatedAnswerNorm
