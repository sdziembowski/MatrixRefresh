import Proofs.Compiler.GateApproximation.Refreshing.EnergyCompression.Approximation
import Proofs.Compiler.GateApproximation.Refreshing.EnergyCompression.Parameters
import Proofs.Compiler.Foundations.LinearAlgebra.Operational



/-!
# Security from energy compression

The modular theorem supplies the actual density recurrences to the numeric induction and the encoding discrepancy to terminal extraction. The local compression procedure is an explicit input, instantiated by the analytic construction in the security assembly.
-/

set_option autoImplicit false

open scoped BigOperators

namespace TableAnalysis.EnergyCompression

open MatrixRefresh Refresh TableAnalysis

noncomputable section

variable {F Z : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype Z] [Nonempty Z] {n : ℕ}

-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

minSecretProbability(F, n) ≤ 1 / 2.
-/
theorem minSecretProbability_le_half (hn : 2 ≤ n) : minSecretProbability F n ≤ 1 / 2 := by
  have hq : (2 : ℝ) ≤ fieldCard F := by exact_mod_cast (fieldCard_ge_two (F := F))
  have hN : (4 : ℝ) ≤ vectorCard F n := vectorCard_real_ge_four hn
  have hd : 0 < (vectorCard F n : ℝ) - 1 := by linarith
  have hq0 : 0 < (fieldCard F : ℝ) := fieldCard_cast_pos
  unfold minSecretProbability
  rw [shareCard_cast_real]
  apply (div_le_iff₀ (mul_pos hq0 hd)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) hd.le]

/-- With a genuine one-round compression procedure, the forward-density proof yields the exact elementary bound for the actual transcript experiment. -/
-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); s, t ∈ F; T ∈ ℕ; θ ∈ ℝ; compress ∈ CompressionProcedure(F, n, Z, θ), assume 2 ≤ n; s ≠ t; 0 ≤ θ. Then

δ(((Prod)₂_*rectangleExecution(p, μₛ, T)), ((Prod)₂_*rectangleExecution(p, μₜ, T))) ≤ min{securityBound(|Z|, minSecretProbability(F, n), θ, |F|, |F|ⁿ, T), 1}.
-/
theorem security_of_compression (hn : 2 ≤ n) (p : RectangleProtocol F n Z)
    (s t : F) (hst : s ≠ t) (T : ℕ) (θ : ℝ) (hθ : 0 ≤ θ)
    (compress : CompressionProcedure F n Z θ) :
    statisticalDistance
      ((rectangleExecution p (mu F n hn s) T).map Prod.snd)
      ((rectangleExecution p (mu F n hn t) T).map Prod.snd) ≤
      min (securityBound (Fintype.card Z) (minSecretProbability F n) θ (fieldCard F) (vectorCard F n) T) 1 := by
  let G := approximateDensity p θ compress
  let E := fun i => approximationError (currentDensity p i) (G i)
  let C := fun i => approximationL2 (G i)
  let B := fun i => approximationNuclear (G i)
  let M := fun i => approximationMass (G i)
  let dist := statisticalDistance
      ((rectangleExecution p (mu F n hn s) T).map Prod.snd)
      ((rectangleExecution p (mu F n hn t) T).map Prod.snd)
  have hK : (1 : ℝ) ≤ Fintype.card Z := by
    exact_mod_cast (Fintype.card_pos (α := Z))
  have hpMin : 0 < minSecretProbability F n := minSecretProbability_pos hn
  have hpMinHalf : minSecretProbability F n ≤ 1 / 2 := minSecretProbability_le_half hn
  have hN : 0 < (vectorCard F n : ℝ) := by linarith [vectorCard_real_ge_four (F := F) hn]
  have hinit := initial_envelopes (Fintype.card Z : ℝ) (minSecretProbability F n) hK hpMin (by linarith)
  have hE0 : E 0 ≤ 0 := le_of_eq (approximateDensity_initial_error p θ compress)
  have hC0 : C 0 ≤ l2Envelope (Fintype.card Z) (minSecretProbability F n) := by
    dsimp [C, G]
    rw [approximateDensity_initial_l2 hn p θ compress]
    exact hinit.1
  have hB0 : B 0 ≤ nuclearEnvelope (Fintype.card Z) (minSecretProbability F n) :=
    (approximateDensity_initial_nuclear hn p θ compress).trans hinit.2
  have hextract : dist ≤ E T / (2 * minSecretProbability F n) + (fieldCard F : ℝ) * B T / Real.sqrt (vectorCard F n) := by
    dsimp [dist, E, B]
    rw [rectangleExecution_statisticalDistance]
    have ht := actual_terminal_nuclear_bound hn s t hst (currentDensity p T) (G T)
    rw [← approximationError_eq_terminalError hn] at ht
    simpa only [approximationNuclear, div_mul_eq_mul_div] using ht
  exact final_numeric_security (Fintype.card Z) (minSecretProbability F n) θ (fieldCard F) (vectorCard F n) dist T E C B M
    hK hpMin hpMinHalf hθ (Nat.cast_nonneg _) hN
    (fun i => approximationNuclear_nonneg (G i)) hE0 hC0 hB0
    (fun i => approximationMass_le hn p i (G i))
    (fun i => approximateDensity_l2_step hn p θ compress i)
    (fun i => approximateDensity_nuclear_step p θ compress i)
    (fun i => approximateDensity_error_step hn p θ hθ compress i)
    (statisticalDistance_le_one _ _) hextract

/-- The exact elementary bound at θ=κ^(1/12), before the analytic adapter supplies its compression procedure. -/
-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); s, t ∈ F; T ∈ ℕ; compress ∈ CompressionProcedure(F, n, Z, θ(F, n)), assume 2 ≤ n; s ≠ t. Then

δ(((Prod)₂_*rectangleExecution(p, μₛ, T)), ((Prod)₂_*rectangleExecution(p, μₜ, T))) ≤ min{securityBound(|Z|, minSecretProbability(F, n), θ(F, n), |F|, |F|ⁿ, T), 1}.
-/
theorem refresh_security_of_compression (hn : 2 ≤ n)
    (p : RectangleProtocol F n Z) (s t : F) (hst : s ≠ t) (T : ℕ)
    (compress : CompressionProcedure F n Z (theta F n)) :
    statisticalDistance
      ((rectangleExecution p (mu F n hn s) T).map Prod.snd)
      ((rectangleExecution p (mu F n hn t) T).map Prod.snd) ≤
      min (securityBound (Fintype.card Z) (minSecretProbability F n)
        (theta F n) (fieldCard F) (vectorCard F n) T) 1 :=
  security_of_compression hn p s t hst T (theta F n)
    (theta_pos hn).le compress

/-- The numeric upper bound is nonnegative, including the zero-round case. -/
-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K, pMin, θ, q, N ∈ ℝ; T ∈ ℕ, assume 0 ≤ K; 0 ≤ θ; 0 ≤ q. Then

0 ≤ securityBound(K, pMin, θ, q, N, T).
-/
theorem securityBound_nonneg (K pMin θ q N : ℝ) (T : ℕ)
    (hK : 0 ≤ K) (hθ : 0 ≤ θ) (hq : 0 ≤ q) :
    0 ≤ securityBound K pMin θ q N T := by
  unfold securityBound
  positivity

/-- Include equal secrets without weakening the experiment or its bound. -/
-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); s, t ∈ F; T ∈ ℕ; θ ∈ ℝ; compress ∈ CompressionProcedure(F, n, Z, θ), assume 2 ≤ n; 0 ≤ θ. Then

δ(((Prod)₂_*rectangleExecution(p, μₛ, T)), ((Prod)₂_*rectangleExecution(p, μₜ, T))) ≤ min{securityBound(|Z|, minSecretProbability(F, n), θ, |F|, |F|ⁿ, T), 1}.
-/
theorem security_of_compression_all (hn : 2 ≤ n) (p : RectangleProtocol F n Z)
    (s t : F) (T : ℕ) (θ : ℝ) (hθ : 0 ≤ θ)
    (compress : CompressionProcedure F n Z θ) :
    statisticalDistance
      ((rectangleExecution p (mu F n hn s) T).map Prod.snd)
      ((rectangleExecution p (mu F n hn t) T).map Prod.snd) ≤
      min (securityBound (Fintype.card Z) (minSecretProbability F n) θ (fieldCard F) (vectorCard F n) T) 1 := by
  by_cases hst : s = t
  · subst t
    rw [statisticalDistance_self]
    exact le_min (securityBound_nonneg _ _ _ _ _ _ (Nat.cast_nonneg _) hθ
      (Nat.cast_nonneg _)) (by norm_num)
  · exact security_of_compression hn p s t hst T θ hθ compress

/-- Specialize the all-secret theorem to the elementary mixing root. -/
-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); s, t ∈ F; T ∈ ℕ; compress ∈ CompressionProcedure(F, n, Z, θ(F, n)), assume 2 ≤ n. Then

δ(((Prod)₂_*rectangleExecution(p, μₛ, T)), ((Prod)₂_*rectangleExecution(p, μₜ, T))) ≤ min{securityBound(|Z|, minSecretProbability(F, n), θ(F, n), |F|, |F|ⁿ, T), 1}.
-/
theorem refresh_security_of_compression_all (hn : 2 ≤ n)
    (p : RectangleProtocol F n Z) (s t : F) (T : ℕ)
    (compress : CompressionProcedure F n Z (theta F n)) :
    statisticalDistance
      ((rectangleExecution p (mu F n hn s) T).map Prod.snd)
      ((rectangleExecution p (mu F n hn t) T).map Prod.snd) ≤
      min (securityBound (Fintype.card Z) (minSecretProbability F n)
        (theta F n) (fieldCard F) (vectorCard F n) T) 1 :=
  security_of_compression_all hn p s t T (theta F n) (theta_pos hn).le compress

omit [Nonempty Z] in
/-- Before any round the public transcript is empty for all initial distributions. -/
-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); initial, other ∈ 𝒟(State(F, n)), we have

δ(((Prod)₂_*rectangleExecution(p, initial, 0)), ((Prod)₂_*rectangleExecution(p, other, 0))) = 0.
-/
theorem rectangleExecution_zero_distance (p : RectangleProtocol F n Z)
    (initial other : FiniteDistribution (State F n)) :
    statisticalDistance ((rectangleExecution p initial 0).map Prod.snd)
      ((rectangleExecution p other 0).map Prod.snd) = 0 := by
  have h := FiniteDistribution.eq_of_subsingleton ((rectangleExecution p initial 0).map Prod.snd)
    ((rectangleExecution p other 0).map Prod.snd)
  rw [h, statisticalDistance_self]

end

end TableAnalysis.EnergyCompression
