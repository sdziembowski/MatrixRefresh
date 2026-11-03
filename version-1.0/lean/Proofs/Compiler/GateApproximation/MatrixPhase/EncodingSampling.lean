import Proofs.Compiler.GateApproximation.MatrixPhase.UniformSampling
import Proofs.Compiler.Construction.Parameters
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.EncodingMeasure



/-!
# Rejection sampling of nonzero shares and inner-product encodings

These bounds discharge the dimension-independent acceptance claims for the initialization samplers. They count proposals and finite sampling error; they do not identify field operations with machine instructions.
-/

set_option autoImplicit false

namespace CircuitCompiler.Sampling

open Refresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Expected proposal count of any capped encoding loop is at most `2q`. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F; attempts ∈ ℕ, assume 2 ≤ n; State(F, n) ≠ ∅. Then

𝔼_(tape ← tapeDistribution(𝒰_(State(F, n)), attempts)) [attemptsUsed(secretTest(s), attempts, tape)] ≤ 2 · |F|.
-/
theorem encoding_expected_attempts {n : ℕ} (hn : 2 ≤ n) [Nonempty (State F n)]
    (s : F) (attempts : ℕ) :
    (tapeDistribution (FiniteDistribution.uniform : FiniteDistribution (State F n)) attempts).expect
      (fun tape => (attemptsUsed (secretTest s) attempts tape : ℝ)) ≤ 2 * fieldCard F := by
  have hq := fieldCard_cast_pos (F := F)
  have hp : 0 < acceptance (FiniteDistribution.uniform : FiniteDistribution (State F n)) (secretTest s) :=
    lt_of_lt_of_le (by positivity) (secret_acceptance_ge hn s)
  have h := expected_attempts_le (FiniteDistribution.uniform : FiniteDistribution (State F n)) (secretTest s) hp attempts
  rw [secret_acceptance, inv_inv] at h
  exact h.trans (densityWeight_le_two_mul_q hn s)

/-- The accepted distribution is the paper's actual uniform encoding distribution `mu_s`. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, assume 2 ≤ n; State(F, n) ≠ ∅; 0 < acceptance(𝒰_(State(F, n)), secretTest(s)). Then

accepted(𝒰_(State(F, n)), secretTest(s)) = μₛ.
-/
theorem accepted_secret_eq_mu {n : ℕ} (hn : 2 ≤ n) [Nonempty (State F n)] (s : F)
    (hp : 0 < acceptance (FiniteDistribution.uniform : FiniteDistribution (State F n)) (secretTest s)) :
    accepted (FiniteDistribution.uniform : FiniteDistribution (State F n)) (secretTest s) hp = mu F n hn s := by
  have hd : (shareCard F n : ℝ) ≠ 0 := ne_of_gt (nonzeroCard_real_pos hn)
  ext state
  rw [mu_weight]
  simp only [accepted]
  rw [secret_acceptance]
  simp only [FiniteDistribution.uniform, state_card, secretTest,
    decide_eq_true_eq, densityWeight, Nat.cast_pow]
  by_cases hs : secret state = s
  · simp [hs, hd, div_eq_mul_inv]
  · simp [hs]

/-- Finite tape sampling of a prescribed encoding has the geometric error bound. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F; fallback ∈ State(F, n); attempts ∈ ℕ, assume 2 ≤ n; State(F, n) ≠ ∅. Then

δ((sample(secretTest(s), fallback, attempts)_*tapeDistribution(𝒰_(State(F, n)), attempts)), μₛ) ≤ (1 - ((2 · |F|))⁻¹)^attempts.
-/
theorem encoding_sample_distance {n : ℕ} (hn : 2 ≤ n) [Nonempty (State F n)] (s : F)
    (fallback : State F n) (attempts : ℕ) :
    statisticalDistance
      ((tapeDistribution (FiniteDistribution.uniform : FiniteDistribution (State F n)) attempts).map
        (sample (secretTest s) fallback attempts)) (mu F n hn s) ≤
      (1 - (2 * (fieldCard F : ℝ))⁻¹) ^ attempts := by
  have hq := fieldCard_cast_pos (F := F)
  have hp : 0 < acceptance (FiniteDistribution.uniform : FiniteDistribution (State F n)) (secretTest s) :=
    lt_of_lt_of_le (by positivity) (secret_acceptance_ge hn s)
  rw [← accepted_secret_eq_mu hn s hp, sample_distribution]
  exact capped_distance_le_of_acceptance _ _ _ (by positivity) (secret_acceptance_ge hn s) attempts

/-- A single cap works for vector, matrix, and encoding loops: `2q` is a constant when the field is fixed. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For calls, σ ∈ ℕ, we have

calls · (1 - ((2 · |F|))⁻¹)^(2 · |F| · (σ + Nat.clog(2, calls))) ≤ (1 / 2)^σ.
-/
theorem field_sampler_union_bound (calls σ : ℕ) :
    (calls : ℝ) * (1 - (2 * (fieldCard F : ℝ))⁻¹) ^
      (2 * fieldCard F * (σ + Nat.clog 2 calls)) ≤ (1 / 2 : ℝ) ^ σ := by
  have hq := fieldCard_cast_ge_two (F := F)
  apply geometric_tail_union (by positivity)
  · exact inv_le_one_of_one_le₀ (by linarith)
  · simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [mul_inv_cancel₀ (by positivity : (2 * (fieldCard F : ℝ)) ≠ 0)]

/-- In particular the total number of permitted proposals is polynomial in the security parameter and the number of loops. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For calls, σ ∈ ℕ, we have

calls · (2 · |F| · (σ + Nat.clog(2, calls))) ≤ 2 · |F| · calls · (σ + calls).
-/
theorem field_sampler_total_cap_le (calls σ : ℕ) :
    calls * (2 * fieldCard F * (σ + Nat.clog 2 calls)) ≤
      2 * fieldCard F * calls * (σ + calls) := by
  have hlog : Nat.clog 2 calls ≤ calls :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt calls.lt_two_pow_self)
  calc
    _ ≤ calls * (2 * fieldCard F * (σ + calls)) := by gcongr
    _ = _ := by ring

end CircuitCompiler.Sampling
