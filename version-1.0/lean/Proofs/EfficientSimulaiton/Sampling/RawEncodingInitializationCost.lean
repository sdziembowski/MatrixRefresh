import Proofs.Compiler.Foundations.Sampling.RawEncodingInitialization
import Proofs.EfficientSimulaiton.Sampling.SamplerPMFCost
import Proofs.Compiler.Construction.Parameters



/-!
# Counted input initialization

The returned encoding and its work counter are read from the same actual raw rejection tape. Work charges random field coordinates and the explicit zero tests, dot products, and target comparison. The finite expectation is proved in extended nonnegative reals.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators ENNReal

namespace CircuitCompiler.Sampling.RawEncoding

open Refresh MatrixRefresh Unbounded Composition

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F; x ∈ Raw(F, n), we have

proposalWork(s, x) ≤ 6 · n + 1.
-/
theorem proposalWork_le {n : ℕ} (s : F) (x : Raw F n) : proposalWork s x ≤ 6*n+1 := by
  have h := proposal_operations_le s x
  unfold proposalWork
  omega

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, assume 2 ≤ n. Then

((Prod)₁_*sampleCosted(s)) = toPMF(μₛ).
-/
theorem sampleCosted_marginal {n : ℕ} (hn : 2 ≤ n) (s : F) :
    (sampleCosted hn s).map Prod.fst = toPMF (mu F n hn s) := by
  rw [sampleCosted,PMF.map_comp]
  exact returned_mu hn s

/-- Uniform inverse-acceptance bound used by the actual work estimate. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, assume 2 ≤ n. Then

1 / acceptance(𝒰_(Raw(F, n)), accept(s)) ≤ 8 · |F|.
-/
theorem inverse_acceptance_le {n : ℕ} (hn : 2 ≤ n) (s : F) :
    1 / acceptance (FiniteDistribution.uniform : FiniteDistribution (Raw F n)) (accept s) ≤ 8*(fieldCard F:ℝ) := by
  apply (div_le_iff₀ (acceptance_pos hn s)).mpr
  have hb := acceptance_ge hn s
  have hq := fieldCard_cast_pos (F := F)
  have hm := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ 8*(fieldCard F:ℝ))
  have he : (8*(fieldCard F:ℝ))⁻¹ * (8*(fieldCard F:ℝ)) = 1 := inv_mul_cancel₀ (by positivity)
  rw [he] at hm
  simpa [mul_comm] using hm

/-- Actual expected sampling and arithmetic work, with no retry cap. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, assume 2 ≤ n. Then

workExpectation(sampleCosted(s), ((result ↦ (result)₂))) ≤ 8 · |F| · (6 · n + 1).
-/
theorem sampleCosted_work_le {n : ℕ} (hn : 2 ≤ n) (s : F) :
    workExpectation (sampleCosted hn s) (fun result => (result.2 : ℝ≥0∞)) ≤
      (8*fieldCard F*(6*n+1):ℕ) := by
  rw [sampleCosted,workExpectation_map]
  simp only [traceNatWork_cast]
  have h := workExpectation_trace_le (FiniteDistribution.uniform : FiniteDistribution (Raw F n)) (accept s)
    (acceptance_pos hn s) (fun x => (proposalWork s x : ℝ≥0∞)) (6*n+1:ℕ)
    (fun x => by exact_mod_cast proposalWork_le s x)
  apply h.trans
  have hp : ENNReal.ofReal (1/acceptance (FiniteDistribution.uniform : FiniteDistribution (Raw F n)) (accept s)) ≤
      (8*fieldCard F:ℕ) := by
    simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 8),ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat,
      Nat.cast_mul,Nat.cast_ofNat] using ENNReal.ofReal_le_ofReal (inverse_acceptance_le hn s)
  simpa only [Nat.cast_mul] using mul_le_mul hp (le_refl ((6*n+1:ℕ):ℝ≥0∞)) (by positivity) (by positivity)

/-- Erasing counters recovers exactly the raw initializer used for security. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, inputs ∈ ℕ; input ∈ {0,…,inputs-1} → F, assume 2 ≤ n. Then

((Prod)₁_*initializeCosted(input)) = initializeWires(input).
-/
theorem initializeCosted_marginal {n inputs : ℕ} (hn : 2 ≤ n) (input : Fin inputs → F) :
    (initializeCosted hn input).map Prod.fst = initializeWires hn input := by
  induction inputs with
  | zero => simp only [initializeCosted,initializeWires,PMF.pure_map]
  | succ k ih =>
      simp only [initializeCosted,PMF.map_bind,PMF.map_comp,Function.comp_def]
      rw [initializeWires,← ih]
      simp only [PMF.bind_map,Function.comp_def,sampleCosted,PMF.map_comp]

/-- Input initialization contributes work linear in the number of inputs. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, inputs ∈ ℕ; input ∈ {0,…,inputs-1} → F, assume 2 ≤ n. Then

workExpectation(initializeCosted(input), ((result ↦ (result)₂))) ≤ inputs · (8 · |F| · (6 · n + 1)) .
-/
theorem initializeCosted_work_le {n inputs : ℕ} (hn : 2 ≤ n) (input : Fin inputs → F) :
    workExpectation (initializeCosted hn input) (fun result => (result.2 : ℝ≥0∞)) ≤
      (inputs*(8*fieldCard F*(6*n+1)):ℕ) := by
  induction inputs with
  | zero => simp [initializeCosted]
  | succ k ih =>
      simp only [initializeCosted,workExpectation_bind,workExpectation_map,Nat.cast_add]
      simp_rw [workExpectation_add,workExpectation_const]
      have hlast := workExpectation_mono (initializeCosted hn (Fin.init input))
        (fun _ => sampleCosted_work_le hn (input (Fin.last k)))
      simp only [workExpectation_const] at hlast
      have hsum := add_le_add (ih (Fin.init input)) hlast
      simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hsum

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, inputs ∈ ℕ; input ∈ {0,…,inputs-1} → F, assume 2 ≤ n. Then

((Prod)₁_*initializeSharesCosted(input)) = initializeShares(input).
-/
theorem initializeSharesCosted_marginal {n inputs : ℕ} (hn : 2 ≤ n) (input : Fin inputs → F) :
    (initializeSharesCosted hn input).map Prod.fst = initializeShares hn input := by
  rw [initializeSharesCosted,PMF.map_comp,initializeShares,← initializeCosted_marginal hn input,
    PMF.map_comp]
  rfl

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, inputs ∈ ℕ; input ∈ {0,…,inputs-1} → F, assume 2 ≤ n. Then

workExpectation(initializeSharesCosted(input), ((result ↦ (result)₂))) ≤ inputs · (8 · |F| · (6 · n + 1)) .
-/
theorem initializeSharesCosted_work_le {n inputs : ℕ} (hn : 2 ≤ n) (input : Fin inputs → F) :
    workExpectation (initializeSharesCosted hn input) (fun result => (result.2 : ℝ≥0∞)) ≤
      (inputs*(8*fieldCard F*(6*n+1)):ℕ) := by
  rw [initializeSharesCosted,workExpectation_map]
  exact initializeCosted_work_le hn input

end

end CircuitCompiler.Sampling.RawEncoding
