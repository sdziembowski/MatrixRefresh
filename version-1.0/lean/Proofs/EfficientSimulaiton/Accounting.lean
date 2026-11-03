import Proofs.EfficientSimulaiton.Model
import Proofs.EfficientSimulaiton.Sampling.SamplerPMFCost

/-!
# Work accounting for the same visible simulation

Adding a private work counter leaves the complete visible distribution unchanged. Nonnegative extended-real expectations satisfy 𝔼[W+A] = 𝔼[W] + 𝔼[A], even when the additional work depends on hidden sampler tapes or has infinite expectation. Consequently the proved sampler budget W gives relative runtime W+cR when each of the c local-answer evaluations is charged R, and gives W+𝔼[A] for an arbitrary joint accounting of actual additional computation.
-/

noncomputable section
open scoped ENNReal

namespace EfficientSimulationProof

open EfficientSimulation CircuitCompiler.Sampling.Unbounded

/-- Charging a private oracle-time budget preserves the full visible distribution: Distribution(view,W+calls·R) projects to Distribution(view). -/
@[simp] theorem viewLaw_chargeOracleBudget {V : Type*} [Fintype V]
    (run : PMF (V × ℕ)) (calls R : ℕ) :
    viewLaw (chargeOracleBudget run calls R) = viewLaw run := by
  simp only [viewLaw, chargeOracleBudget, PMF.map_comp, Function.comp_def]

/-- A fixed charge adds its exact value to expected work: 𝔼[W+calls·R] = 𝔼[W]+calls·R. No finiteness assumption on 𝔼[W] is needed. -/
theorem expectedWork_chargeOracleBudget {V : Type*}
    (run : PMF (V × ℕ)) (calls R : ℕ) :
    expectedWork (chargeOracleBudget run calls R) =
      expectedWork run + (calls * R : ℕ) := by
  change workExpectation (chargeOracleBudget run calls R) (fun z => (z.2 : ℝ≥0∞)) =
    workExpectation run (fun z => (z.2 : ℝ≥0∞)) + (calls * R : ℕ)
  simp only [chargeOracleBudget, workExpectation_map,
    Nat.cast_add, workExpectation_add, workExpectation_const]

/-- Any correct joint accounting preserves the complete visible distribution, regardless of the additional counter's dependence on hidden randomness. -/
theorem viewLaw_totalRun {V : Type*} [Fintype V] (run : PMF (V × ℕ))
    (accounting : AccountingLaw V) (haccounting : AccountsFor run accounting) :
    viewLaw (totalRun accounting) = viewLaw run := by
  change accounting.map Prod.fst = run at haccounting
  unfold viewLaw
  have hmarginal : (totalRun accounting).map Prod.fst = run.map Prod.fst := by
    calc
      _ = (accounting.map Prod.fst).map Prod.fst := by
        simp only [totalRun, PMF.map_comp, Function.comp_def]
      _ = _ := by rw [haccounting]
  rw [hmarginal]

/-- Correct joint accounting gives the exact total expectation 𝔼[W+A] = 𝔼[W]+𝔼[A]. Both sides may be infinite, and no independence assumption is made. -/
theorem expectedWork_totalRun {V : Type*} (run : PMF (V × ℕ))
    (accounting : AccountingLaw V) (haccounting : AccountsFor run accounting) :
    expectedWork (totalRun accounting) =
      expectedWork run + additionalExpectedWork accounting := by
  change accounting.map Prod.fst = run at haccounting
  change workExpectation (totalRun accounting) (fun z => (z.2 : ℝ≥0∞)) =
    workExpectation run (fun z => (z.2 : ℝ≥0∞)) +
      workExpectation accounting (fun z => (z.2 : ℝ≥0∞))
  calc
    _ = workExpectation accounting (fun z => (z.1.2 : ℝ≥0∞)) +
        workExpectation accounting (fun z => (z.2 : ℝ≥0∞)) := by
      simp only [totalRun, workExpectation_map, Nat.cast_add, workExpectation_add]
    _ = workExpectation (accounting.map Prod.fst) (fun z => (z.2 : ℝ≥0∞)) +
        workExpectation accounting (fun z => (z.2 : ℝ≥0∞)) := by
      simp only [workExpectation_map]
    _ = _ := by rw [haccounting]

/-- An arbitrary accounting of actual extra computation adds at most its own expectation to the proved sampler budget: 𝔼[total] ≤ W+𝔼[A]. -/
theorem totalRun_expected_le {V : Type*} (run : PMF (V × ℕ))
    (accounting : AccountingLaw V) (haccounting : AccountsFor run accounting)
    {W : ℝ≥0∞} (hwork : expectedWork run ≤ W) :
    expectedWork (totalRun accounting) ≤ W + additionalExpectedWork accounting := by
  rw [expectedWork_totalRun run accounting haccounting]
  exact add_le_add hwork le_rfl

end EfficientSimulationProof
