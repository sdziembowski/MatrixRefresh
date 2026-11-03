import Proofs.EfficientSimulaiton.Sampling.CostedRunner
import Proofs.EfficientSimulaiton.Sampling.RawEncodingInitializationCost
import Proofs.EfficientSimulaiton.Sampling.RectangularImplementedGateCost
import Proofs.Compiler.Construction.Parameters



/-!
# Expected polynomial work of the actual compiler and simulator

The costed execution uses the same raw sampling distributions as the security theorem. Its counter includes random field coordinates, field operations and zero tests in all rejected proposals. Leakage functions are oracle calls; their arbitrary computation is not charged. This is an expected sampling and scalar-operation counter bound, not a claim about extracted machine code or worst-case rejection-sampling time.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2600000

open scoped ENNReal

namespace CircuitCompiler.Rectangular.Implemented

open Refresh MatrixRefresh Composition Composition.TopologicalExecution
  Sampling Sampling.Unbounded

noncomputable section

variable {F ML MR BL BR V : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ML] [Nonempty ML] [Fintype MR] [Nonempty MR]
  [Fintype BL] [Nonempty BL] [Fintype BR] [Nonempty BR] [Fintype V]
  {n t inputs T k : ℕ} {hdim : n*n+1 = n+t}

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ FullyTapedStrategy(F, ML, MR, BL, BR, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → (ML × MR) × (BL × BR); left, right ∈ U(F, n) × U(F, n), assume 2 ≤ n. Then

toFinite(((Prod)₁_*costedGate(strategy, i, gate, history, left, right))) = real(protocol(strategy))(i, gate, history, left, right).
-/
theorem costedGate_marginal (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → (ML × MR) × (BL × BR)) (left right : U F n × U F n) :
    toFinite ((costedGate strategy hn i gate history left right).map Prod.fst) =
      (strategy.shareProtocol hn).real i gate history left right := by
  unfold costedGate
  rw [strategy.costedShareExecution_forget_real,toFinite_toPMF]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ FullyTapedStrategy(F, ML, MR, BL, BR, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → (ML × MR) × (BL × BR); left, right ∈ U(F, n) × U(F, n), assume 2 ≤ n. Then

workExpectation(costedGate(strategy, i, gate, history, left, right), ((z ↦ (z)₂))) ≤ 100 · (n + t + 1)³.
-/
theorem costedGate_expected_le (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → (ML × MR) × (BL × BR)) (left right : U F n × U F n) :
    workExpectation (costedGate strategy hn i gate history left right)
      (fun z => (z.2 : ℝ≥0∞)) ≤ 100*(n+t+1)^3 := by
  unfold costedGate FullyTapedStrategy.costedShareExecution
  rw [workExpectation_map]
  exact strategy.implementedExecution_expected_le hn i gate history
    ((stateEquivProd F n).symm left) ((stateEquivProd F n).symm right)

end
end CircuitCompiler.Rectangular.Implemented
