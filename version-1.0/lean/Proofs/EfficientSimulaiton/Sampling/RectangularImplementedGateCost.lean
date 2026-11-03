import Proofs.EfficientSimulaiton.Sampling.AugmentedEncodingCost
import Proofs.EfficientSimulaiton.Sampling.MatrixTapeCost
import Proofs.EfficientSimulaiton.Sampling.RectangularCostedGate
import Proofs.EfficientSimulaiton.Sampling.RectangularTapeCost
import Proofs.Compiler.Construction.Parameters



/-!
# Polynomial expected work for the exact implemented gate

The cost counter charges all random field coordinates, Gaussian tests and solves, refresh multiplications, tensor-feature products, and shortening work. It is attached to the same PMF whose output marginal is used in the security theorem; it is not a bound for a separate primitive-oracle implementation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2500000

open scoped ENNReal Classical

namespace CircuitCompiler.Rectangular.FullyTapedStrategy

open Refresh MatrixRefresh TableAnalysis Shortening RefreshAnalysis

open Composition Composition.TopologicalExecution Sampling Sampling.Unbounded

noncomputable section

variable {F ML MR BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
  {n t inputs : ℕ} {hdim : n*n+1 = n+t}

/-- A tower bound for the actual dependent nested sampler. Only the work counters, rather than the output or leakage distributions, are abstract here. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ FullyTapedStrategy(F, ML, MR, BL, BR, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → (ML × MR) × (BL × BR); left, right ∈ State(F, n); matrixWork ∈ StoppedTape(F^({0,…,(n + t)−1} × {0,…,(n + t)−1})) → ℕ; shorteningWork ∈ ∏_(u(v) ∈ U(F, (n + t))) MarkedTape(Attempt(n = n, u), Taped.Mark(F, n, (n + t))) → ℕ; matrixBound, shorteningBound ∈ ℝ ≥ 0∞, assume 2 ≤ n; workExpectation(distribution(FiniteDistribution.uniform, invertibleTest, matrixAcceptancePositive(F = F, (n + t))), ((z ↦ matrixWork(z)))) ≤ matrixBound; ∀ u, v, workExpectation(Taped.fullTapeDistribution(u, v), ((z ↦ shorteningWork(u, v, z)))) ≤ shorteningBound. Then

workExpectation(strategy.costedExecution(i, gate, history, left, right, matrixWork, shorteningWork), ((z ↦ (z)₂))) ≤ matrixBound + shorteningBound.
-/
theorem costedExecution_expected_le
    (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → (ML × MR) × (BL × BR)) (left right : State F n)
    (matrixWork : StoppedTape (Matrix (Fin (n+t)) (Fin (n+t)) F) → ℕ)
    (shorteningWork : (u v : U F (n+t)) →
      MarkedTape (Attempt (n := n) u) (Taped.Mark F n (n+t)) → ℕ)
    (matrixBound shorteningBound : ℝ≥0∞)
    (hm : workExpectation (distribution FiniteDistribution.uniform invertibleTest
      (matrixAcceptancePositive (F := F) (n+t))) (fun z => (matrixWork z : ℝ≥0∞)) ≤ matrixBound)
    (hs : ∀ u v, workExpectation (Taped.fullTapeDistribution hn u v)
      (fun z => (shorteningWork u v z : ℝ≥0∞)) ≤ shorteningBound) :
    workExpectation (strategy.costedExecution hn i gate history left right matrixWork shorteningWork)
      (fun z => (z.2 : ℝ≥0∞)) ≤ matrixBound+shorteningBound := by
  unfold costedExecution
  rw [workExpectation_bind]
  simp only [workExpectation_map,Taped.costedShorteningExecution,Nat.cast_add,
    workExpectation_add,workExpectation_const]
  refine add_le_add hm ?_
  apply (workExpectation_mono _ ?_).trans_eq (workExpectation_const _ shorteningBound)
  intro z
  exact hs _ _

/-- Exact physical gate PMF, now with its concrete scalar-operation counter. -/
/-
Mathematical definition (normal notation): For strategy ∈ FullyTapedStrategy(F, ML, MR, BL, BR, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → (ML × MR) × (BL × BR); left, right ∈ State(F, n), assume 2 ≤ n. define

implementedExecution(strategy, i, gate, history, left, right) := strategy.costedExecution(i, gate, history, left, right, implementedMatrixWork(hdim = hdim, gate, left, right), Taped.shorteningTotalWork).
-/
def implementedExecution (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → (ML × MR) × (BL × BR)) (left right : State F n) :=
  strategy.costedExecution hn i gate history left right
    (implementedMatrixWork (hdim := hdim) gate left right)
    Taped.shorteningTotalWork

/-- The concrete scalar counter has a polynomial expectation for every gate, input, history, and local leakage strategy. Random coordinate draws count as unit operations; arbitrary adversarial computations are oracle calls. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ FullyTapedStrategy(F, ML, MR, BL, BR, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → (ML × MR) × (BL × BR); left, right ∈ State(F, n), assume 2 ≤ n. Then

workExpectation(strategy.implementedExecution(i, gate, history, left, right), ((z ↦ (z)₂))) ≤ 100 · (n + t + 1)³.
-/
theorem implementedExecution_expected_le
    (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → (ML × MR) × (BL × BR)) (left right : State F n) :
    workExpectation (strategy.implementedExecution hn i gate history left right)
      (fun z => (z.2 : ℝ≥0∞)) ≤ 100*(n+t+1)^3 := by
  have hm : workExpectation (distribution FiniteDistribution.uniform invertibleTest
      (matrixAcceptancePositive (F := F) (n+t)))
      (fun z => (implementedMatrixWork (hdim := hdim) gate left right z : ℝ≥0∞)) ≤
      2*n*n+26*(n+t+1)^3 := by
    simp only [implementedMatrixWork,Gaussian.augmentedShareData_operations,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
      workExpectation_add,workExpectation_const]
    convert add_le_add_left (SamplerCost.matrixPhaseTotalWork_expected_le
      (augmentedLeftFeature hdim gate.kind.affineConstant (augmentedOldPorts left right).1).val
      (augmentedRightFeature hdim (augmentedOldPorts left right).2).val) (2*n*n) using 1 <;> (try simp only [Nat.cast_add]) <;> ring
  have h := strategy.costedExecution_expected_le hn i gate history left right
    (implementedMatrixWork (hdim := hdim) gate left right)
    Taped.shorteningTotalWork _ _ hm (Taped.shorteningTotalWork_expected_le hn)
  apply h.trans
  exact_mod_cast (show 2*n*n+26*(n+t+1)^3+64*(n+1)^2*(n+t+1) ≤ 100*(n+t+1)^3 by
    have hsmall : (n+1)^2*(n+t+1) ≤ (n+t+1)^3 := by
      have hpow : (n+1)^2 ≤ (n+t+1)^2 := Nat.pow_le_pow_left (by omega) 2
      simpa only [pow_succ] using Nat.mul_le_mul_right (n+t+1) hpow
    nlinarith)

/-- The expected-cost implementation has exactly the real gate marginal used by the checked security theorem. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ FullyTapedStrategy(F, ML, MR, BL, BR, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → (ML × MR) × (BL × BR); left, right ∈ State(F, n), assume 2 ≤ n. Then

((Prod)₁_*strategy.implementedExecution(i, gate, history, left, right)) = toPMF(real(strategy.protocol)(i, gate, history, left, right)) .
-/
theorem implementedExecution_forget_real
    (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → (ML × MR) × (BL × BR)) (left right : State F n) :
    (strategy.implementedExecution hn i gate history left right).map Prod.fst =
      toPMF ((strategy.protocol hn).real i gate history left right) :=
  strategy.costedExecution_forget_real hn i gate history left right _ _

end

end CircuitCompiler.Rectangular.FullyTapedStrategy
