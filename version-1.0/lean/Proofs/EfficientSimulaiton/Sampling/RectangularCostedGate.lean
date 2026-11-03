import Proofs.Compiler.GateApproximation.Shortening.RectangularFullyTapedProgram
import Proofs.Compiler.Construction.Parameters



/-!
# Work counters on the actual complete gate execution

The costed experiment executes the same raw matrix, nonzero-row, completion, and outer rejection tapes as the concrete security theorem. Forgetting its cost counter is proved to give exactly that theorem's physical gate distribution. Costs may count any specified operations on these traces; no complexity bound is assumed by the marginal identities in this module.
-/
set_option autoImplicit false

set_option maxHeartbeats 2200000

open scoped Classical

namespace CircuitCompiler.Rectangular

open Refresh MatrixRefresh TableAnalysis Shortening RefreshAnalysis

open Composition Composition.TopologicalExecution Sampling Sampling.Unbounded

noncomputable section

variable {F O A BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [Fintype A] [Fintype BL] [Fintype BR] {n t : ℕ}

namespace Taped

/-- The counter retains exactly the same raw shortening execution. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F; fallback ∈ Fiber(F, n, s); left ∈ A → O → ∏_(u ∈ U(F, (n + t))) StoppedTape(AttemptSampler.Record(n = n, u)) → BL; right ∈ A → O → U(F, (n + t)) → RightView(F, n, (n + t)) → BR; o ∈ O × O; x ∈ Fiber(F, (n + t), s); α ∈ A; work ∈ MarkedTape(Attempt(n = n, x.val.L), Mark(F, n, (n + t))) → ℕ, assume 2 ≤ n. Then

((Prod)₁_*costedShorteningExecution(fallback, left, right, o, x, α, work)) = toPMF(rawShorteningExecution(fallback, left, right, o, x, α)).
-/
theorem costedShorteningExecution_forget {s : F} (hn : 2 ≤ n) (fallback : Fiber F n s)
    (left : A → O → (u : U F (n+t)) → StoppedTape (AttemptSampler.Record (n := n) u) → BL)
    (right : A → O → U F (n+t) → RightView F n (n+t) → BR)
    (o : O × O) (x : Fiber F (n+t) s) (α : A)
    (work : MarkedTape (Attempt (n := n) x.val.L) (Mark F n (n+t)) → ℕ) :
    (costedShorteningExecution hn fallback left right o x α work).map Prod.fst =
      toPMF (rawShorteningExecution hn fallback left right o x α) := by
  unfold costedShorteningExecution rawShorteningExecution
  rw [PMF.map_comp,toPMF_toFinite]
  rfl

end Taped

namespace FullyTapedStrategy

variable {ML MR : Type*} [Fintype ML] [Fintype MR]

variable {inputs : ℕ} {hdim : n*n+1 = n+t}

/-- Forgetting the operation counter recovers exactly the raw implementation. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ FullyTapedStrategy(F, ML, MR, BL, BR, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → (ML × MR) × (BL × BR); left, right ∈ State(F, n); matrixWork ∈ StoppedTape(F^({0,…,(n + t)−1} × {0,…,(n + t)−1})) → ℕ; shorteningWork ∈ ∏_(u(v) ∈ U(F, (n + t))) MarkedTape(Attempt(n = n, u), Taped.Mark(F, n, (n + t))) → ℕ, assume 2 ≤ n. Then

((Prod)₁_*strategy.costedExecution(i, gate, history, left, right, matrixWork, shorteningWork)) = toPMF(strategy.rawExecution(i, gate, history, left, right)).
-/
theorem costedExecution_forget (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → (ML × MR) × (BL × BR)) (left right : State F n)
    (matrixWork : StoppedTape (Matrix (Fin (n+t)) (Fin (n+t)) F) → ℕ)
    (shorteningWork : (u v : U F (n+t)) →
      MarkedTape (Attempt (n := n) u) (Taped.Mark F n (n+t)) → ℕ) :
    (strategy.costedExecution hn i gate history left right matrixWork shorteningWork).map Prod.fst =
      toPMF (strategy.rawExecution hn i gate history left right) := by
  unfold costedExecution rawExecution rawMatrixExecution observe
  rw [toPMF_map,toPMF_bind,toPMF_toFinite,PMF.bind_map,PMF.map_bind,PMF.map_bind]
  dsimp only
  congr 1
  funext matrixTape
  rw [PMF.map_comp]
  have h := Taped.costedShorteningExecution_forget hn
    (TapedAugmentedStrategy.fallback (hdim := hdim) hn gate left right)
    (strategy.left i gate history) (strategy.right i gate history) (augmentedOldPorts left right)
    (refreshInFiber (gateInput (augmentedLeftFeature hdim gate.kind.affineConstant)
      (augmentedRightFeature hdim) (augmentedOldPorts left right)) (matrixReturned matrixTape.2.2))
    (strategy.matrixLeft i gate history (augmentedOldPorts left right).1 matrixTape,
      strategy.matrixRight i gate history (augmentedOldPorts left right).2 matrixTape)
    (shorteningWork _ (refreshInFiber (gateInput
      (augmentedLeftFeature hdim gate.kind.affineConstant) (augmentedRightFeature hdim)
      (augmentedOldPorts left right)) (matrixReturned matrixTape.2.2)).val.R)
  simpa only [PMF.map_comp,Function.comp_def] using
    congrArg (fun P => P.map (fun z => (z.1.val,z.2))) h

/-- The runtime theorem and security theorem refer to the very same real gate. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ FullyTapedStrategy(F, ML, MR, BL, BR, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → (ML × MR) × (BL × BR); left, right ∈ State(F, n); matrixWork ∈ StoppedTape(F^({0,…,(n + t)−1} × {0,…,(n + t)−1})) → ℕ; shorteningWork ∈ ∏_(u(v) ∈ U(F, (n + t))) MarkedTape(Attempt(n = n, u), Taped.Mark(F, n, (n + t))) → ℕ, assume 2 ≤ n. Then

((Prod)₁_*strategy.costedExecution(i, gate, history, left, right, matrixWork, shorteningWork)) = toPMF(real(strategy.protocol)(i, gate, history, left, right)) .
-/
theorem costedExecution_forget_real (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → (ML × MR) × (BL × BR)) (left right : State F n)
    (matrixWork : StoppedTape (Matrix (Fin (n+t)) (Fin (n+t)) F) → ℕ)
    (shorteningWork : (u v : U F (n+t)) →
      MarkedTape (Attempt (n := n) u) (Taped.Mark F n (n+t)) → ℕ) :
    (strategy.costedExecution hn i gate history left right matrixWork shorteningWork).map Prod.fst =
      toPMF ((strategy.protocol hn).real i gate history left right) := by
  rw [strategy.real_eq_rawExecution]
  exact strategy.costedExecution_forget hn i gate history left right matrixWork shorteningWork

/-- Cost erasure is exact also for the representation used by composition. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ FullyTapedStrategy(F, ML, MR, BL, BR, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → (ML × MR) × (BL × BR); left, right ∈ U(F, n) × U(F, n); matrixWork ∈ StoppedTape(F^({0,…,(n + t)−1} × {0,…,(n + t)−1})) → ℕ; shorteningWork ∈ ∏_(u(v) ∈ U(F, (n + t))) MarkedTape(Attempt(n = n, u), Taped.Mark(F, n, (n + t))) → ℕ, assume 2 ≤ n. Then

((Prod)₁_*strategy.costedShareExecution(i, gate, history, left, right, matrixWork, shorteningWork)) = toPMF(real(strategy.shareProtocol)(i, gate, history, left, right)) .
-/
theorem costedShareExecution_forget_real
    (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → (ML × MR) × (BL × BR)) (left right : U F n × U F n)
    (matrixWork : StoppedTape (Matrix (Fin (n+t)) (Fin (n+t)) F) → ℕ)
    (shorteningWork : (u v : U F (n+t)) →
      MarkedTape (Attempt (n := n) u) (Taped.Mark F n (n+t)) → ℕ) :
    (strategy.costedShareExecution hn i gate history left right matrixWork shorteningWork).map Prod.fst =
      toPMF ((strategy.shareProtocol hn).real i gate history left right) := by
  rw [strategy.share_real_eq_rawExecution,toPMF_map]
  unfold costedShareExecution
  have h := strategy.costedExecution_forget hn i gate history
    ((stateEquivProd F n).symm left) ((stateEquivProd F n).symm right) matrixWork shorteningWork
  simpa only [PMF.map_comp,Function.comp_def] using
    congrArg (fun P => P.map (fun z => (stateEquivProd F n z.1,z.2))) h

end FullyTapedStrategy

end

end CircuitCompiler.Rectangular
