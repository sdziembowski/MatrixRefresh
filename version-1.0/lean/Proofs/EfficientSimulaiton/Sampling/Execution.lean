import Proofs.EfficientSimulaiton.Model
import Proofs.Compiler.Simulation.RawGates
import Proofs.EfficientSimulaiton.Sampling.ProtectedGate
import Proofs.EfficientSimulaiton.Sampling.MatrixTapeCost

/-!
# Counted execution of the actual mixed operations

Every marginal below is obtained by forgetting a counter attached to the actual sampler. The common polynomial bound is uniform in the preceding state and history; no independence of running times or leakage answers is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open scoped BigOperators ENNReal Classical

namespace CircuitCompiler.Operations.Counted

open Refresh MatrixRefresh Sampling Sampling.Unbounded
  _root_.CircuitCompiler.Composition _root_.CircuitCompiler.Composition.TopologicalExecution

variable {F ML MR BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ML] [Nonempty ML] [Fintype MR] [Nonempty MR]
  [Fintype BL] [Nonempty BL] [Fintype BR] [Nonempty BR]
  {n t inputs S : ℕ} {hdim : n*n+1 = n+t}

/-- Counter erasure is exact for the two-phase computation, one-phase refresh, and direct public sampler, including every rejected proposal. -/
theorem instruction_marginal
    (strategy : Operations.Strategy F ML MR BL BR n t inputs hdim) (hn : 2 ≤ n)
    (i : ℕ) (instruction : Instruction F (inputs+i)) (history : Fin i → Operations.Answer ML MR BL BR)
    (old : Fin (inputs+i) → U F n × U F n) :
    toFinite ((instructionExecution strategy hn i instruction history old).map Prod.fst) =
      (strategy.protocol hn).real i instruction history old := by
  cases instruction with
  | compute gate =>
    have h := Rectangular.Implemented.costedGate_marginal strategy.compute hn i gate history
      (old gate.left) (old gate.right)
    rw [Rectangular.FullyTapedStrategy.share_real_eq_rawExecution,
      Rectangular.FullyTapedStrategy.rawExecution_eq_direct] at h
    exact h
  | refresh port =>
    simp only [instructionExecution,refreshExecution,Operations.Strategy.protocol,
      Operations.Strategy.refreshExecution,PMF.map_comp,Function.comp_def]
  | sample value =>
    simp only [instructionExecution,publicExecution,Operations.Strategy.protocol,
      Operations.Strategy.publicExecution,PMF.map_comp,Function.comp_def]

omit [Nonempty ML] [Nonempty MR] [Nonempty BL] [Nonempty BR] in
/-- Square refresh work is bounded uniformly in both old shares. -/
theorem refresh_expected_le
    (strategy : Operations.Strategy F ML MR BL BR n t inputs hdim)
    (i : ℕ) (port : Fin (inputs+i)) (history : Fin i → Operations.Answer ML MR BL BR)
    (old : U F n × U F n) :
    workExpectation (refreshExecution strategy i port history old) (fun z => (z.2 : ℝ≥0∞)) ≤
      26*(n+1)^3 := by
  rw [refreshExecution,workExpectation_map]
  exact Rectangular.SamplerCost.matrixPhaseTotalWork_expected_le old.1.val old.2.val

omit [Nonempty ML] [Nonempty MR] [Nonempty BL] [Nonempty BR] in
/-- Direct public sampling has the same actual raw-pair work as trusted initialization; its extra leakage callbacks do not change the sampler. -/
theorem public_expected_le
    (strategy : Operations.Strategy F ML MR BL BR n t inputs hdim) (hn : 2 ≤ n)
    (i : ℕ) (value : F) (history : Fin i → Operations.Answer ML MR BL BR) :
    workExpectation (publicExecution strategy hn i value history) (fun z => (z.2 : ℝ≥0∞)) ≤
      (8*fieldCard F*(6*n+1) : ℕ) := by
  rw [publicExecution,workExpectation_map]
  have h := RawEncoding.sampleCosted_work_le hn value
  rw [RawEncoding.sampleCosted,workExpectation_map] at h
  exact h

/-- One polynomial dominates each active operation, including every inner and outer retry. It applies on every state, not only a canonical supported state. -/
theorem instruction_expected_le
    (strategy : Operations.Strategy F ML MR BL BR n t inputs hdim)
    (hq : fieldCard F = 2) (hn : 2 ≤ n) (i : ℕ)
    (instruction : Instruction F (inputs+i)) (history : Fin i → Operations.Answer ML MR BL BR)
    (old : Fin (inputs+i) → U F n × U F n) :
    workExpectation (instructionExecution strategy hn i instruction history old)
      (fun z => (z.2 : ℝ≥0∞)) ≤ (100*(n*n+2)^3 : ℕ) := by
  cases instruction with
  | compute gate =>
    have h := Rectangular.Implemented.costedGate_expected_le strategy.compute hn i gate history
      (old gate.left) (old gate.right)
    have hd : n+t+1=n*n+2 := by omega
    have hd' : (n:ℝ≥0∞)+t+1 = (n:ℝ≥0∞)*n+2 := by exact_mod_cast hd
    simpa only [instructionExecution,hd',Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat] using h
  | refresh port =>
    apply (refresh_expected_le strategy i port history (old port)).trans
    have hdim : n+1≤n*n+2 := by nlinarith
    have hp := Nat.pow_le_pow_left hdim 3
    have hc : 26*(n+1)^3≤100*(n*n+2)^3 := by nlinarith
    exact_mod_cast hc
  | sample value =>
    apply (public_expected_le strategy hn i value history).trans
    rw [hq]
    have hlinear : 8*2*(6*n+1)≤100*(n*n+2) := by nlinarith
    have hpower : n*n+2≤(n*n+2)^3 := by
      calc
        _ = (n*n+2)^1 := by simp
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    exact_mod_cast hlinear.trans (Nat.mul_le_mul_left 100 hpower)

/-- Counter erasure commutes with every chronological append. -/
theorem runner_erase
    (strategy : Operations.Strategy F ML MR BL BR n t inputs hdim) (hn : 2 ≤ n)
    (program : Operations.Program F inputs S) :
    (runner strategy hn program).erase = (strategy.protocol hn).realRunner program := by
  induction program with
  | nil => rfl
  | @snoc S prior instruction ih =>
    simp only [runner,CostedRunner.erase,Operations.Protocol.realRunner,ih]
    congr 1
    funext state
    exact instruction_marginal strategy hn S instruction state.2 state.1

/-- Exact full-state marginal of actual initialization and mixed execution. -/
theorem execution_marginal (program : Operations.Program F inputs S)
    (strategy : Operations.Strategy F ML MR BL BR n t inputs hdim) (hn : 2 ≤ n)
    (input : Fin inputs → F) :
    (execution program strategy hn input).map Prod.fst =
      toPMF (((strategy.protocol hn).realRunner program).execute
        (toFinite (RawEncoding.initializeShares hn input))) := by
  rw [execution,CostedRunner.execute_erase,runner_erase,RawEncoding.initializeSharesCosted_marginal]

/-- Actual initialization and all operations have a uniform polynomial expected sampling and scalar-operation counter bound. No retry cap is required for this expectation. -/
theorem execution_expected_le (program : Operations.Program F inputs S)
    (strategy : Operations.Strategy F ML MR BL BR n t inputs hdim)
    (hq : fieldCard F = 2) (hn : 2 ≤ n) (input : Fin inputs → F) :
    workExpectation (execution program strategy hn input) (fun z => (z.2 : ℝ≥0∞)) ≤
      (inputs*(16*(6*n+1))+S*(100*(n*n+2)^3) : ℕ) := by
  have hb : (runner strategy hn program).Bounded ((100*(n*n+2)^3 : ℕ) : ℝ≥0∞) := by
    induction program with
    | nil => trivial
    | @snoc S prior instruction ih =>
      exact ⟨ih,fun state => instruction_expected_le strategy hq hn S instruction state.2 state.1⟩
  have h := CostedRunner.execute_work_le (RawEncoding.initializeSharesCosted hn input)
    (runner strategy hn program) _ hb
  apply h.trans
  have hi := RawEncoding.initializeSharesCosted_work_le hn input
  rw [hq] at hi
  simpa only [show (8:ℕ)*2=16 by norm_num,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,
    Nat.cast_ofNat] using add_le_add hi (le_refl ((S:ℝ≥0∞)*(100*(n*n+2)^3)))

end CircuitCompiler.Operations.Counted
