import Proofs.Compiler.Operations.Model
import Proofs.Compiler.GateApproximation.FullRetry
import Proofs.Compiler.GateApproximation.Refreshing.LocalApproximation
import Proofs.Compiler.GateApproximation.MatrixPhase.MatrixSamplerTapes
import Proofs.Compiler.Simulation.RawGates
import Proofs.Compiler.Foundations.Sampling.RawEncodingInitialization

/-!
# Exact distributions of computation, refresh, and public sampling

The computation case uses the existing full-retry H-shortening theorem. The refresh case is the actual shared square-matrix action. Public sampling uses its complete raw-pair rejection tape. In each case the new encoding is fresh before conditioning on the current answers; those answers may correlate arbitrarily with it and are retained by exact disintegration.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.Operations

open Refresh MatrixRefresh TableAnalysis CircuitCompiler CircuitCompiler.Operations
  CircuitCompiler.Sampling CircuitCompiler.Sampling.Unbounded
  CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution

/-- Forgetting a conditional answer leaves the original marginal. -/
theorem joint_first {X A : Type*} [Fintype X] [Fintype A]
    (P : FiniteDistribution X) (Q : X → FiniteDistribution A) :
    (P.joint Q).map Prod.fst = P := by
  ext x
  simp only [FiniteDistribution.map,FiniteDistribution.bind,FiniteDistribution.pure,
    FiniteDistribution.joint,Fintype.sum_prod_type]
  simp only [mul_ite,mul_one,mul_zero]
  rw [Finset.sum_eq_single x]
  · simp only [ite_true]
    rw [← Finset.mul_sum,(Q x).total,mul_one]
  · intro y _ hy
    simp [Ne.symm hy]
  · intro hx
    exact False.elim (hx (Finset.mem_univ x))

/-- A bijective output-coordinate change preserves the full joint distribution. -/
theorem joint_equiv {X Y A : Type*} [Fintype X] [Fintype Y] [Fintype A]
    (P : FiniteDistribution X) (Q : X → FiniteDistribution A) (e : X ≃ Y) :
    (P.joint Q).map (fun z => (e z.1,z.2)) =
      (P.map e).joint (fun y => Q (e.symm y)) := by
  ext ⟨y,a⟩
  change ((P.joint Q).map (e.prodCongr (Equiv.refl A))).weight (y,a) = _
  rw [FiniteDistribution.map_equiv_weight]
  change P.weight (e.symm y)*(Q (e.symm y)).weight a =
    (P.map e).weight y*(Q (e.symm y)).weight a
  rw [FiniteDistribution.map_equiv_weight]

/-- At a positive-mass output, the conditional of a normalized joint distribution is its specified conditional answer, rather than an independent-answer claim. -/
theorem answer_joint {X A : Type*} [Fintype X] [DecidableEq X] [Fintype A]
    (P : FiniteDistribution X) (Q : X → FiniteDistribution A) (x : X)
    (hx : 0 < P.weight x) : Canonical.answer (P.joint Q) x = Q x := by
  ext a
  rw [Canonical.answer_weight _ _ _ (by rw [joint_first]; exact hx),joint_first]
  change P.weight x*(Q x).weight a/P.weight x = _
  exact mul_div_cancel_left₀ _ (ne_of_gt hx)

/-- The actual physical conditional answer always gives exact disintegration. -/
theorem protocol_joint {F E A : Type*} [Fintype E] [DecidableEq E] [Fintype A]
    {inputs : ℕ} (protocol : Operations.Protocol F E A inputs) (i : ℕ)
    (instruction : Instruction F (inputs+i)) (history : Fin i → A)
    (old : Fin (inputs+i) → E) :
    protocol.real i instruction history old =
      ((protocol.real i instruction history old).map Prod.fst).joint
        (protocol.answer i instruction history old) :=
  (Canonical.disintegration _).symm

variable {F ML MR BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
  {n t inputs : ℕ} {hdim : n*n+1 = n+t}

/-- The fixed-prefix refresh has the exact ordinary square-refresh canonical distribution, retaining the answer of its matrix-dependent rectangle. -/
theorem fixed_refresh_joint
    (strategy : Operations.FixedStrategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (port : Fin (inputs+i))
    (history : Fin i → Operations.Answer ML MR BL BR)
    (old : Fin (inputs+i) → U F n × U F n) :
    (strategy.protocol hn).real i (.refresh port) history old =
      (encodingDistribution hn (secret ((stateEquivProd F n).symm (old port)))).joint
        (fun output => RefreshAnalysis.answerDistribution id id
          (strategy.refresh i port history) (old port).1 (old port).2
          ((stateEquivProd F n).symm output)) := by
  letI : Nonempty (U F n) := ⟨(old port).1⟩
  have h := congrArg (fun P : FiniteDistribution (State F n × Operations.Answer ML MR BL BR) =>
    P.map (fun z => (stateEquivProd F n z.1,z.2)))
    (RefreshAnalysis.feature_execution_eq_canonical hn (id : U F n → U F n) id
      (strategy.refresh i port history) (old port).1 (old port).2)
  rw [joint_equiv] at h
  simpa only [Operations.FixedStrategy.protocol,FiniteDistribution.map_map,Function.comp_def,
    encodingDistribution,mu,RefreshAnalysis.refreshedEncoding,id_eq,
    secret,stateLeftShare,stateRightShare,refresh,stateEquivProd,
    Equiv.coe_fn_mk,Equiv.coe_fn_symm_mk] using h

/-- A direct public sampler returns the exact uniform encoding of its fixed public value, even though its own leakage can reveal both output shares. -/
theorem public_output_uniform
    (left : (i : ℕ) → F → (Fin i → Operations.Answer ML MR BL BR) → Operations.PublicTape F n → ML × BL)
    (right : (i : ℕ) → F → (Fin i → Operations.Answer ML MR BL BR) → U F n → MR × BR)
    (hn : 2 ≤ n) (i : ℕ) (value : F) (history : Fin i → Operations.Answer ML MR BL BR) :
    (toFinite ((RawEncoding.tapeDistribution hn value).map fun tape =>
      let output := (RawEncoding.returned hn value tape.2.2).val
      ((output.L,output.R),answerRegroup ML MR BL BR
        (left i value history tape,right i value history output.R)))).map Prod.fst =
      encodingDistribution hn value := by
  rw [← toFinite_map]
  simp only [PMF.map_comp,Function.comp_def]
  have h := congrArg (fun P : PMF (State F n) => P.map (stateEquivProd F n))
    (RawEncoding.returned_mu hn value)
  rw [PMF.map_comp,← toPMF_map] at h
  simpa only [Function.comp_def,stateEquivProd,stateLeftShare,stateRightShare,
    Equiv.coe_fn_mk,toFinite_toPMF,encodingDistribution,mu] using
    congrArg toFinite h

/-- Every fixed-prefix instruction has an exactly fresh output encoding for all incoming histories and operand encodings. This includes public samplers. -/
theorem fixed_output_uniform
    (strategy : Operations.FixedStrategy F ML MR BL BR n t inputs hdim)
    (hq : fieldCard F = 2) (hn : 2 ≤ n) (i : ℕ)
    (instruction : Instruction F (inputs+i)) (history : Fin i → Operations.Answer ML MR BL BR)
    (old : Fin (inputs+i) → U F n × U F n) :
    ((strategy.protocol hn).real i instruction history old).map Prod.fst =
      encodingDistribution hn (instruction.eval
        (fun w => secret ((stateEquivProd F n).symm (old w)))) := by
  cases instruction with
  | compute gate =>
    exact FullRetry.share_output_uniform (strategy.compute.stochasticStrategy hn)
      hq hn i gate history (old gate.left) (old gate.right)
  | refresh port => rw [fixed_refresh_joint,joint_first]; rfl
  | sample value => exact public_output_uniform strategy.publicLeft strategy.publicRight hn i value history

/-- Exact freshness disintegrates the full current answer; no answer transcript is conditioned away when forming the canonical operation. -/
theorem fixed_real_joint
    (strategy : Operations.FixedStrategy F ML MR BL BR n t inputs hdim)
    (hq : fieldCard F = 2) (hn : 2 ≤ n) (i : ℕ)
    (instruction : Instruction F (inputs+i)) (history : Fin i → Operations.Answer ML MR BL BR)
    (old : Fin (inputs+i) → U F n × U F n) :
    (strategy.protocol hn).real i instruction history old =
      (encodingDistribution hn (instruction.eval
        (fun w => secret ((stateEquivProd F n).symm (old w))))).joint
          ((strategy.protocol hn).answer i instruction history old) := by
  rw [protocol_joint, fixed_output_uniform strategy hq hn]

end CompilerProof.Operations
