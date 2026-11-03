import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.GateApproximation.MatrixPhase.Factorization
import Proofs.Compiler.GateApproximation.MatrixPhase.PhysicalProgram
import Proofs.Compiler.GateApproximation.MatrixPhase.ProtocolTransport
/-!
# The actual physical protocol in the paired-share representation
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace CircuitCompiler
open Refresh Composition Composition.TopologicalExecution
variable {F Alpha Beta : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype Alpha] [Fintype Beta] {n t inputs : ℕ}
namespace PhysicalStrategy
noncomputable def shareProtocol (strategy : PhysicalStrategy F Alpha Beta n t inputs)
    (hn : 2 ≤ n) (hdim : n * n = n + t) : GateProtocol F (U F n × U F n) (Alpha × Beta) inputs :=
  (strategy.protocol hn hdim).transport (stateEquivProd F n)
theorem share_local_coupling (strategy : PhysicalStrategy F Alpha Beta n t inputs)
    (hn : 2 ≤ n) (hdim : n * n = n + t)
    (i : ℕ) (gate : Gate F (inputs + i)) (history : Fin i → Alpha × Beta)
    (left right : U F n × U F n) :
    statisticalDistance ((strategy.shareProtocol hn hdim).real i gate history left right)
      (((mu F n hn (gate.kind.eval (secret ((stateEquivProd F n).symm left))
        (secret ((stateEquivProd F n).symm right)))).map (stateEquivProd F n)).joint
        ((strategy.shareProtocol hn hdim).answer i gate history left right)) ≤
      1 / (fieldCard F : ℝ) ^ (n + t - 1) + ((fieldCard F : ℝ) + 1) / (fieldCard F : ℝ) ^ n :=
  (strategy.protocol hn hdim).transport_local_coupling (stateEquivProd F n) secret (mu F n hn)
    _ (strategy.local_coupling hn hdim) i gate history left right
end PhysicalStrategy
theorem encodingDistribution_supports (hn : 2 ≤ n) (s : F) :
    (encodingDistribution hn s).Supports (fun xy => secret ((stateEquivProd F n).symm xy) = s) :=
  GateProtocol.transport_encoding_support secret (mu F n hn) (stateEquivProd F n) (mu_supports n hn) s
theorem encodingDistribution_left [Nonempty (U F n)] (hn : 2 ≤ n) (s : F) :
    (encodingDistribution hn s).map Prod.fst = FiniteDistribution.uniform := by
  have hleft : @stateLeftShare F _ n = (fun x : State F n => x.L) := by
    funext x
    cases x
    rfl
  simpa! only [encodingDistribution, mu, FiniteDistribution.map_map, stateEquivProd, uniformShare, hleft, Function.comp_def, Equiv.coe_fn_mk] using mu_left_marginal n hn s
theorem encodingDistribution_right [Nonempty (U F n)] (hn : 2 ≤ n) (s : F) :
    (encodingDistribution hn s).map Prod.snd = FiniteDistribution.uniform := by
  have hright : @stateRightShare F _ n = (fun x : State F n => x.R) := by
    funext x
    cases x
    rfl
  simpa! only [encodingDistribution, mu, FiniteDistribution.map_map, stateEquivProd, uniformShare, hright, Function.comp_def, Equiv.coe_fn_mk] using mu_right_marginal n hn s
theorem encodingDistribution_scalar [Nonempty (U F n)] (hn : 2 ≤ n) (s t : F) (a b : U F n → ℝ) :
    |(encodingDistribution hn s).expect (fun xy => a xy.1 * b xy.2) -
      (encodingDistribution hn t).expect (fun xy => a xy.1 * b xy.2)| ≤
      zeta F n * Real.sqrt (FiniteDistribution.uniform.expect (fun x => a x ^ 2)) *
        Real.sqrt (FiniteDistribution.uniform.expect (fun y => b y ^ 2)) := by
  simpa only [encodingDistribution, mu, uniformShare] using wire_scalar_discrepancy hn s t a b
end CircuitCompiler
