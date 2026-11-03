import Proofs.Compiler.Model
import Proofs.Compiler.Stateful.Unrolling
import Proofs.Compiler.Stateful.Correctness
import Proofs.Compiler.Stateful.Timing
import Proofs.Compiler.Adaptive.Prefixes
import Proofs.Compiler.Direct.Canonical
import Mathlib.Data.Fin.Tuple.Take

/-!
# Correctness of the trusted stateful decoder

Public inputs chosen at an invocation start are the same at every sampler in that invocation. Freezing those choices along a formal transcript gives the ordinary unrolled transition circuit. Exact physical freshness then shows that every designated output encoding decodes to the ideal oracle response. This justifies replacing the real decoder by the common public observation function in the security proof.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open scoped Classical
namespace Compiler.Stateful
open Refresh MatrixRefresh CircuitCompiler Compiler.Adaptive
  CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution
  CircuitCompiler.AveragedEnergyComparison CircuitCompiler.Sampling.Unbounded

/-- Incoming answer vectors are precisely the corresponding list prefixes. -/
theorem incomingVector_list {A : Type*} {S : ℕ} (z : Fin S → A) (i : Fin S) :
    List.ofFn (incomingVector z i) = (List.ofFn z).take i.val := by
  exact Fin.ofFn_take_eq_take_ofFn (Nat.le_of_lt i.isLt) z

namespace Circuit
variable {m d c g k n ml sl : ℕ} (circuit : Circuit m d c g k)

/-- Along a complete formal transcript, every physical public sampler uses the bit of the single causally chosen input for its invocation. -/
theorem sampler_values (T : ℕ) (adversary : Adversary m d k n ml sl) (oracle : Oracle d k)
    (z : Fin (circuit.unrolling T).schedule.compile.operations → Compiler.Answer ml sl) :
    ∀ i tag, (circuit.unrolling T).schedule.sampleAt i.val = some tag →
      circuit.sampleValues T adversary oracle i (incomingVector z i) =
        Sum.elim circuit.constantValues
          (fun p => inputAt c g adversary.choose oracle (List.ofFn z) p.1.val p.2) tag := by
  intro i tag hi
  simp only [sampleValues, hi]
  cases tag with
  | inl j => rfl
  | inr p =>
    rcases p with ⟨t,j⟩
    have ht := circuit.unroll_sampler_after T T (le_refl _) i.val t j hi
    have he : (List.ofFn (incomingVector z i)).take (startTime c d g t.val) =
        (List.ofFn z).take (startTime c d g t.val) := by
      rw [incomingVector_list, List.take_take, Nat.min_eq_left ht]
    exact congrFun (inputAt_congr c g adversary.choose oracle _ _ t.val he) j

/-- The induced labels at all original designated output addresses are exactly the ideal stateful outputs, for every formal leakage history. -/
theorem evaluated_outputs (T : ℕ) (adversary : Adversary m d k n ml sl)
    (initial : Fin m → Bit)
    (z : Fin (circuit.unrolling T).schedule.compile.operations → Compiler.Answer ml sl)
    (t : Fin T) (j : Fin k) :
    Compiler.Adaptive.evaluate initial (circuit.unrolling T).schedule.compile.program
      (circuit.sampleValues T adversary (circuit.oracle initial)) z
      ((circuit.unrolling T).schedule.compile.original ((circuit.unrolling T).outputs t j)) =
    (recordAt c g adversary.choose (circuit.oracle initial) (List.ofFn z) t.val).2 j := by
  let inputs := inputAt c g adversary.choose (circuit.oracle initial) (List.ofFn z)
  let publicValues : PublicPort c d T → Bit := Sum.elim circuit.constantValues
    (fun p => inputs p.1.val p.2)
  have he := Schedule.online_evaluate (circuit.unrolling T).schedule publicValues initial
    (circuit.sampleValues T adversary (circuit.oracle initial)) z
    (circuit.sampler_values T adversary (circuit.oracle initial) z)
  have hs := circuit.unroll_values T T (le_refl _) initial inputs publicValues
    (fun _ => rfl) (fun _ _ => rfl)
  exact (he.1 ((circuit.unrolling T).outputs t j)).trans
    ((hs.2.2 t j).trans (congrFun (recordAt_output circuit adversary.choose initial (List.ofFn z) t.val).symm j))

/-- The real stateful view is the common public function of the leakage transcript. The equality includes the actual physical trusted decoder, all rejected sampler tapes, and every adaptive public input. -/
theorem realView_eq_observed (T : ℕ) (adversary : Adversary m d k n ml sl)
    (hn : 2 ≤ n) (initial : Fin m → Bit) :
    circuit.realView T adversary hn initial =
      (circuit.runState T adversary hn (circuit.oracle initial) initial).map
        (fun state => circuit.observe T adversary (circuit.oracle initial) state.2) := by
  unfold realView runState
  rw [Compiler.Adaptive.raw_view_eq_mixture, Compiler.Adaptive.raw_view_eq_mixture]
  congr 1
  funext tape
  apply CompilerProof.Direct.map_eq_on_support
  intro state hstate
  have hbinary : fieldCard Bit = 2 := by simp [fieldCard,Bit]
  let strategy := Operations.FixedStrategy.fixSeeds
    (GateProtocol.extendTape
      ((CircuitCompiler.Sampling.matrixPrefixDistribution (F := Bit) (n+shorteningExtra n)).support_nonempty.choose,
       (CircuitCompiler.Sampling.matrixPrefixDistribution (F := Bit) n).support_nonempty.choose) tape)
    (adversary.strategy c g T (circuit.oracle initial)).fixedPrefix
  have hgate : ∀ i instruction history old,
      Refresh.statisticalDistance ((strategy.protocol hn).real i instruction history old)
        ((encodingDistribution hn (instruction.eval
          (fun w => secret ((stateEquivProd Bit n).symm (old w))))).joint
            ((strategy.protocol hn).answer i instruction history old)) ≤ 0 := by
    intro i instruction history old
    rw [CompilerProof.Operations.fixed_real_joint strategy hbinary hn]
    exact (statisticalDistance_self _).le
  have hsupport := canonical_support (strategy.protocol hn)
    (fun e => secret ((stateEquivProd Bit n).symm e)) (encodingDistribution hn)
    (encodingDistribution_supports hn) initial (circuit.unrolling T).schedule.compile.program
    (circuit.sampleValues T adversary (circuit.oracle initial))
  rw [←real_eq_canonical (strategy.protocol hn) _ (encodingDistribution hn)
    (encodingDistribution_supports hn) hgate] at hsupport
  have hv := hsupport state (by
    simpa only [CircuitCompiler.Sampling.RawEncoding.initializeShares_eq_independent,
      toFinite_toPMF] using hstate)
  refine Prod.ext ?_ ?_
  · rfl
  funext t
  refine Prod.ext ?_ ?_
  · rfl
  funext j
  exact (hv ((circuit.unrolling T).schedule.compile.original
    ((circuit.unrolling T).outputs t j))).trans
      (circuit.evaluated_outputs T adversary initial state.2 t j)

end Circuit
end Compiler.Stateful
