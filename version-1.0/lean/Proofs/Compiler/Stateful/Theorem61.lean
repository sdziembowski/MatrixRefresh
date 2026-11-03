import Proofs.Compiler.Stateful.Decoder
import Proofs.Compiler.Direct.Theorem52

/-!
# Continual stateful privacy

The actual decoder and ideal oracle give the same public responses. For each fixed initial state, the real and dummy executions therefore use the same causal public-input policy and the same history-dependent local functions. The checked physical adaptive composition theorem compares their leakage transcripts. Applying their common public observation function gives the complete interactive-view bound, without passing the private state to the simulator.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace Compiler.Stateful
open Refresh CircuitCompiler Compiler.Adaptive CircuitCompiler.Sampling.Unbounded

/-- One oracle simulator works for every initial state against an adaptive input and local-leakage adversary. Its complete view includes all public input/output records and all leakage answers. The explicit error has S = 3Tg+Td+c and K = 2²⁽ᵐˡ⁺ˢˡ⁾. -/
theorem theorem_stateful {m d c g k n ml sl : ℕ} (circuit : Circuit m d c g k)
    (T : ℕ) (adversary : Adversary m d k n ml sl) (hn : 2 ≤ n) :
    ∃ simulate : Oracle d k → Refresh.FiniteDistribution (circuit.View T ml sl),
      simulate = circuit.simulatedView T adversary hn ∧
      ∀ initial : Fin m → Compiler.Bit,
        Refresh.statisticalDistance (circuit.realView T adversary hn initial)
          (simulate (circuit.oracle initial)) ≤ min 1 (circuit.privacyBound T n ml sl) := by
  refine ⟨circuit.simulatedView T adversary hn,rfl,?_⟩
  intro initial
  apply le_min (statisticalDistance_le_one _ _)
  rw [Circuit.realView_eq_observed]
  change statisticalDistance
    ((circuit.runState T adversary hn (circuit.oracle initial) initial).map
      (fun state => circuit.observe T adversary (circuit.oracle initial) state.2))
    ((circuit.runState T adversary hn (circuit.oracle initial) (fun _ => 0)).map
      (fun state => circuit.observe T adversary (circuit.oracle initial) state.2)) ≤ _
  have hmap := statisticalDistance_map_le
    ((circuit.runState T adversary hn (circuit.oracle initial) initial).map Prod.snd)
    ((circuit.runState T adversary hn (circuit.oracle initial) (fun _ => 0)).map Prod.snd)
    (circuit.observe T adversary (circuit.oracle initial))
  have h := Compiler.Adaptive.raw_transcript_bound
    (circuit.unrolling T).schedule.compile.program (circuit.unrolling T).schedule.distinct
    (circuit.unrolling T).schedule.degree_le_three
    (adversary.strategy c g T (circuit.oracle initial)) hn
    (circuit.sampleValues T adversary (circuit.oracle initial)) initial (fun _ => 0)
  have hb : statisticalDistance
      ((circuit.runState T adversary hn (circuit.oracle initial) initial).map Prod.snd)
      ((circuit.runState T adversary hn (circuit.oracle initial) (fun _ => 0)).map Prod.snd) ≤
      circuit.privacyBound T n ml sl := by
    simpa only [Circuit.runState, Circuit.privacyBound, circuit.unrolled_operationCount,
      CompilerProof.Direct.answer_card, CompilerProof.Direct.share_card] using h
  exact (show statisticalDistance _ _ ≤ _ from by
    simpa only [FiniteDistribution.map_map, Function.comp_def] using hmap).trans hb

end Compiler.Stateful
