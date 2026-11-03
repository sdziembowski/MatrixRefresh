import Proofs.Compiler.Model
import Proofs.Compiler.Direct.Correctness
import Proofs.Compiler.Operations.Execution
import Proofs.Compiler.Operations.Prefixes

/-!
# Exact canonical execution and hidden-output correctness

Every actual operation outputs a fresh encoding of its prescribed bit. Disintegrating the same joint transition retains its current leakage answer and yields the unconditional independent-wire canonical experiment. No independence after observing a transcript is used. The trusted decoder is exact on the resulting supported states, so its plaintext output can be appended to the transcript without disclosing any encoding pair.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.Direct
open Refresh MatrixRefresh Compiler Compiler.Direct CircuitCompiler CircuitCompiler.Operations
  CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution
  CircuitCompiler.AveragedEnergyComparison CircuitCompiler.Sampling.Unbounded
  CompilerProof.Operations

variable {P U T k n ml sl : ℕ}

/-- Mapping a finite distribution by functions that agree on its support gives the same distribution. -/
theorem map_eq_on_support {α β : Type*} [Fintype α] [Fintype β]
    (law : FiniteDistribution α) (f g : α → β)
    (h : ∀ a, law.weight a≠0 → f a=g a) : law.map f=law.map g := by
  ext b
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hz : law.weight a=0
  · simp [FiniteDistribution.map,FiniteDistribution.bind,hz]
  · dsimp only
    rw [h a hz]

/-- The actual private-prefix-fixed program is supported on encodings of its ordinary evaluated wire bits, including its hidden designated outputs. -/
theorem fixed_state_support
    (strategy : Operations.FixedStrategy Bit (LeakageOutput ml) (LeakageOutput ml)
      (LeakageOutput sl) (LeakageOutput sl) n (shorteningExtra n) P (longDimension n))
    (hn : 2≤n) {S : ℕ} (program : Operations.Program Bit P S) (input : Fin P → Bit) :
    (((strategy.protocol hn).realRunner program).execute
      (toFinite (Sampling.RawEncoding.initializeShares hn input))).Supports
      (fun state=>∀ w, secret ((stateEquivProd Bit n).symm (state.1 w))=program.eval input w) := by
  have hbinary : fieldCard Bit=2 := by simp [fieldCard,Bit]
  have hgate : ∀ i instruction history old,
      Refresh.statisticalDistance ((strategy.protocol hn).real i instruction history old)
        ((encodingDistribution hn (instruction.eval (fun w=>
          secret ((stateEquivProd Bit n).symm (old w))))).joint
            ((strategy.protocol hn).answer i instruction history old))≤0 := by
    intro i instruction history old
    rw [fixed_real_joint strategy hbinary hn]
    exact (statisticalDistance_self _).le
  rw [Sampling.RawEncoding.initializeShares_eq_independent,toFinite_toPMF,
    (strategy.protocol hn).real_eq_canonical
      (fun e=>secret ((stateEquivProd Bit n).symm e)) (encodingDistribution hn)
      (encodingDistribution_supports hn) hgate input program]
  apply Canonical.execute_support (fun i => encodingDistribution hn (input i))
    ((strategy.protocol hn).canonicalRunner (encodingDistribution hn) input program)
    (fun w e=>secret ((stateEquivProd Bit n).symm e)=program.eval input w)
  intro w
  rw [Operations.Protocol.canonical_wireDistributions]
  exact encodingDistribution_supports hn _

/-- Fixed sampler prefixes preserve the exact trusted-decoder output, independently of all observed leakage answers. -/
theorem fixed_decoded_eq (source : Source P U T k)
    (strategy : Operations.FixedStrategy Bit (LeakageOutput ml) (LeakageOutput ml)
      (LeakageOutput sl) (LeakageOutput sl) n (shorteningExtra n) P (longDimension n))
    (hn : 2≤n) (input : Fin P → Bit) :
    ((((strategy.protocol hn).realRunner source.compiledProgram).execute
      (toFinite (Sampling.RawEncoding.initializeShares hn input))).map fun state=>
        ((answersEquiv _ _).symm state.2,Compiler.Direct.decode source state.1)) =
    ((((strategy.protocol hn).realRunner source.compiledProgram).execute
      (toFinite (Sampling.RawEncoding.initializeShares hn input))).map fun state=>
        ((answersEquiv _ _).symm state.2,source.outputValues input)) := by
  apply map_eq_on_support
  intro state hstate
  have h := fixed_state_support strategy hn source.compiledProgram input state hstate
  congr 1
  funext j
  exact (h (source.outputSlot j)).trans (source.compiled_output input j)

/-- The actual raw physical view is exactly its leakage transcript with the source plaintext output appended; output shares remain hidden. -/
theorem realView_eq_transcript_output (source : Source P U T k)
    (strategy : Compiler.Direct.Strategy source n ml sl) (hn : 2≤n) (input : Fin P → Bit) :
    Compiler.Direct.realView strategy hn input=
      (Compiler.Direct.transcript strategy hn input).map
        (fun history=>(history,source.outputValues input)) := by
  unfold Compiler.Direct.realView Compiler.Direct.transcript Compiler.Direct.runState
  rw [FiniteDistribution.map_map]
  rw [Operations.raw_view_eq_mixture,Operations.raw_view_eq_mixture]
  congr 1
  funext tape
  exact fixed_decoded_eq source _ hn input

/-- The fixed-prefix actual transcript is exactly the independent-wire canonical network at the compiled program's valid evaluated labels. -/
theorem fixed_transcript_canonical (source : Source P U T k)
    (strategy : Operations.FixedStrategy Bit (LeakageOutput ml) (LeakageOutput ml)
      (LeakageOutput sl) (LeakageOutput sl) n (shorteningExtra n) P (longDimension n))
    (hn : 2≤n) (defaultAnswer : Compiler.Answer ml sl) (input : Fin P → Bit) :
    ((((strategy.protocol hn).realRunner source.compiledProgram).execute
      (toFinite (Sampling.RawEncoding.initializeShares hn input))).map
        (fun state=>(answersEquiv _ _).symm state.2)) =
      (strategy.protocol hn).canonicalNetworkView (fixed_strategy_local strategy hn)
        defaultAnswer source.compiledProgram (encodingDistribution hn)
          (source.compiledProgram.eval input) Prod.fst := by
  have hbinary : fieldCard Bit=2 := by simp [fieldCard,Bit]
  simpa only [Sampling.RawEncoding.initializeShares_eq_independent,toFinite_toPMF] using
    fixed_canonical_eq strategy hbinary hn defaultAnswer source.compiledProgram input Prod.fst

end CompilerProof.Direct
