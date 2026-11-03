import Proofs.Compiler.Direct.LocalData
import Proofs.Compiler.Direct.NetworkWeights
import Proofs.Compiler.Direct.Incidence
import Proofs.Compiler.DirectComposition.Theorem57

/-!
# Instantiating direct composition with the physical NAND compiler

Public samplers have a singleton scope whose label is fixed by its ordinary sampling equation. Every remaining operation is certified by the actual square-refresh or protected-NAND estimate. The physical input-port chains prove incidence at most three, including arbitrary source fanout and equal source operands. Unused private inputs need no equality assumption because the generic composition theorem integrates only active scopes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.Direct
open Refresh MatrixRefresh Compiler Compiler.Direct CircuitCompiler CircuitCompiler.Operations
  CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution
  CircuitCompiler.AveragedEnergyComparison CircuitCompiler.Sampling.Unbounded
  CompilerProof.Operations CompilerProof.DirectComposition Ports

variable {P U T k n ml sl : ℕ}

/-- The public boundary consists only of scopes of the explicitly unsigned public samplers. It contains no private input, gate output, or trusted output encoding. -/
def publicWires {S : ℕ} (program : Operations.Program Bit P S) : Finset (Fin (P+S)) :=
  (Finset.univ.filter (fun i=>i∉approximated program)).biUnion program.scope

/-- A publicly sampled operation has only its fresh output in its complete scope. -/
theorem sample_scope {S : ℕ} (program : Operations.Program Bit P S) (i : Fin S) (value : Bit)
    (hi : program.instructionAt i=.sample value) : program.scope i={newWire (P:=P) i} := by
  simp only [Operations.Program.scope,Operations.Program.sourceInstruction_eq_at,hi,
    Operations.Instruction.mapPorts,Operations.Instruction.inputs,Finset.insert_empty]
  rfl

/-- Two globally valid labelings agree on all sampler scopes because those outputs encode the same prescribed public bits. -/
theorem public_label_agreement {S : ℕ} (program : Operations.Program Bit P S)
    (first second : Fin (P+S) → Bit)
    (hf : ∀ i,program.valid first i) (hs : ∀ i,program.valid second i) :
    ∀ w∈publicWires program,first w=second w := by
  intro w hw
  rcases Finset.mem_biUnion.mp hw with ⟨i,hi,hw⟩
  have hout : i∉approximated program := (Finset.mem_filter.mp hi).2
  cases he : program.instructionAt i with
  | compute gate => exact False.elim (hout (by simp [approximated,he]))
  | refresh port => exact False.elim (hout (by simp [approximated,he]))
  | sample value =>
    rw [sample_scope program i value he,Finset.mem_singleton] at hw
    subst w
    have hfirst := valid_at program i first (hf i)
    have hsecond := valid_at program i second (hs i)
    rw [he] at hfirst hsecond
    exact hfirst.trans hsecond.symm

/-- The actual fixed-prefix transcript satisfies the direct bound between any two private inputs. The independent wire experiment is obtained by exact disintegration of that same physical execution. -/
theorem fixed_transcript_bound (source : Source P U T k)
    (strategy : Operations.FixedStrategy Bit (LeakageOutput ml) (LeakageOutput ml)
      (LeakageOutput sl) (LeakageOutput sl) n (shorteningExtra n) P (longDimension n))
    (hn : 2≤n) (defaultAnswer : Compiler.Answer ml sl) (first second : Fin P → Bit) :
    Refresh.statisticalDistance
      ((((strategy.protocol hn).realRunner source.compiledProgram).execute
        (toFinite (Sampling.RawEncoding.initializeShares hn first))).map
          (fun state=>(answersEquiv _ _).symm state.2))
      ((((strategy.protocol hn).realRunner source.compiledProgram).execute
        (toFinite (Sampling.RawEncoding.initializeShares hn second))).map
          (fun state=>(answersEquiv _ _).symm state.2))≤
      1000000*(source.operationCount:ℝ)*(Fintype.card (Compiler.Answer ml sl):ℝ)^9*
        (Fintype.card (Refresh.U Bit n):ℝ)^(-1/27:ℝ) := by
  letI : Nonempty (Refresh.U Bit n) := ⟨unitShare ⟨0,by omega⟩⟩
  let protocol := strategy.protocol hn
  let hlocal := fixed_strategy_local strategy hn
  let program := source.compiledProgram
  let firstLabel := program.eval first
  let secondLabel := program.eval second
  let fp := flatCanonical protocol hlocal defaultAnswer program (encodingDistribution hn) firstLabel
  let sp := flatCanonical protocol hlocal defaultAnswer program (encodingDistribution hn) secondLabel
  have hdegree : ∀ w,(Finset.univ.filter (fun i=>w∈program.scope i)).card≤3 := by
    intro w
    simpa [Compiler.Direct.Incidence.incidence] using source.incidence_le_three w
  have hnonempty : ∀ i∈approximated program,(program.scope i).Nonempty := by
    intro i hi
    exact ⟨newWire i,newWire_mem program i⟩
  have hpublic : ∀ i,i∉approximated program→program.scope i⊆publicWires program := by
    intro i hi w hw
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,hw⟩
  have hcomparison := Compiler.Direct.direct_composition hn program.scope
    (protocol.probabilities hlocal defaultAnswer program) program.valid (approximated program)
    (physicalData source strategy hn defaultAnswer) source.scope_card_le_three hdegree hnonempty
    (publicWires program) hpublic firstLabel secondLabel
    (fun i _=>evaluated_valid program first i) (fun i _=>evaluated_valid program second i)
    (public_label_agreement program firstLabel secondLabel
      (evaluated_valid program first) (evaluated_valid program second)) fp sp
    (by intro z; dsimp only [fp]; exact flatCanonical_weight protocol hlocal defaultAnswer program (encodingDistribution hn) firstLabel z)
    (by intro z; dsimp only [sp]; exact flatCanonical_weight protocol hlocal defaultAnswer program (encodingDistribution hn) secondLabel z)
  rw [fixed_transcript_canonical source strategy hn defaultAnswer first,
    fixed_transcript_canonical source strategy hn defaultAnswer second]
  have hmap (label : Fin (P+source.operationCount) → Bit) :
      (flatCanonical protocol hlocal defaultAnswer program (encodingDistribution hn) label).map
        (answersEquiv (Compiler.Answer ml sl) source.operationCount).symm=
      protocol.canonicalNetworkView hlocal defaultAnswer program (encodingDistribution hn) label Prod.fst := by
    rw [flatCanonical_eq_map,FiniteDistribution.map_map]
    simp only [Function.comp_def,Equiv.symm_apply_apply]
    ext z
    change ((_ : FiniteDistribution _).map (Equiv.refl _)).weight z=_
    rw [FiniteDistribution.map_equiv_weight]
    rfl
  rw [←hmap firstLabel,←hmap secondLabel]
  exact (statisticalDistance_map_le fp sp _).trans hcomparison

/-- Independent rejected-prefix averaging transfers the proved fixed-prefix bound to the actual raw physical transcript. Every retry remains present in its appropriate local answer. -/
theorem raw_transcript_bound (source : Source P U T k)
    (strategy : Compiler.Direct.Strategy source n ml sl) (hn : 2≤n) (first second : Fin P → Bit) :
    Refresh.statisticalDistance (Compiler.Direct.transcript strategy hn first)
      (Compiler.Direct.transcript strategy hn second)≤
      1000000*(source.operationCount:ℝ)*(Fintype.card (Compiler.Answer ml sl):ℝ)^9*
        (Fintype.card (Refresh.U Bit n):ℝ)^(-1/27:ℝ) := by
  let defaultAnswer : Compiler.Answer ml sl := Classical.choice inferInstance
  unfold Compiler.Direct.transcript Compiler.Direct.runState
  rw [Operations.raw_view_eq_mixture,Operations.raw_view_eq_mixture]
  apply countableMixture_distance_le
  intro tape
  exact fixed_transcript_bound source _ hn defaultAnswer first second

end CompilerProof.Direct
