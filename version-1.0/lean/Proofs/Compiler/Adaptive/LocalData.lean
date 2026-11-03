import Proofs.Compiler.Adaptive.Canonical
import Proofs.Compiler.Direct.LocalData

/-!
# Local certificates survive online public sampling

The scopes and every approximated operation are fixed by the template. Online choices affect only public sampler values. Computation and refresh factors therefore retain their established physical certificates, uniformly in every formal prefix and induced valid labeling.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators Classical

namespace Compiler.Adaptive
open Refresh MatrixRefresh CircuitCompiler CircuitCompiler.Operations
  CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution
  CircuitCompiler.AveragedEnergyComparison CompilerProof.Direct
  CompilerProof.DirectComposition CompilerProof.Operations

variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq E] {P S : ℕ}

/-- At an approximated position, selecting an online public value changes nothing: that position is a refresh or computation, not a public sampler. -/
theorem operationAnswer_eq_original (protocol : Operations.Protocol Bit E A P)
    (defaultAnswer : A) (program : Operations.Program Bit P S) (values : SampleValues Bit A S)
    (i : Fin S) (hi : i ∈ approximated program) (h : List A) (e : Fin (P+S) → E) :
    operationAnswer protocol defaultAnswer program values i h e =
      protocol.operationAnswerDistribution defaultAnswer program i h e := by
  induction program with
  | nil => exact Fin.elim0 i
  | @snoc S prior instruction ih =>
    revert hi
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro hi
      cases he : instruction with
      | compute gate => simp [operationAnswer, Operations.Protocol.operationAnswerDistribution, selectInstruction]
      | refresh old => simp [operationAnswer, Operations.Protocol.operationAnswerDistribution, selectInstruction]
      | sample value =>
        simp [approximated, Operations.Program.instructionAt, he] at hi
    · intro hi
      simp only [operationAnswer, Operations.Protocol.operationAnswerDistribution,
        Fin.lastCases_castSucc]
      apply ih (fun i => values i.castSucc) j
      cases he : prior.instructionAt j <;>
        simp [approximated, Operations.Program.instructionAt, he] at hi ⊢

/-- Every induced labeling satisfies all refresh and computation equations, at every complete formal history. Public sampler labels are supplied by the online policy instead of the template's dummy values. -/
theorem evaluate_valid (input : Fin P → Bit) (program : Operations.Program Bit P S)
    (values : SampleValues Bit A S) (z : Fin S → A)
    (i : Fin S) (hi : i ∈ approximated program) :
    program.valid (evaluate input program values z) i := by
  induction program with
  | nil => exact Fin.elim0 i
  | @snoc S prior instruction ih =>
    let old := evaluate input prior (fun i => values i.castSucc) (Fin.init z)
    have hprefix : evaluate input (prior.snoc instruction) values z ∘ Fin.castSucc = old := by
      funext w
      simp [evaluate, old]
    revert hi
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro hi
      simp only [Operations.Program.valid, Operations.Program.sourceInstruction_snoc_last,
        Instruction.eval_mapPorts]
      change evaluate input (prior.snoc instruction) values z (Fin.last _) = _
      rw [hprefix]
      cases he : instruction with
      | compute gate => simp [evaluate, selectInstruction, old]
      | refresh port => simp [evaluate, selectInstruction, old]
      | sample value =>
        simp [approximated, Operations.Program.instructionAt, he] at hi
    · intro hi
      dsimp only [Operations.Program.valid]
      rw [Operations.Program.sourceInstruction_snoc_old, Instruction.eval_mapPorts]
      change evaluate input (prior.snoc instruction) values z (Fin.natAdd P j).castSucc =
        (prior.sourceInstruction j).eval (evaluate input (prior.snoc instruction) values z ∘ Fin.castSucc)
      rw [hprefix]
      simp only [evaluate, Fin.snoc_castSucc]
      change prior.valid old j
      apply ih (fun i => values i.castSucc) (Fin.init z) j
      cases he : prior.instructionAt j <;>
        simp [approximated, Operations.Program.instructionAt, he] at hi ⊢

namespace LocalData
variable {W X F : Type*} [Fintype W] [DecidableEq W] [Fintype X] [Nonempty X]
  {scope : Fin S → Finset W}
  {first second : ScopedProbabilities (E := X×X) (A := A) scope}
  {law : F → FiniteDistribution (X×X)} {valid : (W → F) → Fin S → Prop}
  {selected : Finset (Fin S)} {β ε : ℝ}

/-- Reuse the same approximations and factors when true probabilities agree at every approximated operation. Differences at unsigned public samplers require no analytic assumption. -/
def changeNetwork (data : CompilerProof.DirectComposition.LocalData scope first law valid selected β ε)
    (heq : ∀ i ∈ selected, ∀ h e a, second.prob i h e a = first.prob i h e a) :
    CompilerProof.DirectComposition.LocalData scope second law valid selected β ε where
  gate i h a :=
    { approximation := (data.gate i h a).approximation
      factors := (data.gate i h a).factors
      left_max := (data.gate i h a).left_max
      right_max := (data.gate i h a).right_max
      left_mean := (data.gate i h a).left_mean
      right_mean := (data.gate i h a).right_mean
      all_labels_rms := (data.gate i h a).all_labels_rms
      valid_error_rms := by
        intro label hv
        simp_rw [heq i hv.2]
        exact (data.gate i h a).valid_error_rms label hv
    }
  left_locality := data.left_locality
  right_locality := data.right_locality

end LocalData

variable {n t : ℕ} {hdim : n*n+1 = n+t}
  {ML MR BL BR : Type*} [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
  [Nonempty (Refresh.U Bit n)]

/-- Online public-input sampling preserves the actual fixed-prefix refresh and rectangular-shortening certificates on every approximated operation. -/
def physicalData (program : Operations.Program Bit P S) (hd : program.DistinctInputs)
    (strategy : Operations.FixedStrategy Bit ML MR BL BR n t P hdim)
    (hn : 2 ≤ n) (defaultAnswer : Operations.Answer ML MR BL BR)
    (values : SampleValues Bit (Operations.Answer ML MR BL BR) S) :
    CompilerProof.DirectComposition.LocalData program.scope
      (probabilities (strategy.protocol hn) (fixed_strategy_local strategy hn) defaultAnswer program values)
      (encodingDistribution hn) program.valid (approximated program)
      (betaParameter (Fintype.card (Refresh.U Bit n)))
      (rawErrorParameter (Fintype.card (Refresh.U Bit n))) :=
  LocalData.changeNetwork (programPhysicalData program hd strategy hn defaultAnswer)
    (fun i hi h e a => congrArg (fun Q : FiniteDistribution _ => Q.weight a)
      (operationAnswer_eq_original (strategy.protocol hn) defaultAnswer program values i hi h e))

end Compiler.Adaptive
