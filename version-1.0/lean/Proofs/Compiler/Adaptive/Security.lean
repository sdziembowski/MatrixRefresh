import Proofs.Compiler.Adaptive.LocalData
import Proofs.Compiler.Direct.Incidence
import Proofs.Compiler.DirectComposition.AdaptiveTheorem57

/-!
# Physical security with online public values

This instantiates causal composition with the actual fixed-prefix physical kernels. The only graph premises are distinct computation operands and incidence three; the stateful refresh-chain compiler proves both. Public sampler values can depend arbitrarily on earlier leakage, provided the two compared executions use the same online policy.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open scoped BigOperators Classical

namespace Compiler.Adaptive
open Refresh MatrixRefresh CircuitCompiler CircuitCompiler.Operations
  CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution
  CircuitCompiler.AveragedEnergyComparison CompilerProof.Direct
  CompilerProof.DirectComposition CompilerProof.Operations CompilerProof.Direct.Ports

variable {P S : ℕ} {A : Type*} [Fintype A]

/-- The value of a public sampler's fresh wire is its online policy's value at that operation's incoming history. -/
theorem evaluate_sample (input : Fin P → Bit) (program : Operations.Program Bit P S)
    (values : SampleValues Bit A S) (z : Fin S → A) (i : Fin S) (value : Bit)
    (hi : program.instructionAt i = .sample value) :
    evaluate input program values z (newWire i) = values i (incomingVector z i) := by
  induction program generalizing value with
  | nil => exact Fin.elim0 i
  | @snoc S prior instruction ih =>
    revert value hi
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro value hi
      simp only [Operations.Program.instructionAt, Fin.lastCases_last] at hi
      subst instruction
      simp only [evaluate, selectInstruction, newWire, Fin.snoc_last, Instruction.eval]
      change Fin.snoc _ _ (Fin.last (P+S)) = _
      rw [Fin.snoc_last]
      rfl
    · intro value hi
      have hp : prior.instructionAt j = .sample value := by
        simpa only [Operations.Program.instructionAt, Fin.lastCases_castSucc] using hi
      have hw : newWire (P := P) j.castSucc = (newWire (P := P) j).castSucc := rfl
      rw [hw]
      simp only [evaluate, Fin.snoc_castSucc]
      exact ih (fun i => values i.castSucc) (Fin.init z) j value hp

/-- Public wire locations are precisely the union of scopes of unsigned public samplers. Private input and retained state encodings are excluded. -/
def publicWires (program : Operations.Program Bit P S) : Finset (Fin (P+S)) :=
  (Finset.univ.filter (fun i => i ∉ approximated program)).biUnion program.scope

/-- The two induced labelings agree on every public sampler scope, even though the common public value is chosen online. -/
theorem evaluate_public_agreement (first second : Fin P → Bit)
    (program : Operations.Program Bit P S) (values : SampleValues Bit A S) (z : Fin S → A) :
    ∀ w ∈ publicWires program,
      evaluate first program values z w = evaluate second program values z w := by
  intro w hw
  rcases Finset.mem_biUnion.mp hw with ⟨i, hi, hw⟩
  have hout : i ∉ approximated program := (Finset.mem_filter.mp hi).2
  cases he : program.instructionAt i with
  | compute gate => exact False.elim (hout (by simp [approximated, he]))
  | refresh old => exact False.elim (hout (by simp [approximated, he]))
  | sample value =>
    have hs : program.scope i = {newWire (P := P) i} := by
      simp only [Operations.Program.scope, Operations.Program.sourceInstruction_eq_at, he,
        Operations.Instruction.mapPorts, Operations.Instruction.inputs, Finset.insert_empty]
      rfl
    rw [hs, Finset.mem_singleton] at hw
    subst w
    rw [evaluate_sample first program values z i value he,
      evaluate_sample second program values z i value he]

variable {n t : ℕ} {hdim : n*n+1 = n+t}
  {ML MR BL BR : Type*} [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
  [Nonempty ML] [Nonempty MR] [Nonempty BL] [Nonempty BR]

/-- The concrete fixed-prefix physical execution obeys the direct privacy bound with online public inputs. The initial private boundary is sampled only once for the entire program. -/
theorem fixed_transcript_bound (program : Operations.Program Bit P S)
    (hd : program.DistinctInputs)
    (hdegree : ∀ w, (Finset.univ.filter (fun i => w ∈ program.scope i)).card ≤ 3)
    (strategy : Operations.FixedStrategy Bit ML MR BL BR n t P hdim)
    (hn : 2 ≤ n) (defaultAnswer : Operations.Answer ML MR BL BR)
    (values : SampleValues Bit (Operations.Answer ML MR BL BR) S)
    (first second : Fin P → Bit) :
    Refresh.statisticalDistance
      (((realRunner (strategy.protocol hn) program values).execute
        (independentDistribution (fun i => encodingDistribution hn (first i)))).map Prod.snd)
      (((realRunner (strategy.protocol hn) program values).execute
        (independentDistribution (fun i => encodingDistribution hn (second i)))).map Prod.snd) ≤
      1000000*(S:ℝ)*(Fintype.card (Operations.Answer ML MR BL BR):ℝ)^9 *
        (Fintype.card (Refresh.U Bit n):ℝ)^(-1/27:ℝ) := by
  letI : Nonempty (Refresh.U Bit n) := ⟨unitShare ⟨0,by omega⟩⟩
  let protocol := strategy.protocol hn
  let locality := fixed_strategy_local strategy hn
  let left := canonicalRealization protocol locality defaultAnswer
    (encodingDistribution hn) first program values
  let right := canonicalRealization protocol locality defaultAnswer
    (encodingDistribution hn) second program values
  have hpublic : ∀ i, i ∉ approximated program → program.scope i ⊆ publicWires program := by
    intro i hi w hw
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩, hw⟩
  have hnonempty : ∀ i ∈ approximated program, (program.scope i).Nonempty := by
    intro i hi
    exact ⟨newWire i, newWire_mem program i⟩
  have h := Compiler.Direct.adaptive_composition hn program.scope
    (probabilities protocol locality defaultAnswer program values) program.valid (approximated program)
    (physicalData program hd strategy hn defaultAnswer values)
    (Compiler.Direct.Incidence.scope_card_le_three program) hdegree hnonempty
    (publicWires program) hpublic (evaluate first program values) (evaluate second program values)
    left right (fun z i hi => evaluate_valid first program values z i hi)
    (fun z i hi => evaluate_valid second program values z i hi)
    (fun z => evaluate_public_agreement first second program values z)
  have hbinary : fieldCard Bit = 2 := by simp [fieldCard, Bit]
  have hgate : ∀ i instruction history old,
      Refresh.statisticalDistance (protocol.real i instruction history old)
        ((encodingDistribution hn (instruction.eval
          (fun w => secret ((stateEquivProd Bit n).symm (old w))))).joint
            (protocol.answer i instruction history old)) ≤ 0 := by
    intro i instruction history old
    rw [fixed_real_joint strategy hbinary hn]
    exact (statisticalDistance_self _).le
  rw [real_eq_canonical protocol _ (encodingDistribution hn) (encodingDistribution_supports hn)
      hgate first program values,
    real_eq_canonical protocol _ (encodingDistribution hn) (encodingDistribution_supports hn)
      hgate second program values]
  exact h

end Compiler.Adaptive
