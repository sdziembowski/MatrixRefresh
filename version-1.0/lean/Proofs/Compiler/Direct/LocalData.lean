import Proofs.Compiler.Direct.Ports
import Proofs.Compiler.Direct.Resources
import Proofs.Compiler.DirectComposition.Model
import Proofs.Compiler.DirectComposition.BinaryParameters
import Proofs.Compiler.Operations.CertificateLifts
import Proofs.Compiler.Operations.ComputeCertificate
import Proofs.Compiler.Operations.RefreshCertificate

/-!
# The actual direct compiler's local approximation data

The two-port square-refresh and three-port protected-computation estimates are lifted to the complete physical wire array. Every selected factor still reads only the active operation's scope. Public sampling is left in the true normalized probability network and is never approximated.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.Direct
open Refresh MatrixRefresh CircuitCompiler CircuitCompiler.Operations
  CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution
  CircuitCompiler.AveragedEnergyComparison CompilerProof.Operations
  CompilerProof.DirectComposition CircuitCompiler.SimulationParameters Ports

variable {P U T k n t : ℕ} {hdim : n*n+1=n+t}
  {ML MR BL BR : Type*} [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
  [Nonempty (Refresh.U Compiler.Bit n)]

/-- Exactly the refresh and protected-computation operations need local analytic approximations. Public samplers retain their true probability tables throughout the comparison. -/
def approximated {S : ℕ} (program : Operations.Program Compiler.Bit P S) : Finset (Fin S) :=
  Finset.univ.filter (fun i=>match program.instructionAt i with | .sample _=>False | _=>True)

/-- The selected certificate retains factor-by-factor locality, which is needed when its separate party energies are trimmed. -/
private structure ScopedCertificate {S : ℕ} (program : Operations.Program Compiler.Bit P S)
    (strategy : Operations.FixedStrategy Compiler.Bit ML MR BL BR n t P hdim)
    (hn : 2≤n) (defaultAnswer : Operations.Answer ML MR BL BR) (i : Fin S)
    (history : List (Operations.Answer ML MR BL BR)) (z : Operations.Answer ML MR BL BR) where
  data : GateLocalEstimates (CompilerProof.DirectComposition.groupedLaw (encodingDistribution hn))
    (fun label=>program.valid label i ∧ i∈approximated program)
    (fun _ left right=>
      ((strategy.protocol hn).probabilities (fixed_strategy_local strategy hn)
        defaultAnswer program).prob i history (fun w=>(left w,right w)) z)
    (betaParameter (Fintype.card (Refresh.U Compiler.Bit n)))
    (rawErrorParameter (Fintype.card (Refresh.U Compiler.Bit n)))
  left_locality : ∀ j, Scoped (program.scope i)
    (fun e : Fin (P+S) → Refresh.U Compiler.Bit n × Refresh.U Compiler.Bit n=>data.factors.left (fun w=>(e w).1) j)
  right_locality : ∀ j, Scoped (program.scope i)
    (fun e : Fin (P+S) → Refresh.U Compiler.Bit n × Refresh.U Compiler.Bit n=>data.factors.right (fun w=>(e w).2) j)

/-- Rewriting the true table through a proved identity retains the chosen factors definitionally; only the valid-label error proof changes. -/
private def replaceOriginal {X L : Type*} [Fintype X] [Nonempty X]
    {laws : L → FiniteDistribution (X×X)} {valid : L → Prop}
    {original : L → X → X → ℝ} {β ε : ℝ}
    (data : GateLocalEstimates laws valid original β ε)
    (original' : L → X → X → ℝ) (heq : original'=original) :
    GateLocalEstimates laws valid original' β ε where
  approximation := data.approximation
  factors := data.factors
  left_max := data.left_max
  right_max := data.right_max
  left_mean := data.left_mean
  right_mean := data.right_mean
  all_labels_rms := data.all_labels_rms
  valid_error_rms label hv := by
    rw [heq]
    exact data.valid_error_rms label hv

/-- Choose a genuine certificate for the actual fixed-prefix physical operation, including the full rejected-shortener answer tapes. No execution comparison is assumed. -/
private def operationCertificate {S : ℕ} (program : Operations.Program Compiler.Bit P S)
    (hd : program.DistinctInputs)
    (strategy : Operations.FixedStrategy Compiler.Bit ML MR BL BR n t P hdim)
    (hn : 2≤n) (defaultAnswer : Operations.Answer ML MR BL BR) (i : Fin S)
    (history : List (Operations.Answer ML MR BL BR)) (z : Operations.Answer ML MR BL BR) :
    ScopedCertificate program strategy hn defaultAnswer i history z := by
  let q : ℝ := Fintype.card (Refresh.U Compiler.Bit n)
  have hbinary : fieldCard Compiler.Bit=2 := by simp [fieldCard,Compiler.Bit]
  have hq : 1≤q := (show (1:ℝ)≤3 by norm_num).trans (share_card_ge_three hbinary hn)
  let valid' := fun label : Fin (P+S) → Compiler.Bit => program.valid label i ∧ i∈approximated program
  let original := fun (_ : Fin (P+S) → Compiler.Bit) (left right : Fin (P+S) → Refresh.U Compiler.Bit n)=>
    ((strategy.protocol hn).probabilities (fixed_strategy_local strategy hn)
      defaultAnswer program).prob i history (fun w=>(left w,right w)) z
  let H := GateProtocol.completeHistory defaultAnswer history i.val
  have hβ := (betaParameter_bounds hq).1
  have hβone := (betaParameter_bounds hq).2
  cases hi : program.instructionAt i with
  | compute gate =>
    let l := oldWire i gate.left
    let r := oldWire i gate.right
    let o := newWire (P:=P) i
    have hlr : l≠r := by
      have hh := instructionAt_distinct program hd i
      rw [hi] at hh
      exact fun he=>hh ((oldWire_injective i) he)
    have hlo : l≠o := oldWire_ne_newWire i gate.left
    have hro : r≠o := oldWire_ne_newWire i gate.right
    have hthreshold : 1≤(Fintype.card (Refresh.U Compiler.Bit n × Refresh.U Compiler.Bit n):ℝ)*(betaParameter q)^3 := by
      simpa only [Fintype.card_prod,Nat.cast_mul,pow_two,q] using direct_compute_admissible hq
    let base := enlargeError (computePortEstimates strategy hbinary hn i.val gate H z
      (betaParameter q) hβ hβone hthreshold) (raw_error_dominates hq (binary_retry_le hn))
    let labels := fun label : Fin (P+S) → Compiler.Bit => ((label l,label r),label o)
    have hv : ∀ label, valid' label → (labels label).2=gate.kind.eval (labels label).1.1 (labels label).1.2 := by
      intro label hvalid
      have h := valid_at program i label hvalid.1
      rw [hi] at h
      exact h
    let lifted := (relabelCertificate base labels valid' hv).pullback
      (CompilerProof.DirectComposition.groupedLaw (encodingDistribution hn)) (projectTriple l r o) (projectTriple l r o)
      (uniform_projectTriple l r o hlr hlo hro) (uniform_projectTriple l r o hlr hlo hro)
      (fun label=>grouped_projectTriple hn label l r o hlr hlo hro)
    have horiginal : original=(fun (_ : Fin (P+S) → Compiler.Bit) left right=>
        computeProbability strategy hn i.val gate H z (projectTriple l r o left) (projectTriple l r o right)) := by
      funext label left right
      dsimp only [original,Operations.Protocol.probabilities]
      rw [operation_probability,hi]
      symm
      exact computeProbability_eq_answer strategy hn i.val gate H z _ _ _ rfl rfl
    change ScopedCertificate program strategy hn defaultAnswer i history z
    refine ⟨replaceOriginal lifted original horiginal,?_,?_⟩
    · intro j first second heq
      have hl := oldWire_mem program i gate.left (by rw [hi]; simp [Instruction.inputs])
      have hr := oldWire_mem program i gate.right (by rw [hi]; simp [Instruction.inputs])
      have ho := newWire_mem program i
      change base.factors.left (projectTriple l r o (fun w=>(first w).1)) j=
        base.factors.left (projectTriple l r o (fun w=>(second w).1)) j
      simp only [projectTriple,heq l hl,heq r hr,heq o ho]
    · intro j first second heq
      have hl := oldWire_mem program i gate.left (by rw [hi]; simp [Instruction.inputs])
      have hr := oldWire_mem program i gate.right (by rw [hi]; simp [Instruction.inputs])
      have ho := newWire_mem program i
      change base.factors.right (projectTriple l r o (fun w=>(first w).2)) j=
        base.factors.right (projectTriple l r o (fun w=>(second w).2)) j
      simp only [projectTriple,heq l hl,heq r hr,heq o ho]
  | refresh port =>
    let l := oldWire i port
    let o := newWire (P:=P) i
    have hlo : l≠o := oldWire_ne_newWire i port
    have herror : 396*(betaParameter q)^(1/3:ℝ)≤rawErrorParameter q := by
      have hh := raw_error_dominates hq (show (0:ℝ)≤2*q^(-1/9:ℝ) by positivity)
      simpa only [add_zero] using hh
    let base := enlargeError (refreshPortEstimates strategy hbinary hn i.val port H z
      (betaParameter q) hβ hβone (direct_refresh_admissible hq)) herror
    let labels := fun label : Fin (P+S) → Compiler.Bit => (label l,label o)
    have hv : ∀ label, valid' label → (labels label).1=(labels label).2 := by
      intro label hvalid
      have h := valid_at program i label hvalid.1
      rw [hi] at h
      exact h.symm
    let lifted := (relabelCertificate base labels valid' hv).pullback
      (CompilerProof.DirectComposition.groupedLaw (encodingDistribution hn)) (projectPair l o) (projectPair l o)
      (uniform_projectPair l o hlo) (uniform_projectPair l o hlo)
      (fun label=>grouped_projectPair hn label l o hlo)
    have horiginal : original=(fun (_ : Fin (P+S) → Compiler.Bit) left right=>
        refreshProbability strategy hn i.val port H z (projectPair l o left) (projectPair l o right)) := by
      funext label left right
      dsimp only [original,Operations.Protocol.probabilities]
      rw [operation_probability,hi]
      symm
      exact refreshProbability_eq_answer strategy hn i.val port H z _ _ _ rfl
    refine ⟨replaceOriginal lifted original horiginal,?_,?_⟩
    · intro j first second heq
      have hl := oldWire_mem program i port (by rw [hi]; simp [Instruction.inputs])
      have ho := newWire_mem program i
      change base.factors.left (projectPair l o (fun w=>(first w).1)) j=
        base.factors.left (projectPair l o (fun w=>(second w).1)) j
      simp only [projectPair,heq l hl,heq o ho]
    · intro j first second heq
      have hl := oldWire_mem program i port (by rw [hi]; simp [Instruction.inputs])
      have ho := newWire_mem program i
      change base.factors.right (projectPair l o (fun w=>(first w).2)) j=
        base.factors.right (projectPair l o (fun w=>(second w).2)) j
      simp only [projectPair,heq l hl,heq o ho]
  | sample value =>
    have hfalse : ∀ label, valid' label→False := by
      intro label hh
      simpa [approximated,hi] using hh.2
    refine ⟨zeroCertificate (CompilerProof.DirectComposition.groupedLaw (encodingDistribution hn)) valid' original _ _ hβ hfalse,?_,?_⟩
    · intro j first second heq
      rfl
    · intro j first second heq
      rfl

/-- Any chronological physical template with distinct computation operands has the established local refresh and shortening certificates. Public sampler values do not enter the approximated-operation set. -/
def programPhysicalData {S : ℕ} (program : Operations.Program Compiler.Bit P S)
    (hd : program.DistinctInputs)
    (strategy : Operations.FixedStrategy Compiler.Bit ML MR BL BR n t P hdim)
    (hn : 2≤n) (defaultAnswer : Operations.Answer ML MR BL BR) :
    LocalData program.scope
      ((strategy.protocol hn).probabilities (fixed_strategy_local strategy hn) defaultAnswer program)
      (encodingDistribution hn) program.valid (approximated program)
      (betaParameter (Fintype.card (Refresh.U Compiler.Bit n)))
      (rawErrorParameter (Fintype.card (Refresh.U Compiler.Bit n))) where
  gate i h z := (operationCertificate program hd strategy hn defaultAnswer i h z).data
  left_locality i h z := (operationCertificate program hd strategy hn defaultAnswer i h z).left_locality
  right_locality i h z := (operationCertificate program hd strategy hn defaultAnswer i h z).right_locality

/-- All analytic inputs of the generic direct-composition proof are discharged for the compiled physical protocol. The certificate contains only established local estimates and port locality. -/
def physicalData (source : Compiler.Direct.Source P U T k)
    (strategy : Operations.FixedStrategy Compiler.Bit ML MR BL BR n t P hdim)
    (hn : 2≤n) (defaultAnswer : Operations.Answer ML MR BL BR) :
    LocalData source.compiledProgram.scope
      ((strategy.protocol hn).probabilities (fixed_strategy_local strategy hn) defaultAnswer source.compiledProgram)
      (encodingDistribution hn) source.compiledProgram.valid (approximated source.compiledProgram)
      (betaParameter (Fintype.card (Refresh.U Compiler.Bit n)))
      (rawErrorParameter (Fintype.card (Refresh.U Compiler.Bit n))) :=
  programPhysicalData source.compiledProgram source.compiled_distinct strategy hn defaultAnswer

end CompilerProof.Direct
