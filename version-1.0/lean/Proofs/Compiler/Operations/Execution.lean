import Proofs.Compiler.Operations.OperationLaws
import Proofs.Compiler.Operations.Program
import Proofs.Compiler.LocalComparisons.Framework.CanonicalExecution
import Proofs.Compiler.LocalComparisons.Framework.ProgramNetwork
import Proofs.Compiler.LocalComparisons.NetworkInterface
import Proofs.Compiler.LocalComparisons.ScopedSplit

/-!
# The exact canonical experiment for heterogeneous operations

Each operation allocates a fresh encoding of its ordinary output label, then samples its actual answer conditional on that new encoding. The independent wire experiment is an unconditional distribution identity. It does not assert independence of wire encodings after observing the answer transcript.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open scoped BigOperators Classical

namespace CircuitCompiler.Operations.Protocol

open Refresh MatrixRefresh _root_.CircuitCompiler.Composition
  _root_.CircuitCompiler.Composition.TopologicalExecution
  _root_.CircuitCompiler.AveragedEnergyComparison

variable {F E A V : Type*} [Mul F] [Sub F]
  [Fintype E] [DecidableEq E] [Fintype A] [Fintype V] {inputs S : ℕ}

/-- Dependence only on predecessor ports is a pure locality property of an operation distribution. The concrete physical strategies satisfy it by construction. -/
def Local (protocol : Protocol F E A inputs) : Prop :=
  ∀ i instruction history first second,
    (∀ w ∈ instruction.inputs, first w = second w) →
      protocol.real i instruction history first = protocol.real i instruction history second

/-- Sequentially sample fresh wire encodings and the complete conditional answer, in the same forward physical order. -/
def canonicalRunner (protocol : Protocol F E A inputs)
    (law : F → FiniteDistribution E) (input : Fin inputs → F) :
    {S : ℕ} → Operations.Program F inputs S → Canonical E A inputs S
  | 0,.nil => .nil
  | _+1,.snoc prior instruction => .snoc (canonicalRunner protocol law input prior)
      (law (instruction.eval (prior.eval input)))
      (fun state output => protocol.answer _ instruction state.2 state.1 output)

/-- The distributions of all wires are their ordinary evaluated labels. -/
theorem canonical_wireDistributions (protocol : Protocol F E A inputs)
    (law : F → FiniteDistribution E) (input : Fin inputs → F)
    (program : Operations.Program F inputs S) :
    (protocol.canonicalRunner law input program).wireDistributions (fun i => law (input i)) =
      fun w => law (program.eval input w) := by
  induction program with
  | nil => rfl
  | @snoc S prior instruction ih =>
    funext w
    refine Fin.lastCases ?_ (fun j => ?_) w
    · simp [canonicalRunner,Canonical.wireDistributions,Operations.Program.eval]
    · simp [canonicalRunner,Canonical.wireDistributions,Operations.Program.eval,ih]

/-- Local freshness is used only on correctly labelled supported prefixes. -/
theorem real_canonical_coupled (protocol : Protocol F E A inputs)
    (decode : E → F) (law : F → FiniteDistribution E)
    (hsupport : ∀ s, (law s).Supports (fun e => decode e = s))
    (hgate : ∀ i instruction history old,
      statisticalDistance (protocol.real i instruction history old)
        ((law (instruction.eval (fun w => decode (old w)))).joint
          (protocol.answer i instruction history old)) ≤ 0)
    (input : Fin inputs → F) (program : Operations.Program F inputs S) :
    (protocol.realRunner program).CoupledOn (independentDistribution (fun i => law (input i))) 0
      (protocol.canonicalRunner law input program).runner := by
  induction program with
  | nil => trivial
  | @snoc S prior instruction ih =>
    refine ⟨ih,?_⟩
    intro state hstate
    have hvalid (w : Fin (inputs+S)) : decode (state.1 w) = prior.eval input w := by
      have h := (protocol.canonicalRunner law input prior).execute_support
        (fun i => law (input i)) (fun w e => decode e = prior.eval input w)
        (by intro w; rw [canonical_wireDistributions]; exact hsupport _)
      exact h state hstate w
    have he : (fun w => decode (state.1 w)) = prior.eval input := funext hvalid
    simpa only [realRunner,canonicalRunner,Canonical.runner,he] using
      hgate S instruction state.2 state.1

/-- With exact output freshness, the actual runner and the canonical runner have the same complete joint distribution, without endpoint losses. -/
theorem real_eq_canonical (protocol : Protocol F E A inputs)
    (decode : E → F) (law : F → FiniteDistribution E)
    (hsupport : ∀ s, (law s).Supports (fun e => decode e = s))
    (hgate : ∀ i instruction history old,
      statisticalDistance (protocol.real i instruction history old)
        ((law (instruction.eval (fun w => decode (old w)))).joint
          (protocol.answer i instruction history old)) ≤ 0)
    (input : Fin inputs → F) (program : Operations.Program F inputs S) :
    (protocol.realRunner program).execute (independentDistribution (fun i => law (input i))) =
      (protocol.canonicalRunner law input program).runner.execute
        (independentDistribution (fun i => law (input i))) := by
  apply CompilerProof.Canonical.eq_of_distance_nonpos
  have h := Runner.execute_distance_on_support _ _ _ 0
    (protocol.real_canonical_coupled decode law hsupport hgate input program)
  simpa only [mul_zero] using h

/-- The chronological conditional table, independent of the private labels. -/
def chronologicalAnswerProb (protocol : Protocol F E A inputs) :
    {S : ℕ} → Operations.Program F inputs S → List A → (Fin (inputs+S) → E) → A → ℝ
  | 0,.nil,_,_,_ => 0
  | s+1,.snoc prior instruction,history,encoding,a =>
    if h : history.length=s then
      (protocol.answer s instruction (fun i => history[i.val]'(by omega))
        (Fin.init encoding) (encoding (Fin.last _))).weight a
    else chronologicalAnswerProb protocol prior history (Fin.init encoding) a

/-- Ordinary and canonical executions use the same chronological answers. -/
theorem canonical_answerTable (protocol : Protocol F E A inputs)
    (law : F → FiniteDistribution E) (input : Fin inputs → F)
    (program : Operations.Program F inputs S) :
    (protocol.canonicalRunner law input program).answerTable = protocol.chronologicalAnswerProb program := by
  induction program with
  | nil => rfl
  | @snoc S prior instruction ih =>
    funext history encoding a
    simp only [canonicalRunner,Canonical.answerTable,chronologicalAnswerProb,ih]

/-- A normalized total conditional distribution for every formal history and complete encoding assignment, including impossible public-sampler outputs. -/
def operationAnswerDistribution (protocol : Protocol F E A inputs) (defaultAnswer : A) :
    {S : ℕ} → Operations.Program F inputs S → Fin S → List A →
      (Fin (inputs+S) → E) → FiniteDistribution A
  | 0,.nil,i,_,_ => Fin.elim0 i
  | s+1,.snoc prior instruction,i,history,encoding => Fin.lastCases
    (protocol.answer s instruction (GateProtocol.completeHistory defaultAnswer history s)
      (Fin.init encoding) (encoding (Fin.last _)))
    (fun j => operationAnswerDistribution protocol defaultAnswer prior j history (Fin.init encoding)) i

/-- Complete operation answers depend only on the operation's full local scope. -/
theorem operationAnswerDistribution_scoped (protocol : Protocol F E A inputs) (hlocal : protocol.Local)
    (defaultAnswer : A) (program : Operations.Program F inputs S) (i : Fin S)
    (history : List A) (a : A) : Scoped (program.scope i)
      (fun encoding => (protocol.operationAnswerDistribution defaultAnswer program i history encoding).weight a) := by
  induction program with
  | nil => exact Fin.elim0 i
  | @snoc S prior instruction ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Operations.Program.scope_snoc_last]
      intro first second heq
      have ho := heq (Fin.last (inputs+S)) (by simp)
      have hi : ∀ w ∈ instruction.inputs, (Fin.init first) w = (Fin.init second) w := by
        intro w hw
        exact heq w.castSucc (Finset.mem_insert_of_mem (Finset.mem_map_of_mem Fin.castSuccEmb hw))
      simp only [operationAnswerDistribution,Fin.lastCases_last,answer]
      rw [hlocal S instruction _ _ _ hi]
      exact congrArg (fun output => ((conditional
        (protocol.real S instruction (GateProtocol.completeHistory defaultAnswer history S)
          (Fin.init second)) Prod.fst output).map Prod.snd).weight a) ho
    · rw [Operations.Program.scope_snoc_old]
      intro first second heq
      simp only [operationAnswerDistribution,Fin.lastCases_castSucc]
      apply ih j
      intro w hw
      exact heq w.castSucc (Finset.mem_map_of_mem Fin.castSuccEmb hw)

/-- Total formal histories coincide with the actual chronological prefix. -/
theorem chronological_eq_operationAnswerDistribution (protocol : Protocol F E A inputs)
    (defaultAnswer : A) (program : Operations.Program F inputs S)
    (history : List A) (hlt : history.length<S) (encoding : Fin (inputs+S) → E) (a : A) :
    protocol.chronologicalAnswerProb program history encoding a =
      (protocol.operationAnswerDistribution defaultAnswer program ⟨history.length,hlt⟩ history encoding).weight a := by
  induction program with
  | nil => omega
  | @snoc S prior instruction ih =>
    by_cases hlast : history.length=S
    · have hi : (⟨history.length,hlt⟩ : Fin (S+1)) = Fin.last S := Fin.ext hlast
      rw [hi]
      simp only [operationAnswerDistribution,Fin.lastCases_last,chronologicalAnswerProb,dif_pos hlast]
      have hh : GateProtocol.completeHistory defaultAnswer history S =
          fun i : Fin S => history[i.val]'(by omega) := by
        funext i
        exact List.getD_eq_getElem history defaultAnswer (by omega)
      rw [hh]
    · have hp : history.length<S := by omega
      have hi : (⟨history.length,hlt⟩ : Fin (S+1)) = (⟨history.length,hp⟩ : Fin S).castSucc := rfl
      rw [hi]
      simp only [operationAnswerDistribution,Fin.lastCases_castSucc,chronologicalAnswerProb,dif_neg hlast]
      exact ih hp (Fin.init encoding)

/-- The true unsigned probability network is normalized at every encoding, including publicly inconsistent labels. Public samplers stay in this network. -/
def probabilities (protocol : Protocol F E A inputs) (hlocal : protocol.Local)
    (defaultAnswer : A) (program : Operations.Program F inputs S) :
    ScopedProbabilities (E := E) (A := A) program.scope where
  prob i h e a := (protocol.operationAnswerDistribution defaultAnswer program i h e).weight a
  nonneg _ _ _ _ := FiniteDistribution.nonneg _ _
  total_le _ _ _ := (FiniteDistribution.total _).le
  locality := operationAnswerDistribution_scoped protocol hlocal defaultAnswer program

/-- A zero signed component is sufficient for the exact canonical identity. -/
private def canonicalAdapter (protocol : Protocol F E A inputs) (hlocal : protocol.Local)
    (defaultAnswer : A) (program : Operations.Program F inputs S) :
    ScopedTables (E := E) (A := A) program.scope 0 where
  original i h e a := (protocol.operationAnswerDistribution defaultAnswer program i h e).weight a
  real i h e a := (protocol.operationAnswerDistribution defaultAnswer program i h e).weight a
  signed _ _ _ _ := 0
  original_nonneg _ _ _ _ := FiniteDistribution.nonneg _ _
  original_total _ _ _ := FiniteDistribution.total _
  real_nonneg _ _ _ _ := FiniteDistribution.nonneg _ _
  real_total_le _ _ _ := (FiniteDistribution.total _).le
  signed_budget _ _ _ := by simp
  original_scoped := operationAnswerDistribution_scoped protocol hlocal defaultAnswer program
  real_scoped := operationAnswerDistribution_scoped protocol hlocal defaultAnswer program
  signed_scoped _ _ _ _ _ _ := rfl

/-- The canonical distribution at arbitrary wire labels. These labels need not obey the program's equations during the signed comparison. -/
def canonicalNetworkView (protocol : Protocol F E A inputs) (hlocal : protocol.Local)
    (defaultAnswer : A) (program : Operations.Program F inputs S) (law : F → FiniteDistribution E)
    (label : Fin (inputs+S) → F) (observe : Answers A S × (Fin (inputs+S) → E) → V) :
    FiniteDistribution V :=
  (canonicalAdapter protocol hlocal defaultAnswer program).canonicalDistribution
    (fun w => law (label w)) observe

/-- Exact sequential-to-independent-wire identity, retaining all answers and any finite observation of the complete final encoding assignment. -/
theorem canonicalRunner_observed_eq (protocol : Protocol F E A inputs) (hlocal : protocol.Local)
    (defaultAnswer : A) (program : Operations.Program F inputs S) (law : F → FiniteDistribution E)
    (input : Fin inputs → F) (observe : Answers A S × (Fin (inputs+S) → E) → V) :
    (((protocol.canonicalRunner law input program).runner.execute
      (independentDistribution (fun i => law (input i)))).map
      (fun state => observe ((answersEquiv A S).symm state.2,state.1))) =
      protocol.canonicalNetworkView hlocal defaultAnswer program law (program.eval input) observe := by
  have hk : ∀ history, history.length<S → ∀ encoding a,
      (canonicalAdapter protocol hlocal defaultAnswer program).answerTable (fun _ => .original)
        history encoding a = (protocol.canonicalRunner law input program).answerTable history encoding a := by
    intro history hlt encoding a
    rw [protocol.canonical_answerTable]
    simp only [ScopedTables.answerTable,dif_pos hlt,ScopedTables.choose,canonicalAdapter]
    exact (protocol.chronological_eq_operationAnswerDistribution defaultAnswer program history hlt encoding a).symm
  rw [Canonical.execute_eq_network _ _ (canonicalAdapter protocol hlocal defaultAnswer program) hk]
  rw [FiniteDistribution.map_map,canonical_wireDistributions]
  simp only [canonicalNetworkView,ScopedTables.canonicalDistribution,Function.comp_def,stateAnswerEquiv,
    Equiv.prodCongr_apply,Equiv.refl_apply,Prod.map,Equiv.symm_apply_apply]

/-- The unsigned network's scalar weights are exactly those used by the signed walk, with its arbitrary signed table ignored at the empty signed set. -/
theorem canonicalNetworkView_weight (protocol : Protocol F E A inputs) (hlocal : protocol.Local)
    (defaultAnswer : A) (program : Operations.Program F inputs S) (law : F → FiniteDistribution E)
    (label : Fin (inputs+S) → F) (observe : Answers A S × (Fin (inputs+S) → E) → V)
    (unused : Fin S → List A → (Fin (inputs+S) → E) → A → ℝ) :
    (protocol.canonicalNetworkView hlocal defaultAnswer program law label observe).weight =
      ErrorProcess.observedWeight (independentDistribution (fun w => law (label w)))
        (ErrorProcess.fromTables ((protocol.probabilities hlocal defaultAnswer program).mixed unused ∅)
          (fun _ _ => 1) S []) observe := by
  rw [canonicalNetworkView,ScopedTables.canonicalDistribution_weight]
  unfold ScopedTables.view ScopedTables.process
  congr 2

end CircuitCompiler.Operations.Protocol

namespace CompilerProof.Operations

open Refresh MatrixRefresh CircuitCompiler CircuitCompiler.Operations
  CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution
  CircuitCompiler.AveragedEnergyComparison

variable {F ML MR BL BR V : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR] [Fintype V]
  {n t inputs S : ℕ} {hdim : n*n+1 = n+t}

/-- Physical callbacks receive only the active operation's predecessor shares. -/
theorem strategy_local
    (strategy : Operations.Strategy F ML MR BL BR n t inputs hdim) (hn : 2 ≤ n) :
    (strategy.protocol hn).Local := by
  intro i instruction history first second heq
  cases instruction with
  | compute gate =>
    have hl := heq gate.left (by simp [Instruction.inputs])
    have hr := heq gate.right (by simp [Instruction.inputs])
    simp only [Operations.Strategy.protocol,hl,hr]
  | refresh port =>
    have h := heq port (by simp [Instruction.inputs])
    simp only [Operations.Strategy.protocol,h]
  | sample value => rfl

/-- Fixing independent prefixes preserves the same physical gate locality. -/
theorem fixed_strategy_local
    (strategy : Operations.FixedStrategy F ML MR BL BR n t inputs hdim) (hn : 2 ≤ n) :
    (strategy.protocol hn).Local := by
  intro i instruction history first second heq
  cases instruction with
  | compute gate =>
    have hl := heq gate.left (by simp [Instruction.inputs])
    have hr := heq gate.right (by simp [Instruction.inputs])
    simp only [Operations.FixedStrategy.protocol,hl,hr]
  | refresh port =>
    have h := heq port (by simp [Instruction.inputs])
    simp only [Operations.FixedStrategy.protocol,h]
  | sample value => rfl

/-- Exact canonical representation of any fixed-prefix heterogeneous program, including raw H retries, control refreshes and unsigned public samplers. -/
theorem fixed_canonical_eq
    (strategy : Operations.FixedStrategy F ML MR BL BR n t inputs hdim)
    (hq : fieldCard F = 2) (hn : 2 ≤ n) (defaultAnswer : Operations.Answer ML MR BL BR)
    (program : Operations.Program F inputs S) (input : Fin inputs → F)
    (observe : Answers (Operations.Answer ML MR BL BR) S ×
      (Fin (inputs+S) → U F n × U F n) → V) :
    ((((strategy.protocol hn).realRunner program).execute
      (independentDistribution (fun i => encodingDistribution hn (input i)))).map
      (fun state => observe ((answersEquiv _ _).symm state.2,state.1))) =
      (strategy.protocol hn).canonicalNetworkView (fixed_strategy_local strategy hn)
        defaultAnswer program (encodingDistribution hn) (program.eval input) observe := by
  have hgate : ∀ i instruction history old,
      statisticalDistance ((strategy.protocol hn).real i instruction history old)
        ((encodingDistribution hn (instruction.eval (fun w =>
          secret ((stateEquivProd F n).symm (old w))))).joint
          ((strategy.protocol hn).answer i instruction history old)) ≤ 0 := by
    intro i instruction history old
    rw [fixed_real_joint strategy hq hn]
    exact (statisticalDistance_self _).le
  rw [(strategy.protocol hn).real_eq_canonical
    (fun e => secret ((stateEquivProd F n).symm e)) (encodingDistribution hn)
    (encodingDistribution_supports hn) hgate input program]
  exact (strategy.protocol hn).canonicalRunner_observed_eq (fixed_strategy_local strategy hn)
    defaultAnswer program (encodingDistribution hn) input observe

end CompilerProof.Operations
