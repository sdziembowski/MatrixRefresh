import Mathlib.Data.List.GetD
import Proofs.Compiler.GateApproximation.MatrixPhase.LocalApproximationNetwork
import Proofs.Compiler.LocalComparisons.Framework.ProgramExecution



/-!
# The original local table of a syntactic program
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler.Composition.TopologicalExecution

open Refresh ErrorProcess

variable {F E A : Type*} [Mul F] [Sub F] [Fintype E] [Fintype A] {inputs T : ℕ}

namespace GateProtocol

/-- Values at unreachable history positions merely complete the total answer table. -/
/-
Mathematical definition (normal notation): For defaultAnswer ∈ A; history ∈ A*; n ∈ ℕ, define

completeHistory(defaultAnswer, history, n) := (i ↦ history.getD(i, defaultAnswer)).
-/
def completeHistory (defaultAnswer : A) (history : List A) (n : ℕ) : Fin n → A :=
  fun i => history.getD i.val defaultAnswer

/-- Every syntactic gate supplies a normalized answer distribution on every outer port tuple. The completed history is only used for unreachable lengths. -/
/- Mathematical definition (normal notation): For any syntactic gate, prior answer list, and complete encoding assignment, return the protocol's normalized conditional answer distribution on its three ports. Pad an underspecified history with the chosen default answer; actual chronological prefixes use their original entries. -/
noncomputable def gateAnswerDistribution (protocol : GateProtocol F E A inputs) (defaultAnswer : A) :
    {T : ℕ} → Program F inputs T → Fin T → List A → (Fin (inputs + T) → E) → FiniteDistribution A
  | 0, .nil, i, _, _ => Fin.elim0 i
  | t + 1, .snoc prior gate, i, history, encoding => Fin.lastCases
      (protocol.answer t gate (completeHistory defaultAnswer history t)
        (encoding gate.left.castSucc) (encoding gate.right.castSucc) (encoding (Fin.last _)))
      (fun j => protocol.gateAnswerDistribution defaultAnswer prior j history (Fin.init encoding)) i

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For protocol ∈ GateProtocol(F, E, A, inputs); defaultAnswer ∈ A; program ∈ Program(F, inputs, T); i ∈ {0,…,T-1}; history ∈ A*; a ∈ A, we have

Scoped(program.scope(i), ((encoding ↦ protocol.gateAnswerDistribution(defaultAnswer, program, i, history, encoding)(a)))).
-/
theorem gateAnswerDistribution_scoped (protocol : GateProtocol F E A inputs) (defaultAnswer : A)
    (program : Program F inputs T) (i : Fin T) (history : List A) (a : A) :
    Scoped (program.scope i) (fun encoding => (protocol.gateAnswerDistribution defaultAnswer program i history encoding).weight a) := by
  induction program with
  | nil => exact Fin.elim0 i
  | @snoc t prior gate ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Program.scope_last]
        intro first second heq
        have hl := heq gate.left.castSucc (by simp)
        have hr := heq gate.right.castSucc (by simp)
        have ho := heq (Fin.last (inputs + t)) (by simp)
        simp only [gateAnswerDistribution, Fin.lastCases_last, hl, hr]
        exact congrArg (fun output => (protocol.answer t gate
          (completeHistory defaultAnswer history t) (second gate.left.castSucc)
          (second gate.right.castSucc) output).weight a) ho
      · rw [Program.scope_old]
        intro first second heq
        simp only [gateAnswerDistribution, Fin.lastCases_castSucc]
        apply ih j
        intro w hw
        exact heq w.castSucc (Finset.mem_map_of_mem Fin.castSuccEmb hw)

/-- At a reachable chronological position, the total local answer table agrees exactly with the canonical sequential gate. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For protocol ∈ GateProtocol(F, E, A, inputs); defaultAnswer ∈ A; program ∈ Program(F, inputs, T); history ∈ A*; encoding ∈ {0,…,(inputs + T)-1} → E; a ∈ A, assume |history| < T. Then

protocol.chronologicalAnswerProb(program, history, encoding, a) = protocol.gateAnswerDistribution(defaultAnswer, program, |history|, history, encoding)(a).
-/
theorem chronological_eq_gateAnswerDistribution (protocol : GateProtocol F E A inputs) (defaultAnswer : A)
    (program : Program F inputs T) (history : List A) (hlt : history.length < T)
    (encoding : Fin (inputs + T) → E) (a : A) :
    protocol.chronologicalAnswerProb program history encoding a =
      (protocol.gateAnswerDistribution defaultAnswer program ⟨history.length, hlt⟩ history encoding).weight a := by
  induction program with
  | nil => omega
  | @snoc t prior gate ih =>
      by_cases hlast : history.length = t
      · have hi : (⟨history.length, hlt⟩ : Fin (t + 1)) = Fin.last t := Fin.ext hlast
        rw [hi]
        simp only [gateAnswerDistribution, Fin.lastCases_last, chronologicalAnswerProb, dif_pos hlast]
        have hh : completeHistory defaultAnswer history t =
            fun i : Fin t => history[i.val]'(by omega) := by
          funext i
          exact List.getD_eq_getElem history defaultAnswer (by omega)
        rw [hh]
      · have hprior : history.length < t := by omega
        have hi : (⟨history.length, hlt⟩ : Fin (t + 1)) = (⟨history.length, hprior⟩ : Fin t).castSucc := rfl
        rw [hi]
        simp only [gateAnswerDistribution, Fin.lastCases_castSucc, chronologicalAnswerProb, dif_neg hlast]
        exact ih hprior (Fin.init encoding)

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The concrete table on local left/right port vectors. Filling the unused outside wires with a fixed value has no effect by proved scope locality. -/
/-
Mathematical definition (normal notation): For protocol ∈ GateProtocol(F, (X × Y), A, inputs); defaultAnswer ∈ A; defaultEncoding ∈ X × Y; program ∈ Program(F, inputs, T); i ∈ {0,…,T-1}; history ∈ A*; a ∈ A; left ∈ {w | w ∈ program.scope(i)} → X; right ∈ {w | w ∈ program.scope(i)} → Y, define

localOriginal(protocol, defaultAnswer, defaultEncoding, program, i, history, a, left, right) := protocol.gateAnswerDistribution(defaultAnswer, program, i, history, joinScope(program.scope(i), ((w ↦ (left(w), right(w)))), ((x₁ ↦ defaultEncoding))))(a).
-/
noncomputable def localOriginal
    (protocol : GateProtocol F (X × Y) A inputs) (defaultAnswer : A) (defaultEncoding : X × Y)
    (program : Program F inputs T) (i : Fin T) (history : List A) (a : A)
    (left : {w // w ∈ program.scope i} → X) (right : {w // w ∈ program.scope i} → Y) : ℝ :=
  (protocol.gateAnswerDistribution defaultAnswer program i history
    (joinScope (program.scope i) (fun w => (left w, right w)) (fun _ => defaultEncoding))).weight a

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For protocol ∈ GateProtocol(F, (X × Y), A, inputs); defaultAnswer ∈ A; defaultEncoding ∈ X × Y; program ∈ Program(F, inputs, T); i ∈ {0,…,T-1}; history ∈ A*; a ∈ A; left ∈ {w | w ∈ program.scope(i)} → X; right ∈ {w | w ∈ program.scope(i)} → Y, we have

0 ≤ protocol.localOriginal(defaultAnswer, defaultEncoding, program, i, history, a, left, right).
-/
theorem localOriginal_nonneg
    (protocol : GateProtocol F (X × Y) A inputs) (defaultAnswer : A) (defaultEncoding : X × Y)
    (program : Program F inputs T) (i : Fin T) (history : List A) (a : A)
    (left : {w // w ∈ program.scope i} → X) (right : {w // w ∈ program.scope i} → Y) :
    0 ≤ protocol.localOriginal defaultAnswer defaultEncoding program i history a left right :=
  FiniteDistribution.nonneg _ a

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For protocol ∈ GateProtocol(F, (X × Y), A, inputs); defaultAnswer ∈ A; defaultEncoding ∈ X × Y; program ∈ Program(F, inputs, T); i ∈ {0,…,T-1}; history ∈ A*; left ∈ {w | w ∈ program.scope(i)} → X; right ∈ {w | w ∈ program.scope(i)} → Y, we have

(∑ₐ (protocol.localOriginal(defaultAnswer, defaultEncoding, program, i, history, a, left, right))) = 1.
-/
theorem localOriginal_total
    (protocol : GateProtocol F (X × Y) A inputs) (defaultAnswer : A) (defaultEncoding : X × Y)
    (program : Program F inputs T) (i : Fin T) (history : List A)
    (left : {w // w ∈ program.scope i} → X) (right : {w // w ∈ program.scope i} → Y) :
    (∑ a, protocol.localOriginal defaultAnswer defaultEncoding program i history a left right) = 1 :=
  FiniteDistribution.total _

/-- Reassembling a local table into the global network recovers the actual syntactic gate answer table, including on all off-fiber encodings. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For protocol ∈ GateProtocol(F, (X × Y), A, inputs); defaultAnswer ∈ A; defaultEncoding ∈ X × Y; program ∈ Program(F, inputs, T); i ∈ {0,…,T-1}; history ∈ A*; a ∈ A; encoding ∈ {0,…,(inputs + T)-1} → X × Y, we have

protocol.localOriginal(defaultAnswer, defaultEncoding, program, i, history, a, LocalApproximationData.leftPort(i, encoding), LocalApproximationData.rightPort(i, encoding)) = protocol.gateAnswerDistribution(defaultAnswer, program, i, history, encoding)(a).
-/
theorem localOriginal_restrict
    (protocol : GateProtocol F (X × Y) A inputs) (defaultAnswer : A) (defaultEncoding : X × Y)
    (program : Program F inputs T) (i : Fin T) (history : List A) (a : A)
    (encoding : Fin (inputs + T) → X × Y) :
    protocol.localOriginal defaultAnswer defaultEncoding program i history a
      (LocalApproximationData.leftPort i encoding) (LocalApproximationData.rightPort i encoding) =
        (protocol.gateAnswerDistribution defaultAnswer program i history encoding).weight a := by
  apply protocol.gateAnswerDistribution_scoped defaultAnswer program i history a
  intro w hw
  simp [LocalApproximationData.leftPort, LocalApproximationData.rightPort, joinScope_of_mem, hw]

/-- Common-truncation network construction preserves the actual original chronological answer table, so its canonicalDistribution is the sequential runner distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For protocol ∈ GateProtocol(F, (X × Y), A, inputs); defaultAnswer ∈ A; defaultEncoding ∈ X × Y; program ∈ Program(F, inputs, T); data ∈ LocalApproximationData(X = X, Y = Y, A = A, program.scope); B ∈ ℝ; wireDistribution ∈ F → 𝒟((X × Y)); input ∈ {0,…,inputs-1} → F; history ∈ A*; encoding ∈ {0,…,(inputs + T)-1} → X × Y; a ∈ A, assume data.original = protocol.localOriginal(defaultAnswer, defaultEncoding, program); 0 ≤ B; |history| < T. Then

answerTable(data.network(B))(((x₁ ↦ original)), history, encoding, a) = answerTable(protocol.canonicalRunner(wireDistribution, input, program))(history, encoding, a).
-/
theorem network_answerTable_eq
    (protocol : GateProtocol F (X × Y) A inputs) (defaultAnswer : A) (defaultEncoding : X × Y)
    (program : Program F inputs T)
    (data : LocalApproximationData (X := X) (Y := Y) (A := A) program.scope)
    (hdata : data.original = protocol.localOriginal defaultAnswer defaultEncoding program)
    (B : ℝ) (hB : 0 ≤ B) (wireDistribution : F → FiniteDistribution (X × Y)) (input : Fin inputs → F)
    (history : List A) (hlt : history.length < T) (encoding : Fin (inputs + T) → X × Y) (a : A) :
    (data.network B hB).answerTable (fun _ => .original) history encoding a =
      (protocol.canonicalRunner wireDistribution input program).answerTable history encoding a := by
  rw [protocol.canonical_answerTable]
  simp only [ScopedTables.answerTable, dif_pos hlt, ScopedTables.choose,
    LocalApproximationData.network, hdata]
  rw [protocol.localOriginal_restrict]
  exact (protocol.chronological_eq_gateAnswerDistribution defaultAnswer program history hlt encoding a).symm

/-- The exact physical original tables and local gate coupling close the actual-to-canonical premise of the signed-network composition theorem. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; protocol ∈ GateProtocol(F, (X × Y), A, inputs); defaultAnswer ∈ A; defaultEncoding ∈ X × Y; program ∈ Program(F, inputs, T); data ∈ LocalApproximationData(X = X, Y = Y, A = A, program.scope); B ∈ ℝ; decode ∈ X × Y → F; wireDistribution ∈ F → 𝒟((X × Y)); τ ∈ ℝ; input ∈ {0,…,inputs-1} → F; observe ∈ Answers(A, T) × ({0,…,(inputs + T)-1} → X × Y) → V, assume V is finite; data.original = protocol.localOriginal(defaultAnswer, defaultEncoding, program); 0 ≤ B; ∀ value, Supports(wireDistribution(value))(((encoding ↦ decode(encoding) = value))); ∀ t, gate, history, left, right, δ(protocol.real(t, gate, history, left, right), joint(wireDistribution(gate.kind.eval(decode(left), decode(right))))(protocol.answer(t, gate, history, left, right))) ≤ τ. Then

δ((((state ↦ observe(((answersEquiv(A, T))⁻¹((state)₂), (state)₁))))_*execute(protocol.realRunner(program))(independentDistribution(((i ↦ wireDistribution(input(i))))))), canonicalDistribution(data.network(B))(((w ↦ wireDistribution(program.eval(input, w)))), observe)) ≤ T · τ.
-/
theorem actual_network_distance {V : Type*} [Fintype V]
    (protocol : GateProtocol F (X × Y) A inputs) (defaultAnswer : A) (defaultEncoding : X × Y)
    (program : Program F inputs T)
    (data : LocalApproximationData (X := X) (Y := Y) (A := A) program.scope)
    (hdata : data.original = protocol.localOriginal defaultAnswer defaultEncoding program)
    (B : ℝ) (hB : 0 ≤ B) (decode : X × Y → F) (wireDistribution : F → FiniteDistribution (X × Y))
    (hsupport : ∀ value, (wireDistribution value).Supports (fun encoding => decode encoding = value))
    (τ : ℝ)
    (hgate : ∀ t gate history left right,
      statisticalDistance (protocol.real t gate history left right)
        ((wireDistribution (gate.kind.eval (decode left) (decode right))).joint
          (protocol.answer t gate history left right)) ≤ τ)
    (input : Fin inputs → F)
    (observe : Answers A T × (Fin (inputs + T) → X × Y) → V) :
    statisticalDistance
      (((protocol.realRunner program).execute (independentDistribution (fun i => wireDistribution (input i)))).map
        (fun state => observe ((answersEquiv A T).symm state.2, state.1)))
      ((data.network B hB).canonicalDistribution (fun w => wireDistribution (program.eval input w)) observe) ≤ (T : ℝ) * τ := by
  have h := Runner.actual_canonical_network_distance_on_support
    (fun i => wireDistribution (input i)) (protocol.realRunner program)
    (protocol.canonicalRunner wireDistribution input program) τ
    (protocol.real_canonical_coupled decode wireDistribution hsupport τ hgate input program)
    (data.network B hB) (protocol.network_answerTable_eq defaultAnswer defaultEncoding program data hdata B hB wireDistribution input)
    observe
  simpa only [protocol.canonical_wireDistributions] using h

end GateProtocol

end CircuitCompiler.Composition.TopologicalExecution
