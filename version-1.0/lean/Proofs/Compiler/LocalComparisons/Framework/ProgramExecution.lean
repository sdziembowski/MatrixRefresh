import Proofs.Compiler.LocalComparisons.Framework.CanonicalExecution
import Proofs.Compiler.LocalComparisons.Framework.CircuitScopes
import Proofs.Compiler.Construction.Parameters



/-!
# Executing the stated circuit syntax with local randomized gate answer tables
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler.Composition.TopologicalExecution

open Refresh

universe u v w

variable {F : Type u} {E : Type v} {A : Type w}
  [Mul F] [Sub F] [Fintype E] [Fintype A] {inputs T : ℕ}

namespace GateProtocol

/- Mathematical definition (normal notation): At each gate, independently sample a fresh encoding of its correct plaintext output, then sample the protocol's conditional answer given the two old operand encodings and that new output. Iterate this procedure chronologically. -/
noncomputable def canonicalRunner (protocol : GateProtocol F E A inputs)
    (wireDistribution : F → FiniteDistribution E) (input : Fin inputs → F) :
    {T : ℕ} → Program F inputs T → Canonical E A inputs T
  | 0, .nil => .nil
  | t + 1, .snoc prior gate => .snoc (protocol.canonicalRunner wireDistribution input prior)
      (wireDistribution (gate.eval (prior.eval input)))
      (fun state output => protocol.answer t gate state.2
        (state.1 gate.left) (state.1 gate.right) output)

/-- Each canonical wire distribution is the encoding distribution of its actual circuit value. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For protocol ∈ GateProtocol(F, E, A, inputs); wireDistribution ∈ F → 𝒟(E); input ∈ {0,…,inputs-1} → F; program ∈ Program(F, inputs, T), we have

wireDistributions(protocol.canonicalRunner(wireDistribution, input, program))(((i ↦ wireDistribution(input(i))))) = (w ↦ wireDistribution(program.eval(input, w))).
-/
theorem canonical_wireDistributions (protocol : GateProtocol F E A inputs)
    (wireDistribution : F → FiniteDistribution E) (input : Fin inputs → F) (program : Program F inputs T) :
    (protocol.canonicalRunner wireDistribution input program).wireDistributions (fun i => wireDistribution (input i)) =
      fun w => wireDistribution (program.eval input w) := by
  induction program with
  | nil => rfl
  | @snoc t prior gate ih =>
      funext w
      refine Fin.lastCases ?_ (fun j => ?_) w
      · simp [canonicalRunner, Canonical.wireDistributions, Program.eval]
      · simp [canonicalRunner, Canonical.wireDistributions, Program.eval, ih]

/-- The physical gate estimate is used only on correctly typed canonical prefixes; their types follow from the per-wire encoding support. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For protocol ∈ GateProtocol(F, E, A, inputs); decode ∈ E → F; wireDistribution ∈ F → 𝒟(E); τ ∈ ℝ; input ∈ {0,…,inputs-1} → F; program ∈ Program(F, inputs, T), assume ∀ value, Supports(wireDistribution(value))(((encoding ↦ decode(encoding) = value))); ∀ t, gate, history, left, right, δ(protocol.real(t, gate, history, left, right), joint(wireDistribution(gate.kind.eval(decode(left), decode(right))))(protocol.answer(t, gate, history, left, right))) ≤ τ. Then

CoupledOn(protocol.realRunner(program))(independentDistribution(((i ↦ wireDistribution(input(i))))), τ, runner(protocol.canonicalRunner(wireDistribution, input, program))).
-/
theorem real_canonical_coupled (protocol : GateProtocol F E A inputs)
    (decode : E → F) (wireDistribution : F → FiniteDistribution E)
    (hsupport : ∀ value, (wireDistribution value).Supports (fun encoding => decode encoding = value))
    (τ : ℝ)
    (hgate : ∀ t gate history left right,
      statisticalDistance (protocol.real t gate history left right)
        ((wireDistribution (gate.kind.eval (decode left) (decode right))).joint
          (protocol.answer t gate history left right)) ≤ τ)
    (input : Fin inputs → F) (program : Program F inputs T) :
    (protocol.realRunner program).CoupledOn (independentDistribution (fun i => wireDistribution (input i))) τ
      (protocol.canonicalRunner wireDistribution input program).runner := by
  induction program with
  | nil => trivial
  | @snoc t prior gate ih =>
      refine ⟨ih, ?_⟩
      intro state hstate
      have hvalid (w : Fin (inputs + t)) : decode (state.1 w) = prior.eval input w := by
        have h := (protocol.canonicalRunner wireDistribution input prior).execute_support
          (fun i => wireDistribution (input i)) (fun w encoding => decode encoding = prior.eval input w)
          (by intro w; rw [protocol.canonical_wireDistributions]; exact hsupport _)
        exact h state hstate w
      have h := hgate t gate state.2 (state.1 gate.left) (state.1 gate.right)
      simpa only [realRunner, canonicalRunner, Canonical.runner, hvalid,
        Gate.eval] using h

/-- Full topological execution is coupled to fresh wire encodings, retaining all operands, every output, and the entire adaptive transcript. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For protocol ∈ GateProtocol(F, E, A, inputs); decode ∈ E → F; wireDistribution ∈ F → 𝒟(E); τ ∈ ℝ; input ∈ {0,…,inputs-1} → F; program ∈ Program(F, inputs, T), assume ∀ value, Supports(wireDistribution(value))(((encoding ↦ decode(encoding) = value))); ∀ t, gate, history, left, right, δ(protocol.real(t, gate, history, left, right), joint(wireDistribution(gate.kind.eval(decode(left), decode(right))))(protocol.answer(t, gate, history, left, right))) ≤ τ. Then

δ(execute(protocol.realRunner(program))(independentDistribution(((i ↦ wireDistribution(input(i)))))), runner.execute(protocol.canonicalRunner(wireDistribution, input, program))(independentDistribution(((i ↦ wireDistribution(input(i))))))) ≤ T · τ.
-/
theorem real_canonical_distance (protocol : GateProtocol F E A inputs)
    (decode : E → F) (wireDistribution : F → FiniteDistribution E)
    (hsupport : ∀ value, (wireDistribution value).Supports (fun encoding => decode encoding = value))
    (τ : ℝ)
    (hgate : ∀ t gate history left right,
      statisticalDistance (protocol.real t gate history left right)
        ((wireDistribution (gate.kind.eval (decode left) (decode right))).joint
          (protocol.answer t gate history left right)) ≤ τ)
    (input : Fin inputs → F) (program : Program F inputs T) :
    statisticalDistance
      ((protocol.realRunner program).execute (independentDistribution (fun i => wireDistribution (input i))))
      ((protocol.canonicalRunner wireDistribution input program).runner.execute
        (independentDistribution (fun i => wireDistribution (input i)))) ≤ (T : ℝ) * τ :=
  Runner.execute_distance_on_support _ _ _ τ
    (protocol.real_canonical_coupled decode wireDistribution hsupport τ hgate input program)

/-- A local answer table independent of the secret input assignment. Its chronological position determines which syntactic gate is being queried. -/
/- Mathematical definition (normal notation): For a previous answer prefix, use its length to identify the next source gate. Read that gate's two operand encodings and output encoding from the complete assignment, and evaluate its conditional answer probability. The table contains no separate plaintext-label parameter. -/
noncomputable def chronologicalAnswerProb (protocol : GateProtocol F E A inputs) :
    {T : ℕ} → Program F inputs T → List A → (Fin (inputs + T) → E) → A → ℝ
  | 0, .nil, _, _, _ => 0
  | t + 1, .snoc prior gate, history, encoding, a =>
      if h : history.length = t then
        (protocol.answer t gate (fun i => history[i.val]'(by omega))
          (encoding gate.left.castSucc) (encoding gate.right.castSucc)
          (encoding (Fin.last _))).weight a
      else protocol.chronologicalAnswerProb prior history (Fin.init encoding) a

/-- Canonical executions for different secret inputs use exactly the same local answer table, even though their fresh wire distributions differ. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For protocol ∈ GateProtocol(F, E, A, inputs); wireDistribution ∈ F → 𝒟(E); input ∈ {0,…,inputs-1} → F; program ∈ Program(F, inputs, T), we have

answerTable(protocol.canonicalRunner(wireDistribution, input, program)) = protocol.chronologicalAnswerProb(program).
-/
theorem canonical_answerTable (protocol : GateProtocol F E A inputs)
    (wireDistribution : F → FiniteDistribution E) (input : Fin inputs → F) (program : Program F inputs T) :
    (protocol.canonicalRunner wireDistribution input program).answerTable = protocol.chronologicalAnswerProb program := by
  induction program with
  | nil => rfl
  | @snoc t prior gate ih =>
      funext history encoding a
      simp only [canonicalRunner, Canonical.answerTable, chronologicalAnswerProb, ih]
      rfl

/-- The common chronological answer table reads only the gate's two operands and its own output, despite arbitrary dependence on previous answers. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For protocol ∈ GateProtocol(F, E, A, inputs); program ∈ Program(F, inputs, T); history ∈ A*; a ∈ A, assume |history| < T. Then

Scoped(program.scope(|history|), ((encoding ↦ protocol.chronologicalAnswerProb(program, history, encoding, a)))).
-/
theorem chronological_scoped (protocol : GateProtocol F E A inputs)
    (program : Program F inputs T) (history : List A) (hlt : history.length < T) (a : A) :
    Scoped (program.scope ⟨history.length, hlt⟩)
      (fun encoding => protocol.chronologicalAnswerProb program history encoding a) := by
  induction program with
  | nil => omega
  | @snoc t prior gate ih =>
      by_cases hlast : history.length = t
      · have hi : (⟨history.length, hlt⟩ : Fin (t + 1)) = Fin.last t := Fin.ext hlast
        rw [hi, Program.scope_last]
        intro first second heq
        have hl := heq gate.left.castSucc (by simp)
        have hr := heq gate.right.castSucc (by simp)
        have ho := heq (Fin.last (inputs + t)) (by simp)
        simp only [chronologicalAnswerProb, dif_pos hlast, hl, hr]
        exact congrArg (fun output => (protocol.answer t gate
          (fun i => history[i.val]'(by omega)) (second gate.left.castSucc)
          (second gate.right.castSucc) output).weight a) ho
      · have hprior : history.length < t := by omega
        have hi : (⟨history.length, hlt⟩ : Fin (t + 1)) = (⟨history.length, hprior⟩ : Fin t).castSucc := rfl
        rw [hi, Program.scope_old]
        intro first second heq
        simp only [chronologicalAnswerProb, dif_neg hlast]
        apply ih hprior
        intro w hw
        exact heq w.castSucc (Finset.mem_map_of_mem Fin.castSuccEmb hw)

end GateProtocol

end CircuitCompiler.Composition.TopologicalExecution
