import Proofs.Compiler.Model

/-!
# Plaintext semantics of source unrolling

Appending public samplers leaves older source values unchanged. Appending a NAND source embeds its ordinary evaluation. These two identities prove that the retained register addresses and designated outputs implement the repeated transition circuit, including aliases and direct input outputs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace Compiler.Stateful
open Compiler.Direct CircuitCompiler

/-- Appending one scalar to a tuple does not change a position strictly before its new last position. -/
theorem snoc_old {N : ℕ} (f : Fin N → Bit) (value : Bit) (w : Fin (N+1)) (h : w.val < N) :
    Fin.snoc (α := fun _ => Bit) f value w = f ⟨w.val,h⟩ := by
  have hw : w = (⟨w.val,h⟩ : Fin N).castSucc := Fin.ext rfl
  exact (congrArg (Fin.snoc (α := fun _ => Bit) f value) hw).trans (by simp only [Fin.snoc_castSucc])

namespace Schedule
variable {J : Type*} {P U T : ℕ}

/-- Every older logical source wire retains its value when a public-input block is appended. -/
theorem appendSamples_old (schedule : Schedule J P U T) (input : Fin P → Bit)
    (publicValues : J → Bit) {d : ℕ} (tags : Fin d → J) (w : Fin (P+U+T)) :
    (schedule.appendSamples tags).evaluate input publicValues
      ⟨w.val, by have := w.isLt; omega⟩ = schedule.evaluate input publicValues w := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [appendSamples, evaluate]
    rw [snoc_old _ _ _ (by
      have hbound : w.val < P + (U + d) + T := by
        have := w.isLt
        omega
      simpa only [Fin.val_cast] using hbound)]
    exact ih (fun i => tags i.castSucc)

/-- A freshly sampled public source wire contains its specified tagged bit, in the original input order. -/
theorem appendSamples_new (schedule : Schedule J P U T) (input : Fin P → Bit)
    (publicValues : J → Bit) {d : ℕ} (tags : Fin d → J) (j : Fin d) :
    (schedule.appendSamples tags).evaluate input publicValues
      ⟨P+U+T+j.val, by have := j.isLt; omega⟩ = publicValues (tags j) := by
  induction d with
  | zero => exact Fin.elim0 j
  | succ d ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [appendSamples, evaluate, Fin.val_last]
      have hw : (Fin.cast (by omega) (⟨P+U+T+d, by omega⟩ : Fin (P+(U+(d+1))+T)) :
          Fin (P+(U+d)+T+1)) = Fin.last (P+(U+d)+T) := by
        apply Fin.ext
        dsimp
        omega
      rw [hw, Fin.snoc_last]
    · simp only [appendSamples, evaluate, Fin.val_castSucc]
      rw [snoc_old _ _ _ (by
        have hbound : P + U + T + j.val < P + (U + d) + T := by
          have := j.isLt
          omega
        simpa only [Fin.val_cast] using hbound)]
      exact ih (fun i => tags i.castSucc) j

/-- The first public-sampler block preserves its trusted private inputs. -/
theorem initialSamples_old (input : Fin P → Bit) (publicValues : J → Bit)
    {d : ℕ} (tags : Fin d → J) (j : Fin P) :
    (initialSamples tags).evaluate input publicValues ⟨j.val, by have := j.isLt; omega⟩ = input j := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [initialSamples, evaluate]
    rw [snoc_old _ _ _ (by have := j.isLt; dsimp; omega)]
    exact ih (fun i => tags i.castSucc)

/-- Every sampler in the first public block contains its tagged value. -/
theorem initialSamples_new (input : Fin P → Bit) (publicValues : J → Bit)
    {d : ℕ} (tags : Fin d → J) (j : Fin d) :
    (initialSamples tags).evaluate input publicValues ⟨P+j.val, by have := j.isLt; omega⟩ =
      publicValues (tags j) := by
  induction d with
  | zero => exact Fin.elim0 j
  | succ d ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [initialSamples, evaluate, Fin.val_last]
      have hw : (Fin.cast (by omega) (⟨P+d, by omega⟩ : Fin (P+(d+1)+0)) :
          Fin (P+d+0+1)) = Fin.last (P+d+0) := by apply Fin.ext; rfl
      rw [hw, Fin.snoc_last]
    · simp only [initialSamples, evaluate, Fin.val_castSucc]
      rw [snoc_old _ _ _ (by have := j.isLt; dsimp; omega)]
      exact ih (fun i => tags i.castSucc) j

/-- Embedding a NAND program preserves every prior source value and computes each of its mapped wires exactly. -/
theorem appendGates_evaluate {inputs g : ℕ} (schedule : Schedule J P U T)
    (ports : Fin inputs → Fin (P+U+T)) (program : NandProgram inputs g)
    (input : Fin P → Bit) (publicValues : J → Bit) :
    (∀ w : Fin (P+U+T),
      (schedule.appendGates ports program).schedule.evaluate input publicValues
        ⟨w.val, by have := w.isLt; omega⟩ = schedule.evaluate input publicValues w) ∧
    (∀ w, (schedule.appendGates ports program).schedule.evaluate input publicValues
      ((schedule.appendGates ports program).wires w) =
        program.eval (fun j => schedule.evaluate input publicValues (ports j)) w) := by
  induction program with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | @snoc g prior left right ih =>
    constructor
    · intro w
      simp only [appendGates, evaluate]
      rw [snoc_old _ _ _ (by have := w.isLt; dsimp; omega)]
      exact ih.1 w
    · intro w
      refine Fin.lastCases ?_ (fun j => ?_) w
      · simp only [appendGates, evaluate, Fin.snoc_last, NandProgram.eval]
        rw [ih.2 left, ih.2 right]
        exact Fin.snoc_last _ _
      · simp only [appendGates, evaluate, Fin.snoc_castSucc, NandProgram.eval]
        exact ih.2 j

end Schedule

namespace Circuit
variable {m d c g k : ℕ} (circuit : Circuit m d c g k)

/-- The initial chronological source retains the trusted state and samples precisely the stated constants. -/
theorem initial_values (total : ℕ) (initial : Fin m → Bit)
    (publicValues : PublicPort c d total → Bit) :
    (∀ j, (circuit.initialUnrolling total).schedule.evaluate initial publicValues
      ((circuit.initialUnrolling total).state j) = initial j) ∧
    (∀ j, (circuit.initialUnrolling total).schedule.evaluate initial publicValues
      ((circuit.initialUnrolling total).constants j) = publicValues (.inl j)) := by
  exact ⟨fun j => Schedule.initialSamples_old initial publicValues
    (fun j : Fin c => Sum.inl j) j,
    fun j => Schedule.initialSamples_new initial publicValues
      (fun j : Fin c => Sum.inl j) j⟩

/-- One appended invocation computes its transition on the retained state and newly sampled inputs. Older constants and already published output positions retain their values. -/
theorem next_values {total done : ℕ} (previous : Unrolling circuit total done)
    (h : done < total) (initial : Fin m → Bit) (publicValues : PublicPort c d total → Bit)
    (state : Fin m → Bit)
    (hstate : ∀ j, previous.schedule.evaluate initial publicValues (previous.state j) = state j)
    (hconstants : ∀ j, previous.schedule.evaluate initial publicValues (previous.constants j) =
      circuit.constantValues j) :
    (∀ j, (circuit.nextUnrolling previous h).schedule.evaluate initial publicValues
      ((circuit.nextUnrolling previous h).state j) =
        circuit.step state (fun j => publicValues (.inr (⟨done,h⟩,j))) j) ∧
    (∀ j, (circuit.nextUnrolling previous h).schedule.evaluate initial publicValues
      ((circuit.nextUnrolling previous h).constants j) = circuit.constantValues j) ∧
    (∀ t j, (circuit.nextUnrolling previous h).schedule.evaluate initial publicValues
      ((circuit.nextUnrolling previous h).outputs t.castSucc j) =
        previous.schedule.evaluate initial publicValues (previous.outputs t j)) ∧
    (∀ j, (circuit.nextUnrolling previous h).schedule.evaluate initial publicValues
      ((circuit.nextUnrolling previous h).outputs (Fin.last done) j) =
        circuit.output state (fun j => publicValues (.inr (⟨done,h⟩,j))) j) := by
  let sampled := previous.schedule.appendSamples
    (fun j : Fin d => Sum.inr (⟨done,h⟩,j))
  let old : Fin (m+publicCount c d done+gateCount g done) →
      Fin (m+(publicCount c d done+d)+gateCount g done) :=
    fun w => ⟨w.val, by have := w.isLt; omega⟩
  let fresh : Fin d → Fin (m+(publicCount c d done+d)+gateCount g done) :=
    fun j => ⟨m+publicCount c d done+gateCount g done+j.val, by have := j.isLt; omega⟩
  let ports : Fin (m+d+c) → Fin (m+(publicCount c d done+d)+gateCount g done) :=
    Fin.addCases (Fin.addCases (fun j => old (previous.state j)) fresh)
      (fun j => old (previous.constants j))
  have hports : (fun j => sampled.evaluate initial publicValues (ports j)) =
      Fin.addCases (Fin.addCases state (fun j => publicValues (.inr (⟨done,h⟩,j))))
        circuit.constantValues := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro j
        simp only [ports, Fin.addCases_left, Fin.addCases_right]
        change sampled.evaluate initial publicValues (old (previous.state j)) = state j
        exact (Schedule.appendSamples_old _ _ _ _ _).trans (hstate j)
      · intro j
        simp only [ports, Fin.addCases_left, Fin.addCases_right]
        exact Schedule.appendSamples_new _ _ _ _ j
    · intro j
      simp only [ports, Fin.addCases_left, Fin.addCases_right]
      change sampled.evaluate initial publicValues (old (previous.constants j)) = _
      exact (Schedule.appendSamples_old _ _ _ _ _).trans (hconstants j)
  have he := Schedule.appendGates_evaluate sampled ports circuit.program initial publicValues
  constructor
  · intro j
    change (sampled.appendGates ports circuit.program).schedule.evaluate initial publicValues
      ((sampled.appendGates ports circuit.program).wires (circuit.nextState j)) = _
    rw [he.2, hports]
    rfl
  constructor
  · intro j
    change (sampled.appendGates ports circuit.program).schedule.evaluate initial publicValues
      ⟨(previous.constants j).val, _⟩ = _
    exact (he.1 (old (previous.constants j))).trans
      ((Schedule.appendSamples_old _ _ _ _ _).trans (hconstants j))
  constructor
  · intro t j
    simp only [nextUnrolling, Fin.snoc_castSucc]
    exact (he.1 (old (previous.outputs t j))).trans
      (Schedule.appendSamples_old _ _ _ _ _)
  · intro j
    simp only [nextUnrolling, Fin.snoc_last]
    exact (he.2 (circuit.outputs j)).trans (by rw [hports]; rfl)

/-- The full unrolling has the exact register-state and public-output semantics of repeated execution of the source transition circuit. -/
theorem unroll_values (total done : ℕ) (h : done ≤ total) (initial : Fin m → Bit)
    (inputs : ℕ → Fin d → Bit) (publicValues : PublicPort c d total → Bit)
    (hc : ∀ j, publicValues (.inl j) = circuit.constantValues j)
    (hx : ∀ t : Fin total, ∀ j, publicValues (.inr (t,j)) = inputs t.val j) :
    (∀ j, (circuit.unrollPrefix total done h).schedule.evaluate initial publicValues
      ((circuit.unrollPrefix total done h).state j) = circuit.stateAt initial inputs done j) ∧
    (∀ j, (circuit.unrollPrefix total done h).schedule.evaluate initial publicValues
      ((circuit.unrollPrefix total done h).constants j) = circuit.constantValues j) ∧
    (∀ t j, (circuit.unrollPrefix total done h).schedule.evaluate initial publicValues
      ((circuit.unrollPrefix total done h).outputs t j) = circuit.outputAt initial inputs t.val j) := by
  induction done with
  | zero =>
    have hi := circuit.initial_values total initial publicValues
    exact ⟨hi.1, fun j => (hi.2 j).trans (hc j), fun t => Fin.elim0 t⟩
  | succ done ih =>
    have hp := ih (by omega)
    have hn := circuit.next_values (circuit.unrollPrefix total done (by omega))
      (by omega) initial publicValues (circuit.stateAt initial inputs done) hp.1 hp.2.1
    have hi : (fun j => publicValues (.inr (⟨done,by omega⟩,j))) = inputs done :=
      funext (hx ⟨done,by omega⟩)
    refine ⟨?_, hn.2.1, ?_⟩
    · intro j
      simpa only [hi, stateAt, unrollPrefix] using hn.1 j
    · intro t j
      refine Fin.lastCases ?_ (fun t => ?_) t
      · simpa only [hi, Fin.val_last, outputAt, unrollPrefix] using hn.2.2.2 j
      · exact (hn.2.2.1 t j).trans (hp.2.2 t j)

end Circuit

end Compiler.Stateful
