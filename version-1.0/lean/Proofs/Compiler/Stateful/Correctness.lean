import Proofs.Compiler.Model
import Proofs.Compiler.Adaptive.Specialization
import Proofs.Compiler.Direct.Correctness

/-!
# Ordinary correctness of interleaved compilation

At a fixed formal transcript, freeze the public bits selected along that transcript. The resulting ordinary program has the same source and live-chain plaintext values. The proof reuses the checked correctness of the direct compiler's actual two refreshes and NAND, and adds the interleaved public-sampler case.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace Compiler.Stateful.Schedule
open Compiler.Direct Compiler.Adaptive CircuitCompiler
variable {J A : Type*} {P U T : ℕ}

/-- The ordinary physical program after the public bits at each source sampler have been fixed. Address maps and refresh chains stay those of the original compilation. -/
def fixedProgram (publicValues : J → Bit) :
    {U T : ℕ} → (schedule : Schedule J P U T) →
      Operations.Program Bit P schedule.compile.operations
  | _, _, .nil => .nil
  | _, _, .sample prior tag => (fixedProgram publicValues prior).snoc (.sample (publicValues tag))
  | _, _, .nand prior left right =>
      let state : Compilation P _ _ := { prior.compile with program := fixedProgram publicValues prior }
      (state.step left right).program

/-- Both original source-wire addresses and live chain endpoints carry the ordinary source values in the fixed public execution. -/
theorem fixedProgram_evaluate (schedule : Schedule J P U T) (publicValues : J → Bit)
    (input : Fin P → Bit) :
    (∀ w, (fixedProgram publicValues schedule).eval input (schedule.compile.original w) =
      schedule.evaluate input publicValues w) ∧
    (∀ w, (fixedProgram publicValues schedule).eval input (schedule.compile.live w) =
      schedule.evaluate input publicValues w) := by
  induction schedule with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | @sample U T prior tag ih =>
    have hh (addresses : Fin (P+U+T) → Fin (P+prior.compile.operations))
        (ha : ∀ w, (fixedProgram publicValues prior).eval input (addresses w) =
          prior.evaluate input publicValues w)
        (v : Fin (P+U+T+1)) :
        ((fixedProgram publicValues prior).snoc (.sample (publicValues tag))).eval input
          (Fin.lastCases (Fin.last (P+prior.compile.operations))
            (fun j => (addresses j).castSucc) v) =
          Fin.snoc (α := fun _ => Bit) (prior.evaluate input publicValues) (publicValues tag) v := by
      refine Fin.lastCases ?_ (fun j => ?_) v
      · simp [Operations.Program.eval, Operations.Instruction.eval]
      · simpa [Operations.Program.eval] using ha j
    constructor
    · intro w
      exact hh prior.compile.original ih.1 (Fin.cast (by omega) w)
    · intro w
      exact hh prior.compile.live ih.2 (Fin.cast (by omega) w)
  | @nand U T prior left right ih =>
    let state : Compilation P U T := { prior.compile with program := fixedProgram publicValues prior }
    constructor
    · intro w
      refine Fin.lastCases ?_ (fun j => ?_) w
      · rw [Schedule.evaluate, Fin.snoc_last]
        exact (Compilation.step_original_new state left right input).trans
          (by simp only [state, ih.2])
      · rw [Schedule.evaluate, Fin.snoc_castSucc]
        exact (Compilation.step_original_old state left right j input).trans (ih.1 j)
    · intro w
      refine Fin.lastCases ?_ (fun j => ?_) w
      · rw [Schedule.evaluate, Fin.snoc_last]
        change (state.step left right).program.eval input ((state.step left right).live (Fin.last _)) = _
        exact (congrArg (fun slot => (state.step left right).program.eval input slot)
          (Compilation.step_live_new state left right)).trans
            ((Compilation.step_original_new state left right input).trans
              (by simp only [state, ih.2]))
      · rw [Schedule.evaluate, Fin.snoc_castSucc]
        exact (Compilation.step_live_old state left right j input).trans (ih.2 j)

/-- Specializing the sampler bits to their tagged values gives exactly the fixed public physical program. Values at refresh and NAND positions do not affect this identity. -/
theorem specialize_eq_fixedProgram (schedule : Schedule J P U T) (publicValues : J → Bit)
    (values : Fin schedule.compile.operations → Bit)
    (hvalues : ∀ i tag, schedule.sampleAt i.val = some tag → values i = publicValues tag) :
    specialize schedule.compile.program values = fixedProgram publicValues schedule := by
  induction schedule with
  | nil => rfl
  | @sample U T prior tag ih =>
    simp only [compile, Compilation.publicStep, specialize, fixedProgram, selectInstruction]
    congr 1
    · apply ih (Fin.init values)
      intro i other hi
      apply hvalues i.castSucc other
      simpa [sampleAt, ne_of_lt i.isLt] using hi
    · exact congrArg Operations.Instruction.sample
        (hvalues (Fin.last prior.compile.operations) tag (by simp [sampleAt]))
  | nand prior left right ih =>
    have hp : specialize prior.compile.program (Fin.init (Fin.init (Fin.init values))) =
        fixedProgram publicValues prior := by
      apply ih
      intro i tag hi
      apply hvalues i.castSucc.castSucc.castSucc tag
      exact hi
    simp only [compile, Compilation.step, specialize, selectInstruction, fixedProgram, hp]

/-- The online execution's induced plaintext labels match the source values whenever each tagged public sampler uses the specified bit along the fixed formal history. -/
theorem online_evaluate (schedule : Schedule J P U T) (publicValues : J → Bit)
    (input : Fin P → Bit) (values : SampleValues Bit A schedule.compile.operations)
    (z : Fin schedule.compile.operations → A)
    (hvalues : ∀ i tag, schedule.sampleAt i.val = some tag →
      values i (incomingVector z i) = publicValues tag) :
    (∀ w, Compiler.Adaptive.evaluate input schedule.compile.program values z (schedule.compile.original w) =
      schedule.evaluate input publicValues w) ∧
    (∀ w, Compiler.Adaptive.evaluate input schedule.compile.program values z (schedule.compile.live w) =
      schedule.evaluate input publicValues w) := by
  rw [evaluate_eq_specialize, specialize_eq_fixedProgram schedule publicValues _ hvalues]
  exact fixedProgram_evaluate schedule publicValues input

end Compiler.Stateful.Schedule
