import Proofs.Compiler.Model

/-!
# Correctness of the direct executable compiler

The source wire map and the current refresh-chain endpoint map carry the same plaintext value. The proof follows the actual left-refresh, right-refresh, NAND execution. In particular, coinciding source operands still produce two distinct physical inputs. The source program may be empty and designated outputs may repeat or directly name input wires.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Compiler.Direct.Compilation
open CircuitCompiler
variable {P U T : ℕ}

/-- The public-sampler prefix leaves each trusted private input unchanged. -/
theorem publicProgram_eval_private (values : Fin U → Bit) (privateValues : Fin P → Bit)
    (i : Fin P) :
    (publicProgram values).eval privateValues (Fin.castAdd U i)=privateValues i := by
  induction U with
  | zero => rfl
  | succ u ih =>
    change Fin.snoc _ _ (Fin.castAdd u i).castSucc=_
    rw [Fin.snoc_castSucc]
    exact ih _

/-- The public-sampler prefix writes each specified public bit into its own source-input slot. -/
theorem publicProgram_eval_public (values : Fin U → Bit) (privateValues : Fin P → Bit)
    (j : Fin U) :
    (publicProgram values).eval privateValues (Fin.natAdd P j)=values j := by
  induction U with
  | zero => exact Fin.elim0 j
  | succ u ih =>
    refine Fin.lastCases ?_ (fun a=>?_) j
    · change Fin.snoc _ _ (Fin.last (P+u))=_
      rw [Fin.snoc_last]
      rfl
    · change Fin.snoc _ _ (Fin.natAdd P a).castSucc=_
      rw [Fin.snoc_castSucc]
      exact ih _ a

/-- The complete input array after public sampling agrees pointwise with private/public concatenation. -/
theorem publicProgram_eval (values : Fin U → Bit) (privateValues : Fin P → Bit) :
    (publicProgram values).eval privateValues=Fin.addCases privateValues values := by
  funext w
  refine Fin.addCases (fun i=>?_) (fun j=>?_) w
  · simpa using publicProgram_eval_private values privateValues i
  · simpa using publicProgram_eval_public values privateValues j

/-- Appending a source module leaves all earlier original encoding locations unchanged. -/
theorem step_original_old (state : Compilation P U T) (left right w : Fin (P+U+T))
    (privateValues : Fin P → Bit) :
    (state.step left right).program.eval privateValues
      ((state.step left right).original w.castSucc)=
      state.program.eval privateValues (state.original w) := by
  simp [step,Operations.Program.eval,Fin.snoc_castSucc]

/-- Refreshing either source-port chain preserves the bit carried by every old current endpoint. -/
theorem step_live_old (state : Compilation P U T) (left right w : Fin (P+U+T))
    (privateValues : Fin P → Bit) :
    (state.step left right).program.eval privateValues
      ((state.step left right).live w.castSucc)=
      state.program.eval privateValues (state.live w) := by
  have hw := (state.live w).isLt
  have hlv := (state.live left).isLt
  have hrv := (state.live right).isLt
  by_cases hrl : right=left <;> by_cases hr : w=right <;> by_cases hl : w=left <;>
    subst_vars <;>
    simp_all [step,Operations.Program.eval,Operations.Instruction.eval,Fin.snoc,Nat.add_assoc] <;>
    split_ifs <;> simp_all <;> omega

/-- The fresh module output is exactly the NAND of the old live source operands, including when their source wire is the same. -/
theorem step_original_new (state : Compilation P U T) (left right : Fin (P+U+T))
    (privateValues : Fin P → Bit) :
    (state.step left right).program.eval privateValues
      ((state.step left right).original (Fin.last (P+U+T)))=
      1+state.program.eval privateValues (state.live left)*
        state.program.eval privateValues (state.live right) := by
  have hlv := (state.live left).isLt
  have hrv := (state.live right).isLt
  by_cases h : right=left <;> subst_vars <;>
    simp_all [step,Operations.Program.eval,Operations.Instruction.eval,Gate.eval,GateKind.eval,
      sub_eq_add_neg,CharTwo.neg_eq,Fin.snoc,Nat.add_assoc] <;>
    split_ifs <;> simp_all <;> omega

/-- A newly produced source wire starts its chain at its own original encoding. -/
theorem step_live_new (state : Compilation P U T) (left right : Fin (P+U+T)) :
    (state.step left right).live (Fin.last (P+U+T))=
      (state.step left right).original (Fin.last (P+U+T)) := by
  simp [step]

end Compiler.Direct.Compilation

namespace Compiler.Direct.NandProgram
open CircuitCompiler

/-- Both address maps of every actual compiled prefix carry exactly the source wire value. -/
theorem compile_eval {P U T : ℕ} (program : NandProgram (P+U) T)
    (publicValues : Fin U → Bit) (privateValues : Fin P → Bit) :
    (∀ w, (program.compile publicValues).program.eval privateValues
      ((program.compile publicValues).original w)=program.eval
        (Fin.addCases privateValues publicValues) w) ∧
    (∀ w, (program.compile publicValues).program.eval privateValues
      ((program.compile publicValues).live w)=program.eval
        (Fin.addCases privateValues publicValues) w) := by
  induction program with
  | nil =>
    constructor <;> intro w <;>
      exact congrFun (Compilation.publicProgram_eval publicValues privateValues) w
  | @snoc t prior left right ih =>
    constructor
    · intro w
      refine Fin.lastCases ?_ (fun a=>?_) w
      · rw [NandProgram.eval,Fin.snoc_last]
        change ((prior.compile publicValues).step left right).program.eval privateValues
          (((prior.compile publicValues).step left right).original (Fin.last (P+U+t))) =
          1+prior.eval (Fin.addCases privateValues publicValues) left*
            prior.eval (Fin.addCases privateValues publicValues) right
        simpa only [ih.2] using
          Compilation.step_original_new (prior.compile publicValues) left right privateValues
      · rw [NandProgram.eval,Fin.snoc_castSucc]
        change ((prior.compile publicValues).step left right).program.eval privateValues
          (((prior.compile publicValues).step left right).original a.castSucc) =
          prior.eval (Fin.addCases privateValues publicValues) a
        exact (Compilation.step_original_old (prior.compile publicValues) left right a privateValues).trans (ih.1 a)
    · intro w
      refine Fin.lastCases ?_ (fun a=>?_) w
      · rw [NandProgram.eval,Fin.snoc_last]
        change ((prior.compile publicValues).step left right).program.eval privateValues
          (((prior.compile publicValues).step left right).live (Fin.last (P+U+t))) =
          1+prior.eval (Fin.addCases privateValues publicValues) left*
            prior.eval (Fin.addCases privateValues publicValues) right
        rw [Compilation.step_live_new (prior.compile publicValues) left right]
        simpa only [ih.2] using
          Compilation.step_original_new (prior.compile publicValues) left right privateValues
      · rw [NandProgram.eval,Fin.snoc_castSucc]
        change ((prior.compile publicValues).step left right).program.eval privateValues
          (((prior.compile publicValues).step left right).live a.castSucc) =
          prior.eval (Fin.addCases privateValues publicValues) a
        exact (Compilation.step_live_old (prior.compile publicValues) left right a privateValues).trans (ih.2 a)

end Compiler.Direct.NandProgram

namespace Compiler.Direct.Source
variable {P U T k : ℕ} (source : Source P U T k)

/-- Every original physical encoding location contains the correct source-wire bit. -/
theorem compiled_evaluate (privateValues : Fin P → Bit) (w : Fin (P+U+T)) :
    source.compiledProgram.eval privateValues (source.compilation.original w)=
      source.evaluate privateValues w := by
  exact (source.program.compile_eval source.publicValues privateValues).1 w

/-- The trusted decoder reads the specified source output tuple exactly, including repeated or directly selected input wires. -/
theorem compiled_output (privateValues : Fin P → Bit) (j : Fin k) :
    source.compiledProgram.eval privateValues (source.outputSlot j)=source.outputValues privateValues j := by
  exact source.compiled_evaluate privateValues (source.outputWires j)

end Compiler.Direct.Source
