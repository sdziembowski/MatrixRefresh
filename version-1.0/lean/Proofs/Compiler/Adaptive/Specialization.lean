import Proofs.Compiler.Model

/-!
# Ordinary evaluation along a formal transcript

Once a complete formal transcript is fixed for the analysis, every online public value along it is fixed too. Freezing those values gives the same plaintext wire labels. This is an algebraic identity for correctness, not a claim that future public values may be sampled before earlier leakage is known.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Compiler.Adaptive
open CircuitCompiler CircuitCompiler.Operations
variable {F A : Type*} [Mul F] [Sub F] {P S : ℕ}

/-- Freezing the policy along one transcript preserves every plaintext wire label. -/
theorem evaluate_eq_specialize (input : Fin P → F) (program : Operations.Program F P S)
    (values : SampleValues F A S) (z : Fin S → A) :
    evaluate input program values z =
      (specialize program (fun i => values i (incomingVector z i))).eval input := by
  induction program with
  | nil => rfl
  | @snoc S prior instruction ih =>
    have hv : Fin.init (fun i => values i (incomingVector z i)) =
        (fun i => values i.castSucc (incomingVector (Fin.init z) i)) := rfl
    simp only [evaluate, specialize, Operations.Program.eval, hv]
    rw [ih]
    rfl

/-- Public values at non-sampler positions are irrelevant to the specialized physical program. -/
theorem specialize_congr (program : Operations.Program F P S) (first second : Fin S → F)
    (h : ∀ i value, program.instructionAt i = .sample value → first i = second i) :
    specialize program first = specialize program second := by
  induction program with
  | nil => rfl
  | @snoc S prior instruction ih =>
    simp only [specialize]
    congr 1
    · apply ih
      intro i value hi
      apply h i.castSucc value
      simpa only [Operations.Program.instructionAt, Fin.lastCases_castSucc] using hi
    · cases hi : instruction with
      | compute gate => rfl
      | refresh old => rfl
      | sample value =>
        dsimp only [selectInstruction]
        congr 1
        exact h (Fin.last S) value (by simp [Operations.Program.instructionAt, hi])

end Compiler.Adaptive
