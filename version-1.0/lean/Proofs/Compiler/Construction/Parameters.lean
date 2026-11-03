import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.Construction.CountedExecution
/-!
# Binary circuits, encodings, and compiler parameters

Binary field, share, leakage, and parameter conventions shared by the direct and stateful compilers. The chronological NAND source is in Compiler.lean and permits repeated operands and arbitrary fanout.

The construction modules below this interface define the physical rectangular shortener, complete rejection tapes, and counted probability distributions. No security claim or admitted reference theorem is imported here.
-/
section CompilerPublicModel
set_option autoImplicit false
noncomputable section
namespace Compiler
end Compiler
end
end CompilerPublicModel
