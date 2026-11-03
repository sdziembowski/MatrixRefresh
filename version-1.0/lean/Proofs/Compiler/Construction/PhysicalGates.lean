import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.Construction.Initialization
/-!
# Physical protected NAND execution

The operation tensors its operands, refreshes the long encoding with the full raw matrix tape, and shortens it using the full raw rectangular-attempt records. Both parties receive only their permitted local views. The construction has no selectors or preinitialized control encodings.
-/
set_option backward.isDefEq.respectTransparency false
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
open scoped Classical
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh TableAnalysis Shortening RefreshAnalysis
open Composition Composition.TopologicalExecution Sampling Sampling.Unbounded
noncomputable section
variable {F O A BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [Fintype A] [Fintype BL] [Fintype BR] {n t : ℕ}
namespace Taped
end Taped
namespace FullyTapedStrategy
variable {ML MR : Type*} [Fintype ML] [Fintype MR] {inputs : ℕ} {hdim : n*n+1 = n+t}
end FullyTapedStrategy
end
end CircuitCompiler.Rectangular
end
