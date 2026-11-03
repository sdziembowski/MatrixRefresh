import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.LocalComparisons.NetworkInterface
import Proofs.Compiler.LocalComparisons.HistoryProducts
/-!
# Local input to direct composition

The comparison is between unconditional canonical executions: each wire encoding is sampled independently before the adaptive answers are generated. The records below retain only local approximation facts and scope locality; none assumes a bound for complete executions or for marked sums.

The physical compiler supplies these data from the established matrix-refresh and rectangular-shortening lemmas. Public samplers remain true probability factors and therefore require no approximation certificate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
namespace CompilerProof.DirectComposition
open Refresh MatrixRefresh CircuitCompiler.Composition
  CircuitCompiler.AveragedEnergyComparison
variable {W X A F : Type*} [Fintype W] [DecidableEq W]
  [Fintype X] [Nonempty X] [Fintype A] {S : ℕ}
end CompilerProof.DirectComposition
