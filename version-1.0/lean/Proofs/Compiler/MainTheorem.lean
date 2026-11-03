import Proofs.Compiler.DirectComposition.Theorem57
import Proofs.Compiler.DirectComposition.AdaptiveTheorem57
import Proofs.Compiler.Direct.Theorem52
import Proofs.Compiler.Stateful.Theorem61

/-!
# Main theorem for Compiler

The fixed-label, causal, direct-privacy, and stateful proofs establish the four
conjuncts of the public compiler theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators Classical ENNReal
namespace Compiler
open Refresh MatrixRefresh CircuitCompiler CircuitCompiler.Composition
  CircuitCompiler.AveragedEnergyComparison CompilerProof.DirectComposition
theorem main_theorem.{u,v} :
    Direct.directCompositionClaim.{u,v} ∧
    Direct.adaptiveCompositionClaim.{u,v} ∧
    Direct.directPrivacyClaim ∧ Stateful.statefulPrivacyClaim := by
  change Direct.directCompositionClaim.{u,v} ∧ Direct.adaptiveCompositionClaim.{u,v} ∧
    Direct.directPrivacyClaim ∧ Stateful.statefulPrivacyClaim
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact @Direct.direct_composition
  · exact @Direct.adaptive_composition
  · exact @Direct.theorem_direct
  · exact @Stateful.theorem_stateful
end Compiler
end
