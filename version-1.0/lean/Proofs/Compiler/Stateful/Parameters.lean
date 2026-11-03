import Proofs.Compiler.Model
import Proofs.EfficientSimulaiton.Direct.Parameters

/-!
# Binary stateful rate and logarithmic share length

The total operation count already includes every invocation. The scalar conversion therefore has no additional dependence on T: K⁹ = 2¹⁸λ and (2ⁿ−1)⁻¹⁄²⁷ ≤ 2·2⁻ⁿ⁄²⁷. The existing conservative logarithmic threshold applies with this total count.
-/

set_option autoImplicit false
noncomputable section
namespace Compiler.Stateful.Circuit
open Compiler
variable {m d c g k n ml sl : ℕ}

/-- The nonzero-share bound implies the binary rate 2·10⁶ S·2^(18λ−n/27), with no invocation-dependent constant. -/
theorem privacyBound_binary (circuit : Circuit m d c g k) (T : ℕ) (hn : 2 ≤ n) :
    circuit.privacyBound T n ml sl ≤
      2000000*(circuit.operationCount T:ℝ)*(2:ℝ)^(18*((ml+sl:ℕ):ℝ)-(n:ℝ)/27) := by
  exact CompilerProof.Direct.direct_bound_binary hn

/-- A single absolute sufficient threshold gives distance 2⁻κ with share length logarithmic in the total number of operations. The logarithm is natural. -/
theorem privacyBound_logarithmic (circuit : Circuit m d c g k) (T : ℕ)
    (hn : 2 ≤ n) {κ : ℝ} (hκ : 1 ≤ κ)
    (hsize : 12000*(κ+((ml+sl:ℕ):ℝ)+Real.log ((circuit.operationCount T:ℝ)+2)) ≤ n) :
    circuit.privacyBound T n ml sl ≤ (2:ℝ)^(-κ) := by
  exact EfficientSimulationProof.Direct.direct_bound_le hn hκ hsize

end Compiler.Stateful.Circuit
