import Proofs.EfficientSimulaiton.Direct.Theorem52
import Proofs.EfficientSimulaiton.Stateful.Theorem61

/-!
# Main theorem for EfficientSimulation

The direct and stateful simulator proofs establish both efficiency claims.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical ENNReal

namespace EfficientSimulation
theorem main_theorem :
  Direct.directSimulationClaim ∧ Stateful.statefulSimulationClaim := by
  constructor
  · simpa only [Direct.directSimulationClaim, Direct.workBound, Direct.oracleCalls, Direct.runtimeBound,
      Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      Direct.theorem_simulation
  · intro m d c g k n ml sl circuit T adversary hn
    simpa only [Stateful.statefulSimulationClaim, Stateful.workBound, Stateful.runtimeBound, Adaptive.workBound,
      Compiler.Stateful.Circuit.privacyBound, Compiler.K, Compiler.q,
      Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      Stateful.theorem_simulation circuit T adversary hn
end EfficientSimulation
