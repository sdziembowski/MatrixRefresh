import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.Construction.RectangularAlgebra
/-!
# Counted binary linear algebra

Concrete arithmetic operations and their private work counters. The counters do not alter sampled values or observations.

This module is part of the constructive compiler model; it imports no compiler proof theorem. The public source and execution interfaces are in Compiler.Direct and Compiler.Stateful.
-/
set_option backward.isDefEq.respectTransparency false
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular.Gaussian
variable {F : Type*} [Field F] [DecidableEq F]
/-- Remove the first row after eliminating its pivot from all remaining rows. -/

def reduce {n m : ℕ} (H : Fin (n+1) → Fin m → F) (j : Fin m) :
    Fin n → Fin m → F :=
  fun i k => H i.succ k - (H i.succ j / H 0 j) * H 0 k
end CircuitCompiler.Rectangular.Gaussian
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular.Gaussian
variable {F : Type*} [Field F] [DecidableEq F]
end CircuitCompiler.Rectangular.Gaussian
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular.Gaussian
variable {F : Type*} [Field F] [DecidableEq F]
end CircuitCompiler.Rectangular.Gaussian
end
section
/-!
# AlgebraCost

Definitions used by the headline security statements. The construction facts are included in this self-contained model.
-/
/-!
## GaussianAlgebraCost
-/
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular.Gaussian
variable {F : Type*} [Field F] [DecidableEq F]
end CircuitCompiler.Rectangular.Gaussian
end
/-!
## GaussianSolveCost
-/
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular.Gaussian
variable {F : Type*} [Field F] [DecidableEq F]
end CircuitCompiler.Rectangular.Gaussian
end
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace CircuitCompiler.Rectangular.Gaussian
open Refresh
variable {F : Type*} [Field F] [DecidableEq F]
end CircuitCompiler.Rectangular.Gaussian
end
