import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.Construction.PhysicalGates
/-!
# Counted physical sampling and preparation

Concrete matrix, initialization, and protected-gate work counters. No leakage evaluation is assigned an artificial constant cost.

This module is part of the constructive compiler model; it imports no compiler proof theorem. The public source and execution interfaces are in Compiler.Direct and Compiler.Stateful.
-/
set_option backward.isDefEq.respectTransparency false
section
/-!
# EfficientSimulation

Definitions used by the headline security statements. The construction facts are included in this self-contained model.
-/
/-! ## RectangularImplementedGateCost -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped ENNReal Classical
namespace CircuitCompiler.Rectangular.FullyTapedStrategy
open Refresh MatrixRefresh TableAnalysis Shortening RefreshAnalysis
open Composition Composition.TopologicalExecution Sampling Sampling.Unbounded
noncomputable section
variable {F ML MR BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
  {n t inputs : ℕ} {hdim : n*n+1 = n+t}
end
end CircuitCompiler.Rectangular.FullyTapedStrategy
end
/-! ## RawEncodingInitializationCost -/
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.RawEncoding
open Refresh MatrixRefresh Unbounded Composition
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Sampling.RawEncoding
end
/-! ## RectangularImplementedRuntime -/
section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open scoped ENNReal
namespace CircuitCompiler.Rectangular.Implemented
open Refresh MatrixRefresh Composition Composition.TopologicalExecution
  Sampling Sampling.Unbounded
noncomputable section
variable {F ML MR BL BR V : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ML] [Nonempty ML] [Fintype MR] [Nonempty MR]
  [Fintype BL] [Nonempty BL] [Fintype BR] [Nonempty BR] [Fintype V]
  {n t inputs T k : ℕ} {hdim : n*n+1 = n+t}
end
end CircuitCompiler.Rectangular.Implemented
end
namespace CircuitCompiler.Program
open Rectangular.Gaussian
variable {F : Type*}
end CircuitCompiler.Program
end
