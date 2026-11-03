import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.Construction.StoppedSampling
/-!
# Concrete completion tapes and work

Raw affine-completion proposals, accepted matrices, private prefixes, and the cost of their actual sampling tapes.

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
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular.CompletionSampler
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular.CompletionSampler
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular.CompletionSampler
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular.CompletionSampler
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular.CompletionSampler
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular.CompletionSampler
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
instance acceptedNonempty {n t : ℕ} (u : U F (n+t)) (a : U F n) :
    Nonempty {w : FreeRows F n (n+t) (pivot a) // accept u a w = true} := by
  letI := completion_nonempty u a
  exact ⟨(acceptedEquiv u a).symm (Classical.choice inferInstance)⟩
end
end CircuitCompiler.Rectangular.CompletionSampler
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular.CompletionSampler
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular.CompletionSampler
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Exact full-tape disintegration by the returned completion. This is a proved identity for the field-entry sampler, not a postulated conditional tape distribution. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): The complete stopped tape of the completion rejection sampler can be generated by independently sampling its rejected prefix and a uniform accepted completion H, then appending the unique free-row representation of H to that prefix. -/
theorem tapeDistribution_eq_reconstructed {n t : ℕ} (u : U F (n+t)) (a : U F n) :
    letI := completion_nonempty u a
    tapeDistribution u a = (rejectedDistribution u a).bind (fun p =>
      (Unbounded.toPMF (FiniteDistribution.uniform : FiniteDistribution (Completion u a))).map (reconstruct u a p)) := by
  letI := completion_nonempty u a
  have hU : (FiniteDistribution.uniform : FiniteDistribution {w : FreeRows F n (n+t) (pivot a) // accept u a w = true}) =
      (FiniteDistribution.uniform : FiniteDistribution (Completion u a)).map (acceptedEquiv u a).symm :=
    (uniform_equiv (acceptedEquiv u a).symm).symm
  unfold tapeDistribution rejectedDistribution
  rw [Unbounded.distribution_eq_prefix_bind,accepted_uniform,hU]
  simp only [FiniteDistribution.map_map,Unbounded.toPMF_map,PMF.map_comp,Function.comp_def]
  rfl
/-- Equivalent order: choose the uniform accepted matrix first, then its exact conditional internal failed-prefix tape. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): Equivalently, first sample the accepted completion H uniformly, then independently sample the rejected prefix, and reconstruct the full stopped tape. The resulting distribution equals the actual completion sampler's tape distribution. -/
theorem tapeDistribution_eq_uniform_prefix {n t : ℕ} (u : U F (n+t)) (a : U F n) :
    letI := completion_nonempty u a
    tapeDistribution u a = (Unbounded.toPMF (FiniteDistribution.uniform : FiniteDistribution (Completion u a))).bind
      (fun H => (rejectedDistribution u a).map (fun p => reconstruct u a p H)) := by
  letI := completion_nonempty u a
  rw [tapeDistribution_eq_reconstructed]
  exact PMF.bind_comm _ _ _
end
end CircuitCompiler.Rectangular.CompletionSampler
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular.SamplerCost
open Refresh MatrixRefresh Sampling Gaussian
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular.SamplerCost
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
@[simp] theorem sigmaPMF_apply {I : Type*} {J : I → Type*}
    (P : PMF I) (Q : ∀ i, PMF (J i)) (i : I) (j : J i) :
    sigmaPMF P Q ⟨i,j⟩ = P i * Q i j :=
  rfl
/-- Forgetting an internal mark recovers the original sampler exactly. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): Discarding the conditional mark from the joint distribution with masses P(i)Qᵢ(j) gives exactly P. -/
theorem sigmaPMF_fst {I : Type*} {J : I → Type*}
    (P : PMF I) (Q : ∀ i, PMF (J i)) :
    (sigmaPMF P Q).map Sigma.fst = P := by
  apply PMF.ext
  intro i
  rw [PMF.map_apply, ENNReal.tsum_sigma']
  simp only [sigmaPMF_apply]
  have h (j : I) : (∑' x : J j, if i = j then P j * Q j x else 0) =
      if i = j then P j else 0 := by
    by_cases hj : i = j <;> simp [hj, ENNReal.tsum_mul_left, PMF.tsum_coe]
  simp_rw [h]
  exact (tsum_eq_single i (fun a ha => if_neg (Ne.symm ha))).trans (if_pos rfl)
/-- Disintegrating a marked observation keeps the actual conditional mark distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): To observe f(i,j) from the joint distribution P(i)Qᵢ(j), one may equivalently first sample i ∼ P, then j ∼ Qᵢ, and return f(i,j). The two resulting view distributions are equal. -/
theorem sigmaPMF_observation {I V : Type*} {J : I → Type*}
    (P : PMF I) (Q : ∀ i, PMF (J i)) (f : (Σ i, J i) → V) :
    (sigmaPMF P Q).map f = P.bind (fun i => (Q i).map (fun j => f ⟨i,j⟩)) := by
  apply PMF.ext
  intro v
  rw [PMF.map_apply, ENNReal.tsum_sigma', PMF.bind_apply]
  apply tsum_congr
  intro i
  rw [PMF.map_apply, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro j
  simp only [sigmaPMF_apply, mul_ite, mul_zero]
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α]
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
/-- The nonnegative expected cost, defined by summing probability times cost over the countable sample space. -/
def workExpectation {α : Type*} (P : PMF α) (cost : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, P a*cost a
/-- Add up the nonnegative cost of each attempted proposal. -/

def prefixWork {α : Type*} (cost : α → ℝ≥0∞) : (k : ℕ) → Tape α k → ℝ≥0∞
  | 0,_ => 0
  | k+1,t => cost t.1+prefixWork cost k t.2
variable {α β : Type*} [Fintype α]
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators ENNReal
namespace CircuitCompiler.Rectangular.SamplerCost
open Refresh MatrixRefresh Sampling Sampling.Unbounded Gaussian
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ}
end
end CircuitCompiler.Rectangular.SamplerCost
end
