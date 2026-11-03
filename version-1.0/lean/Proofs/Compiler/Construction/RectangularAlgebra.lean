import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.Construction.MatrixSampling
/-!
# Rectangular shortening

Full-row-rank completions, nonzero outputs, and the finite attempt distribution used by the ordinary computation gadget.

This module is part of the constructive compiler model; it imports no compiler proof theorem. The public source and execution interfaces are in Compiler.Direct and Compiler.Stateful.
-/
set_option backward.isDefEq.respectTransparency false
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
instance fullRankFintype (n m : ℕ) : Fintype (FullRank F n m) := Fintype.ofFinite _
end
end CircuitCompiler.Rectangular
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Left multiplication by an invertible square matrix preserves full row rank. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; H ∈ FullRank(F, n, m); B ∈ GLₙ(F), we have

FullRowRank((B · H)).
-/
theorem fullRowRank_left {n m : ℕ} (H : FullRank F n m) (B : Refresh.«GL» F n) :
    FullRowRank (B.val * H.val) := by
  obtain ⟨J,hJ⟩ := H.property
  refine ⟨J * (B⁻¹).val, ?_⟩
  calc
    _ = B.val * (H.val * J) * (B⁻¹).val := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hJ]; simp
end
end CircuitCompiler.Rectangular
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- A change of basis in the short row space preserves the attempt space. -/

def attemptAction {n m : ℕ} {u : U F m} (B : Refresh.«GL» F n)
    (p : Attempt (n := n) u) : Attempt (n := n) u :=
  ⟨(rowRefresh p.val.1 B,
    ⟨(B⁻¹).val * p.val.2.val, fullRowRank_left p.val.2 B⁻¹⟩), by
    change Matrix.vecMul (Matrix.vecMul p.val.1.val B.val)
      ((B⁻¹).val * p.val.2.val) = u.val
    simpa [Matrix.vecMul_vecMul, ← Matrix.mul_assoc] using p.property⟩
/-- Equal-sized completion sets explain why uniform rows followed by uniform completions give the uniform joint attempt distribution. -/

def completionEquiv {n m : ℕ} (u : U F m) (a : U F n) (B : Refresh.«GL» F n) :
    Completion u a ≃ Completion u (rowRefresh a B) where
  toFun H := ⟨⟨(B⁻¹).val * H.val.val, fullRowRank_left H.val B⁻¹⟩, by
    change Matrix.vecMul (Matrix.vecMul a.val B.val) ((B⁻¹).val * H.val.val) = u.val
    simpa [Matrix.vecMul_vecMul, ← Matrix.mul_assoc] using H.property⟩
  invFun H := ⟨⟨B.val * H.val.val, fullRowRank_left H.val B⟩, by
    change Matrix.vecMul a.val (B.val * H.val.val) = u.val
    simpa only [rowRefresh, Matrix.vecMul_vecMul] using H.property⟩
  left_inv H := by
    apply Subtype.ext
    apply Subtype.ext
    simp [← Matrix.mul_assoc]
  right_inv H := by
    apply Subtype.ext
    apply Subtype.ext
    simp [← Matrix.mul_assoc]
end
end CircuitCompiler.Rectangular
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
theorem completion_card_eq {n m : ℕ} (u : U F m) (a b : U F n) :
    Fintype.card (Completion u a) = Fintype.card (Completion u b) := by
  obtain ⟨B,hB⟩ := exists_rowRefresh_eq a b
  rw [← hB]
  exact Fintype.card_congr (completionEquiv u a B)
end
end CircuitCompiler.Rectangular
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- A uniform dependent pair can be sampled sequentially when every fiber has the same cardinality. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): Let I and all sets Jᵢ be finite and nonempty, with |Jᵢ| independent of i. Sampling i uniformly from I, then j uniformly from Jᵢ, gives the uniform distribution on the disjoint union {(i,j):i ∈ I,j ∈ Jᵢ}. -/
theorem uniform_sigma_bind {I : Type*} [Fintype I] [Nonempty I]
    {J : I → Type*} [∀ i, Fintype (J i)] [∀ i, Nonempty (J i)]
    [Nonempty (Sigma J)]
    (i₀ : I) (hc : ∀ i, Fintype.card (J i) = Fintype.card (J i₀)) :
    (FiniteDistribution.uniform : FiniteDistribution I).bind
      (fun i => (FiniteDistribution.uniform : FiniteDistribution (J i)).map (Sigma.mk i)) =
      (FiniteDistribution.uniform : FiniteDistribution (Sigma J)) := by
  classical
  letI : DecidableEq (Sigma J) := Classical.decEq _
  have hcard : Fintype.card (Sigma J) = Fintype.card I * Fintype.card (J i₀) := by
    rw [Fintype.card_sigma]
    simp [hc]
  ext p
  simp only [FiniteDistribution.bind, FiniteDistribution.map, FiniteDistribution.pure, FiniteDistribution.uniform, hc, hcard]
  simp_rw [← Finset.mul_sum]
  have hs : (∑ i : I, ∑ j : J i, if p = ⟨i,j⟩ then (1 : ℝ) else 0) = 1 := by
    obtain ⟨i,j⟩ := p
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      apply Finset.sum_eq_zero
      intro k _
      simp [Sigma.mk.inj_iff, Ne.symm hb]
    · simp
  change (Fintype.card I : ℝ)⁻¹ * ((Fintype.card (J i₀) : ℝ)⁻¹ *
    (∑ i : I, ∑ j : J i, if p = ⟨i,j⟩ then (1 : ℝ) else 0)) = _
  rw [hs]
  simp [Nat.cast_mul, mul_comm]
/-- Uniform distributions commute with a bijective relabeling. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For I,J a set; e ∈ I ≃ J, assume I is finite; J is finite; I ≠ ∅; J ≠ ∅. Then

(e_*𝒰_I) = 𝒰_J.
-/
theorem uniform_equiv {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (e : I ≃ J) :
    (FiniteDistribution.uniform : FiniteDistribution I).map e = (FiniteDistribution.uniform : FiniteDistribution J) := by
  classical
  apply FiniteDistribution.uniform_map_of_fiber_card _ 1
  intro j
  letI : Unique {i : I // e i = j} :=
    ⟨⟨e.symm j,e.apply_symm_apply j⟩, fun i =>
      Subtype.ext (e.injective (i.property.trans (e.apply_symm_apply j).symm))⟩
  exact Fintype.card_unique
end
end CircuitCompiler.Rectangular
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
theorem attemptDistribution_uniform {n t : ℕ} (hn : 2 ≤ n) (u : U F (n+t))
    [Nonempty (Attempt (n := n) u)] :
    attemptDistribution hn u = (FiniteDistribution.uniform : FiniteDistribution (Attempt (n := n) u)) := by
  classical
  let a₀ : U F n := unitShare ⟨0,by omega⟩
  letI : Nonempty (U F n) := ⟨a₀⟩
  letI : ∀ a : U F n, Nonempty (Completion u a) := fun a => completion_nonempty u a
  letI : Nonempty ((a : U F n) × Completion u a) :=
    ⟨⟨a₀, Classical.choice (completion_nonempty u a₀)⟩⟩
  unfold attemptDistribution
  rw [uniform_sigma_bind a₀ (fun a => completion_card_eq u a a₀)]
  exact uniform_equiv (attemptSigmaEquiv (n := n) u).symm
end
end CircuitCompiler.Rectangular
end
