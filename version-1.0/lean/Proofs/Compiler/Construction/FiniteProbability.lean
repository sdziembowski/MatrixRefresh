import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.Construction.Encodings
/-!
# Finite probability and encoding initialization

Finite real probability distributions, pushforwards, uniform sampling, and constructive nonemptiness of every binary encoding fiber.

This module is part of the constructive compiler model; it imports no compiler proof theorem. The public source and execution interfaces are in Compiler.Direct and Compiler.Stateful.
-/
set_option backward.isDefEq.respectTransparency false
section
/-!
# Probability

Definitions used by the headline security statements. The construction facts are included in this self-contained model.
-/
/-!
## FiniteProbability
-/
section
set_option autoImplicit false
open scoped BigOperators
namespace Refresh
namespace FiniteDistribution
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
/-- Independent sampling is the special case with a constant conditional distribution. -/

noncomputable def prod (P : FiniteDistribution α) (Q : FiniteDistribution β) : FiniteDistribution (α × β) :=
  P.joint (fun _ => Q)
/-- Every point with nonzero mass satisfies the given property. -/

def Supports (P : FiniteDistribution α) (p : α → Prop) : Prop :=
  ∀ a, P.weight a ≠ 0 → p a
end FiniteDistribution
end Refresh
end
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
open scoped BigOperators
namespace Refresh
namespace FiniteDistribution
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
/-- Starting at a fixed point and sampling its conditional distribution gives that distribution. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ α; Q ∈ α → 𝒟(β), we have

bind(pure(a), Q) = Q(a).
-/
@[simp] theorem pure_bind (a : α) (Q : α → FiniteDistribution β) : (pure a).bind Q = Q a := by
  classical
  ext b
  simp [bind, pure]
/-- The distribution of three successive samples does not depend on how the first two sampling operations are parenthesized. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); Q ∈ α → 𝒟(β); R ∈ β → 𝒟(γ), we have

bind(bind(P, Q), R) = bind(P, ((a ↦ bind(Q(a), R)))).
-/
theorem bind_assoc (P : FiniteDistribution α) (Q : α → FiniteDistribution β) (R : β → FiniteDistribution γ) :
    (P.bind Q).bind R = P.bind (fun a => (Q a).bind R) := by
  ext c
  simp only [bind, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm
/-- Two successive deterministic maps equal pushing forward through their composition. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); f ∈ α → β; g ∈ β → γ, we have

(g_*(f_*P)) = ((g ∘ f)_*P).
-/
theorem map_map (P : FiniteDistribution α) (f : α → β) (g : β → γ) :
    (P.map f).map g = P.map (g ∘ f) := by
  simp [map, bind_assoc]
/-- Uniform sampling followed by a function weights an output by its fiber cardinality. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ α → β; b ∈ β, assume α ≠ ∅. Then

(f_*𝒰_α)(b) = |{a ∈ α | f(a) = b}| / |α|.
-/
theorem uniform_map_weight [Nonempty α] [DecidableEq β] (f : α → β) (b : β) :
    ((uniform : FiniteDistribution α).map f).weight b =
      (Fintype.card {a : α // f a = b} : ℝ) / (Fintype.card α : ℝ) := by
  classical
  simp [map, bind, pure, uniform, Fintype.card_subtype,
    div_eq_mul_inv, mul_comm, eq_comm]
  rw [← Finset.sum_filter]
  simp [mul_comm]
/-- A function whose output fibers all have the same cardinality sends a uniform input distribution to the uniform output distribution. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ α → β; k ∈ ℕ, assume α ≠ ∅; β ≠ ∅; ∀ b, |{a ∈ α | f(a) = b}| = k. Then

(f_*𝒰_α) = 𝒰ᵦ.
-/
theorem uniform_map_of_fiber_card [Nonempty α] [Nonempty β] [DecidableEq β] (f : α → β) (k : ℕ)
    (hk : ∀ b, Fintype.card {a : α // f a = b} = k) :
    (uniform : FiniteDistribution α).map f = (uniform : FiniteDistribution β) := by
  classical
  have hc : Fintype.card α = Fintype.card β * k := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_sigma]
    simp [hk]
  have hk0 : k ≠ 0 := by
    intro h
    have := Fintype.card_ne_zero (α := α)
    simp [hc, h] at this
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  ext b
  rw [uniform_map_weight, hk, hc]
  simp [uniform, Nat.cast_mul, hkR, div_eq_mul_inv]
end FiniteDistribution
end Refresh
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end Refresh
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end Refresh
end
