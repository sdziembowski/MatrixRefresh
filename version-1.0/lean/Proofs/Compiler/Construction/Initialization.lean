import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.Construction.RectangularExecution
/-!
# Input tapes and countable executions

Concrete nonzero encoding initialization and the countable rejection machinery used to retain private tapes and expected work.

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
namespace CircuitCompiler.Sampling.RawEncoding
open Refresh MatrixRefresh Unbounded Rectangular.Gaussian
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Sampling.RawEncoding
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Sampling.RawEncoding
open Refresh MatrixRefresh Unbounded Rectangular.Gaussian
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Sampling.RawEncoding
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Sampling.RawEncoding
open Refresh MatrixRefresh Unbounded Rectangular.Gaussian
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Identify vectors accepted by the nonzero test with the subtype of nonzero shares. -/
def nonzeroEquiv (n : ℕ) :
    {v : V F n // nonzeroTest v = true} ≃ U F n :=
  Equiv.subtypeEquiv (Equiv.refl _) (fun v => by simp [nonzeroTest])
end
end CircuitCompiler.Sampling.RawEncoding
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Sampling.RawEncoding
open Refresh MatrixRefresh Unbounded Rectangular.Gaussian
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- First rejecting zero coordinates and then the wrong inner product gives the same acceptance fraction as this single raw-pair predicate. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ≥ 2, sample two independent uniform vectors L,R ∈ Fⁿ. Acceptance requires L ≠ 0, R ≠ 0, and L · R = s. Thus

Pr[L ≠ 0,R ≠ 0,L · R = s] = Pr_((L,R) ← U × U) [L · R = s] · Pr_(X ← Fⁿ) [X ≠ 0]², U = Fⁿ ∖ {0}.

This identifies rejection on raw vector pairs with rejection after first conditioning both vectors to be nonzero.
-/
theorem acceptance_factorization {n : ℕ} (hn : 2 ≤ n) (s : F) :
    letI : Nonempty (State F n) := ⟨(Classical.choice (fiber_nonempty F n hn s)).val⟩
    acceptance (FiniteDistribution.uniform : FiniteDistribution (Raw F n)) (accept s) =
      acceptance (FiniteDistribution.uniform : FiniteDistribution (State F n)) (secretTest s) *
        (acceptance (FiniteDistribution.uniform : FiniteDistribution (V F n)) nonzeroTest)^2 := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0,by omega⟩⟩
  letI : Nonempty (State F n) := ⟨(Classical.choice (fiber_nonempty F n hn s)).val⟩
  have hsecret : Fintype.card {x : State F n // secretTest s x = true} =
      Fintype.card (Fiber F n s) := Fintype.card_congr
    (Equiv.subtypeEquiv (Equiv.refl _) (fun x => by simp [secretTest]))
  have hstate : Fintype.card (State F n) = Fintype.card (U F n)^2 := by
    rw [Fintype.card_congr (stateEquivProd F n),Fintype.card_prod,pow_two]
  have hu : (Fintype.card (U F n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hv : (Fintype.card (V F n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [acceptance_uniform,Fintype.card_congr (acceptedEquiv s),hsecret,
    Fintype.card_congr (nonzeroEquiv (F := F) n),hstate,Raw,Fintype.card_prod,Nat.cast_mul,Nat.cast_pow]
  field_simp
/-- In every fixed field there is a dimension-independent lower bound. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, assume 2 ≤ n. Then

((8 · |F|))⁻¹ ≤ acceptance(𝒰_(Raw(F, n)), accept(s)).
-/
theorem acceptance_ge {n : ℕ} (hn : 2 ≤ n) (s : F) :
    (8*(fieldCard F:ℝ))⁻¹ ≤ acceptance (FiniteDistribution.uniform : FiniteDistribution (Raw F n)) (accept s) := by
  letI : Nonempty (State F n) := ⟨(Classical.choice (fiber_nonempty F n hn s)).val⟩
  have hq := fieldCard_cast_pos (F := F)
  have hs := secret_acceptance_ge hn s
  have hz := nonzero_acceptance_ge_half (F := F) (by omega : 1 ≤ n)
  rw [acceptance_factorization hn]
  have hz2 : (1/4:ℝ) ≤ (acceptance (FiniteDistribution.uniform : FiniteDistribution (V F n)) nonzeroTest)^2 := by
    nlinarith
  have hm := mul_le_mul hs hz2 (by positivity : (0:ℝ) ≤ 1/4)
    (acceptance_nonneg (FiniteDistribution.uniform : FiniteDistribution (State F n)) (secretTest s))
  have he : (8*(fieldCard F:ℝ))⁻¹ = (2*(fieldCard F:ℝ))⁻¹ * (1/4) := by field_simp; ring
  rw [he]
  exact hm
end
end CircuitCompiler.Sampling.RawEncoding
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Sampling.RawEncoding
open Refresh MatrixRefresh Unbounded Rectangular.Gaussian
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Sampling.RawEncoding
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Sampling.RawEncoding
open Refresh MatrixRefresh Unbounded Composition
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Sampling.RawEncoding
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators ENNReal
namespace CircuitCompiler.Composition.TopologicalExecution
open Refresh Sampling.Unbounded
noncomputable section
universe u v
variable {E : Type u} {A : Type v} [Fintype E] [Fintype A] {inputs T : ℕ}
namespace CostedRunner
end CostedRunner
namespace GateProtocol
variable {F : Type*} [Mul F] [Sub F]
/-- Compile the same syntactic program using its actual cost-returning local implementation, reading exactly the program's two operand positions. -/

def costedRunner
    (implementation : (t : ℕ) → Gate F (inputs+t) → (Fin t → A) → E → E → PMF ((E×A)×ℕ)) :
    {T : ℕ} → Program F inputs T → CostedRunner E A inputs T
  | 0,.nil => .nil
  | t+1,.snoc prior gate => .snoc (costedRunner implementation prior)
      (fun state => implementation t gate state.2 (state.1 gate.left) (state.1 gate.right))
end GateProtocol
end
end CircuitCompiler.Composition.TopologicalExecution
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Sampling.CountableRejection
open Refresh Unbounded
noncomputable section
variable {α β : Type*}
end
end CircuitCompiler.Sampling.CountableRejection
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Sampling.CountableRejection
open Refresh Unbounded
noncomputable section
variable {α β : Type*}
end
end CircuitCompiler.Sampling.CountableRejection
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Sampling.CountableRejection
open Refresh Unbounded
noncomputable section
variable {α β : Type*}
end
end CircuitCompiler.Sampling.CountableRejection
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Sampling.CountableRejection
open Refresh Unbounded
noncomputable section
variable {α β : Type*}
end
end CircuitCompiler.Sampling.CountableRejection
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Sampling.CountableRejection
open Refresh Unbounded
noncomputable section
variable {α β : Type*}
end
end CircuitCompiler.Sampling.CountableRejection
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Sampling.CountableRejection
open Refresh Unbounded
noncomputable section
variable {α β : Type*}
end
end CircuitCompiler.Sampling.CountableRejection
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Sampling.CountableRejection
open Refresh Unbounded
noncomputable section
variable {α β : Type*}
end
end CircuitCompiler.Sampling.CountableRejection
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Sampling.CountableRejection
open Refresh Unbounded
noncomputable section
variable {α β : Type*}
theorem probability_map (P : PMF α) (f : α → β) (accept : β → Bool) :
    probability (P.map f) accept = probability P (accept ∘ f) := by
  simp only [probability,PMF.map_comp]
/-- The new generic acceptance probability agrees with the existing finite real-weight interface when its proposal distribution is finite. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool, assume α is finite. Then

probability(toPMF(P), accept) = Sampling.acceptance(P, accept).
-/
theorem probability_toPMF [Fintype α] (P : FiniteDistribution α) (accept : α → Bool) :
    probability (toPMF P) accept = Sampling.acceptance P accept := by
  unfold probability
  rw [← toPMF_map,toFinite_toPMF]
  simp only [FiniteDistribution.map,FiniteDistribution.bind,FiniteDistribution.pure,
    Sampling.acceptance]
  apply Finset.sum_congr rfl
  intro x _
  cases hx : accept x <;> simp [hx]
end
end CircuitCompiler.Sampling.CountableRejection
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*}
/-- One actual proposal together with its conditional private tape. -/

def enrichedProposal [Fintype α] (P : FiniteDistribution α) (R : α → PMF β) : PMF (α × β) :=
  ⟨fun z => toPMF P z.1 * R z.1 z.2,by
    apply ENNReal.summable.hasSum_iff.mpr
    rw [ENNReal.tsum_prod']
    simp only [ENNReal.tsum_mul_left,PMF.tsum_coe,mul_one]⟩
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*}
@[simp] theorem enrichedProposal_apply [Fintype α] (P : FiniteDistribution α) (R : α → PMF β) (z : α × β) :
    enrichedProposal P R z = toPMF P z.1 * R z.1 z.2 :=
  rfl
theorem enrichedProposal_eq_sigma [Fintype α] (P : FiniteDistribution α) (R : α → PMF β) :
    enrichedProposal P R = (sigmaPMF (toPMF P) R).map (fun z => (z.1,z.2)) := by
  apply PMF.ext
  intro z
  rcases z with ⟨za,zb⟩
  rw [PMF.map_apply,ENNReal.tsum_sigma']
  simp only [sigmaPMF_apply,Prod.mk.injEq]
  rw [tsum_eq_single za]
  · simp only [true_and,eq_self_iff_true,enrichedProposal_apply,toPMF_apply]
    rw [tsum_eq_single zb]
    · simp
    · intro b hb
      exact if_neg (Ne.symm hb)
  · intro a ha
    simp [Ne.symm ha]
theorem enrichedProposal_fst [Fintype α] (P : FiniteDistribution α) (R : α → PMF β) :
    (enrichedProposal P R).map Prod.fst = toPMF P := by
  rw [enrichedProposal_eq_sigma,PMF.map_comp]
  exact sigmaPMF_fst _ _
theorem enrichedProposal_probability [Fintype α] (P : FiniteDistribution α) (accept : α → Bool)
    (R : α → PMF β) :
    CountableRejection.probability (enrichedProposal P R) (accept ∘ Prod.fst) = acceptance P accept := by
  rw [← CountableRejection.probability_map,enrichedProposal_fst,CountableRejection.probability_toPMF]
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Rectangular.Taped
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n t : ℕ}
end
end CircuitCompiler.Rectangular.Taped
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Rectangular.Taped
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n t : ℕ}
theorem raw_proposal_distribution (hn : 2 ≤ n) (u : U F (n+t)) :
    (enrichedProposal (attemptDistribution hn u) (fun p => markDistribution hn u p.val.1)).map
      (fun pm => rawAttempt u pm.1 pm.2) = AttemptSampler.sequentialDistribution (by omega : 1 ≤ n) u := by
  rw [enrichedProposal_eq_sigma,PMF.map_comp]
  exact proposal_distribution_actual hn u
@[simp] theorem rawAccept_rawAttempt (u v : U F (n+t))
    (p : Attempt (n := n) u) (mark : Mark F n (n+t)) :
    rawAccept u v (rawAttempt u p mark) = decide (rightOutput v p ≠ 0) := by
  simp only [rawAccept,rawAttempt_returned]
end
end CircuitCompiler.Rectangular.Taped
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Rectangular.Taped
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n t : ℕ}
end
end CircuitCompiler.Rectangular.Taped
end
