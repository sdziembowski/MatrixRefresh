import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.Construction.Arithmetic
/-!
# Stopped rejection tapes

Probability distributions for unbounded rejection sampling, retained rejected proposals, and independent matrix-prefix decompositions.

This module is part of the constructive compiler model; it imports no compiler proof theorem. The public source and execution interfaces are in Compiler.Direct and Compiler.Stateful.
-/
set_option backward.isDefEq.respectTransparency false
section
/-!
# Geometric probability masses for rejection sampling

The geometric mass function gₚ(k) = (1 − p)ᵏp is used by the finite-tape sampler model. Its probability-mass formulation is provided explicitly because the current Mathlib API presents the same distribution as a measure.
-/
namespace ProbabilityTheory
end ProbabilityTheory
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
/-- Embed a finite real probability distribution in the countable-PMF interface. -/

def toPMF (P : FiniteDistribution α) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (P.weight a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => P.nonneg a), P.total]
    simp)
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
@[simp] theorem toPMF_apply (P : FiniteDistribution α) (a : α) :
    toPMF P a = ENNReal.ofReal (P.weight a) :=
  rfl
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
@[simp] theorem toFinite_toPMF (P : FiniteDistribution α) : toFinite (toPMF P) = P := by
  ext a
  exact ENNReal.toReal_ofReal (P.nonneg a)
theorem toPMF_map (P : FiniteDistribution α) (f : α → β) :
    toPMF (P.map f) = (toPMF P).map f := by
  classical
  apply PMF.ext
  intro b
  rw [PMF.map_apply, tsum_fintype]
  change ENNReal.ofReal (∑ a, P.weight a * (FiniteDistribution.pure (f a)).weight b) = _
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => mul_nonneg (P.nonneg _) ((FiniteDistribution.pure _).nonneg _))]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : b = f a <;> simp [FiniteDistribution.pure, h]
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
@[simp] theorem distribution_apply (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (t : StoppedTape α) :
    distribution P accept hp t = ENNReal.ofReal (traceWeight P accept t) :=
  rfl
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
@[simp] theorem prefixDistribution_apply (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (t : FailedPrefix α) :
    prefixDistribution P accept hp t =
      ENNReal.ofReal (prefixWeight P accept t.1 t.2 * acceptance P accept) :=
  rfl
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
/-- Exact factorization of the probability of every complete internal tape. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; t ∈ FailedPrefix(α); a ∈ α, assume 0 < acceptance(P, accept). Then

distribution(P, accept, joinPrefix(t, a)) = prefixDistribution(P, accept, t) · toPMF(accepted(P, accept), a).
-/
theorem distribution_joinPrefix (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (t : FailedPrefix α) (a : α) :
    distribution P accept hp (joinPrefix t a) =
      prefixDistribution P accept hp t * toPMF (accepted P accept hp) a := by
  rw [distribution_apply, prefixDistribution_apply, toPMF_apply,
    ← ENNReal.ofReal_mul (mul_nonneg (prefixWeight_nonneg P accept _ _) hp.le)]
  congr 1
  change prefixWeight P accept t.1 t.2 * (if accept a then P.weight a else 0) =
    (prefixWeight P accept t.1 t.2 * acceptance P accept) *
      ((if accept a then P.weight a else 0) / acceptance P accept)
  field_simp
/-- Reconstruct a complete sampler tape by independently choosing the failed prefix and the accepted terminal proposal. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool, assume 0 < acceptance(P, accept). Then

distribution(P, accept) = bind(prefixDistribution(P, accept), ((t ↦ (joinPrefix(t)_*toPMF(accepted(P, accept)))))).
-/
theorem distribution_eq_prefix_bind (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) :
    distribution P accept hp = (prefixDistribution P accept hp).bind
      (fun t => (toPMF (accepted P accept hp)).map (joinPrefix t)) := by
  classical
  apply PMF.ext
  intro t
  rw [PMF.bind_apply]
  have hm (p : FailedPrefix α) :
      ((toPMF (accepted P accept hp)).map (joinPrefix p)) t =
        if p = ⟨t.1,t.2.1⟩ then toPMF (accepted P accept hp) t.2.2 else 0 := by
    rw [PMF.map_apply, tsum_fintype]
    by_cases h : p = ⟨t.1,t.2.1⟩
    · subst p
      rcases t with ⟨k,p,a⟩
      simp [joinPrefix]
    · apply Eq.trans (Finset.sum_eq_zero (fun a _ => ?_)) (if_neg h).symm
      apply if_neg
      intro he
      have := congrArg (fun z : StoppedTape α => (⟨z.1,z.2.1⟩ : FailedPrefix α)) he
      exact h this.symm
  simp_rw [hm, mul_ite, mul_zero]
  rw [tsum_ite_eq]
  exact distribution_joinPrefix P accept hp ⟨t.1,t.2.1⟩ t.2.2
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh Sampling
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
set_option maxHeartbeats 1800000
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
/-- Finite sequential sampling has the same countable-PMF interpretation. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); Q ∈ α → 𝒟(β), we have

toPMF(bind(P, Q)) = bind(toPMF(P), ((a ↦ toPMF(Q(a))))).
-/
theorem toPMF_bind (P : FiniteDistribution α) (Q : α → FiniteDistribution β) :
    toPMF (P.bind Q) = (toPMF P).bind (fun a => toPMF (Q a)) := by
  apply PMF.ext
  intro b
  rw [PMF.bind_apply,tsum_fintype]
  change ENNReal.ofReal (∑ a, P.weight a * (Q a).weight b) = _
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => mul_nonneg (P.nonneg a) ((Q a).nonneg b))]
  apply Finset.sum_congr rfl
  intro a _
  exact ENNReal.ofReal_mul (P.nonneg a)
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
/-- A conditional answer distribution summarizes further private-tape observations and may depend on every value in the outer tape. -/

def observeDistribution (P : FiniteDistribution α) (accept : α → Bool) (hp : 0 < acceptance P accept)
    (f : StoppedTape α → FiniteDistribution β) : FiniteDistribution β :=
  toFinite ((distribution P accept hp).bind (fun t => toPMF (f t)))
end
end CircuitCompiler.Sampling.Unbounded
namespace CircuitCompiler.Rectangular
open Refresh Sampling
noncomputable section
variable {F Z : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype Z]
/-- Average arbitrary local private randomness after fixing the full outer tape. -/

def fullTapeAnswerDistribution {n t : ℕ} (hn : 2 ≤ n) (u v : U F (n+t))
    (f : FullTape (n := n) u → FiniteDistribution Z) : FiniteDistribution Z :=
  Unbounded.observeDistribution (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0))
    (attempt_acceptance_pos hn u v) f
end
end CircuitCompiler.Rectangular
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh MeasureTheory TableAnalysis
noncomputable section
variable {Ω V : Type*} [Countable Ω] [Fintype V]
/-- A countable auxiliary tape followed by a finite conditional experiment. -/

def countableMixture (tape : PMF Ω) (P : Ω → FiniteDistribution V) : FiniteDistribution V :=
  toFinite (tape.bind (fun ω => toPMF (P ω)))
end
end CircuitCompiler.Sampling.Unbounded
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical
namespace CircuitCompiler.RefreshAnalysis
open Refresh MatrixRefresh TableAnalysis
noncomputable section
variable {F X Z : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype X] [Nonempty X] [Fintype Z] {m : ℕ}
/-- Refresh the selected left and right shares with one invertible matrix. -/
def refreshedEncoding (a b : X → U F m) (x y : X) (M : Refresh.«GL» F m) : State F m :=
  refresh ⟨a x, b y⟩ M
/-- The complete local answer distribution after fixing the refresh matrix and the old local inputs. -/
def fixedMatrixAnswerDistribution (p : TableRectanglePartition X (Refresh.«GL» F m) Z)
    (x y : X) (M : Refresh.«GL» F m) : FiniteDistribution Z where
  weight z := p.toRoundPartition.weight z M (x,y)
  nonneg z := p.toRoundPartition.nonneg z M _
  total := p.toRoundPartition.complete M _
/-- Average the complete local answer over refresh matrices conditioned on the specified new encoding. -/
def answerDistribution (a b : X → U F m)
    (p : TableRectanglePartition X (Refresh.«GL» F m) Z) (x y : X) (u : State F m) : FiniteDistribution Z :=
  (conditional (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F m))
    (refreshedEncoding a b x y) u).bind (fixedMatrixAnswerDistribution p x y)
end
end CircuitCompiler.RefreshAnalysis
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
open scoped BigOperators Classical
namespace CircuitCompiler.Sampling
open Refresh MatrixRefresh TableAnalysis Unbounded
noncomputable section
variable {F X L R V : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype L] [Fintype R] [Fintype V] {m : ℕ}
/-- A complete finite prefix of rejected square-matrix proposals. -/
abbrev MatrixPrefix (F : Type*) (m : ℕ) :=
  FailedPrefix (Matrix (Fin m) (Fin m) F)
/-- The actual distribution of the rejected square-matrix prefix before the accepted invertible matrix. -/
def matrixPrefixDistribution (m : ℕ) : PMF (MatrixPrefix F m) :=
  prefixDistribution FiniteDistribution.uniform invertibleTest (matrixAcceptancePositive (F := F) m)
/-- Full internal tape, reconstructed from independent failures and the final invertible matrix. Every rejected raw matrix is still available to leakage. -/

def matrixTrace (failures : MatrixPrefix F m) (M : Refresh.«GL» F m) :
    StoppedTape (Matrix (Fin m) (Fin m) F) := joinPrefix failures M.val
/-- Fixing only the failed prefix produces a valid matrix-dependent rectangle partition for any two local leakage functions. -/

def matrixTapePartition
    (left : X → StoppedTape (Matrix (Fin m) (Fin m) F) → L)
    (right : X → StoppedTape (Matrix (Fin m) (Fin m) F) → R)
    (failures : MatrixPrefix F m) : TableRectanglePartition X (Refresh.«GL» F m) (L × R) where
  left z M x := decide (left x (matrixTrace failures M) = z.1)
  right z M y := decide (right y (matrixTrace failures M) = z.2)
  complete M x y := by
    classical
    simp [Fintype.sum_prod_type]
end
end CircuitCompiler.Sampling
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
namespace CircuitCompiler.Sampling
open Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Test whether an encoding’s inner product equals its prescribed secret. -/
def secretTest {n : ℕ} (s : F) (state : State F n) : Bool := decide (secret state = s)
end CircuitCompiler.Sampling
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
namespace CircuitCompiler.Sampling
open Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
theorem nonzero_acceptance {n : ℕ} :
    acceptance (FiniteDistribution.uniform : FiniteDistribution (V F n)) nonzeroTest =
      ((fieldCard F ^ n : ℕ) - 1 : ℕ) / (fieldCard F ^ n : ℝ) := by
  rw [acceptance_uniform, vector_card]
  have hcard : Fintype.card {v : V F n // nonzeroTest v = true} =
      Fintype.card (U F n) := by
    exact Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _)
      (fun v => by simp [nonzeroTest]))
  rw [hcard, nonzero_vector_card]
  simp
theorem nonzero_acceptance_ge_half {n : ℕ} (hn : 1 ≤ n) :
    (1 / 2 : ℝ) ≤ acceptance (FiniteDistribution.uniform : FiniteDistribution (V F n)) nonzeroTest := by
  rw [nonzero_acceptance]
  have htwo : 2 ≤ fieldCard F ^ n := (fieldCard_ge_two (F := F)).trans
    (by simpa using Nat.pow_le_pow_right (fieldCard_pos (F := F)) hn)
  have hreal : (2 : ℝ) ≤ (fieldCard F : ℝ) ^ n := by exact_mod_cast htwo
  rw [Nat.cast_sub (by omega : 1 ≤ fieldCard F ^ n), Nat.cast_one, Nat.cast_pow]
  apply (le_div_iff₀ (by positivity)).mpr
  linarith
theorem state_card (n : ℕ) : Fintype.card (State F n) = shareCard F n ^ 2 := by
  rw [Fintype.card_congr (stateEquivProd F n), Fintype.card_prod, nonzero_vector_card]
  simp [shareCard, vectorCard, pow_two]
theorem secret_acceptance {n : ℕ} [Nonempty (State F n)] (s : F) :
    acceptance (FiniteDistribution.uniform : FiniteDistribution (State F n)) (secretTest s) =
      (densityWeight F n s)⁻¹ := by
  rw [acceptance_uniform, state_card]
  have hcard : Fintype.card {state : State F n // secretTest s state = true} =
      Fintype.card (Fiber F n s) := by
    exact Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _)
      (fun state => by simp [secretTest]))
  rw [hcard]
  simp [densityWeight]
/-- Rejection from two independent nonzero shares accepts with constant probability for fixed field size, including the zero plaintext. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, assume 2 ≤ n; State(F, n) ≠ ∅. Then

((2 · |F|))⁻¹ ≤ acceptance(𝒰_(State(F, n)), secretTest(s)).
-/
theorem secret_acceptance_ge {n : ℕ} (hn : 2 ≤ n) [Nonempty (State F n)] (s : F) :
    (2 * (fieldCard F : ℝ))⁻¹ ≤
      acceptance (FiniteDistribution.uniform : FiniteDistribution (State F n)) (secretTest s) := by
  rw [secret_acceptance]
  have hq := fieldCard_cast_pos (F := F)
  exact (inv_le_inv₀ (by positivity : (0 : ℝ) < 2 * fieldCard F)
    (densityWeight_pos hn s)).mpr (densityWeight_le_two_mul_q hn s)
end CircuitCompiler.Sampling
end
