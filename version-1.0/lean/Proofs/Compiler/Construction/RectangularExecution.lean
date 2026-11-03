import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.Construction.Programs
/-!
# The physical rectangular-shortening execution

Raw rectangular-attempt tapes, their local leakage views, conditional answer distributions, and the actual full-retry execution used by ordinary computation gadgets.

This module is part of the constructive compiler model; it imports no compiler proof theorem. The public source and execution interfaces are in Compiler.Direct and Compiler.Stateful.
-/
set_option backward.isDefEq.respectTransparency false
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.AttemptSampler
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Nonzero rows and accepted raw vector proposals are identical choices. -/

def rowAcceptedEquiv (n : ℕ) :
    {v : V F n // nonzeroTest v = true} ≃ U F n :=
  Equiv.subtypeEquiv (Equiv.refl _) (fun v => by simp [nonzeroTest])
/-- A positive vector dimension supplies a nonzero row. -/
theorem rowNonempty {n : ℕ} (hn : 1 ≤ n) : Nonempty (U F n) := ⟨rowDefault hn⟩
end
end CircuitCompiler.Rectangular.AttemptSampler
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.AttemptSampler
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular.AttemptSampler
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.AttemptSampler
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular.AttemptSampler
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.AttemptSampler
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
@[simp] theorem rowReturned_nonzero {n : ℕ} (hn : 1 ≤ n) (a : U F n) :
    rowReturned hn a.val = a := by
  simp only [rowReturned,dif_pos a.property]
end
end CircuitCompiler.Rectangular.AttemptSampler
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.AttemptSampler
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular.AttemptSampler
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.AttemptSampler
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- All internal zero rejections are independent of the accepted nonzero row. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): For n ≥ 1, a rejection-sampled nonzero row and its complete sampling tape have the following equivalent generation: first choose the final row uniformly from 𝔽ⁿ ∖ {0}, independently sample the rejected prefix with its rejection-prefix distribution, and append that row. This produces exactly the original stopped-tape distribution. -/
theorem rowDistribution_eq_uniform_prefix {n : ℕ} (hn : 1 ≤ n) :
    letI := rowNonempty (F := F) hn
    rowDistribution (F := F) hn = (toPMF (FiniteDistribution.uniform : FiniteDistribution (U F n))).bind
      (fun a => (rowRejectedDistribution hn).map (fun p => reconstructRow p a)) := by
  letI := rowNonempty (F := F) hn
  letI : Nonempty {v : V F n // nonzeroTest v = true} :=
    ⟨(rowAcceptedEquiv n).symm (rowDefault hn)⟩
  have hU : (FiniteDistribution.uniform : FiniteDistribution {v : V F n // nonzeroTest v = true}) =
      (FiniteDistribution.uniform : FiniteDistribution (U F n)).map (rowAcceptedEquiv n).symm :=
    (uniform_equiv (rowAcceptedEquiv n).symm).symm
  unfold rowDistribution rowRejectedDistribution
  rw [distribution_eq_prefix_bind,accepted_uniform,hU]
  simp only [FiniteDistribution.map_map,toPMF_map,PMF.map_comp,Function.comp_def]
  change (prefixDistribution FiniteDistribution.uniform nonzeroTest _).bind (fun p =>
    (toPMF (FiniteDistribution.uniform : FiniteDistribution (U F n))).bind (fun a =>
      PMF.pure (reconstructRow p a))) = _
  exact PMF.bind_comm _ _ _
end
end CircuitCompiler.Rectangular.AttemptSampler
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.AttemptSampler
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end
end CircuitCompiler.Rectangular.AttemptSampler
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.AttemptSampler
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Exact implementation distribution for one outer proposal, retaining both internal raw proposal tapes. The conditional mark distribution is derived from the two real rejection samplers and keeps its `(U,A)` dependence. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; u ∈ U(F, (n + t)), assume 2 ≤ n. Then

sequentialDistribution(, u) = bind(toPMF(attemptDistribution(u)), ((p ↦ (reconstruct(u, p)_*markDistribution(, u, (p)₁))))).
-/
theorem sequentialDistribution_eq_marked {n t : ℕ} (hn : 2 ≤ n) (u : U F (n+t)) :
    sequentialDistribution (by omega : 1 ≤ n) u =
      (toPMF (attemptDistribution hn u)).bind (fun p =>
        (markDistribution (by omega : 1 ≤ n) u p.val.1).map (reconstruct u p)) := by
  letI := rowNonempty (F := F) (show 1 ≤ n by omega)
  letI : ∀ a : U F n, Nonempty (Completion u a) := fun a => completion_nonempty u a
  unfold sequentialDistribution
  rw [rowDistribution_eq_uniform_prefix,PMF.bind_bind]
  simp only [PMF.bind_map,Function.comp_def,reconstructRow,joinPrefix]
  simp_rw [CompletionSampler.tapeDistribution_eq_uniform_prefix,PMF.map_bind]
  unfold attemptDistribution
  simp only [toPMF_map,toPMF_bind,PMF.bind_bind,PMF.bind_map,Function.comp_def]
  congr 1
  funext a
  rw [rowReturned_nonzero]
  rw [PMF.bind_comm]
  congr 1
  funext H
  unfold markDistribution
  rw [PMF.map_bind]
  congr 1
  funext r
  simp only [PMF.map_comp,Function.comp_def,reconstruct,attemptSigmaEquiv]
  rfl
end
end CircuitCompiler.Rectangular.AttemptSampler
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
/-- Independently sampling two marks is their explicit product distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For I,J a set; P ∈ PMF(I); Q ∈ PMF(J), we have

productPMF(P, Q) = bind(P, ((i ↦ (Prod.mk(i)_*Q)))).
-/
theorem productPMF_eq_bind {I J : Type*} (P : PMF I) (Q : PMF J) :
    productPMF P Q = P.bind (fun i => Q.map (Prod.mk i)) := by
  classical
  apply PMF.ext
  intro ⟨i,j⟩
  rw [PMF.bind_apply,tsum_eq_single i]
  · rw [PMF.map_apply]
    simp
    rfl
  · intro k hk
    rw [PMF.map_apply]
    simp [Ne.symm hk]
variable {α β Z : Type*} [Fintype α] [Fintype Z]
/-- First-attempt success has no previous marks: its sole private mark has exactly the proposal's own conditional distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): For a trace consisting of a single accepted proposal a, sampling its private mark and then applying an observation is exactly sampling b ∼ R(a) and observing the pair consisting of an empty rejected-mark prefix and b. -/
theorem first_traceMarks_observation (R : α → PMF β) (a : α)
    (f : Tape β 0 × β → Z) :
    toFinite ((traceMarks R ⟨0,(PUnit.unit,a)⟩).map f) =
      toFinite ((R a).map (fun b => f (PUnit.unit,b))) := by
  unfold traceMarks
  rw [prefixMarks,productPMF_eq_bind,PMF.pure_bind]
  rw [PMF.map_comp]
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
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh
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
open Refresh MatrixRefresh
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
open Refresh MatrixRefresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- The nonzero long right shares mapped to a prescribed nonzero short right share by H. -/
abbrev Preimage {n m : ℕ} (H : FullRank F n m) (r : U F n) :=
  {v : U F m // H.val.mulVec v.val = r.val}
/-- Every nonzero right fiber is an affine copy of the full kernel. -/

def preimageEquivKernel {n m : ℕ} (H : FullRank F n m) (r : U F n) :
    Preimage H r ≃ {v : V F m // H.val.mulVec v = 0} where
  toFun v := ⟨v.val.val - (rightInverse H).mulVec r.val, by
    rw [Matrix.mulVec_sub, v.property, Matrix.mulVec_mulVec,
      mul_rightInverse, Matrix.one_mulVec, sub_self]⟩
  invFun k := ⟨⟨k.val + (rightInverse H).mulVec r.val, by
    intro hz
    have h := congrArg H.val.mulVec hz
    simp only [Matrix.mulVec_add, k.property, Matrix.mulVec_mulVec,
      mul_rightInverse, Matrix.one_mulVec, zero_add, Matrix.mulVec_zero] at h
    exact r.property h⟩, by
    rw [Matrix.mulVec_add, k.property, Matrix.mulVec_mulVec,
      mul_rightInverse, Matrix.one_mulVec, zero_add]⟩
  left_inv v := by apply Subtype.ext; apply Subtype.ext; exact sub_add_cancel _ _
  right_inv k := by apply Subtype.ext; exact add_sub_cancel_right _ _
/-- The vector-space kernel of the rectangular matrix H. -/
abbrev Kernel {n m : ℕ} (H : FullRank F n m) := {v : V F m // H.val.mulVec v = 0}
instance kernelNonempty {n m : ℕ} (H : FullRank F n m) : Nonempty (Kernel H) := ⟨⟨0,by simp⟩⟩
/-- Recover a long right share from its short image and a kernel coordinate. -/
def rightLift {n m : ℕ} (H : FullRank F n m) (r : U F n) (k : Kernel H) : U F m :=
  ((preimageEquivKernel H r).symm k).val
end
end CircuitCompiler.Rectangular
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh
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
set_option maxHeartbeats 1500000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh
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
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh Shortening
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- The reverse record reconstructed from a short output and a kernel vector. -/

def reverseRecord {n m : ℕ} {s : F} (p : Fiber F n s) (H : FullRank F n m)
    (k : Kernel H) : Backward F n m s :=
  ⟨(p,H,((preimageEquivKernel H p.val.R).symm k).val),
    ((preimageEquivKernel H p.val.R).symm k).property⟩
/-- The full conditional observation distribution, given the fresh short output. -/

def recordAnswerDistribution {Z : Type*} [Fintype Z] {n t : ℕ} {s : F}
    [Nonempty (FullRank F n (n+t))]
    (observe : Backward F n (n+t) s → FiniteDistribution Z) (p : Fiber F n s) : FiniteDistribution Z :=
  (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).bind fun H =>
    (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).bind fun k => observe (reverseRecord p H k)
end
end CircuitCompiler.Rectangular
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh TableAnalysis Shortening
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {O A B : Type*} [Fintype O] [DecidableEq O] [Nonempty O]
  [Fintype A] [Fintype B]
variable {n t : ℕ} [Nonempty (U F n)] [Nonempty (U F (n+t))]
  [Nonempty (FullRank F n (n+t))]
/-- The private right-side coordinate in a successful shortening record. -/

def recordNoise {s : F} (p : Backward F n (n+t) s) : Kernel p.val.2.1 :=
  preimageEquivKernel p.val.2.1 p.val.1.val.R ⟨p.val.2.2,p.property⟩
end
end CircuitCompiler.Rectangular
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh Shortening RefreshAnalysis TableAnalysis
noncomputable section
variable {F O A B : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [DecidableEq O] [Nonempty O] [Fintype A] [Fintype B]
variable {n t : ℕ}
/-- The matrix-phase conditional answer on any prescribed output fiber. -/

def longAnswer {s : F} (a b : O → U F (n+t))
    (p : TableRectanglePartition O (Refresh.«GL» F (n+t)) A)
    (o : O × O) (x : Fiber F (n+t) s) : FiniteDistribution A :=
  answerDistribution a b p o.1 o.2 x.val
end
end CircuitCompiler.Rectangular
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh TableAnalysis Shortening RefreshAnalysis
open Composition Composition.TopologicalExecution
noncomputable section
variable {F O A B : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [Fintype A] [Fintype B]
/-- An explicit full-row-rank rectangular matrix is always available. -/
instance fullRankNonempty (n t : ℕ) : Nonempty (FullRank F n (n+t)) :=
  ⟨⟨projection n t, projection_fullRowRank n t⟩⟩
/-- Reindex the matrix tape in a leakage partition along the same equality. -/

def matrixPartitionDimension {m k : ℕ} (h : m = k)
    (p : TableRectanglePartition O (Refresh.«GL» F m) A) :
    TableRectanglePartition O (Refresh.«GL» F k) A := by
  subst k
  exact p
variable {n t inputs T : ℕ}
end
end CircuitCompiler.Rectangular
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Shortening
open Refresh MatrixRefresh TableAnalysis
/-- Nonnegative local answer masks, including conditional averages over private local randomness. The complete joint answer distribution has total mass one. -/

structure FractionalRectanglePartition (B X Y : Type*) [Fintype B] where
  left : B → X → ℝ
  right : B → Y → ℝ
  left_nonneg : ∀ b x, 0 ≤ left b x
  left_le_one : ∀ b x, left b x ≤ 1
  right_nonneg : ∀ b y, 0 ≤ right b y
  right_le_one : ∀ b y, right b y ≤ 1
  partition : ∀ x y, (∑ b, left b x * right b y) = 1
namespace FractionalRectanglePartition
variable {B X Y D : Type*} [Fintype B]
/-- The joint conditional answer distribution specified by the two local masks. -/

def answer (r : FractionalRectanglePartition B X Y) (x : X) (y : Y) : FiniteDistribution B where
  weight b := r.left b x * r.right b y
  nonneg b := mul_nonneg (r.left_nonneg b x) (r.right_nonneg b y)
  total := r.partition x y
end FractionalRectanglePartition
end CircuitCompiler.Shortening
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Shortening
open Refresh MatrixRefresh TableAnalysis
namespace FractionalRectanglePartition
variable {B X Y D : Type*} [Fintype B]
theorem weight_le_one {E : Type*} [Fintype E] (P : FiniteDistribution E) (e : E) :
    P.weight e ≤ 1 := by
  have h := Finset.single_le_sum (fun a (_ : a ∈ (Finset.univ : Finset E)) => P.nonneg a)
    (Finset.mem_univ e)
  simpa only [P.total] using h
end FractionalRectanglePartition
end CircuitCompiler.Shortening
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Shortening
open Refresh MatrixRefresh TableAnalysis
namespace FractionalRectanglePartition
variable {B X Y D : Type*} [Fintype B]
/-- Input-dependent local conditional answer distributions induce fractional rectangles. Locality and conditional independence are represented explicitly by the separate functions `L` and `R`. -/

def ofLocalDistributions {BL BR : Type*} [Fintype BL] [Fintype BR]
    (L : X → FiniteDistribution BL) (R : Y → FiniteDistribution BR) :
    FractionalRectanglePartition (BL × BR) X Y where
  left b x := (L x).weight b.1
  right b y := (R y).weight b.2
  left_nonneg b x := (L x).nonneg b.1
  left_le_one b x := weight_le_one (L x) b.1
  right_nonneg b y := (R y).nonneg b.2
  right_le_one b y := weight_le_one (R y) b.2
  partition x y := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, (R y).total, mul_one, (L x).total]
end FractionalRectanglePartition
end CircuitCompiler.Shortening
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Shortening
open Refresh MatrixRefresh TableAnalysis
namespace FractionalRectanglePartition
variable {B X Y D : Type*} [Fintype B]
@[simp] theorem ofLocalDistributions_answer {BL BR : Type*} [Fintype BL] [Fintype BR]
    (L : X → FiniteDistribution BL) (R : Y → FiniteDistribution BR) (x : X) (y : Y) :
    (ofLocalDistributions L R).answer x y = (L x).prod (R y) := by
  ext b
  rfl
end FractionalRectanglePartition
end CircuitCompiler.Shortening
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular.Fractional
open Refresh MatrixRefresh TableAnalysis Shortening
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {O A B : Type*} [Fintype O] [DecidableEq O] [Nonempty O]
  [Fintype A] [Fintype B]
variable {n t : ℕ} [Nonempty (U F n)] [Nonempty (U F (n+t))]
  [Nonempty (FullRank F n (n+t))]
/-- Conditional shortening answer after averaging the local private tapes. -/

def rectangleRecordAnswer {s : F}
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (O × U F n) ((O × U F n) × Kernel H))
    (o : O × O) (p : Backward F n (n+t) s) (a : A) : FiniteDistribution B :=
  (r a p.val.2.1).answer (o.1,p.val.1.val.L) ((o.2,p.val.1.val.R),recordNoise p)
/-- Retain both the matrix-phase answer and the shortening-phase answer. -/

def rectangleRecordLeak {s : F}
    (K : O × O → Fiber F (n+t) s → FiniteDistribution A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (O × U F n) ((O × U F n) × Kernel H))
    (o : O × O) (p : Backward F n (n+t) s) : FiniteDistribution (A × B) :=
  (K o (backwardSource p)).joint (rectangleRecordAnswer r o p)
/-- The conditional complete answer after a first-attempt successful shortening. -/

def shortenedAnswerDistribution {s : F}
    (K : O × O → Fiber F (n+t) s → FiniteDistribution A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (O × U F n) ((O × U F n) × Kernel H))
    (o : O × O) (p : Fiber F n s) : FiniteDistribution (A × B) :=
  recordAnswerDistribution (rectangleRecordLeak K r o) p
end
end CircuitCompiler.Rectangular.Fractional
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators
namespace CircuitCompiler.Rectangular.Fractional
open Refresh MatrixRefresh Shortening RefreshAnalysis TableAnalysis
noncomputable section
variable {F O A B : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [DecidableEq O] [Nonempty O] [Fintype A] [Fintype B]
variable {n t : ℕ}
/-- The actual unbounded shortening phase, retaining its matrix answer and any finite leakage observation of the outer rectangular retry tape. -/

def shorteningExecution {s : F} (hn : 2 ≤ n) (fallback : Fiber F n s)
    (leak : (x : Fiber F (n+t) s) → A → FullTape (n := n) x.val.L → FiniteDistribution B)
    (x : Fiber F (n+t) s) (α : A) : FiniteDistribution (Fiber F n s × (A × B)) :=
  fullTapeAnswerDistribution hn x.val.L x.val.R (fun tape =>
    (leak x α tape).map (fun β => (returnedOutput fallback x tape.2.2,(α,β))))
/-- The real gate samples one shared square matrix and then executes the unbounded rectangular sampler with primitive uniform completion choices. The matrix has been erased before `leak`. -/

def fullGateExecution (hn : 2 ≤ n) (a b : O → U F (n+t))
    (p : TableRectanglePartition O (Refresh.«GL» F (n+t)) A) (o : O × O)
    (fallback : Fiber F n (gateSecret a b o))
    (leak : (x : Fiber F (n+t) (gateSecret a b o)) → A → FullTape (n := n) x.val.L → FiniteDistribution B) :
    FiniteDistribution (Fiber F n (gateSecret a b o) × (A × B)) :=
  ((FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n+t))).joint (fixedMatrixAnswerDistribution p o.1 o.2)).bind
    (fun ma => shorteningExecution hn fallback leak
      (refreshInFiber (gateInput a b o) ma.1) ma.2)
variable [Nonempty (FullRank F n (n+t))]
/-- The accepted conditional answer, preceded by the exact fresh output distribution. -/

def fullGateCanonical (hn : 2 ≤ n) (a b : O → U F (n+t))
    (p : TableRectanglePartition O (Refresh.«GL» F (n+t)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (O × U F n) ((O × U F n) × Kernel H)) (o : O × O) :
    FiniteDistribution (Fiber F n (gateSecret a b o) × (A × B)) := by
  letI := fiber_nonempty F n hn (gateSecret a b o)
  exact (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (gateSecret a b o))).joint
    (shortenedAnswerDistribution (longAnswer a b p) r o)
/-- A normalized common-state conditional distribution. Values outside the output secret fiber are irrelevant to the fresh-encoding canonical transition. -/

def ambientGateAnswerDistribution (hn : 2 ≤ n) (a b : O → U F (n+t))
    (p : TableRectanglePartition O (Refresh.«GL» F (n+t)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (O × U F n) ((O × U F n) × Kernel H)) (o : O × O)
    (u : State F n) : FiniteDistribution (A × B) :=
  if hu : secret u = gateSecret a b o then
    shortenedAnswerDistribution (longAnswer a b p) r o ⟨u,hu⟩
  else (fullGateCanonical hn a b p r o).map Prod.snd
end
end CircuitCompiler.Rectangular.Fractional
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical
namespace CircuitCompiler.Rectangular.Fractional
open Refresh MatrixRefresh TableAnalysis Shortening RefreshAnalysis
open Composition Composition.TopologicalExecution
noncomputable section
variable {F O A B : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [Fintype A] [Fintype B]
variable {n t inputs T : ℕ}
/-- Adaptive choices between gates, and actual observations within each gate. `firstLeak` is the concrete first-success rectangle condition of the model. -/

structure AugmentedStrategy (F A B : Type*) [Field F] [Fintype F] [DecidableEq F]
    [Fintype A] [Fintype B] (n t inputs : ℕ) (hdim : n*n+1 = n+t) where
  matrix : (i : ℕ) → Gate F (inputs+i) → (Fin i → A × B) →
    TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A
  rectangles : (i : ℕ) → Gate F (inputs+i) → (Fin i → A × B) →
    A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (GateSide F n n) ((GateSide F n n) × Kernel H)
  fallback : (i : ℕ) → (gate : Gate F (inputs+i)) → (Fin i → A × B) →
    (left right : State F n) →
    Fiber F n (gateSecret (augmentedLeftFeature hdim gate.kind.affineConstant)
      (augmentedRightFeature hdim) (augmentedOldPorts left right))
  leak : (i : ℕ) → (gate : Gate F (inputs+i)) → (Fin i → A × B) →
    (left right : State F n) →
    (x : Fiber F (n+t) (gateSecret (augmentedLeftFeature hdim gate.kind.affineConstant)
      (augmentedRightFeature hdim) (augmentedOldPorts left right))) →
    A → FullTape (n := n) x.val.L → FiniteDistribution B
  firstLeak : ∀ i gate history left right x α (z : Success (n := n) x.val.L x.val.R),
    leak i gate history left right x α ⟨0,(PUnit.unit,z.val)⟩ =
      rectangleRecordAnswer (rectangles i gate history) (augmentedOldPorts left right)
        (successfulJointEquiv _ ⟨x,z⟩) α
namespace AugmentedStrategy
variable {hdim : n*n+1 = n+t}
/-- The actual augmented matrix phase followed by all rectangular retries. -/

def protocol (strategy : AugmentedStrategy F A B n t inputs hdim) (hn : 2 ≤ n) :
    GateProtocol F (State F n) (A × B) inputs := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  exact {
    real := fun i gate history left right =>
      (fullGateExecution hn (augmentedLeftFeature hdim gate.kind.affineConstant)
        (augmentedRightFeature hdim) (matrixPartitionDimension hdim (strategy.matrix i gate history))
        (augmentedOldPorts left right) (strategy.fallback i gate history left right)
        (strategy.leak i gate history left right)).map (fun z => (z.1.val,z.2))
    answer := fun i gate history left right output =>
      ambientGateAnswerDistribution hn (augmentedLeftFeature hdim gate.kind.affineConstant)
        (augmentedRightFeature hdim) (matrixPartitionDimension hdim (strategy.matrix i gate history))
        (strategy.rectangles i gate history) (augmentedOldPorts left right) output }
/-- The same real implementation on the paired-share wire carrier. -/

def shareProtocol (strategy : AugmentedStrategy F A B n t inputs hdim) (hn : 2 ≤ n) :
    GateProtocol F (U F n × U F n) (A × B) inputs :=
  (strategy.protocol hn).transport (stateEquivProd F n)
end AugmentedStrategy
end
end CircuitCompiler.Rectangular.Fractional
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators
namespace CircuitCompiler.Rectangular.Taped
open Refresh MatrixRefresh Sampling Sampling.Unbounded Shortening
noncomputable section
variable {F O A BL BR M : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [Fintype A] [Fintype BL] [Fintype BR]
variable {n t : ℕ}
/-- The left shortening view contains every proposal pair and its corresponding private internal sampler marks. -/
abbrev LeftView (F M : Type*) [Field F] (n m : ℕ) :=
  MarkedTape (U F n × FullRank F n m) M
/-- The left party has all proposal values and its own private marks. -/

def leftView {u : U F (n+t)} (z : FullTape (n := n) u) (marks : Tape M z.1 × M) :
    LeftView F M n (n+t) := ⟨mapStopped Subtype.val z,marks⟩
/-- Conditional distribution of both answers, derived by averaging the actual private marks. The mark distribution may depend arbitrarily on the local long share and short row; its dependence is never discarded. -/

def leakageAnswerDistribution
    (κ : U F (n+t) → U F n → PMF M)
    (left : A → O → U F (n+t) → LeftView F M n (n+t) → BL)
    (right : A → O → U F (n+t) → RightView F n (n+t) → BR)
    (o : O × O) {s : F} (x : Fiber F (n+t) s) (α : A)
    (z : FullTape (n := n) x.val.L) : FiniteDistribution (BL × BR) :=
  (toFinite ((traceMarks (fun a : Attempt (n := n) x.val.L => κ x.val.L a.val.1) z).map
    (fun marks => left α o.1 x.val.L (leftView z marks)))).prod
      (FiniteDistribution.pure (right α o.2 x.val.R (rightView z)))
/-- The first-success masks are defined for every local input, before any plaintext labels are fixed. The long left share is reconstructed as `A H`. -/

def rectangles
    (κ : U F (n+t) → U F n → PMF M)
    (left : A → O → U F (n+t) → LeftView F M n (n+t) → BL)
    (right : A → O → U F (n+t) → RightView F n (n+t) → BR)
    (α : A) (H : FullRank F n (n+t)) :
    FractionalRectanglePartition (BL × BR) (O × U F n) ((O × U F n) × Kernel H) :=
  FractionalRectanglePartition.ofLocalDistributions
    (fun x => toFinite ((κ (leftShare H x.2) x.2).map (fun mark =>
      left α x.1 (leftShare H x.2) ⟨⟨0,(PUnit.unit,(x.2,H))⟩,(PUnit.unit,mark)⟩)))
    (fun y => FiniteDistribution.pure (right α y.1.1 (rightLift H y.1.2 y.2) ⟨0,(PUnit.unit,H)⟩))
end
end CircuitCompiler.Rectangular.Taped
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators
namespace CircuitCompiler.Rectangular.Taped
open Refresh MatrixRefresh Sampling Sampling.Unbounded Shortening
noncomputable section
variable {F O A BL BR M : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [Fintype A] [Fintype BL] [Fintype BR]
variable {n t : ℕ}
@[simp] theorem rightLift_recordNoise {s : F} (p : Backward F n (n+t) s) :
    rightLift p.val.2.1 p.val.1.val.R (recordNoise p) = p.val.2.2 := by
  unfold rightLift recordNoise
  simp
/-- First success has precisely the derived fractional local distribution. This is a proved view identity, not an assumption of independence from the inputs. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For κ ∈ U(F, (n + t)) → U(F, n) → PMF(M); left ∈ A → O → U(F, (n + t)) → LeftView(F, M, n, (n + t)) → BL; right ∈ A → O → U(F, (n + t)) → RightView(F, n, (n + t)) → BR; o ∈ O × O; s ∈ F; x ∈ Fiber(F, (n + t), s); α ∈ A; z ∈ Success(n = n, x.val.L, x.val.R), we have

leakageAnswerDistribution(κ, left, right, o, x, α, (0, (PUnit.unit, z))) = Fractional.rectangleRecordAnswer(rectangles(κ, left, right), o, successfulJointEquiv(s, (x, z)), α).
-/
theorem first_leak_eq_rectangles
    (κ : U F (n+t) → U F n → PMF M)
    (left : A → O → U F (n+t) → LeftView F M n (n+t) → BL)
    (right : A → O → U F (n+t) → RightView F n (n+t) → BR)
    (o : O × O) {s : F} (x : Fiber F (n+t) s) (α : A)
    (z : Success (n := n) x.val.L x.val.R) :
    leakageAnswerDistribution κ left right o x α ⟨0,(PUnit.unit,z.val)⟩ =
      Fractional.rectangleRecordAnswer (rectangles κ left right) o
        (successfulJointEquiv s ⟨x,z⟩) α := by
  unfold leakageAnswerDistribution
  rw [first_traceMarks_observation]
  unfold Fractional.rectangleRecordAnswer rectangles
  rw [FractionalRectanglePartition.ofLocalDistributions_answer,rightLift_recordNoise]
  have hL : leftShare z.val.val.2 z.val.val.1 = x.val.L :=
    Subtype.ext z.val.property
  change _ = (toFinite ((κ (leftShare z.val.val.2 z.val.val.1) z.val.val.1).map
    (fun mark => left α o.1 (leftShare z.val.val.2 z.val.val.1)
      ⟨⟨0,(PUnit.unit,(z.val.val.1,z.val.val.2))⟩,(PUnit.unit,mark)⟩))).prod
        (FiniteDistribution.pure (right α o.2 x.val.R ⟨0,(PUnit.unit,z.val.val.2)⟩))
  rw [hL]
  rfl
end
end CircuitCompiler.Rectangular.Taped
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
open scoped BigOperators ENNReal
namespace CircuitCompiler.Rectangular.Taped
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n t : ℕ}
end
end CircuitCompiler.Rectangular.Taped
end
section
/-!
# Construction lemmas

These lemmas justify the model definitions and probability constructions. They are not security assumptions.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
open scoped BigOperators ENNReal
namespace CircuitCompiler.Rectangular.Taped
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n t : ℕ}
@[simp] theorem rawAttempt_tagged (u : U F (n+t)) (p : Attempt (n := n) u)
    (mark : AttemptSampler.Mark (m := n+t) p.val.1) :
    rawAttempt u p ⟨p.val.1,mark⟩ = AttemptSampler.reconstruct u p mark := by
  simp [rawAttempt]
@[simp] theorem rawAttempt_returned (u : U F (n+t)) (p : Attempt (n := n) u)
    (mark : Mark F n (n+t)) : AttemptSampler.returned u (rawAttempt u p mark) = p := by
  unfold rawAttempt
  split_ifs <;> exact AttemptSampler.returned_reconstruct _ _ _
/-- The marked proposal is exactly the concrete sequential row/completion sampler after reconstructing its raw internal tapes. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u ∈ U(F, (n + t)), assume 2 ≤ n. Then

(((pm ↦ rawAttempt(u, (pm)₁, (pm)₂)))_*sigmaPMF(toPMF(attemptDistribution(u)), ((p ↦ markDistribution(u, (p)₁))))) = AttemptSampler.sequentialDistribution(, u).
-/
theorem proposal_distribution_actual (hn : 2 ≤ n) (u : U F (n+t)) :
    (sigmaPMF (toPMF (attemptDistribution hn u)) (fun p => markDistribution hn u p.val.1)).map
        (fun pm => rawAttempt u pm.1 pm.2) =
      AttemptSampler.sequentialDistribution (by omega : 1 ≤ n) u := by
  rw [sigmaPMF_observation,AttemptSampler.sequentialDistribution_eq_marked hn]
  congr 1
  funext p
  unfold markDistribution
  rw [PMF.map_comp]
  simp only [Function.comp_def,rawAttempt_tagged]
end
end CircuitCompiler.Rectangular.Taped
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
open scoped BigOperators ENNReal
namespace CircuitCompiler.Rectangular.Taped
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n t : ℕ}
end
end CircuitCompiler.Rectangular.Taped
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators
namespace CircuitCompiler.Rectangular.Taped
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F O A BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [Fintype A] [Fintype BL] [Fintype BR]
variable {n t : ℕ}
/-- Decode raw tapes from the local proposal values and a private mark. This is total even on tuples outside the sampler's support. -/

def rawLocalAttempt (u : U F (n+t)) (p : U F n × FullRank F n (n+t))
    (mark : Mark F n (n+t)) : AttemptSampler.Record (n := n) u :=
  let k : AttemptSampler.Mark (m := n+t) p.1 :=
    if h : mark.1 = p.1 then h ▸ mark.2 else emptyMark p.1
  ⟨p.1,(AttemptSampler.reconstructRow k.1 p.1,
    joinPrefix k.2 (fun i j => p.2.val i.val j))⟩
/-- Reconstruct the rejected physical shortening proposals visible in the left party’s local tape. -/
def rawLocalPrefix (u : U F (n+t)) : (k : ℕ) → Tape (U F n × FullRank F n (n+t)) k →
    Tape (Mark F n (n+t)) k → Tape (AttemptSampler.Record (n := n) u) k
  | 0, _, _ => PUnit.unit
  | k+1, a, b => (rawLocalAttempt u a.1 b.1,rawLocalPrefix u k a.2 b.2)
/-- Reconstruct the left party’s full physical shortening tape, including the accepted proposal. -/
def rawLeftView (u : U F (n+t)) (z : LeftView F (Mark F n (n+t)) n (n+t)) :
    StoppedTape (AttemptSampler.Record (n := n) u) :=
  ⟨z.1.1,(rawLocalPrefix u z.1.1 z.1.2.1 z.2.1,rawLocalAttempt u z.1.2.2 z.2.2)⟩
/-- Interpret an arbitrary observer of actual raw tapes as a local marked view. -/

def leftObserver
    (left : A → O → (u : U F (n+t)) → StoppedTape (AttemptSampler.Record (n := n) u) → BL) :
    A → O → U F (n+t) → LeftView F (Mark F n (n+t)) n (n+t) → BL :=
  fun α o u z => left α o u (rawLeftView u z)
end
end CircuitCompiler.Rectangular.Taped
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2600000
open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh TableAnalysis Shortening RefreshAnalysis
open Composition Composition.TopologicalExecution Sampling Sampling.Unbounded
noncomputable section
variable {F A BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype A] [Fintype BL] [Fintype BR]
variable {n t inputs T : ℕ}
/-- A concrete adaptive strategy for the implemented shortening samplers. The matrix is erased before either shortening observer is invoked. -/

structure TapedAugmentedStrategy (F A BL BR : Type*) [Field F] [Fintype F] [DecidableEq F]
    [Fintype A] [Fintype BL] [Fintype BR] (n t inputs : ℕ) (hdim : n*n+1 = n+t) where
  matrix : (i : ℕ) → Gate F (inputs+i) → (Fin i → A × (BL × BR)) →
    TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A
  left : (i : ℕ) → Gate F (inputs+i) → (Fin i → A × (BL × BR)) →
    A → (U F n × U F n) → (u : U F (n+t)) →
      StoppedTape (AttemptSampler.Record (n := n) u) → BL
  right : (i : ℕ) → Gate F (inputs+i) → (Fin i → A × (BL × BR)) →
    A → (U F n × U F n) → U F (n+t) → Taped.RightView F n (n+t) → BR
namespace TapedAugmentedStrategy
variable {hdim : n*n+1 = n+t}
/-- Exact embedding in the proved fractional interface. Every conditional private-tape distribution is derived from the concrete row/completion samplers. -/

def stochasticStrategy (strategy : TapedAugmentedStrategy F A BL BR n t inputs hdim)
    (hn : 2 ≤ n) : Fractional.AugmentedStrategy F A (BL × BR) n t inputs hdim where
  matrix := strategy.matrix
  rectangles i gate history := Taped.rectangles (Taped.markDistribution hn)
    (Taped.leftObserver (strategy.left i gate history)) (strategy.right i gate history)
  fallback i gate history left right := fallback hn gate left right
  leak i gate history left right := Taped.leakageAnswerDistribution (Taped.markDistribution hn)
    (Taped.leftObserver (strategy.left i gate history)) (strategy.right i gate history)
    (augmentedOldPorts left right)
  firstLeak i gate history left right x α z :=
    Taped.first_leak_eq_rectangles (Taped.markDistribution hn)
      (Taped.leftObserver (strategy.left i gate history)) (strategy.right i gate history)
      (augmentedOldPorts left right) x α z
/-- The identical implementation on the paired-share carrier. -/

def shareProtocol (strategy : TapedAugmentedStrategy F A BL BR n t inputs hdim) (hn : 2 ≤ n) :
    GateProtocol F (U F n × U F n) (A × (BL × BR)) inputs :=
  (strategy.stochasticStrategy hn).shareProtocol hn
end TapedAugmentedStrategy
end
end CircuitCompiler.Rectangular
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option maxHeartbeats 2600000
open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh TableAnalysis Shortening RefreshAnalysis
open Composition Composition.TopologicalExecution Sampling Sampling.Unbounded
noncomputable section
variable {F ML MR BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
variable {n t inputs T : ℕ}
namespace FullyTapedStrategy
variable {hdim : n*n+1 = n+t}
/-- Fixing the rejected matrix prefix leaves precisely the concrete shortening-tape strategy. The prefix distribution is independent of all shares, whereas the private shortening tape distributions may depend on their shares. -/

def fixedPrefix (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim)
    (failures : MatrixPrefix F (n+t)) : TapedAugmentedStrategy F (ML × MR) BL BR n t inputs hdim where
  matrix i gate history := matrixPartitionDimension hdim.symm
    (matrixTapePartition (strategy.matrixLeft i gate history) (strategy.matrixRight i gate history) failures)
  left := strategy.left
  right := strategy.right
/-- The same implementation on the share-pair carrier used by composition. -/

def shareProtocol (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim) (hn : 2 ≤ n) :
    GateProtocol F (U F n × U F n) ((ML × MR) × (BL × BR)) inputs :=
  GateProtocol.mixSeeds (fun _ => matrixPrefixDistribution (F := F) (n+t))
    (fun failures => (strategy.fixedPrefix failures).shareProtocol hn)
end FullyTapedStrategy
end
end CircuitCompiler.Rectangular
end
section
/-!
# Model definitions

These are the original definitions used by the security theorems. The construction lemmas are included here; analytical security arguments are in the proof folders.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped Classical
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh TableAnalysis Shortening RefreshAnalysis
open Composition Composition.TopologicalExecution Sampling Sampling.Unbounded
noncomputable section
variable {F O A BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [Fintype A] [Fintype BL] [Fintype BR] {n t : ℕ}
namespace Taped
end Taped
namespace FullyTapedStrategy
variable {ML MR : Type*} [Fintype ML] [Fintype MR]
variable {inputs : ℕ} {hdim : n*n+1 = n+t}
end FullyTapedStrategy
end
end CircuitCompiler.Rectangular
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
namespace CircuitCompiler.Rectangular.Taped
open Refresh MatrixRefresh Sampling Sampling.Unbounded Gaussian
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n t : ℕ}
end
end CircuitCompiler.Rectangular.Taped
end
