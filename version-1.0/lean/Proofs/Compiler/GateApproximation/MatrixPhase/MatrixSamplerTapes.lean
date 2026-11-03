import Proofs.Compiler.GateApproximation.MatrixPhase.CountableMixture
import Proofs.Compiler.GateApproximation.Shortening.RectangularShortening
import Proofs.Compiler.GateApproximation.MatrixPhase.RefreshAnswerProbabilities
import Proofs.Compiler.GateApproximation.MatrixPhase.RejectionPrefix
import Proofs.Compiler.Construction.Parameters



/-!
# The internal rejection tape of uniform matrix sampling

Uniform raw matrices are proposed until one is invertible. The failed prefix is independent of the returned invertible matrix. Fixing that prefix turns arbitrary local leakage of every proposal into an ordinary answer rectangle.
-/
set_option autoImplicit false

open scoped BigOperators Classical

namespace CircuitCompiler.Sampling

open Refresh MatrixRefresh TableAnalysis Unbounded

noncomputable section

variable {F X L R V : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype L] [Fintype R] [Fintype V] {m : ℕ}

/-- The exact unbounded rejection-sampler distribution for every finite observation. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ StoppedTape(F^({0,…,m−1} × {0,…,m−1})) → V, we have

observe(FiniteDistribution.uniform, invertibleTest, matrixAcceptancePositive(F = F, m), f) = toFinite(bind(matrixPrefixDistribution(F = F, m), ((failures ↦ toPMF((((M ↦ f(matrixTrace(failures, M))))_*𝒰_(GLₘ(F)))))))).
-/
theorem matrix_observe_eq_prefix_uniform
    (f : StoppedTape (Matrix (Fin m) (Fin m) F) → V) :
    observe FiniteDistribution.uniform invertibleTest (matrixAcceptancePositive (F := F) m) f =
      toFinite ((matrixPrefixDistribution (F := F) m).bind (fun failures =>
        toPMF ((FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F m)).map
          (fun M => f (matrixTrace failures M))))) := by
  rw [uniform_observe_eq_prefix_bind,
    ← Rectangular.uniform_equiv (invertibleEquiv (F := F) m)]
  simp only [FiniteDistribution.map_map, Function.comp_def]
  rfl

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For left ∈ X → StoppedTape(F^({0,…,m−1} × {0,…,m−1})) → L; right ∈ X → StoppedTape(F^({0,…,m−1} × {0,…,m−1})) → R; failures ∈ MatrixPrefix(F, m); x, y ∈ X; M ∈ GLₘ(F), we have

RefreshAnalysis.fixedMatrixAnswerDistribution(matrixTapePartition(left, right, failures), x, y, M) = FiniteDistribution.pure((left(x, matrixTrace(failures, M)), right(y, matrixTrace(failures, M)))).
-/
theorem matrixTapePartition_answer
    (left : X → StoppedTape (Matrix (Fin m) (Fin m) F) → L)
    (right : X → StoppedTape (Matrix (Fin m) (Fin m) F) → R)
    (failures : MatrixPrefix F m) (x y : X) (M : Refresh.«GL» F m) :
    RefreshAnalysis.fixedMatrixAnswerDistribution (matrixTapePartition left right failures) x y M =
      FiniteDistribution.pure (left x (matrixTrace failures M),right y (matrixTrace failures M)) := by
  classical
  ext z
  rcases z with ⟨l,r⟩
  simp only [RefreshAnalysis.fixedMatrixAnswerDistribution, TableRectanglePartition.toRoundPartition,
    TableRectanglePartition.leftIndicator, TableRectanglePartition.rightIndicator,
    matrixTapePartition, Bool.decide_eq_true, FiniteDistribution.pure, Prod.mk.injEq]
  by_cases hl : left x (matrixTrace failures M) = l <;>
    by_cases hr : right y (matrixTrace failures M) = r <;>
      simp_all [eq_comm]

/-- Leakage of the complete concrete sampler equals an independent-prefix mixture of the exact matrix-phase distributions used by the analytic proof. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For left ∈ X → StoppedTape(F^({0,…,m−1} × {0,…,m−1})) → L; right ∈ X → StoppedTape(F^({0,…,m−1} × {0,…,m−1})) → R; x, y ∈ X, we have

observe(FiniteDistribution.uniform, invertibleTest, matrixAcceptancePositive(F = F, m), ((trace ↦ (left(x, trace), right(y, trace))))) = toFinite(bind(matrixPrefixDistribution(F = F, m), ((failures ↦ toPMF(bind(𝒰_(GLₘ(F)), RefreshAnalysis.fixedMatrixAnswerDistribution(matrixTapePartition(left, right, failures), x, y))))))).
-/
theorem matrix_local_leakage_eq
    (left : X → StoppedTape (Matrix (Fin m) (Fin m) F) → L)
    (right : X → StoppedTape (Matrix (Fin m) (Fin m) F) → R) (x y : X) :
    observe FiniteDistribution.uniform invertibleTest (matrixAcceptancePositive (F := F) m)
      (fun trace => (left x trace,right y trace)) =
    toFinite ((matrixPrefixDistribution (F := F) m).bind (fun failures =>
      toPMF ((FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F m)).bind
        (RefreshAnalysis.fixedMatrixAnswerDistribution (matrixTapePartition left right failures) x y)))) := by
  rw [matrix_observe_eq_prefix_uniform]
  have hf (failures : MatrixPrefix F m) :
      RefreshAnalysis.fixedMatrixAnswerDistribution (matrixTapePartition left right failures) x y =
        fun M => FiniteDistribution.pure (left x (matrixTrace failures M),right y (matrixTrace failures M)) :=
    funext (matrixTapePartition_answer left right failures x y)
  simp_rw [hf]
  rfl

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For M ∈ GLₘ(F), we have

matrixReturned(M) = M.
-/
@[simp] theorem matrixReturned_val (M : Refresh.«GL» F m) : matrixReturned M.val = M := by
  have h : invertibleTest M.val = true := (invertibleEquiv m M).property
  rw [matrixReturned, dif_pos h]
  exact (invertibleEquiv m).symm_apply_apply M

/-- Full matrix-phase state and answer, not just a leakage marginal, agree with the independent-prefix representation. A continuation may therefore use the returned matrix and answers jointly without losing their correlation. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For left ∈ X → StoppedTape(F^({0,…,m−1} × {0,…,m−1})) → L; right ∈ X → StoppedTape(F^({0,…,m−1} × {0,…,m−1})) → R; x, y ∈ X; f ∈ GLₘ(F) → L × R → V, we have

observe(FiniteDistribution.uniform, invertibleTest, matrixAcceptancePositive(F = F, m), ((trace ↦ f(matrixReturned(((trace)₂)₂), (left(x, trace), right(y, trace)))))) = countableMixture(matrixPrefixDistribution(F = F, m), ((failures ↦ (((M ↦ f(M, (left(x, matrixTrace(failures, M)), right(y, matrixTrace(failures, M))))))_*𝒰_(GLₘ(F)))))).
-/
theorem matrix_joint_observation_eq
    (left : X → StoppedTape (Matrix (Fin m) (Fin m) F) → L)
    (right : X → StoppedTape (Matrix (Fin m) (Fin m) F) → R) (x y : X)
    (f : Refresh.«GL» F m → L × R → V) :
    observe FiniteDistribution.uniform invertibleTest (matrixAcceptancePositive (F := F) m)
      (fun trace => f (matrixReturned trace.2.2) (left x trace,right y trace)) =
      countableMixture (matrixPrefixDistribution (F := F) m) (fun failures =>
        (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F m)).map (fun M =>
          f M (left x (matrixTrace failures M),right y (matrixTrace failures M)))) := by
  rw [matrix_observe_eq_prefix_uniform]
  simp only [matrixTrace,joinPrefix,matrixReturned_val,countableMixture]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For I,J,W a set; P ∈ 𝒟(I); g ∈ I → J; f ∈ I → J → W, assume I is finite; J is finite; W is finite. Then

(((ij ↦ f((ij)₁, (ij)₂)))_*P.joint(((i ↦ FiniteDistribution.pure(g(i)))))) = (((i ↦ f(i, g(i))))_*P).
-/
private theorem joint_pure_map {I J W : Type*} [Fintype I] [Fintype J] [Fintype W]
    (P : FiniteDistribution I) (g : I → J) (f : I → J → W) :
    ((P.joint (fun i => FiniteDistribution.pure (g i))).map (fun ij => f ij.1 ij.2)) =
      P.map (fun i => f i (g i)) := by
  classical
  ext w
  simp only [FiniteDistribution.map,FiniteDistribution.bind,FiniteDistribution.joint,Fintype.sum_prod_type,FiniteDistribution.pure]
  simp only [mul_ite,mul_zero,mul_one]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (g i)]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- The concrete full-tape sampler gives exactly the matrix-phase experiment used in the security proof, averaged over independent rejected prefixes. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For left ∈ X → StoppedTape(F^({0,…,m−1} × {0,…,m−1})) → L; right ∈ X → StoppedTape(F^({0,…,m−1} × {0,…,m−1})) → R; x, y ∈ X; f ∈ GLₘ(F) → L × R → V, we have

observe(FiniteDistribution.uniform, invertibleTest, matrixAcceptancePositive(F = F, m), ((trace ↦ f(matrixReturned(((trace)₂)₂), (left(x, trace), right(y, trace)))))) = countableMixture(matrixPrefixDistribution(F = F, m), ((failures ↦ (((ma ↦ f((ma)₁, (ma)₂)))_*joint(𝒰_(GLₘ(F)))(RefreshAnalysis.fixedMatrixAnswerDistribution(matrixTapePartition(left, right, failures), x, y)))))) .
-/
theorem matrix_joint_fixedMatrixAnswerDistribution_eq
    (left : X → StoppedTape (Matrix (Fin m) (Fin m) F) → L)
    (right : X → StoppedTape (Matrix (Fin m) (Fin m) F) → R) (x y : X)
    (f : Refresh.«GL» F m → L × R → V) :
    observe FiniteDistribution.uniform invertibleTest (matrixAcceptancePositive (F := F) m)
      (fun trace => f (matrixReturned trace.2.2) (left x trace,right y trace)) =
      countableMixture (matrixPrefixDistribution (F := F) m) (fun failures =>
        ((FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F m)).joint
          (RefreshAnalysis.fixedMatrixAnswerDistribution (matrixTapePartition left right failures) x y)).map
            (fun ma => f ma.1 ma.2)) := by
  rw [matrix_joint_observation_eq]
  congr 1
  funext failures
  have hf : RefreshAnalysis.fixedMatrixAnswerDistribution (matrixTapePartition left right failures) x y =
      fun M => FiniteDistribution.pure (left x (matrixTrace failures M),right y (matrixTrace failures M)) :=
    funext (matrixTapePartition_answer left right failures x y)
  rw [hf,joint_pure_map]

end

end CircuitCompiler.Sampling
