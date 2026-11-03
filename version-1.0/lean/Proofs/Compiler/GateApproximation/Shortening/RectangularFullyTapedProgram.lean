import Proofs.Compiler.Simulation.IndependentRunner
import Proofs.Compiler.GateApproximation.MatrixPhase.MatrixSamplerTapes
import Proofs.Compiler.GateApproximation.Shortening.RectangularTapedProgram
import Proofs.Compiler.Construction.Parameters



/-!
# Concrete leakage from all matrix and shortening sampler tapes

Every adversarial field below is an ordinary deterministic function of a party's local shares, communicated data, and complete private rejection tapes. There are no assumed conditional rectangle decompositions. The square-matrix sampler is the actual iid raw-matrix rejection sampler, and every shortening attempt includes its actual nonzero-row and affine-completion samplers.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

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

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For O,A a set; m, k ∈ ℕ; p ∈ TableRectanglePartition(O, GLₖ(F), A), assume A is finite; m = k. Then

matrixPartitionDimension(matrixPartitionDimension((h)⁻¹, p)) = p.
-/
@[simp] theorem matrixPartitionDimension_roundtrip {O A : Type*} [Fintype A]
    {m k : ℕ} (h : m = k) (p : TableRectanglePartition O (Refresh.«GL» F k) A) :
    matrixPartitionDimension h (matrixPartitionDimension h.symm p) = p := by
  subst k
  rfl

/-- The state-based implementation draws a fresh matrix rejection prefix at every gate, then runs the actual shortening samplers. -/
/-
Mathematical definition (normal notation): For strategy ∈ FullyTapedStrategy(F, ML, MR, BL, BR, n, t, inputs, hdim), assume 2 ≤ n. define

protocol(strategy) := GateProtocol.mixSeeds(((x₁ ↦ matrixPrefixDistribution(F = F, (n + t)))), ((failures ↦ protocol(strategy.fixedPrefix(failures))))) .
-/
def protocol (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim) (hn : 2 ≤ n) :
    GateProtocol F (State F n) ((ML × MR) × (BL × BR)) inputs :=
  GateProtocol.mixSeeds (fun _ => matrixPrefixDistribution (F := F) (n+t))
    (fun failures => (strategy.fixedPrefix failures).protocol hn)

/-- Concrete full gate distribution: first execute raw-matrix rejection, then execute all actual raw row/completion attempts and observe the complete local tapes. -/
/-
Mathematical definition (normal notation): For strategy ∈ FullyTapedStrategy(F, ML, MR, BL, BR, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → (ML × MR) × (BL × BR); left, right ∈ State(F, n), assume 2 ≤ n. define

rawExecution(strategy, i, gate, history, left, right) := (((z ↦ ((z)₁, (z)₂)))_*bind(strategy.rawMatrixExecution(i, gate, history, left, right), ((ma ↦ Taped.rawShorteningExecution(TapedAugmentedStrategy.fallback(hdim = hdim, gate, left, right), strategy.left(i, gate, history), strategy.right(i, gate, history), augmentedOldPorts(left, right), refreshInFiber(gateInput(augmentedLeftFeature(hdim, gate.kind.affineConstant), augmentedRightFeature(hdim), augmentedOldPorts(left, right)), (ma)₁), (ma)₂))))).
-/
def rawExecution (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → (ML × MR) × (BL × BR)) (left right : State F n) :
    FiniteDistribution (State F n × ((ML × MR) × (BL × BR))) :=
  ((strategy.rawMatrixExecution i gate history left right).bind (fun ma =>
    Taped.rawShorteningExecution hn (TapedAugmentedStrategy.fallback (hdim := hdim) hn gate left right)
      (strategy.left i gate history) (strategy.right i gate history) (augmentedOldPorts left right)
      (refreshInFiber (gateInput (augmentedLeftFeature hdim gate.kind.affineConstant)
        (augmentedRightFeature hdim) (augmentedOldPorts left right)) ma.1) ma.2)).map
    (fun z => (z.1.val,z.2))

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ FullyTapedStrategy(F, ML, MR, BL, BR, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → (ML × MR) × (BL × BR); left, right ∈ State(F, n), we have

strategy.rawMatrixExecution(i, gate, history, left, right) = countableMixture(matrixPrefixDistribution(F = F, (n + t)), ((failures ↦ joint(𝒰_(GL_(n + t)(F)))(fixedMatrixAnswerDistribution(matrixTapePartition(strategy.matrixLeft(i, gate, history), strategy.matrixRight(i, gate, history), failures), (augmentedOldPorts(left, right))₁, (augmentedOldPorts(left, right))₂))))).
-/
theorem rawMatrixExecution_eq_mixture
    (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim)
    (i : ℕ) (gate : Gate F (inputs+i)) (history : Fin i → (ML × MR) × (BL × BR))
    (left right : State F n) :
    strategy.rawMatrixExecution i gate history left right =
      countableMixture (matrixPrefixDistribution (F := F) (n+t)) (fun failures =>
        (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n+t))).joint
          (fixedMatrixAnswerDistribution (matrixTapePartition (strategy.matrixLeft i gate history)
            (strategy.matrixRight i gate history) failures)
              (augmentedOldPorts left right).1 (augmentedOldPorts left right).2)) := by
  unfold rawMatrixExecution
  rw [matrix_joint_fixedMatrixAnswerDistribution_eq]
  congr 1
  funext failures
  ext z
  simp [FiniteDistribution.map,FiniteDistribution.bind,FiniteDistribution.pure]

/-- Exact connection between the security proof's real runner and the full implemented sampler distribution. All rejected proposals remain visible to the allowed local leakage functions, including rejected proposals inside shortening. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ FullyTapedStrategy(F, ML, MR, BL, BR, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → (ML × MR) × (BL × BR); left, right ∈ State(F, n), assume 2 ≤ n. Then

real(strategy.protocol)(i, gate, history, left, right) = strategy.rawExecution(i, gate, history, left, right).
-/
theorem real_eq_rawExecution (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → (ML × MR) × (BL × BR)) (left right : State F n) :
    (strategy.protocol hn).real i gate history left right =
      strategy.rawExecution hn i gate history left right := by
  unfold protocol GateProtocol.mixSeeds rawExecution
  rw [rawMatrixExecution_eq_mixture,countableMixture_bind,countableMixture_map]
  dsimp only
  congr 1
  funext failures
  rw [TapedAugmentedStrategy.real_eq_rawExecution]
  unfold TapedAugmentedStrategy.rawExecution fixedPrefix
  simp only [matrixPartitionDimension_roundtrip]

/-- The share-carrier runner used by the final compiler theorem observes the same raw execution, with only a bijective change of wire representation. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ FullyTapedStrategy(F, ML, MR, BL, BR, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → (ML × MR) × (BL × BR); left, right ∈ U(F, n) × U(F, n), assume 2 ≤ n. Then

real(strategy.shareProtocol)(i, gate, history, left, right) = (((z ↦ (stateEquivProd(F, n, (z)₁), (z)₂)))_*strategy.rawExecution(i, gate, history, (stateEquivProd(F, n))⁻¹(left), (stateEquivProd(F, n))⁻¹(right))).
-/
theorem share_real_eq_rawExecution (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → (ML × MR) × (BL × BR)) (left right : U F n × U F n) :
    (strategy.shareProtocol hn).real i gate history left right =
      (strategy.rawExecution hn i gate history ((stateEquivProd F n).symm left)
        ((stateEquivProd F n).symm right)).map
          (fun z => (stateEquivProd F n z.1,z.2)) := by
  change countableMixture (matrixPrefixDistribution (F := F) (n+t))
    (fun failures => (((strategy.fixedPrefix failures).protocol hn).real i gate history
      ((stateEquivProd F n).symm left) ((stateEquivProd F n).symm right)).map
        (fun z => (stateEquivProd F n z.1,z.2))) = _
  rw [← countableMixture_map]
  exact congrArg (fun distribution => distribution.map (fun z => (stateEquivProd F n z.1,z.2)))
    (strategy.real_eq_rawExecution hn i gate history
      ((stateEquivProd F n).symm left) ((stateEquivProd F n).symm right))

end FullyTapedStrategy

end

end CircuitCompiler.Rectangular
