import Proofs.Compiler.GateApproximation.Shortening.RectangularFractionalScope
import Proofs.Compiler.GateApproximation.Shortening.RectangularTapedViews
import Proofs.Compiler.Construction.Parameters



/-!
# Circuit strategies observing every actual shortening sampler tape

The only adversarial inputs are deterministic local leakage functions. Left leakage can inspect every raw nonzero-row and completion proposal on every outer attempt; right leakage sees its own long share and the full communicated matrix sequence. The fractional rectangles and first-success identities are constructed and proved, rather than supplied as strategy hypotheses.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2600000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical

namespace CircuitCompiler.Rectangular

open Refresh MatrixRefresh TableAnalysis Shortening RefreshAnalysis

open Composition Composition.TopologicalExecution Sampling Sampling.Unbounded

noncomputable section

variable {F A BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype A] [Fintype BL] [Fintype BR]

variable {n t inputs T : ℕ}

namespace TapedAugmentedStrategy

variable {hdim : n*n+1 = n+t}

/-- Actual state-based protocol, including both levels of shortening rejection. -/
/-
Mathematical definition (normal notation): For strategy ∈ TapedAugmentedStrategy(F, A, BL, BR, n, t, inputs, hdim), assume 2 ≤ n. define

protocol(strategy) := protocol(strategy.stochasticStrategy).
-/
def protocol (strategy : TapedAugmentedStrategy F A BL BR n t inputs hdim) (hn : 2 ≤ n) :
    GateProtocol F (State F n) (A × (BL × BR)) inputs :=
  (strategy.stochasticStrategy hn).protocol hn

/-- Direct execution as a deterministic observation of the actual complete internal sampler traces. The shared square matrix is still sampled uniformly; its implementation tape is handled by the matrix-sampling refinement. -/
/-
Mathematical definition (normal notation): For strategy ∈ TapedAugmentedStrategy(F, A, BL, BR, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → A × (BL × BR); left, right ∈ State(F, n), assume 2 ≤ n. define

rawExecution(strategy, i, gate, history, left, right) := (((z ↦ ((z)₁, (z)₂)))_*bind(joint(𝒰_(GL_(n + t)(F)))(fixedMatrixAnswerDistribution(matrixPartitionDimension(hdim, strategy.matrix(i, gate, history)), (augmentedOldPorts(left, right))₁, (augmentedOldPorts(left, right))₂)), ((ma ↦ Taped.rawShorteningExecution(fallback(gate, left, right), strategy.left(i, gate, history), strategy.right(i, gate, history), augmentedOldPorts(left, right), refreshInFiber(gateInput(augmentedLeftFeature(hdim, gate.kind.affineConstant), augmentedRightFeature(hdim), augmentedOldPorts(left, right)), (ma)₁), (ma)₂))))).
-/
def rawExecution (strategy : TapedAugmentedStrategy F A BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i)) (history : Fin i → A × (BL × BR))
    (left right : State F n) : FiniteDistribution (State F n × (A × (BL × BR))) :=
  (((FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n+t))).joint
      (fixedMatrixAnswerDistribution (matrixPartitionDimension hdim (strategy.matrix i gate history))
        (augmentedOldPorts left right).1 (augmentedOldPorts left right).2)).bind (fun ma =>
    Taped.rawShorteningExecution hn (fallback hn gate left right)
      (strategy.left i gate history) (strategy.right i gate history) (augmentedOldPorts left right)
      (refreshInFiber (gateInput (augmentedLeftFeature hdim gate.kind.affineConstant)
        (augmentedRightFeature hdim) (augmentedOldPorts left right)) ma.1) ma.2)).map
    (fun z => (z.1.val,z.2))

/-- The circuit runner's real transition observes the actual raw tapes exactly. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ TapedAugmentedStrategy(F, A, BL, BR, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → A × (BL × BR); left, right ∈ State(F, n), assume 2 ≤ n. Then

real(strategy.protocol)(i, gate, history, left, right) = strategy.rawExecution(i, gate, history, left, right).
-/
theorem real_eq_rawExecution (strategy : TapedAugmentedStrategy F A BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i)) (history : Fin i → A × (BL × BR))
    (left right : State F n) :
    (strategy.protocol hn).real i gate history left right =
      strategy.rawExecution hn i gate history left right := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0,by omega⟩⟩
  unfold protocol Fractional.AugmentedStrategy.protocol Fractional.fullGateExecution rawExecution
  dsimp only [stochasticStrategy]
  congr 1
  congr 1
  funext ma
  exact (Taped.rawShorteningExecution_eq_distribution hn (fallback hn gate left right)
    (strategy.left i gate history) (strategy.right i gate history) (augmentedOldPorts left right)
    (refreshInFiber (gateInput (augmentedLeftFeature hdim gate.kind.affineConstant)
      (augmentedRightFeature hdim) (augmentedOldPorts left right)) ma.1) ma.2).symm

/-- Actual private-tape leakage costs only outer first-attempt rejection. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ TapedAugmentedStrategy(F, A, BL, BR, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → A × (BL × BR); left, right ∈ State(F, n), assume 2 ≤ n; |F| = 2. Then

δ(real(strategy.protocol)(i, gate, history, left, right), joint(μ_(gate.kind.eval(secret(left), secret(right))))(answer(strategy.protocol)(i, gate, history, left, right))) ≤ 2 / 2ⁿ.
-/
theorem local_coupling (strategy : TapedAugmentedStrategy F A BL BR n t inputs hdim)
    (hn : 2 ≤ n) (hq : fieldCard F = 2)
    (i : ℕ) (gate : Gate F (inputs+i)) (history : Fin i → A × (BL × BR))
    (left right : State F n) :
    statisticalDistance ((strategy.protocol hn).real i gate history left right)
      ((mu F n hn (gate.kind.eval (secret left) (secret right))).joint
        ((strategy.protocol hn).answer i gate history left right)) ≤ 2/(2:ℝ)^n :=
  (strategy.stochasticStrategy hn).local_coupling hn hq i gate history left right

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ TapedAugmentedStrategy(F, A, BL, BR, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → A × (BL × BR); left, right ∈ U(F, n) × U(F, n), assume 2 ≤ n; |F| = 2. Then

δ(real(strategy.shareProtocol)(i, gate, history, left, right), joint(encodingDistribution(gate.kind.eval(secret((stateEquivProd(F, n))⁻¹(left)), secret((stateEquivProd(F, n))⁻¹(right)))))(answer(strategy.shareProtocol)(i, gate, history, left, right))) ≤ 2 / 2ⁿ.
-/
theorem share_local_coupling (strategy : TapedAugmentedStrategy F A BL BR n t inputs hdim)
    (hn : 2 ≤ n) (hq : fieldCard F = 2)
    (i : ℕ) (gate : Gate F (inputs+i)) (history : Fin i → A × (BL × BR))
    (left right : U F n × U F n) :
    statisticalDistance ((strategy.shareProtocol hn).real i gate history left right)
      ((encodingDistribution hn (gate.kind.eval (secret ((stateEquivProd F n).symm left))
        (secret ((stateEquivProd F n).symm right)))).joint
        ((strategy.shareProtocol hn).answer i gate history left right)) ≤ 2/(2:ℝ)^n :=
  (strategy.stochasticStrategy hn).share_local_coupling hn hq i gate history left right

/-- One common family for every plaintext labeling, with no assumed analytic estimate or supplied conditional-independence premise. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ TapedAugmentedStrategy(F, A, BL, BR, n, t, inputs, hdim); defaultAnswer ∈ A × (BL × BR); defaultEncoding ∈ U(F, n) × U(F, n); program ∈ Program(F, inputs, T), assume 2 ≤ n; |F| = 2; program.DistinctInputs. Then

∃ G ∈ ∏_(i ∈ {0,…,T−1}) (A × (BL × BR))* → A × (BL × BR) → ℝ^(({w | w ∈ program.scope(i)} → U(F, n)) × ({w | w ∈ program.scope(i)} → U(F, n))), (∀ i, history, (∑_ab (‖ G(i, history, ab)‖_*)) ≤ √(|(BL × BR)|) · |A|) ∧ ∀ label, i, program.gateValid(label, i) → ∀ history, (∑_ab (𝔼_(xy ← LocalApproximationData.portDistribution(scope = program.scope, ((w ↦ encodingDistribution(label(w)))), i)) [|localOriginal(strategy.shareProtocol)(defaultAnswer, defaultEncoding, program, i, history, ab, (xy)₁, (xy)₂) - G(i, history, ab, (xy)₁, (xy)₂)|])) ≤ 16 · 208 · |A| · exp((-(log(2)) · n / 4)).
-/
theorem exists_local_approximations (strategy : TapedAugmentedStrategy F A BL BR n t inputs hdim)
    (hn : 2 ≤ n) (hq : fieldCard F = 2)
    (defaultAnswer : A × (BL × BR)) (defaultEncoding : U F n × U F n)
    (program : Program F inputs T) (hd : program.DistinctInputs) :
    ∃ G : (i : Fin T) → List (A × (BL × BR)) → A × (BL × BR) →
      Matrix ({w // w ∈ program.scope i} → U F n) ({w // w ∈ program.scope i} → U F n) ℝ,
      (∀ i history, (∑ ab, tableNuclearNorm (G i history ab)) ≤
        Real.sqrt (Fintype.card (BL × BR)) * Fintype.card A) ∧
      ∀ label i, program.gateValid label i → ∀ history,
        (∑ ab, (LocalApproximationData.portDistribution (scope := program.scope)
          (fun w => encodingDistribution hn (label w)) i).expect (fun xy =>
            |(strategy.shareProtocol hn).localOriginal defaultAnswer defaultEncoding
                program i history ab xy.1 xy.2 - G i history ab xy.1 xy.2|)) ≤
          16*208*Fintype.card A*Real.exp (-Real.log 2 * (n : ℝ) / 4) :=
  (strategy.stochasticStrategy hn).exists_local_approximations hn hq
    defaultAnswer defaultEncoding program hd

end TapedAugmentedStrategy

end

end CircuitCompiler.Rectangular
