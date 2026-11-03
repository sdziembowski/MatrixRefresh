import Proofs.Compiler.GateApproximation.Shortening.RectangularAugmentedProgram
import Proofs.Compiler.GateApproximation.Shortening.RectangularFractionalPhysicalGate
import Proofs.Compiler.Construction.Parameters



/-!
# The fractional conditional-tape gadget as a circuit protocol

This is the stochastic interface: finite leakage distributions may vary with all local input values and the entire outer retry tape. A concrete completion sampler will instantiate these distributions and discharge `firstLeak` exactly.
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

/-- A valid labelled output uses the accepted conditional distribution, regardless of how its plaintext equality is represented in the fiber type. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ O → U(F, (n + t)); p ∈ TableRectanglePartition(O, GL_(n + t)(F), A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(B, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); o ∈ O × O; s ∈ F; u ∈ Fiber(F, n, s), assume O ≠ ∅; 2 ≤ n; gateSecret(a, b, o) = s. Then

ambientGateAnswerDistribution(a, b, p, r, o, u) = shortenedAnswerDistribution(longAnswer(a, b, p), r, o, u).
-/
theorem ambientGateAnswerDistribution_at_label [DecidableEq O] [Nonempty O]
    (hn : 2 ≤ n) (a b : O → U F (n+t))
    (p : TableRectanglePartition O (Refresh.«GL» F (n+t)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (O × U F n) ((O × U F n) × Kernel H)) (o : O × O)
    (s : F) (hs : gateSecret a b o = s) (u : Fiber F n s) :
    ambientGateAnswerDistribution hn a b p r o u.val = shortenedAnswerDistribution (longAnswer a b p) r o u := by
  subst s
  exact ambientGateAnswerDistribution_fiber hn a b p r o u

namespace AugmentedStrategy

variable {hdim : n*n+1 = n+t}

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ AugmentedStrategy(F, A, B, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → A × B; left, right ∈ State(F, n), assume 2 ≤ n; |F| = 2. Then

δ(real(strategy.protocol)(i, gate, history, left, right), joint(μ_(gate.kind.eval(secret(left), secret(right))))(answer(strategy.protocol)(i, gate, history, left, right))) ≤ 2 / 2ⁿ.
-/
theorem local_coupling (strategy : AugmentedStrategy F A B n t inputs hdim)
    (hn : 2 ≤ n) (hq : fieldCard F = 2)
    (i : ℕ) (gate : Gate F (inputs+i)) (history : Fin i → A × B)
    (left right : State F n) :
    statisticalDistance ((strategy.protocol hn).real i gate history left right)
      ((mu F n hn (gate.kind.eval (secret left) (secret right))).joint
        ((strategy.protocol hn).answer i gate history left right)) ≤ 2/(2:ℝ)^n := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  have h := fullGate_ambient_distance hq hn
    (augmentedLeftFeature hdim gate.kind.affineConstant) (augmentedRightFeature hdim)
    (matrixPartitionDimension hdim (strategy.matrix i gate history))
    (strategy.rectangles i gate history) (augmentedOldPorts left right)
    (strategy.fallback i gate history left right) (strategy.leak i gate history left right)
    (strategy.firstLeak i gate history left right)
  have hmu := congrArg (mu F n hn) (augmented_gateSecret_eval hq hdim gate.kind left right)
  rw [hmu] at h
  exact h

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ AugmentedStrategy(F, A, B, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → A × B; left, right ∈ U(F, n) × U(F, n), assume 2 ≤ n; |F| = 2. Then

δ(real(strategy.shareProtocol)(i, gate, history, left, right), joint(encodingDistribution(gate.kind.eval(secret((stateEquivProd(F, n))⁻¹(left)), secret((stateEquivProd(F, n))⁻¹(right)))))(answer(strategy.shareProtocol)(i, gate, history, left, right))) ≤ 2 / 2ⁿ.
-/
theorem share_local_coupling (strategy : AugmentedStrategy F A B n t inputs hdim)
    (hn : 2 ≤ n) (hq : fieldCard F = 2)
    (i : ℕ) (gate : Gate F (inputs+i)) (history : Fin i → A × B)
    (left right : U F n × U F n) :
    statisticalDistance ((strategy.shareProtocol hn).real i gate history left right)
      ((encodingDistribution hn (gate.kind.eval (secret ((stateEquivProd F n).symm left))
        (secret ((stateEquivProd F n).symm right)))).joint
        ((strategy.shareProtocol hn).answer i gate history left right)) ≤ 2/(2:ℝ)^n :=
  (strategy.protocol hn).transport_local_coupling (stateEquivProd F n)
    secret (mu F n hn) _ (strategy.local_coupling hn hq) i gate history left right

/-- On the support of fixed operand labels, the protocol's common ambient answer is exactly the accepted distribution approximated by the local theorem. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ AugmentedStrategy(F, A, B, n, t, inputs, hdim); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → A × B; s₁, s₂ ∈ F; o ∈ (U(F, n) × U(F, n)) × (U(F, n) × U(F, n)); u ∈ Fiber(F, n, (s₁ · s₂ + gate.kind.affineConstant)), assume 2 ≤ n; oldLabelDistribution(s₁, s₂)(o) ≠ 0. Then

answer(strategy.shareProtocol)(i, gate, history, (((o)₁)₁, ((o)₂)₁), (((o)₁)₂, ((o)₂)₂), (u.val.L, u.val.R)) = shortenedAnswerDistribution(((old, (, v, :, Fiber, F, (, n, +, t,), (, s₁, *, s₂, +, gate.kind.affineConstant,),) ↦ augmentedLongAnswerDistribution(hdim, gate.kind.affineConstant, strategy.matrix(i, gate, history), old, v))), strategy.rectangles(i, gate, history), o, u).
-/
theorem share_answer_on_support (strategy : AugmentedStrategy F A B n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i)) (history : Fin i → A × B)
    (s₁ s₂ : F) (o : (U F n × U F n) × (U F n × U F n))
    (ho : (oldLabelDistribution hn s₁ s₂).weight o ≠ 0)
    (u : Fiber F n (s₁*s₂+gate.kind.affineConstant)) :
    (strategy.shareProtocol hn).answer i gate history
      (o.1.1,o.2.1) (o.1.2,o.2.2) (u.val.L,u.val.R) =
    shortenedAnswerDistribution (fun old (v : Fiber F (n+t) (s₁*s₂+gate.kind.affineConstant)) =>
      augmentedLongAnswerDistribution hdim gate.kind.affineConstant (strategy.matrix i gate history) old v.val)
      (strategy.rectangles i gate history) o u := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  change ambientGateAnswerDistribution hn (augmentedLeftFeature hdim gate.kind.affineConstant)
    (augmentedRightFeature hdim) (matrixPartitionDimension hdim (strategy.matrix i gate history))
    (strategy.rectangles i gate history) o u.val = _
  rw [ambientGateAnswerDistribution_at_label hn _ _ _ _ o (s₁*s₂+gate.kind.affineConstant)
    (by rw [augmented_gateSecret, oldLabelDistribution_product hn s₁ s₂ o ho]) u]
  have hk : longAnswer (s := s₁*s₂+gate.kind.affineConstant)
      (augmentedLeftFeature hdim gate.kind.affineConstant) (augmentedRightFeature hdim)
      (matrixPartitionDimension hdim (strategy.matrix i gate history)) =
    fun old (v : Fiber F (n+t) (s₁*s₂+gate.kind.affineConstant)) =>
      augmentedLongAnswerDistribution hdim gate.kind.affineConstant (strategy.matrix i gate history) old v.val := by
    funext old v
    exact augmented_longAnswer hdim gate.kind.affineConstant (strategy.matrix i gate history) old v
  rw [hk]

/-- The chronological real circuit is within the sum of its per-gate retry errors of the fresh-output canonical execution, retaining all wire states. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ AugmentedStrategy(F, A, B, n, t, inputs, hdim); input ∈ {0,…,inputs-1} → F; program ∈ Program(F, inputs, T), assume 2 ≤ n; |F| = 2. Then

δ(execute(realRunner(strategy.protocol)(program))(independentDistribution(((i ↦ μᵢₙₚᵤₜ₍ᵢ₎)))), runner.execute(canonicalRunner(strategy.protocol)(mu(F, n), input, program))(independentDistribution(((i ↦ μᵢₙₚᵤₜ₍ᵢ₎))))) ≤ T · (2 / 2ⁿ).
-/
theorem program_coupling (strategy : AugmentedStrategy F A B n t inputs hdim)
    (hn : 2 ≤ n) (hq : fieldCard F = 2) (input : Fin inputs → F) (program : Program F inputs T) :
    statisticalDistance
      (((strategy.protocol hn).realRunner program).execute
        (independentDistribution (fun i => mu F n hn (input i))))
      (((strategy.protocol hn).canonicalRunner (mu F n hn) input program).runner.execute
        (independentDistribution (fun i => mu F n hn (input i)))) ≤ (T : ℝ)*(2/(2:ℝ)^n) :=
  (strategy.protocol hn).real_canonical_distance secret (mu F n hn) (mu_supports n hn)
    _ (strategy.local_coupling hn hq) input program

end AugmentedStrategy

end

end CircuitCompiler.Rectangular.Fractional
