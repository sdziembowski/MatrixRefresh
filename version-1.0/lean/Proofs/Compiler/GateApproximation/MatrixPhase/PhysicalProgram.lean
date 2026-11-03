import Proofs.Compiler.GateApproximation.MatrixPhase.FullGate
import Proofs.Compiler.LocalComparisons.Framework.ProgramExecution
import Proofs.Compiler.Construction.Parameters



/-!
# The physical multiplication/affine-shortening compiler as a topological runner
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler

open Refresh Shortening TableAnalysis Composition Composition.TopologicalExecution

variable {F Alpha Beta : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype Alpha] [Fintype Beta] {n t inputs T : ℕ}

/- Mathematical definition (normal notation): In the expression c+ε ab, the coefficient is ε = 1 for multiplication and ε = -1 for complemented multiplication. -/
def GateKind.affineSign : GateKind F → F
  | .product => 1
  | .complement _ => -1

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For kind ∈ GateKind(F), we have

kind.affineSign ≠ 0.
-/
theorem GateKind.affineSign_ne_zero (kind : GateKind F) : kind.affineSign ≠ 0 := by
  cases kind <;> simp [GateKind.affineSign]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For kind ∈ GateKind(F); left, right ∈ F, we have

kind.affineConstant + kind.affineSign · (left · right) = kind.eval(left, right).
-/
theorem GateKind.eval_affine (kind : GateKind F) (left right : F) :
    kind.affineConstant + kind.affineSign * (left * right) = kind.eval left right := by
  cases kind <;> simp [GateKind.affineConstant, GateKind.affineSign, GateKind.eval, sub_eq_add_neg]

/-- The strategy chooses each matrix-phase rectangle partition from the previous transcript. After erasure, shortening leakage and the correct fallback can inspect the two operands, long data, and earlier matrix answer. -/
/- Mathematical definition (normal notation): A physical strategy chooses the matrix-phase leakage partition from the previous history. It supplies a shortening-answer distribution and a correctly typed fallback depending on the operand encodings, long data, and matrix-phase answer. The second phase receives no erased refresh matrix. -/
structure PhysicalStrategy (F Alpha Beta : Type*) [Field F] [Fintype F] [DecidableEq F]
    [Fintype Alpha] [Fintype Beta] (n t inputs : ℕ) where
  matrix : (i : ℕ) → Gate F (inputs + i) → (Fin i → Alpha × Beta) →
    TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) Alpha
  leak : (i : ℕ) → Gate F (inputs + i) → (Fin i → Alpha × Beta) →
    (left right : State F n) → Auxiliary F (n + t) (secret left * secret right) → Alpha → FiniteDistribution Beta
  fallback : (i : ℕ) → (gate : Gate F (inputs + i)) → (Fin i → Alpha × Beta) →
    (left right : State F n) → Auxiliary F (n + t) (secret left * secret right) → Alpha →
      FiniteDistribution (Fiber F n (gate.kind.affineConstant + gate.kind.affineSign * (secret left * secret right)) × Beta)

namespace PhysicalStrategy

/-- This protocol performs the actual tensor/shared-matrix/shortening gate; its canonical answer is the exact ambient conditional distribution. -/
/- Mathematical definition (normal notation): Instantiate the actual tensor-refresh/shortening transition from the physical strategy. Pair it with the normalized canonical answer distribution conditioned on the operand and proposed output encodings. -/
noncomputable def protocol (strategy : PhysicalStrategy F Alpha Beta n t inputs)
    (hn : 2 ≤ n) (hdim : n * n = n + t) : GateProtocol F (State F n) (Alpha × Beta) inputs where
  real i gate history left right :=
    (fullGateExecution hdim gate.kind.affineConstant gate.kind.affineSign
      (strategy.matrix i gate history) left right (strategy.leak i gate history left right)
      (strategy.fallback i gate history left right)).map (fun pair => (pair.1.val, pair.2))
  answer i gate history left right output :=
    ambientGateAnswerDistribution hn hdim gate.kind.affineConstant gate.kind.affineSign gate.kind.affineSign_ne_zero
      (strategy.matrix i gate history) left right (strategy.leak i gate history left right) output

/-- The physical protocol supplies the local hypothesis of the actual Program runner with the explicit shortening/virtual-zero error. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ PhysicalStrategy(F, Alpha, Beta, n, t, inputs); i ∈ ℕ; gate ∈ Gate(F, (inputs + i)); history ∈ {0,…,i-1} → Alpha × Beta; left, right ∈ State(F, n), assume 2 ≤ n; n · n = n + t. Then

δ(real(strategy.protocol)(i, gate, history, left, right), joint(μ_(gate.kind.eval(secret(left), secret(right))))(answer(strategy.protocol)(i, gate, history, left, right))) ≤ 1 / (|F|)^(n + t − 1) + (|F| + 1) / (|F|)ⁿ.
-/
theorem local_coupling (strategy : PhysicalStrategy F Alpha Beta n t inputs)
    (hn : 2 ≤ n) (hdim : n * n = n + t)
    (i : ℕ) (gate : Gate F (inputs + i)) (history : Fin i → Alpha × Beta)
    (left right : State F n) :
    statisticalDistance ((strategy.protocol hn hdim).real i gate history left right)
      ((mu F n hn (gate.kind.eval (secret left) (secret right))).joint
        ((strategy.protocol hn hdim).answer i gate history left right)) ≤
      1 / (fieldCard F : ℝ) ^ (n + t - 1) + ((fieldCard F : ℝ) + 1) / (fieldCard F : ℝ) ^ n := by
  have h := fullGate_ambient_distance hn hdim gate.kind.affineConstant gate.kind.affineSign
    gate.kind.affineSign_ne_zero (strategy.matrix i gate history) left right
    (strategy.leak i gate history left right) (strategy.fallback i gate history left right)
  rw [fullGateCanonical_ambient] at h
  have hlabel := congrArg (mu F n hn) (gate.kind.eval_affine (secret left) (secret right))
  rw [hlabel] at h
  exact h

/-- A complete real compiled circuit is within `T·τ` of the canonical fresh-output execution, including the full retained wire state and history. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ PhysicalStrategy(F, Alpha, Beta, n, t, inputs); input ∈ {0,…,inputs-1} → F; program ∈ Program(F, inputs, T), assume 2 ≤ n; n · n = n + t. Then

δ(execute(realRunner(strategy.protocol)(program))(independentDistribution(((i ↦ μᵢₙₚᵤₜ₍ᵢ₎)))), runner.execute(canonicalRunner(strategy.protocol)(mu(F, n), input, program))(independentDistribution(((i ↦ μᵢₙₚᵤₜ₍ᵢ₎))))) ≤ T · (1 / (|F|)^(n + t − 1) + (|F| + 1) / (|F|)ⁿ).
-/
theorem program_coupling (strategy : PhysicalStrategy F Alpha Beta n t inputs)
    (hn : 2 ≤ n) (hdim : n * n = n + t)
    (input : Fin inputs → F) (program : Program F inputs T) :
    statisticalDistance
      (((strategy.protocol hn hdim).realRunner program).execute
        (independentDistribution (fun i => mu F n hn (input i))))
      (((strategy.protocol hn hdim).canonicalRunner (mu F n hn) input program).runner.execute
        (independentDistribution (fun i => mu F n hn (input i)))) ≤
      (T : ℝ) * (1 / (fieldCard F : ℝ) ^ (n + t - 1) + ((fieldCard F : ℝ) + 1) / (fieldCard F : ℝ) ^ n) := by
  exact (strategy.protocol hn hdim).real_canonical_distance secret (mu F n hn)
    (mu_supports n hn) _ (strategy.local_coupling hn hdim) input program

end PhysicalStrategy

end CircuitCompiler
