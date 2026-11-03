import Proofs.Compiler.GateApproximation.MatrixPhase.PhysicalShares
import Proofs.Compiler.GateApproximation.Shortening.RectangularAugmentedApproximation
import Proofs.Compiler.GateApproximation.Shortening.RectangularPhysicalGate
import Proofs.Compiler.Construction.Parameters



/-!
# The augmented rectangular gadget as an executable circuit protocol

A strategy specifies the actual shared-matrix leakage and a finite observation of the complete rectangular retry tape. On the first successful attempt its shortening answer must have the stated rectangle form. The proof does not restrict the observations on the rare branches that retry.
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

omit [Fintype O] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m, k ∈ ℕ; a, b ∈ O → U(F, m); p ∈ TableRectanglePartition(O, GLₘ(F), A); x, y ∈ O; u ∈ State(F, k), assume m = k. Then

answerDistribution(featureDimension(a), featureDimension(b), matrixPartitionDimension(p), x, y, u) = answerDistribution(a, b, p, x, y, (stateDimensionEquiv)⁻¹(u)).
-/
theorem answerDistribution_dimension {m k : ℕ} (h : m = k) (a b : O → U F m)
    (p : TableRectanglePartition O (Refresh.«GL» F m) A) (x y : O) (u : State F k) :
    answerDistribution (featureDimension h a) (featureDimension h b)
      (matrixPartitionDimension h p) x y u =
    answerDistribution a b p x y ((stateDimensionEquiv h).symm u) := by
  subst k
  rfl

omit [Fintype F] [DecidableEq F] [Fintype O] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m, k ∈ ℕ; a, b ∈ O → U(F, m); x, y ∈ O, assume m = k. Then

(featureDimension(a, x) · featureDimension(b, y)) = (a(x) · b(y)).
-/
theorem featureDimension_dot {m k : ℕ} (h : m = k) (a b : O → U F m) (x y : O) :
    dot (featureDimension h a x).val (featureDimension h b y).val =
      dot (a x).val (b y).val := by
  subst k
  rfl

variable {n t inputs T : ℕ}

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c ∈ F; o ∈ (U(F, n) × U(F, n)) × (U(F, n) × U(F, n)), assume n · n + 1 = n + t. Then

gateSecret(augmentedLeftFeature(c), augmentedRightFeature, o) = (((o)₁)₁ · ((o)₂)₁) · (((o)₁)₂ · ((o)₂)₂) + c.
-/
theorem augmented_gateSecret (hdim : n*n+1 = n+t) (c : F)
    (o : (U F n × U F n) × (U F n × U F n)) :
    gateSecret (augmentedLeftFeature hdim c) (augmentedRightFeature hdim) o =
      dot o.1.1.val o.2.1.val * dot o.1.2.val o.2.2.val + c := by
  exact (featureDimension_dot hdim (augmentedShare c) (augmentedShare 1) o.1 o.2).trans
    (augmentedShare_dot c o.1 o.2)

/-- The standard multiplication/complement basis becomes product plus its public constant over a binary field. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For kind ∈ GateKind(F); x, y ∈ F, assume |F| = 2. Then

kind.eval(x, y) = x · y + kind.affineConstant.
-/
theorem gate_eval_product_offset_binary (hq : fieldCard F = 2) (kind : GateKind F) (x y : F) :
    kind.eval x y = x*y+kind.affineConstant := by
  have h := kind.eval_affine x y
  rw [binary_nonzero_eq_one hq kind.affineSign kind.affineSign_ne_zero, one_mul] at h
  simpa only [add_comm] using h.symm

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For kind ∈ GateKind(F); left, right ∈ State(F, n), assume |F| = 2; n · n + 1 = n + t. Then

gateSecret(augmentedLeftFeature(kind.affineConstant), augmentedRightFeature, augmentedOldPorts(left, right)) = kind.eval(secret(left), secret(right)).
-/
theorem augmented_gateSecret_eval (hq : fieldCard F = 2) (hdim : n*n+1 = n+t)
    (kind : GateKind F) (left right : State F n) :
    gateSecret (augmentedLeftFeature hdim kind.affineConstant) (augmentedRightFeature hdim)
      (augmentedOldPorts left right) = kind.eval (secret left) (secret right) := by
  rw [augmented_gateSecret]
  have h := kind.eval_affine (secret left) (secret right)
  rw [binary_nonzero_eq_one hq kind.affineSign kind.affineSign_ne_zero, one_mul] at h
  simpa only [augmentedOldPorts, secret, stateLeftShare, stateRightShare, add_comm] using h

/-- Changing only the long dimension notation leaves the conditional matrix answer exactly equal to the distribution used by the local approximation theorem. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n + 1)(F), A); o ∈ (U(F, n) × U(F, n)) × (U(F, n) × U(F, n)); s ∈ F; u ∈ Fiber(F, (n + t), s), assume n · n + 1 = n + t. Then

longAnswer(augmentedLeftFeature(c), augmentedRightFeature, matrixPartitionDimension(p), o, u) = augmentedLongAnswerDistribution(c, p, o, u).
-/
theorem augmented_longAnswer (hdim : n*n+1 = n+t) (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A)
    (o : (U F n × U F n) × (U F n × U F n)) {s : F} (u : Fiber F (n+t) s) :
    longAnswer (augmentedLeftFeature hdim c) (augmentedRightFeature hdim)
      (matrixPartitionDimension hdim p) o u = augmentedLongAnswerDistribution hdim c p o u.val :=
  answerDistribution_dimension hdim (augmentedShare c) (augmentedShare 1) p o.1 o.2 u.val

/-- A valid labelled output uses the accepted conditional distribution, regardless of how its plaintext equality is represented in the fiber type. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ O → U(F, (n + t)); p ∈ TableRectanglePartition(O, GL_(n + t)(F), A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) RectanglePartition(B, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); o ∈ O × O; s ∈ F; u ∈ Fiber(F, n, s), assume O ≠ ∅; 2 ≤ n; gateSecret(a, b, o) = s. Then

ambientGateAnswerDistribution(a, b, p, r, o, u) = shortenedAnswerDistribution(longAnswer(a, b, p), r, o, u).
-/
theorem ambientGateAnswerDistribution_at_label [DecidableEq O] [Nonempty O]
    (hn : 2 ≤ n) (a b : O → U F (n+t))
    (p : TableRectanglePartition O (Refresh.«GL» F (n+t)) A)
    (r : A → (H : FullRank F n (n+t)) → RectanglePartition B
      (O × U F n) ((O × U F n) × Kernel H)) (o : O × O)
    (s : F) (hs : gateSecret a b o = s) (u : Fiber F n s) :
    ambientGateAnswerDistribution hn a b p r o u.val = shortenedAnswerDistribution (longAnswer a b p) r o u := by
  subst s
  exact ambientGateAnswerDistribution_fiber hn a b p r o u

/-- Adaptive choices between gates, and actual observations within each gate. `firstLeak` is the concrete first-success rectangle condition of the model. -/
/- Mathematical definition (normal notation): An adaptive augmented-gadget strategy specifies, for each gate and prior answer history: a matrix-phase leakage partition, a shortening-phase rectangle family chosen after the matrix answer, a fallback encoding of the correct output value, and a leakage observation of the full shortening tape. On a successful first attempt, that observation must agree with the corresponding rectangle answer. The shortening rectangles and tape observations are deterministic. The long and short dimensions obey n²+1 = n+t. -/
structure AugmentedStrategy (F A B : Type*) [Field F] [Fintype F] [DecidableEq F]
    [Fintype A] [Fintype B] (n t inputs : ℕ) (hdim : n*n+1 = n+t) where
  matrix : (i : ℕ) → Gate F (inputs+i) → (Fin i → A × B) →
    TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A
  rectangles : (i : ℕ) → Gate F (inputs+i) → (Fin i → A × B) →
    A → (H : FullRank F n (n+t)) → RectanglePartition B
      (GateSide F n n) ((GateSide F n n) × Kernel H)
  fallback : (i : ℕ) → (gate : Gate F (inputs+i)) → (Fin i → A × B) →
    (left right : State F n) →
    Fiber F n (gateSecret (augmentedLeftFeature hdim gate.kind.affineConstant)
      (augmentedRightFeature hdim) (augmentedOldPorts left right))
  leak : (i : ℕ) → (gate : Gate F (inputs+i)) → (Fin i → A × B) →
    (left right : State F n) →
    (x : Fiber F (n+t) (gateSecret (augmentedLeftFeature hdim gate.kind.affineConstant)
      (augmentedRightFeature hdim) (augmentedOldPorts left right))) →
    A → FullTape (n := n) x.val.L → B
  firstLeak : ∀ i gate history left right x α (z : Success (n := n) x.val.L x.val.R),
    leak i gate history left right x α ⟨0,(PUnit.unit,z.val)⟩ =
      rectangleRecordAnswer (rectangles i gate history) (augmentedOldPorts left right)
        (successfulJointEquiv _ ⟨x,z⟩) α

namespace AugmentedStrategy

variable {hdim : n*n+1 = n+t}

/-- The actual augmented matrix phase followed by all rectangular retries. -/
/- Mathematical definition (normal notation): Compile each source gate into its augmented tensor matrix phase followed by the rectangular shortening retry procedure. The real transition returns the resulting short encoding and complete leakage answer; the associated canonical conditional answer distribution is obtained from the same fixed gate, history, operand encodings, and proposed output encoding. -/
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

/-- The same real implementation on the paired-share wire carrier. -/
/-
Mathematical definition (normal notation): For strategy ∈ AugmentedStrategy(F, A, B, n, t, inputs, hdim), assume 2 ≤ n. define

shareProtocol(strategy) := transport(strategy.protocol)(stateEquivProd(F, n)).
-/
def shareProtocol (strategy : AugmentedStrategy F A B n t inputs hdim) (hn : 2 ≤ n) :
    GateProtocol F (U F n × U F n) (A × B) inputs :=
  (strategy.protocol hn).transport (stateEquivProd F n)

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

end CircuitCompiler.Rectangular
