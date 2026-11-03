import Proofs.Compiler.GateApproximation.Shortening.RectangularFractionalAugmentedApproximation
import Proofs.Compiler.GateApproximation.Shortening.RectangularFractionalProgram
import Proofs.Compiler.GateApproximation.Shortening.RectangularScopeTables



/-!
# Accepted rectangular-gate approximations on executable circuit scopes

The physical answer identity on consistent tuples provides the required change of representation: all analytic approximation and norm estimates have already been proved for the augmented shared-matrix experiment and rectangular shortening.
-/
set_option autoImplicit false

set_option maxHeartbeats 2200000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.Rectangular.Fractional

open Refresh MatrixRefresh TableAnalysis Shortening Composition Composition.TopologicalExecution

noncomputable section

variable {F A B : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype A] [Fintype B] {n t inputs T : ℕ}

variable [Nonempty (U F n)] [Nonempty (U F (n+t))] [Nonempty (FullRank F n (n+t))]

/-- Extend the accepted-fiber estimate to any normalized ambient answer distribution that agrees with the physical accepted distribution on valid encodings. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n + 1)(F), A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(B, GateSide(F, n, n), (GateSide(F, n, n) × Kernel(H))); K ∈ (U(F, n) × U(F, n)) → (U(F, n) × U(F, n)) → (U(F, n) × U(F, n)) → 𝒟((A × B)), assume |F| = 2; 2 ≤ n; n · n + 1 = n + t; ∀ s₁, s₂, o, (oldLabelDistribution(s₁, s₂)(o) ≠ 0) ⇒ ∀ u ∈ Fiber(F, n, (s₁ · s₂ + c)), K((((o)₁)₁, ((o)₂)₁), (((o)₁)₂, ((o)₂)₂), (u.val.L, u.val.R)) = shortenedAnswerDistribution(((o, (, v, :, Fiber, F, (, n, +, t,), (, s₁, *, s₂, +, c,),) ↦ augmentedLongAnswerDistribution(c, p, o, v))), r, o, u). Then

∃ G ∈ A × B → ℝ^(GateSide(F, n, n) × GateSide(F, n, n)), (∑_ab (‖ G(ab)‖_*)) ≤ √(|B|) · |A| ∧ ∀ s₁, s₂ ∈ F, 𝔼_(op ← (oldLabelDistribution(s₁, s₂) ⊗ μ_(s₁ · s₂ + c))) [∑_ab (|K(((((op)₁)₁)₁, (((op)₁)₂)₁), ((((op)₁)₁)₂, (((op)₁)₂)₂), (op.2.L, op.2.R))(ab) - G(ab, (((op)₁)₁, op.2.L), (((op)₁)₂, op.2.R))|)] ≤ 16 · 208 · |A| · exp((-(log(2)) · n / 4)).
-/
theorem augmented_ambient_local_approximation (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (hdim : n*n+1 = n+t) (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (GateSide F n n) ((GateSide F n n) × Kernel H))
    (K : (U F n × U F n) → (U F n × U F n) → (U F n × U F n) → FiniteDistribution (A × B))
    (hK : ∀ s₁ s₂ o, (oldLabelDistribution hn s₁ s₂).weight o ≠ 0 →
      ∀ u : Fiber F n (s₁*s₂+c),
      K (o.1.1,o.2.1) (o.1.2,o.2.2) (u.val.L,u.val.R) =
        shortenedAnswerDistribution
          (fun o (v : Fiber F (n+t) (s₁*s₂+c)) => augmentedLongAnswerDistribution hdim c p o v.val)
          r o u) :
    ∃ G : A × B → Matrix (GateSide F n n) (GateSide F n n) ℝ,
      (∑ ab, tableNuclearNorm (G ab)) ≤ Real.sqrt (Fintype.card B) * Fintype.card A ∧
      ∀ s₁ s₂ : F,
        ((oldLabelDistribution hn s₁ s₂).prod (mu F n hn (s₁*s₂+c))).expect
          (fun op => ∑ ab,
            |(K (op.1.1.1,op.1.2.1) (op.1.1.2,op.1.2.2) (op.2.L,op.2.R)).weight ab -
              G ab (op.1.1,op.2.L) (op.1.2,op.2.R)|) ≤
          16*208*Fintype.card A*Real.exp (-Real.log 2 * (n : ℝ) / 4) := by
  obtain ⟨G,hG,herr⟩ := augmented_shortened_local_approximation hq hn hdim c p r
  refine ⟨G,hG,?_⟩
  intro s₁ s₂
  letI := encoding_fiber_nonempty hn (s₁*s₂+c)
  have he :
      ((oldLabelDistribution hn s₁ s₂).prod (mu F n hn (s₁*s₂+c))).expect
        (fun op => ∑ ab,
          |(K (op.1.1.1,op.1.2.1) (op.1.1.2,op.1.2.2) (op.2.L,op.2.R)).weight ab -
            G ab (op.1.1,op.2.L) (op.1.2,op.2.R)|) =
      ((oldLabelDistribution hn s₁ s₂).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (s₁*s₂+c)))).expect
        (fun op => ∑ ab, |(shortenedAnswerDistribution
          (fun o (v : Fiber F (n+t) (s₁*s₂+c)) => augmentedLongAnswerDistribution hdim c p o v.val)
          r op.1 op.2).weight ab -
            G ab (op.1.1,op.2.val.L) (op.1.2,op.2.val.R)|) := by
    simp only [expect_prod,mu,expect_map]
    apply Finset.sum_congr rfl
    intro o _
    by_cases ho : (oldLabelDistribution hn s₁ s₂).weight o = 0
    · simp only [ho,zero_mul]
    · congr 1
      apply congrArg (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (s₁*s₂+c))).expect
      funext u
      rw [hK s₁ s₂ o ho u]
  rw [he]
  exact herr s₁ s₂

/-- The common augmented-gate tables reindex to the actual circuit scopes. The hypotheses identify the implementation's normalized answer distribution on valid ports and its plaintext gate operation; no approximation bound is assumed. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For protocol ∈ GateProtocol(F, (U(F, n) × U(F, n)), (A × B), inputs); matrix ∈ ∏_(i ∈ ℕ) Gate(F, (inputs + i)) → ({0,…,i-1} → A × B) → TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n + 1)(F), A); rectangles ∈ ∏_(i ∈ ℕ) Gate(F, (inputs + i)) → ({0,…,i-1} → A × B) → A → ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(B, GateSide(F, n, n), (GateSide(F, n, n) × Kernel(H))); constant ∈ GateKind(F) → F; defaultAnswer ∈ A × B; defaultEncoding ∈ U(F, n) × U(F, n); program ∈ Program(F, inputs, T), assume |F| = 2; 2 ≤ n; n · n + 1 = n + t; ∀ kind, s₁, s₂, kind.eval(s₁, s₂) = s₁ · s₂ + constant(kind); ∀ i, gate, history, s₁, s₂, o, (oldLabelDistribution(s₁, s₂)(o) ≠ 0) ⇒ ∀ u ∈ Fiber(F, n, (s₁ · s₂ + constant(gate.kind))), protocol.answer(i, gate, history, (((o)₁)₁, ((o)₂)₁), (((o)₁)₂, ((o)₂)₂), (u.val.L, u.val.R)) = shortenedAnswerDistribution(((o, (, v, :, Fiber, F, (, n, +, t,), (, s₁, *, s₂, +, constant, gate.kind,),) ↦ augmentedLongAnswerDistribution(constant(gate.kind), matrix(i, gate, history), o, v))), rectangles(i, gate, history), o, u); program.DistinctInputs. Then

∃ G ∈ ∏_(i ∈ {0,…,T−1}) (A × B)* → A × B → ℝ^(({w | w ∈ program.scope(i)} → U(F, n)) × ({w | w ∈ program.scope(i)} → U(F, n))), (∀ i, history, (∑_ab (‖ G(i, history, ab)‖_*)) ≤ √(|B|) · |A|) ∧ ∀ label, i, program.gateValid(label, i) → ∀ history, (∑_ab (𝔼_(xy ← LocalApproximationData.portDistribution(scope = program.scope, ((w ↦ encodingDistribution(label(w)))), i)) [|protocol.localOriginal(defaultAnswer, defaultEncoding, program, i, history, ab, (xy)₁, (xy)₂) - G(i, history, ab, (xy)₁, (xy)₂)|])) ≤ 16 · 208 · |A| · exp((-(log(2)) · n / 4)).
-/
theorem augmented_scope_approximations
    (protocol : GateProtocol F (U F n × U F n) (A × B) inputs)
    (hq : fieldCard F = 2) (hn : 2 ≤ n) (hdim : n*n+1 = n+t)
    (matrix : (i : ℕ) → Gate F (inputs+i) → (Fin i → A × B) →
      TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A)
    (rectangles : (i : ℕ) → Gate F (inputs+i) → (Fin i → A × B) →
      A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
        (GateSide F n n) ((GateSide F n n) × Kernel H))
    (constant : GateKind F → F)
    (hoperation : ∀ kind s₁ s₂, kind.eval s₁ s₂ = s₁*s₂+constant kind)
    (hanswer : ∀ i gate history s₁ s₂ o,
      (oldLabelDistribution hn s₁ s₂).weight o ≠ 0 →
      ∀ u : Fiber F n (s₁*s₂+constant gate.kind),
      protocol.answer i gate history (o.1.1,o.2.1) (o.1.2,o.2.2) (u.val.L,u.val.R) =
        shortenedAnswerDistribution
          (fun o (v : Fiber F (n+t) (s₁*s₂+constant gate.kind)) =>
            augmentedLongAnswerDistribution hdim (constant gate.kind) (matrix i gate history) o v.val)
          (rectangles i gate history) o u)
    (defaultAnswer : A × B) (defaultEncoding : U F n × U F n)
    (program : Program F inputs T) (hd : program.DistinctInputs) :
    ∃ G : (i : Fin T) → List (A × B) → A × B →
      Matrix ({w // w ∈ program.scope i} → U F n) ({w // w ∈ program.scope i} → U F n) ℝ,
      (∀ i history, (∑ ab, tableNuclearNorm (G i history ab)) ≤
        Real.sqrt (Fintype.card B) * Fintype.card A) ∧
      ∀ label i, program.gateValid label i → ∀ history,
        (∑ ab, (LocalApproximationData.portDistribution (scope := program.scope)
          (fun w => encodingDistribution hn (label w)) i).expect (fun xy =>
            |protocol.localOriginal defaultAnswer defaultEncoding program i history ab xy.1 xy.2 -
              G i history ab xy.1 xy.2|)) ≤
          16*208*Fintype.card A*Real.exp (-Real.log 2 * (n : ℝ) / 4) := by
  classical
  let o := fun i => protocol.occurrence defaultAnswer program i
  have htables := fun i history => augmented_ambient_local_approximation hq hn hdim
    (constant (o i).gate.kind)
    (matrix (o i).time (o i).gate (GateProtocol.completeHistory defaultAnswer history (o i).time))
    (rectangles (o i).time (o i).gate (GateProtocol.completeHistory defaultAnswer history (o i).time))
    (protocol.answer (o i).time (o i).gate (GateProtocol.completeHistory defaultAnswer history (o i).time))
    (hanswer (o i).time (o i).gate (GateProtocol.completeHistory defaultAnswer history (o i).time))
  choose tables hnuclear herror using htables
  let G := fun i history ab =>
    reindexTable (tables i history ab) ((o i).portsEquiv hd) ((o i).portsEquiv hd)
  refine ⟨G,?_,?_⟩
  · intro i history
    simpa only [G,reindexTable_tableNuclearNorm] using hnuclear i history
  · intro label i hv history
    have hl : label (o i).output =
        label (o i).left * label (o i).right + constant (o i).gate.kind :=
      ((o i).valid_eq label).mp hv |>.trans (hoperation _ _ _)
    change (∑ ab, (LocalApproximationData.portDistribution (scope := program.scope)
      (fun w => encodingDistribution hn (label w)) i).expect (fun xy =>
        |protocol.localOriginal defaultAnswer defaultEncoding program i history ab xy.1 xy.2 -
          reindexTable (tables i history ab) ((o i).portsEquiv hd) ((o i).portsEquiv hd)
            xy.1 xy.2|)) ≤ _
    rw [scope_error_eq_port_error protocol defaultAnswer defaultEncoding program hd i (o i)
      history hn label (tables i history),hl]
    exact herror i history (label (o i).left) (label (o i).right)

namespace AugmentedStrategy

omit [Nonempty (U F n)] [Nonempty (U F (n+t))] [Nonempty (FullRank F n (n+t))] in
/-- The actual augmented rectangular implementation supplies the common local approximation family on every executable gate scope. Every analytic and physical-answer premise has been discharged. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For strategy ∈ AugmentedStrategy(F, A, B, n, t, inputs); defaultAnswer ∈ A × B; defaultEncoding ∈ U(F, n) × U(F, n); program ∈ Program(F, inputs, T), assume n · n + 1 = n + t; 2 ≤ n; |F| = 2; program.DistinctInputs. Then

∃ G ∈ ∏_(i ∈ {0,…,T−1}) (A × B)* → A × B → ℝ^(({w | w ∈ program.scope(i)} → U(F, n)) × ({w | w ∈ program.scope(i)} → U(F, n))), (∀ i, history, (∑_ab (‖ G(i, history, ab)‖_*)) ≤ √(|B|) · |A|) ∧ ∀ label, i, program.gateValid(label, i) → ∀ history, (∑_ab (𝔼_(xy ← LocalApproximationData.portDistribution(scope = program.scope, ((w ↦ encodingDistribution(label(w)))), i)) [|localOriginal(strategy.shareProtocol)(defaultAnswer, defaultEncoding, program, i, history, ab, (xy)₁, (xy)₂) - G(i, history, ab, (xy)₁, (xy)₂)|])) ≤ 16 · 208 · |A| · exp((-(log(2)) · n / 4)).
-/
theorem exists_local_approximations {hdim : n*n+1 = n+t}
    (strategy : AugmentedStrategy F A B n t inputs hdim)
    (hn : 2 ≤ n) (hq : fieldCard F = 2)
    (defaultAnswer : A × B) (defaultEncoding : U F n × U F n)
    (program : Program F inputs T) (hd : program.DistinctInputs) :
    ∃ G : (i : Fin T) → List (A × B) → A × B →
      Matrix ({w // w ∈ program.scope i} → U F n) ({w // w ∈ program.scope i} → U F n) ℝ,
      (∀ i history, (∑ ab, tableNuclearNorm (G i history ab)) ≤
        Real.sqrt (Fintype.card B) * Fintype.card A) ∧
      ∀ label i, program.gateValid label i → ∀ history,
        (∑ ab, (LocalApproximationData.portDistribution (scope := program.scope)
          (fun w => encodingDistribution hn (label w)) i).expect (fun xy =>
            |(strategy.shareProtocol hn).localOriginal defaultAnswer defaultEncoding
                program i history ab xy.1 xy.2 - G i history ab xy.1 xy.2|)) ≤
          16*208*Fintype.card A*Real.exp (-Real.log 2 * (n : ℝ) / 4) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0,by omega⟩⟩
  letI : Nonempty (U F (n+t)) := ⟨unitShare ⟨0,by omega⟩⟩
  exact augmented_scope_approximations (strategy.shareProtocol hn) hq hn hdim
    strategy.matrix strategy.rectangles GateKind.affineConstant
    (gate_eval_product_offset_binary hq) (strategy.share_answer_on_support hn)
    defaultAnswer defaultEncoding program hd

end AugmentedStrategy

end

end CircuitCompiler.Rectangular.Fractional
