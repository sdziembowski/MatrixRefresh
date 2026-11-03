import Proofs.Compiler.LocalComparisons.NetworkInterface
import Proofs.Compiler.GateApproximation.Interfaces.Gadget.Interface
import Proofs.Compiler.GateApproximation.Shortening.RectangularFractionalScope



/-!
# Concrete local estimates on executable circuit scopes

The chosen factors are merely reindexed along the proved three-port bijection. The original probability is the actual protocol's normalized conditional answer, including its extension to inconsistent encodings.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical

namespace CircuitCompiler.GadgetApproximation

open Refresh MatrixRefresh TableAnalysis RefreshAnalysis

open AveragedEnergyComparison ShorteningTransport Shortening Rectangular

open Composition Composition.TopologicalExecution

noncomputable section

variable {F A B : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype A] [Fintype B] {n t inputs T : ℕ}

variable [Nonempty (U F n)] [Nonempty (U F (n+t))]
  [Nonempty (FullRank F n (n+t))]

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n + 1)(F), A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(B, GateSide(F, n, n), (GateSide(F, n, n) × Kernel(H))); K ∈ (U(F, n) × U(F, n)) → (U(F, n) × U(F, n)) → (U(F, n) × U(F, n)) → 𝒟((A × B)); s₁, s₂ ∈ F; z ∈ A × B; β ∈ ℝ, assume |F| = 2; 2 ≤ n; n · n + 1 = n + t; ∀ s₁, s₂, o, (oldLabelDistribution(s₁, s₂)(o) ≠ 0) ⇒ ∀ u ∈ Fiber(F, n, (s₁ · s₂ + c)), K((((o)₁)₁, ((o)₂)₁), (((o)₁)₂, ((o)₂)₂), (u.val.L, u.val.R)) = Fractional.shortenedAnswerDistribution(((o, (, v, :, Fiber, F, (, n, +, t,), (, s₁, *, s₂, +, c,), ) ↦ augmentedLongAnswerDistribution(c, p, o, v))), r, o, u); 0 < β; β ≤ 1; 1 ≤ |(U(F, n) × U(F, n))| · β³. Then

‖ ((xy ↦ K(((((xy)₁)₁)₁, (((xy)₂)₁)₁), ((((xy)₁)₁)₂, (((xy)₂)₁)₂), (((xy)₁)₂, ((xy)₂)₂))(z) - shortenedApproximation(c, p, r, z, β, (xy)₁, (xy)₂)))‖_(2,independentLabelledPortDistribution(s₁, s₂, (s₁ · s₂ + c))) ≤ 396 · β^(1 / 3).
-/
theorem augmented_ambient_rms_error (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (hdim : n*n+1 = n+t) (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (GateSide F n n) ((GateSide F n n) × Kernel H))
    (K : (U F n × U F n) → (U F n × U F n) → (U F n × U F n) → FiniteDistribution (A × B))
    (hK : ∀ s₁ s₂ o, (oldLabelDistribution hn s₁ s₂).weight o ≠ 0 →
      ∀ u : Fiber F n (s₁*s₂+c),
      K (o.1.1,o.2.1) (o.1.2,o.2.2) (u.val.L,u.val.R) =
        Fractional.shortenedAnswerDistribution
          (fun o (v : Fiber F (n+t) (s₁*s₂+c)) => augmentedLongAnswerDistribution hdim c p o v.val)
          r o u)
    (s₁ s₂ : F) (z : A × B) (β : ℝ) (hβ : 0 < β) (hβone : β ≤ 1)
    (hthreshold : 1 ≤ (Fintype.card (U F n × U F n) : ℝ) * β ^ 3) :
    rms (independentLabelledPortDistribution hn hn s₁ s₂ (s₁*s₂+c))
      (fun xy => (K (xy.1.1.1,xy.2.1.1) (xy.1.1.2,xy.2.1.2) (xy.1.2,xy.2.2)).weight z -
        shortenedApproximation hdim c p r z β xy.1 xy.2) ≤ 396*β^(1/3:ℝ) := by
  letI := encoding_fiber_nonempty hn (s₁*s₂+c)
  letI := encoding_fiber_nonempty (show 2 ≤ n+t by omega) (s₁*s₂+c)
  rw [← fiberTable_rms_eq_labelled hn hn s₁ s₂ (s₁*s₂+c)
    (fun x y => (K (x.1.1,y.1.1) (x.1.2,y.1.2) (x.2,y.2)).weight z -
      shortenedApproximation hdim c p r z β x y)]
  have he : rms ((oldLabelDistribution hn s₁ s₂).prod
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (s₁*s₂+c))))
      (fun ou => (K (ou.1.1.1,ou.1.2.1) (ou.1.1.2,ou.1.2.2)
        (ou.2.val.L,ou.2.val.R)).weight z -
        shortenedApproximation hdim c p r z β (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)) =
      rms ((oldLabelDistribution hn s₁ s₂).prod
        (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (s₁*s₂+c))))
        (fun ou => (Fractional.shortenedAnswerDistribution
          (fun o (v : Fiber F (n+t) (s₁*s₂+c)) => augmentedLongAnswerDistribution hdim c p o v.val)
          r ou.1 ou.2).weight z -
          shortenedApproximation hdim c p r z β (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)) := by
    unfold rms
    congr 1
    unfold FiniteDistribution.expect
    apply Finset.sum_congr rfl
    intro ou _
    by_cases ho : (oldLabelDistribution hn s₁ s₂).weight ou.1 = 0
    · simp [FiniteDistribution.prod, FiniteDistribution.joint, ho]
    · dsimp only
      rw [hK s₁ s₂ ou.1 ho ou.2]
  rw [he]
  exact shortenedApproximation_physical_error hq hn hdim c s₁ s₂ p r z β hβ hβone hthreshold

variable (protocol : GateProtocol F (U F n × U F n) (A × B) inputs)
    (defaultAnswer : A × B) (defaultEncoding : U F n × U F n)
    (program : Program F inputs T) (hd : program.DistinctInputs) (i : Fin T)
    (o : GateOccurrence protocol defaultAnswer program i)

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For label ∈ {0,…,(inputs + T)-1} → F; G ∈ ℝ^(GateSide(F, n, n) × GateSide(F, n, n)), assume 2 ≤ n. Then

‖ ((xy ↦ reindexTable(G, o.portsEquiv(hd), o.portsEquiv(hd), (xy)₁, (xy)₂)))‖_(2,networkPortDistribution(program.scope, ((label, w ↦ encodingDistribution(label(w)))), label, i)) = ‖ ((xy ↦ G((xy)₁, (xy)₂)))‖_(2,independentLabelledPortDistribution(label(o.left), label(o.right), label(o.output))).
-/
theorem scope_rms_eq_ports (hn : 2 ≤ n) (label : Fin (inputs+T) → F)
    (G : Matrix (GateSide F n n) (GateSide F n n) ℝ) :
    rms (networkPortDistribution program.scope (fun label w => encodingDistribution hn (label w)) label i)
      (fun xy => reindexTable G (o.portsEquiv hd) (o.portsEquiv hd) xy.1 xy.2) =
      rms (independentLabelledPortDistribution hn hn (label o.left) (label o.right) (label o.output))
        (fun xy => G xy.1 xy.2) := by
  unfold rms
  congr 1
  change (LocalApproximationData.portDistribution (scope := program.scope)
    (fun w => encodingDistribution hn (label w)) i).expect _ = _
  rw [o.portDistribution_expect hd]
  have hencoding (s : F) :
      encodingDistribution hn s = (mu F n hn s).map (stateEquivProd F n) := rfl
  simp only [hencoding, independentLabelledPortDistribution, expect_prod, expect_map,
    reindexTable, Equiv.symm_apply_apply]
  rfl

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For history ∈ (A × B)*; z ∈ A × B; label ∈ {0,…,(inputs + T)-1} → F; G ∈ ℝ^(GateSide(F, n, n) × GateSide(F, n, n)), assume 2 ≤ n. Then

‖ ((xy ↦ protocol.localOriginal(defaultAnswer, defaultEncoding, program, i, history, z, (xy)₁, (xy)₂) - reindexTable(G, o.portsEquiv(hd), o.portsEquiv(hd), (xy)₁, (xy)₂)))‖_(2,networkPortDistribution(program.scope, ((label, w ↦ encodingDistribution(label(w)))), label, i)) = ‖ ((xy ↦ protocol.answer(o.time, o.gate, GateProtocol.completeHistory(defaultAnswer, history, o.time), ((((xy)₁)₁)₁, (((xy)₂)₁)₁), ((((xy)₁)₁)₂, (((xy)₂)₁)₂), (((xy)₁)₂, ((xy)₂)₂))(z) - G((xy)₁, (xy)₂)))‖_(2,independentLabelledPortDistribution(label(o.left), label(o.right), label(o.output))).
-/
theorem scope_error_rms_eq_ports (history : List (A × B)) (z : A × B)
    (hn : 2 ≤ n) (label : Fin (inputs+T) → F)
    (G : Matrix (GateSide F n n) (GateSide F n n) ℝ) :
    rms (networkPortDistribution program.scope (fun label w => encodingDistribution hn (label w)) label i)
      (fun xy => protocol.localOriginal defaultAnswer defaultEncoding program i history z xy.1 xy.2 -
        reindexTable G (o.portsEquiv hd) (o.portsEquiv hd) xy.1 xy.2) =
      rms (independentLabelledPortDistribution hn hn (label o.left) (label o.right) (label o.output))
        (fun xy => (protocol.answer o.time o.gate
          (GateProtocol.completeHistory defaultAnswer history o.time)
          (xy.1.1.1,xy.2.1.1) (xy.1.1.2,xy.2.1.2) (xy.1.2,xy.2.2)).weight z -
          G xy.1 xy.2) := by
  unfold rms
  congr 1
  change (LocalApproximationData.portDistribution (scope := program.scope)
    (fun w => encodingDistribution hn (label w)) i).expect _ = _
  rw [o.portDistribution_expect hd]
  have hencoding (s : F) :
      encodingDistribution hn s = (mu F n hn s).map (stateEquivProd F n) := rfl
  simp only [hencoding, independentLabelledPortDistribution, expect_prod, expect_map]
  simp_rw [o.localOriginal_ports hd, reindexTable, Equiv.symm_apply_apply]
  rfl

omit defaultEncoding o in
/- Mathematical definition (normal notation): For a concrete executable gate implementing s₁ · s₂+c, assume its conditional answer distribution is the rectangular shortening of the augmented matrix-phase answer distribution. Over the binary field with n ≥ 2, 0<β ≤ 1, and (2ⁿ-1)²β³ ≥ 1, reindex the three-port gadget certificate to the gate's actual wire scope. The resulting certificate has valid-label error 396β^(1/3), all-label L₂ bound 12, pointwise energies 2/β, and mean energies 8. -/
def augmented_scope_local_estimates (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (hdim : n*n+1 = n+t)
    (matrix : (i : ℕ) → Gate F (inputs+i) → (Fin i → A × B) →
      TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A)
    (rectangles : (i : ℕ) → Gate F (inputs+i) → (Fin i → A × B) →
      A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
        (GateSide F n n) ((GateSide F n n) × Kernel H))
    (constant : GateKind F → F)
    (hoperation : ∀ kind s₁ s₂, kind.eval s₁ s₂ = s₁*s₂+constant kind)
    (hanswer : ∀ i gate history s₁ s₂ o,
      (oldLabelDistribution hn s₁ s₂).weight o ≠ 0 → ∀ u : Fiber F n (s₁*s₂+constant gate.kind),
      protocol.answer i gate history (o.1.1,o.2.1) (o.1.2,o.2.2) (u.val.L,u.val.R) =
        Fractional.shortenedAnswerDistribution
          (fun o (v : Fiber F (n+t) (s₁*s₂+constant gate.kind)) =>
            augmentedLongAnswerDistribution hdim (constant gate.kind) (matrix i gate history) o v.val)
          (rectangles i gate history) o u)
    (defaultEncoding : U F n × U F n) (history : List (A × B)) (z : A × B)
    (β : ℝ) (hβ : 0 < β) (hβone : β ≤ 1)
    (hthreshold : 1 ≤ (Fintype.card (U F n × U F n) : ℝ) * β ^ 3) :
    GateLocalEstimates
      (fun label => networkPortDistribution program.scope (fun label w => encodingDistribution hn (label w)) label i)
      (fun label => program.gateValid label i)
      (fun _ => protocol.localOriginal defaultAnswer defaultEncoding program i history z)
      β (396*β^(1/3:ℝ)) := by
  let o := protocol.occurrence defaultAnswer program i
  let h := GateProtocol.completeHistory defaultAnswer history o.time
  let c := constant o.gate.kind
  let p := matrix o.time o.gate h
  let r := rectangles o.time o.gate h
  let data := shortenedGateLocalEstimates hq hn hdim c p r z β hβ hβone hthreshold
  refine {
    approximation := reindexTable data.approximation (o.portsEquiv hd) (o.portsEquiv hd)
    factors := reindexFactors (o.portsEquiv hd) data.factors
    left_max := fun x => data.left_max _
    right_max := fun y => data.right_max _
    left_mean := ?_
    right_mean := ?_
    all_labels_rms := ?_
    valid_error_rms := ?_ }
  · rw [← uavg_eq_expect_uniform, reindexFactors_left_mean, uavg_eq_expect_uniform]
    exact data.left_mean
  · rw [← uavg_eq_expect_uniform, reindexFactors_right_mean, uavg_eq_expect_uniform]
    exact data.right_mean
  · intro label
    rw [scope_rms_eq_ports protocol defaultAnswer program hd i o hn label]
    exact data.all_labels_rms ((label o.left,label o.right),label o.output)
  · intro label hv
    rw [scope_error_rms_eq_ports protocol defaultAnswer defaultEncoding program hd i o history z hn label]
    have hl : label o.output = label o.left*label o.right+c :=
      ((o.valid_eq label).mp hv).trans (hoperation _ _ _)
    rw [hl]
    exact augmented_ambient_rms_error hq hn hdim c p r (protocol.answer o.time o.gate h)
      (hanswer o.time o.gate h) (label o.left) (label o.right) z β hβ hβone hthreshold

/-- All local analytic and physical-answer obligations are discharged for the actual chronological fractional rectangular protocol. -/

/-
Mathematical definition (normal notation): For a binary compiled program whose gates have distinct input wires, lift the shortened-gadget certificates to the executable wire scopes. If n ≥ 2, 0<β ≤ 1, and (2ⁿ-1)² · β³ ≥ 1, every gate, prefix history, and answer has a local certificate with

ε = 396 · β^(1/3).

The underlying wire distributions are independent μ_(s_w); the certificate uses one approximation for all labelings.
-/
def actualNetworkLocalInterface {hdim : n*n+1 = n+t}
    (strategy : Fractional.AugmentedStrategy F A B n t inputs hdim)
    (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (defaultAnswer : A × B) (defaultEncoding : U F n × U F n)
    (program : Program F inputs T) (hd : program.DistinctInputs)
    (β : ℝ) (hβ : 0 < β) (hβone : β ≤ 1)
    (hthreshold : 1 ≤ (Fintype.card (U F n × U F n) : ℝ) * β ^ 3) :
    NetworkLocalInterface program.scope (fun label w => encodingDistribution hn (label w))
      program.gateValid
      (fun _ i h z => (strategy.shareProtocol hn).localOriginal
        defaultAnswer defaultEncoding program i h z) β (396*β^(1/3:ℝ)) where
  gate i h z := augmented_scope_local_estimates (strategy.shareProtocol hn)
    defaultAnswer program hd i hq hn hdim strategy.matrix strategy.rectangles
    GateKind.affineConstant (gate_eval_product_offset_binary hq)
    (strategy.share_answer_on_support hn) defaultEncoding h z β hβ hβone hthreshold

end

end CircuitCompiler.GadgetApproximation
