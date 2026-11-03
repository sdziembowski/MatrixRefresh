import Proofs.Compiler.Operations.PortLaws
import Proofs.Compiler.GateApproximation.MatrixPhase.PhysicalShares
import Proofs.Compiler.GateApproximation.Refreshing.LocalApproximation
import Proofs.Compiler.LocalComparisons.GateInterface

/-!
# Lifting the two- and three-port estimates to canonical wire assignments

The selected factors stay independent of plaintext labels. A label map only specializes the local hypotheses; a coordinate projection only reads the active ports. The distribution identities below average the original unconditional encodings and retain each encoding's left/right correlation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
noncomputable section
namespace CompilerProof.Operations
open Refresh MatrixRefresh CircuitCompiler CircuitCompiler.Composition
  CircuitCompiler.AveragedEnergyComparison CircuitCompiler.GadgetApproximation
  CircuitCompiler.RefreshApproximation

/-- Specialize a local estimate to the labels of a larger network, retaining its chosen approximation. Stronger validity hypotheses can be made explicit. -/
def relabelCertificate {X S R : Type*} [Fintype X] [Nonempty X]
    {laws : S → FiniteDistribution (X×X)} {valid : S → Prop}
    {original : S → X → X → ℝ} {β ε : ℝ}
    (data : GateLocalEstimates laws valid original β ε)
    (labelMap : R → S) (valid' : R → Prop)
    (hvalid : ∀ r, valid' r → valid (labelMap r)) :
    GateLocalEstimates (fun r => laws (labelMap r)) valid'
      (fun r => original (labelMap r)) β ε where
  approximation := data.approximation
  factors := data.factors
  left_max := data.left_max
  right_max := data.right_max
  left_mean := data.left_mean
  right_mean := data.right_mean
  all_labels_rms r := data.all_labels_rms (labelMap r)
  valid_error_rms r hr := data.valid_error_rms (labelMap r) (hvalid r hr)

/-- Increasing an explicit numerical allowance does not alter any factor. -/
def enlargeError {X S : Type*} [Fintype X] [Nonempty X]
    {laws : S → FiniteDistribution (X×X)} {valid : S → Prop}
    {original : S → X → X → ℝ} {β ε ε' : ℝ}
    (data : GateLocalEstimates laws valid original β ε) (hε : ε≤ε') :
    GateLocalEstimates laws valid original β ε' where
  approximation := data.approximation
  factors := data.factors
  left_max := data.left_max
  right_max := data.right_max
  left_mean := data.left_mean
  right_mean := data.right_mean
  all_labels_rms := data.all_labels_rms
  valid_error_rms s hs := (data.valid_error_rms s hs).trans hε

/-- The zero representation is used only where validity is impossible, including public samplers excluded from the approximated-operation set. It makes no claim about approximating a sampler's true answer table. -/
def zeroCertificate {X S : Type*} [Fintype X] [Nonempty X]
    (laws : S → FiniteDistribution (X×X)) (valid : S → Prop)
    (original : S → X → X → ℝ) (β ε : ℝ) (hβ : 0<β)
    (hfalse : ∀ s, valid s → False) : GateLocalEstimates laws valid original β ε where
  approximation _ _ := 0
  factors := {
    rank := 1
    left _ _ := 0
    right _ _ := 0
    reconstruct := by intros; simp }
  left_max x := by simp only [Factors.leftEnergy,zero_pow (by decide : 2≠0),Finset.sum_const_zero]; positivity
  right_max x := by simp only [Factors.rightEnergy,zero_pow (by decide : 2≠0),Finset.sum_const_zero]; positivity
  left_mean := by
    change (FiniteDistribution.uniform : FiniteDistribution X).expect
      (fun _ => ∑ _j : Fin 1, (0:ℝ)^2) ≤ 8
    norm_num [FiniteDistribution.expect_const]
  right_mean := by
    change (FiniteDistribution.uniform : FiniteDistribution X).expect
      (fun _ => ∑ _j : Fin 1, (0:ℝ)^2) ≤ 8
    norm_num [FiniteDistribution.expect_const]
  all_labels_rms s := by simp [rms]
  valid_error_rms s hs := False.elim (hfalse s hs)

variable {W F : Type*} [Fintype W] [DecidableEq W]
  [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- The product of pair-valued wire encodings is the product of encoded states followed by grouping the two parties' coordinates. -/
theorem encoding_groupedLaw (hn : 2≤n) (label : W → F) :
    groupedDistribution (fun w => encodingDistribution hn (label w)) Prod.fst Prod.snd =
      groupedDistribution (fun w => mu F n hn (label w))
        (fun x : State F n => x.L) (fun x => x.R) := by
  have hencoding (s : F) :
      encodingDistribution hn s = (mu F n hn s).map (stateEquivProd F n) := rfl
  simp only [groupedDistribution,hencoding,←independentDistribution_map,
    FiniteDistribution.map_map]
  rfl

/-- The active computation ports have exactly the labelled distribution used by the rectangular gadget certificate. -/
theorem grouped_projectTriple (hn : 2≤n) (label : W → F) (l r o : W)
    (hlr : l≠r) (hlo : l≠o) (hro : r≠o) :
    (groupedDistribution (fun w => encodingDistribution hn (label w)) Prod.fst Prod.snd).map
      (fun xy => (projectTriple l r o xy.1,projectTriple l r o xy.2)) =
      independentLabelledPortDistribution hn hn (label l) (label r) (label o) := by
  rw [encoding_groupedLaw]
  unfold groupedDistribution independentLabelledPortDistribution
  rw [←independent_projectTriple (fun w => mu F n hn (label w)) l r o hlr hlo hro,
    FiniteDistribution.map_map,FiniteDistribution.map_map]
  rfl

/-- The two control-refresh ports have exactly the labelled copy distribution. -/
theorem grouped_projectPair (hn : 2≤n) (label : W → F) (l o : W) (hlo : l≠o) :
    (groupedDistribution (fun w => encodingDistribution hn (label w)) Prod.fst Prod.snd).map
      (fun xy => (projectPair l o xy.1,projectPair l o xy.2)) =
      copyLabelDistribution hn (label l) (label o) := by
  rw [encoding_groupedLaw]
  unfold groupedDistribution copyLabelDistribution
  rw [←independent_projectPair (fun w => mu F n hn (label w)) l o hlo,
    FiniteDistribution.map_map,FiniteDistribution.map_map]
  rfl

end CompilerProof.Operations
