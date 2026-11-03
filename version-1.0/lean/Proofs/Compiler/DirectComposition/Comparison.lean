import Proofs.Compiler.DirectComposition.MarkedActivities
import Proofs.Compiler.DirectComposition.MarkedTensor

/-!
# From local certificates to marked activities

This is the analytic assembly of the direct argument. Separate trimming gives third moments on valid original laws, tensor discrepancy sums over the signed marked-wire weights before taking absolute values, and adaptive isolation enumerates only the resulting closed neighborhood. The hypotheses contain local approximation data only.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.DirectComposition

open Refresh MatrixRefresh CircuitCompiler.Composition
  CircuitCompiler.AveragedEnergyComparison

variable {W X A F : Type*} [Fintype W] [DecidableEq W] [Fintype X] [Nonempty X]
  [Fintype A] [Nonempty A] {S : ℕ} {scope : Fin S→Finset W}
  {network : ScopedProbabilities (E := X×X) (A := A) scope}
  {law : F→FiniteDistribution (X×X)} {valid : (W→F)→Fin S→Prop}
  {approximated : Finset (Fin S)} {β rawε : ℝ}

/-- Each compatible marked sum has one activity K⁹ε per marked local error and K³B³δ per marked wire; incompatible marks vanish by exact resummation. -/
theorem local_marked_bound
    (data : LocalData scope network law valid approximated β rawε)
    (hports : ∀ i,(scope i).card≤3)
    (hdegree : ∀ w,(Finset.univ.filter (fun i=>w∈scope i)).card≤3)
    (hrawε : 0≤rawε) (hleft : ∀ s,(law s).map Prod.fst=FiniteDistribution.uniform)
    (hright : ∀ s,(law s).map Prod.snd=FiniteDistribution.uniform)
    (label : W→F) (hvalid : ∀ i∈approximated,valid label i)
    (errors : Finset (Fin S)) (herrors : errors⊆approximated)
    (wires marked : Finset W) (hmarked : marked⊆wires)
    (hneighbors : neighbors scope marked⊆approximated)
    (hnonempty : ∀ i∈errors,(scope i).Nonempty)
    (δ B ε : ℝ) (hδ : 0≤δ) (hB : 1≤B) (hε : 0≤ε)
    (hscale : (1+B)*rawε^2+16/B≤ε^3)
    (hD : ∀ w∈marked,∀ u v : X→ℝ,
      |∑ x,∑ y,((law (label w)).weight (x,y)-
        (FiniteDistribution.uniform : FiniteDistribution (X×X)).weight (x,y))*u x*v y|≤
        δ*Real.sqrt (FiniteDistribution.uniform.expect (fun x=>u x^2))*
          Real.sqrt (FiniteDistribution.uniform.expect (fun y=>v y^2))) :
    variationNorm (fun z : Fin S→A=>
      ∑ selectedErrors∈approximated.powerset,∑ selectedWires∈wires.powerset,
        if errors⊆selectedErrors ∧ marked⊆selectedWires then
          executionTerm network (fun i h e a=>data.trimmed B i h a e) approximated wires
            (fun w=>law (label w)) (fun _=>FiniteDistribution.uniform)
            selectedErrors selectedWires z else 0) ≤
      ((Fintype.card A : ℝ)^9*ε)^errors.card*
        ((Fintype.card A : ℝ)^3*B^3*δ)^marked.card := by
  have hB0 : 0≤B := by linarith
  have hraw := execution_marked_norm_le network
    (fun i h e a=>data.trimmed B i h a e)
    (fun i h a=>trimFactors (data.gate i h a).factors B)
    (fun i h a=>data.trimmed_scoped B i h a)
    approximated errors wires marked (fun w=>law (label w))
    (fun _=>FiniteDistribution.uniform) δ B hδ hB0 herrors hmarked hneighbors hD
    (fun i h a x=>trimFactors_leftEnergy (data.gate i h a).factors B hB0 x)
    (fun i h a y=>trimFactors_rightEnergy (data.gate i h a).factors B hB0 y)
  have hguard := local_guarded_product_bound data hports hdegree hrawε hleft hright
    label hvalid errors herrors marked hnonempty B ε (by linarith) hε hscale
  apply hraw.trans
  apply (mul_le_mul_of_nonneg_left hguard
    (mul_nonneg (pow_nonneg hδ _) (pow_nonneg hB0 _))).trans
  exact marked_activity_arithmetic (Fintype.card A : ℝ) B δ ε
    (by exact_mod_cast Fintype.card_pos (α:=A)) hB hδ hε _ _ _ _
    (neighbors_card_le scope hdegree marked) (le_refl _)

end CompilerProof.DirectComposition
