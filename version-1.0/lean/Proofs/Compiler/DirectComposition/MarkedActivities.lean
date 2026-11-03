import Proofs.Compiler.DirectComposition.Adaptive
import Proofs.Compiler.DirectComposition.Scopes
import Proofs.Compiler.DirectComposition.Trimming
import Proofs.Compiler.DirectComposition.FiniteMarks

/-!
# Activities of the two kinds of marks

A marked local error costs K⁹ε, and a marked encoding difference costs K³B³δ. The elementary estimates below preserve those separate activities until the final finite inclusion–exclusion sum.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.DirectComposition

open Refresh MatrixRefresh CircuitCompiler.Composition
  CircuitCompiler.AveragedEnergyComparison

/-- The tensor and guard costs separate into one activity for each local-error mark and one for each wire mark. -/
theorem marked_activity_arithmetic (K B δ ε : ℝ) (hK : 1≤K) (hB : 1≤B)
    (hδ : 0≤δ) (hε : 0≤ε) (a w neighbors guards : ℕ)
    (hneighbors : neighbors≤3*w) (hguards : guards≤9*a+3*w) :
    δ^w*B^neighbors*(K^guards*ε^a)≤(K^9*ε)^a*(K^3*B^3*δ)^w := by
  have hK0 : 0≤K := by linarith
  have hB0 : 0≤B := by linarith
  calc
    _ ≤ δ^w*B^(3*w)*(K^(9*a+3*w)*ε^a) := by
      gcongr
    _ = _ := by simp only [mul_pow,← pow_mul,pow_add];ring

variable {W X A F : Type*} [Fintype W] [DecidableEq W] [Fintype X] [Nonempty X]
  [Fintype A] {S : ℕ} {scope : Fin S→Finset W}
  {network : ScopedProbabilities (E := X×X) (A := A) scope}
  {law : F→FiniteDistribution (X×X)} {valid : (W→F)→Fin S→Prop}
  {approximated : Finset (Fin S)} {β rawε : ℝ}

/-- The local trimming lemma supplies the exact third-moment premise used by adaptive marked isolation, for each globally valid labeling. -/
theorem local_moments_of_trimming
    (data : LocalData scope network law valid approximated β rawε)
    (hrawε : 0≤rawε) (hleft : ∀ s,(law s).map Prod.fst=FiniteDistribution.uniform)
    (hright : ∀ s,(law s).map Prod.snd=FiniteDistribution.uniform)
    (label : W→F) (hvalid : ∀ i∈approximated,valid label i)
    (B ε : ℝ) (hB : 0<B) (hscale : (1+B)*rawε^2+16/B≤ε^3) :
    ∀ i∈approximated,∀ h z,
      (independentDistribution (fun w=>law (label w))).expect
        (fun e=>|data.error B i h z e|^3)≤ε^3 := by
  intro i hi h z
  exact (data.trimmed_error_cube hrawε hleft hright label i ⟨hvalid i hi,hi⟩ h z B hB).trans hscale

/-- The averaged product left after tensorizing the marked wire differences is controlled by its closed neighborhood, with no dependence on the total number of formal histories. -/
theorem local_guarded_product_bound [Nonempty A]
    (data : LocalData scope network law valid approximated β rawε)
    (hports : ∀ i,(scope i).card≤3)
    (hdegree : ∀ w,(Finset.univ.filter (fun i=>w∈scope i)).card≤3)
    (hrawε : 0≤rawε) (hleft : ∀ s,(law s).map Prod.fst=FiniteDistribution.uniform)
    (hright : ∀ s,(law s).map Prod.snd=FiniteDistribution.uniform)
    (label : W→F) (hvalid : ∀ i∈approximated,valid label i)
    (errors : Finset (Fin S)) (herrors : errors⊆approximated)
    (wires : Finset W) (hnonempty : ∀ i∈errors,(scope i).Nonempty)
    (B ε : ℝ) (hB : 0<B) (hε : 0≤ε) (hscale : (1+B)*rawε^2+16/B≤ε^3) :
    (∑ z : Fin S→A,(independentDistribution (fun w=>law (label w))).expect (fun e=>
      |∏ i,if i∈errors then data.error B i ((List.ofFn z).take i.val) (z i) e
        else if i∈neighbors scope wires then 1
        else network.prob i ((List.ofFn z).take i.val) e (z i)|)) ≤
      (Fintype.card A : ℝ)^(9*errors.card+3*wires.card)*ε^errors.card := by
  have h := guarded_error_product_bound network (fun w=>law (label w)) errors
    (neighbors scope wires) (errorScope scope errors)
    (fun i h e a=>data.error B i h a e) (fun i h a=>data.error_scoped B i h a)
    (fun i hi w hw=>Finset.mem_biUnion.mpr ⟨i,hi,hw⟩) hdegree ε hε
    (fun i hi h a=>(local_moments_of_trimming data hrawε hleft hright label hvalid B ε hB hscale)
      i (herrors hi) h a)
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hε _)
  apply pow_le_pow_right₀ (by exact_mod_cast Fintype.card_pos (α:=A))
  simpa only [← neighbors_eq_touching] using
    closed_guard_card_le scope hports hdegree errors wires hnonempty

end CompilerProof.DirectComposition
