import Proofs.Compiler.DirectComposition.Comparison
import Proofs.Compiler.DirectComposition.BinaryParameters

/-!
# Direct composition for unconditional canonical transcripts

The theorem compares actual normalized transcript laws from two valid global labelings. Local certificates are the only approximation input. It derives trimming, incidence-three Hölder, signed tensor discrepancy, adaptive marked resummation, and the finite inclusion–exclusion sum internally. Wire encodings remain hidden, and unused private inputs need no equality condition.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators Classical

namespace Compiler.Direct

open Refresh MatrixRefresh CircuitCompiler CircuitCompiler.Composition
  CircuitCompiler.AveragedEnergyComparison CircuitCompiler.SimulationParameters
  CompilerProof.DirectComposition

variable {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [Nonempty A]
  {S n : ℕ} [Nonempty (U Bit n)]

/-- The direct composition bound follows from the actual local approximation certificates and the physical scope-incidence conditions. Public sampler scopes have fixed labels; every other wire encoding is hidden. Both complete transcripts are normalized probability laws, while their shared empty expansion term may be signed. -/
theorem direct_composition (hn : 2≤n) (scope : Fin S→Finset W)
    (network : ScopedProbabilities (E := U Bit n×U Bit n) (A := A) scope)
    (valid : (W→Bit)→Fin S→Prop) (approximated : Finset (Fin S))
    (data : LocalData scope network (encodingDistribution hn) valid approximated
      (betaParameter (Fintype.card (U Bit n):ℝ)) (rawErrorParameter (Fintype.card (U Bit n):ℝ)))
    (hports : ∀ i,(scope i).card≤3)
    (hdegree : ∀ w,(Finset.univ.filter (fun i=>w∈scope i)).card≤3)
    (hnonempty : ∀ i∈approximated,(scope i).Nonempty)
    (publicWires : Finset W) (hpublic : ∀ i,i∉approximated→scope i⊆publicWires)
    (first second : W→Bit)
    (hfirst : ∀ i∈approximated,valid first i)
    (hsecond : ∀ i∈approximated,valid second i)
    (hlabels : ∀ w∈publicWires,first w=second w)
    (P Q : FiniteDistribution (Fin S→A))
    (hP : ∀ z,P.weight z=canonicalWeight scope network (encodingDistribution hn) first z)
    (hQ : ∀ z,Q.weight z=canonicalWeight scope network (encodingDistribution hn) second z) :
    statisticalDistance P Q≤1000000*(S:ℝ)*(Fintype.card A:ℝ)^9*
      (Fintype.card (U Bit n):ℝ)^(-1/27:ℝ) := by
  let q : ℝ := Fintype.card (U Bit n)
  let K : ℝ := Fintype.card A
  let B := trimParameter q
  let ε := cubicErrorParameter q
  let δ := zeta Bit n
  let wires := dynamicWires scope publicWires
  let base := approximated.disjSum wires
  let g := fun i h e a=>data.trimmed B i h a e
  let terms := fun (label : W→Bit) (marks : Finset (Fin S⊕W)) (z : Fin S→A)=>
    executionTerm network g approximated wires
      (fun w=>encodingDistribution hn (label w)) (fun _=>FiniteDistribution.uniform)
      marks.toLeft marks.toRight z
  let activity : Fin S⊕W→ℝ := Sum.elim (fun _=>K^9*ε) (fun _=>K^3*B^3*δ)
  have hb : fieldCard Bit=2 := by simp [fieldCard,Bit]
  have hq3 : 3≤q := share_card_ge_three hb hn
  have hq : 1≤q := by linarith
  have hK : 1≤K := by
    dsimp only [K]
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos (α:=A))
  have hB : 1≤B := trimParameter_one_le hq
  have hε : 0≤ε := mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)
  have hδ : 0≤δ := by unfold δ zeta;positivity
  have hrawε : 0≤rawErrorParameter q :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)
  have hmarked (label : W→Bit) (hvalid : ∀ i∈approximated,valid label i)
      (J : Finset (Fin S⊕W)) (hJ : J⊆base) :
      variationNorm (fun z=>markedSum base (fun marks=>terms label marks z) J)≤
        ∏ m∈J,activity m := by
    have hsplit := Finset.subset_disjSum.mp hJ
    change variationNorm (fun z=>markedSum (approximated.disjSum wires)
      (fun marks=>executionTerm network g approximated wires
        (fun w=>encodingDistribution hn (label w)) (fun _=>FiniteDistribution.uniform)
        marks.toLeft marks.toRight z) J)≤_
    conv_lhs =>
      arg 1
      ext z
      rw [mixed_marked_sum approximated wires
        (fun errors marked=>executionTerm network g approximated wires
          (fun w=>encodingDistribution hn (label w)) (fun _=>FiniteDistribution.uniform)
          errors marked z) J]
    change _≤∏ m∈J,Sum.elim (fun _=>K^9*ε) (fun _=>K^3*B^3*δ) m
    rw [mixed_activity_product]
    exact local_marked_bound data hports hdegree hrawε
      (encodingDistribution_left hn) (encodingDistribution_right hn)
      label hvalid J.toLeft hsplit.1 wires J.toRight hsplit.2
      (dynamic_neighbors_subset scope publicWires approximated hpublic J.toRight hsplit.2)
      (fun i hi=>hnonempty i (hsplit.1 hi)) δ B ε hδ hB hε
      (trimmed_error_parameter hq) (fun w hw=>encoding_independent_scalar hn (label w))
  have hcommon (z : Fin S→A) : terms first ∅ z=terms second ∅ z := by
    change executionTerm network g approximated wires
      (fun w=>encodingDistribution hn (first w)) (fun _=>FiniteDistribution.uniform) ∅ ∅ z =
      executionTerm network g approximated wires
        (fun w=>encodingDistribution hn (second w)) (fun _=>FiniteDistribution.uniform) ∅ ∅ z
    apply execution_empty_eq network g (fun i h a=>data.trimmed_scoped B i h a)
    intro w hw hnwire
    apply congrArg (encodingDistribution hn)
    exact hlabels w (active_not_dynamic_public scope publicWires w hw hnwire)
  have hexp (label : W→Bit) (z : Fin S→A) :
      canonicalWeight scope network (encodingDistribution hn) label z =
        ∑ marks∈base.powerset,terms label marks z := by
    exact (mixed_execution_expansion network g approximated wires
      (fun w=>encodingDistribution hn (label w)) (fun _=>FiniteDistribution.uniform) z).symm
  have hdistance := statisticalDistance_le_marked_activities P Q base (terms first) (terms second)
    activity (fun m hm=>by cases m <;> dsimp [activity] <;> positivity)
    (fun z=>(hP z).trans (hexp first z)) (fun z=>(hQ z).trans (hexp second z)) hcommon
    (fun J hJ _=>hmarked first hfirst J hJ) (fun J hJ _=>hmarked second hsecond J hJ)
  have hsum : (∑ m∈base,activity m)=
      (approximated.card:ℝ)*K^9*ε+(wires.card:ℝ)*K^3*B^3*δ := by
    rw [mixed_activity_sum]
    ring
  rw [hsum] at hdistance
  exact hdistance.trans (direct_activity_bound_nat hq hK
    (by simpa only [Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ approximated))
    (by simpa only [Fintype.card_fin] using dynamicWires_card_le scope publicWires hports)
    (binary_discrepancy_le hn))

end Compiler.Direct
