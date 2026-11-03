import Proofs.Compiler.Model
import Proofs.Compiler.DirectComposition.Comparison

/-!
# Marked terms with history-dependent labels

The finite signed expansion is unchanged at each complete formal transcript. The new step is joint normalization: the original encoding weights and the true answers outside the guards are summed together. A causal realization proves this normalization by a forward probability experiment, equivalently by eliminating answers and newly created encodings in reverse order.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.DirectComposition
open Refresh MatrixRefresh CircuitCompiler.Composition
  CircuitCompiler.AveragedEnergyComparison

variable {W E A F : Type*} [Fintype W] [DecidableEq W]
  [Fintype E] [Nonempty E] [Fintype A] [Nonempty A] {S : ℕ}

/-- Functions of disjoint groups of independently sampled wire encodings have a factored expectation. This assertion is applied separately at each formal transcript. -/
theorem expect_mul_scoped_complement (μ : W → FiniteDistribution E)
    (selected : Finset W) (f g : (W → E) → ℝ)
    (hf : Scoped selected f) (hg : Scoped selectedᶜ g) :
    (independentDistribution μ).expect (fun e => f e * g e) =
      (independentDistribution μ).expect f * (independentDistribution μ).expect g := by
  let inside : selected → E := fun _ => Classical.choice inferInstance
  let outside : {w // w ∉ selected} → E := fun _ => Classical.choice inferInstance
  let left := independentDistribution (fun w : selected => μ w)
  let right := independentDistribution (fun w : {w // w ∉ selected} => μ w)
  let ff := fun x : selected → E => f (joinScope selected x outside)
  let gg := fun y : {w // w ∉ selected} → E => g (joinScope selected inside y)
  have hfi (x : selected → E) (y : {w // w ∉ selected} → E) :
      f (joinScope selected x y) = ff x := by
    apply hf
    intro w hw
    rw [joinScope_of_mem selected x y w hw, joinScope_of_mem selected x outside w hw]
  have hgo (x : selected → E) (y : {w // w ∉ selected} → E) :
      g (joinScope selected x y) = gg y := by
    apply hg
    intro w hw
    have hn := Finset.mem_compl.mp hw
    rw [joinScope_of_not_mem selected x y w hn,
      joinScope_of_not_mem selected inside y w hn]
  have hs := independentDistribution_split_reverse μ (fun w => w ∈ selected)
  have hi : Finset.Subtype.fintype selected = Subtype.fintype (fun w => w ∈ selected) :=
    Subsingleton.elim _ _
  rw [← hi] at hs
  have hff : (independentDistribution μ).expect f = left.expect ff :=
    (expect_scope_eq_global μ selected f hf outside).symm
  have hgg : (independentDistribution μ).expect g = right.expect gg := by
    rw [hs, expect_map, expect_prod]
    change left.expect (fun x => right.expect (fun y => g (joinScope selected x y))) = _
    simp_rw [hgo]
    rw [FiniteDistribution.expect_const]
  rw [hff, hgg, hs, expect_map]
  change (left.prod right).expect
    (fun xy => f (joinScope selected xy.1 xy.2) * g (joinScope selected xy.1 xy.2)) = _
  simp_rw [hfi, hgo]
  rw [expect_prod_mul]

/-- Uniform cubic local moments and incidence three control the marked errors. The remaining answer and encoding weights normalize jointly through their causal realization, at a cost K per guard. -/
theorem causal_guarded_error_product_bound {scope : Fin S → Finset W}
    (network : ScopedProbabilities (E := E) (A := A) scope)
    (law : F → FiniteDistribution E) (label : (Fin S → A) → W → F)
    (realization : Compiler.Adaptive.Realization network law label)
    (marked erased : Finset (Fin S)) (selected : Finset W)
    (error : Fin S → List A → (W → E) → A → ℝ)
    (hlocal : ∀ i h a, Scoped (scope i) (fun e => error i h e a))
    (hcover : ∀ i ∈ marked, scope i ⊆ selected)
    (hdegree : ∀ w, (Finset.univ.filter (fun i => w ∈ scope i)).card ≤ 3)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hmoment : ∀ z, ∀ i ∈ marked,
      (independentDistribution (fun w => law (label z w))).expect
        (fun e => |error i ((List.ofFn z).take i.val) e (z i)|^3) ≤ ε^3) :
    (∑ z : Fin S → A,
      (independentDistribution (fun w => law (label z w))).expect (fun e =>
        |∏ i, if i ∈ marked then error i ((List.ofFn z).take i.val) e (z i)
          else if i ∈ erased then 1
          else network.prob i ((List.ofFn z).take i.val) e (z i)|)) ≤
      (Fintype.card A : ℝ)^((marked ∪ erased ∪ touching scope selected).card) *
        ε^marked.card := by
  let guards := marked ∪ erased ∪ touching scope selected
  let μ := fun z w => law (label z w)
  let f := fun (z : Fin S → A) (e : W → E) =>
    |∏ i ∈ marked, error i ((List.ofFn z).take i.val) e (z i)|
  let q := fun (z : Fin S → A) (e : W → E) =>
    ∏ i, if i ∈ guards then 1 else network.prob i ((List.ofFn z).take i.val) e (z i)
  have hqnonneg (z : Fin S → A) (e : W → E) : 0 ≤ q z e := by
    apply Finset.prod_nonneg
    intro i hi
    split_ifs <;> first | positivity | exact network.nonneg _ _ _ _
  have hfle (z : Fin S → A) : (independentDistribution (μ z)).expect (f z) ≤ ε^marked.card :=
    marked_error_holder (μ z) marked
      (fun i e => error i ((List.ofFn z).take i.val) e (z i))
      (fun i => hlocal i _ _) hdegree ε hε (hmoment z)
  have hfscoped (z : Fin S → A) : Scoped selected (f z) := by
    intro first second he
    apply congrArg abs
    apply Finset.prod_congr rfl
    intro i hi
    exact hlocal i _ _ first second (fun w hw => he w (hcover i hi hw))
  have hqscoped (z : Fin S → A) : Scoped selectedᶜ (q z) := by
    intro first second he
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hg : i ∈ guards
    · simp only [hg, ite_true]
    · simp only [hg, ite_false]
      have hn : i ∉ neighbors scope selected := by
        intro h
        exact hg (Finset.mem_union_right _ h)
      exact network.locality i _ _ first second
        (fun w hw => he w (scope_subset_marked_complement scope selected i hn hw))
  have hpoint (z : Fin S → A) (e : W → E) :
      |∏ i, if i ∈ marked then error i ((List.ofFn z).take i.val) e (z i)
        else if i ∈ erased then 1 else network.prob i ((List.ofFn z).take i.val) e (z i)| ≤
      f z e * q z e := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ i, (if i ∈ marked then |error i ((List.ofFn z).take i.val) e (z i)| else 1) *
          (if i ∈ guards then 1 else network.prob i ((List.ofFn z).take i.val) e (z i)) := by
        apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        intro i hi
        by_cases hm : i ∈ marked
        · have hg : i ∈ guards := Finset.mem_union_left _ (Finset.mem_union_left _ hm)
          simp [hm, hg]
        · by_cases he : i ∈ erased
          · have hg : i ∈ guards := Finset.mem_union_left _ (Finset.mem_union_right _ he)
            simp [hm, he, hg]
          · simp only [hm, he, if_false, one_mul, abs_of_nonneg (network.nonneg _ _ _ _)]
            by_cases hg : i ∈ guards
            · simp only [hg, if_true]
              exact (Finset.single_le_sum (fun a _ => network.nonneg i _ e a)
                (Finset.mem_univ (z i))).trans (network.total_le i _ e)
            · simp [hg]
      _ = f z e * q z e := by
        rw [Finset.prod_mul_distrib]
        simp [f, q, Finset.prod_ite_mem, Finset.abs_prod]
  calc
    _ ≤ ∑ z : Fin S → A, (independentDistribution (μ z)).expect (fun e => f z e * q z e) := by
      apply Finset.sum_le_sum
      intro z hz
      exact (independentDistribution (μ z)).expect_mono (hpoint z)
    _ = ∑ z : Fin S → A,
        (independentDistribution (μ z)).expect (f z) *
          (independentDistribution (μ z)).expect (q z) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact expect_mul_scoped_complement (μ z) selected (f z) (q z) (hfscoped z) (hqscoped z)
    _ ≤ ∑ z : Fin S → A, ε^marked.card * (independentDistribution (μ z)).expect (q z) := by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_right (hfle z)
        ((independentDistribution (μ z)).expect_nonneg _ (hqnonneg z))
    _ = _ := by
      rw [← Finset.mul_sum]
      have h := realization.erased_mass guards
      change (∑ z, (independentDistribution (μ z)).expect (q z)) = _ at h
      rw [h, mul_comm]

variable {X : Type*} [Fintype X] [Nonempty X]
  {scope : Fin S → Finset W}
  {network : ScopedProbabilities (E := X×X) (A := A) scope}
  {law : F → FiniteDistribution (X×X)} {valid : (W → F) → Fin S → Prop}
  {approximated : Finset (Fin S)} {β rawε : ℝ}

/-- The marked-error estimate retains the original law for the induced labeling at every formal transcript. The guard count is still at most 9a+3w. -/
theorem history_guarded_product_bound
    (data : LocalData scope network law valid approximated β rawε)
    (hports : ∀ i, (scope i).card ≤ 3)
    (hdegree : ∀ w, (Finset.univ.filter (fun i => w ∈ scope i)).card ≤ 3)
    (hrawε : 0 ≤ rawε) (hleft : ∀ s, (law s).map Prod.fst = FiniteDistribution.uniform)
    (hright : ∀ s, (law s).map Prod.snd = FiniteDistribution.uniform)
    (label : (Fin S → A) → W → F)
    (realization : Compiler.Adaptive.Realization network law label)
    (hvalid : ∀ z, ∀ i ∈ approximated, valid (label z) i)
    (errors : Finset (Fin S)) (herrors : errors ⊆ approximated)
    (wires : Finset W) (hnonempty : ∀ i ∈ errors, (scope i).Nonempty)
    (B ε : ℝ) (hB : 0 < B) (hε : 0 ≤ ε)
    (hscale : (1+B)*rawε^2+16/B ≤ ε^3) :
    (∑ z : Fin S → A,
      (independentDistribution (fun w => law (label z w))).expect (fun e =>
        |∏ i, if i ∈ errors then data.error B i ((List.ofFn z).take i.val) (z i) e
          else if i ∈ neighbors scope wires then 1
          else network.prob i ((List.ofFn z).take i.val) e (z i)|)) ≤
      (Fintype.card A : ℝ)^(9*errors.card+3*wires.card) * ε^errors.card := by
  have h := causal_guarded_error_product_bound network law label realization errors
    (neighbors scope wires) (errorScope scope errors)
    (fun i h e a => data.error B i h a e) (fun i h a => data.error_scoped B i h a)
    (fun i hi w hw => Finset.mem_biUnion.mpr ⟨i,hi,hw⟩) hdegree ε hε
    (fun z i hi => (local_moments_of_trimming data hrawε hleft hright
      (label z) (hvalid z) B ε hB hscale) i (herrors hi) _ _)
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hε _)
  apply pow_le_pow_right₀ (by exact_mod_cast Fintype.card_pos (α := A))
  have hc := closed_guard_card_le scope hports hdegree errors wires hnonempty
  have hu := Finset.card_union_add_card_inter (errors ∪ neighbors scope wires)
    (neighbors scope (errorScope scope errors))
  have hd := Finset.card_sdiff_add_card_inter (neighbors scope (errorScope scope errors))
    (errors ∪ neighbors scope wires)
  rw [Finset.inter_comm (neighbors scope (errorScope scope errors))] at hd
  change (errors ∪ neighbors scope wires ∪ neighbors scope (errorScope scope errors)).card ≤ _
  omega

/-- Tensor discrepancy is applied at each formal transcript with its induced wire laws, before the absolute values are summed over transcripts. -/
theorem history_execution_marked_norm_le
    (network : ScopedProbabilities (E := X×X) (A := A) scope)
    (g : Fin S → List A → (W → X×X) → A → ℝ)
    (a : ∀ i h z, Factors (fun (left right : W → X) => g i h (fun w => (left w,right w)) z))
    (hg : ∀ i h z, Scoped (scope i) (fun e => g i h e z))
    (operations required : Finset (Fin S)) (wires marked : Finset W)
    (μ : (Fin S → A) → W → FiniteDistribution (X×X))
    (ν : W → FiniteDistribution (X×X))
    (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hrequired : required ⊆ operations) (hmarked : marked ⊆ wires)
    (hneighbors : neighbors scope marked ⊆ operations)
    (hD : ∀ z, ∀ w ∈ marked, ∀ u v : X → ℝ,
      |∑ x, ∑ y, ((μ z w).weight (x,y)-(ν w).weight (x,y))*u x*v y| ≤
        δ*Real.sqrt (FiniteDistribution.uniform.expect (fun x => u x^2))*
          Real.sqrt (FiniteDistribution.uniform.expect (fun y => v y^2)))
    (hleft : ∀ i h z x, (a i h z).leftEnergy x ≤ B)
    (hright : ∀ i h z y, (a i h z).rightEnergy y ≤ B) :
    variationNorm (fun z : Fin S → A =>
      ∑ errors ∈ operations.powerset, ∑ selected ∈ wires.powerset,
        if required ⊆ errors ∧ marked ⊆ selected then
          executionTerm network g operations wires (μ z) ν errors selected z else 0) ≤
      δ^marked.card*B^(neighbors scope marked).card*
        ∑ z : Fin S → A, (independentDistribution (μ z)).expect (fun e =>
          |∏ i, if i ∈ required then
            network.prob i ((List.ofFn z).take i.val) e (z i)-
              g i ((List.ofFn z).take i.val) e (z i)
            else if i ∈ neighbors scope marked then 1
            else network.prob i ((List.ofFn z).take i.val) e (z i)|) := by
  unfold variationNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  dsimp only
  rw [execution_marked_resummation network g operations required wires marked (μ z) ν z
    hrequired hmarked hneighbors]
  by_cases hd : Disjoint required (neighbors scope marked)
  · rw [if_pos hd]
    exact marked_probability_integral_le scope required marked (μ z)
      (fun w x y => (μ z w).weight (x,y)-(ν w).weight (x,y)) δ B hδ hB (hD z)
      (fun i e => network.prob i ((List.ofFn z).take i.val) e (z i))
      (fun i e => g i ((List.ofFn z).take i.val) e (z i))
      (fun i => a i _ _) (fun i => network.locality i _ _) (fun i => hg i _ _)
      (fun i => hleft i _ _) (fun i => hright i _ _) hd
  · rw [if_neg hd, abs_zero]
    exact mul_nonneg (mul_nonneg (pow_nonneg hδ _) (pow_nonneg hB _))
      ((independentDistribution (μ z)).expect_nonneg _ (fun _ => abs_nonneg _))

/-- Each marked local error still costs K⁹ε and each marked wire still costs K³B³δ for causally chosen labels. No normalization or comparison bound is assumed. -/
theorem history_local_marked_bound
    (data : LocalData scope network law valid approximated β rawε)
    (hports : ∀ i, (scope i).card ≤ 3)
    (hdegree : ∀ w, (Finset.univ.filter (fun i => w ∈ scope i)).card ≤ 3)
    (hrawε : 0 ≤ rawε) (hleft : ∀ s, (law s).map Prod.fst = FiniteDistribution.uniform)
    (hright : ∀ s, (law s).map Prod.snd = FiniteDistribution.uniform)
    (label : (Fin S → A) → W → F)
    (realization : Compiler.Adaptive.Realization network law label)
    (hvalid : ∀ z, ∀ i ∈ approximated, valid (label z) i)
    (errors : Finset (Fin S)) (herrors : errors ⊆ approximated)
    (wires marked : Finset W) (hmarked : marked ⊆ wires)
    (hneighbors : neighbors scope marked ⊆ approximated)
    (hnonempty : ∀ i ∈ errors, (scope i).Nonempty)
    (δ B ε : ℝ) (hδ : 0 ≤ δ) (hB : 1 ≤ B) (hε : 0 ≤ ε)
    (hscale : (1+B)*rawε^2+16/B ≤ ε^3)
    (hD : ∀ z, ∀ w ∈ marked, ∀ u v : X → ℝ,
      |∑ x, ∑ y, ((law (label z w)).weight (x,y)-
        (FiniteDistribution.uniform : FiniteDistribution (X×X)).weight (x,y))*u x*v y| ≤
        δ*Real.sqrt (FiniteDistribution.uniform.expect (fun x => u x^2))*
          Real.sqrt (FiniteDistribution.uniform.expect (fun y => v y^2))) :
    variationNorm (fun z : Fin S → A =>
      ∑ selectedErrors ∈ approximated.powerset, ∑ selectedWires ∈ wires.powerset,
        if errors ⊆ selectedErrors ∧ marked ⊆ selectedWires then
          executionTerm network (fun i h e a => data.trimmed B i h a e) approximated wires
            (fun w => law (label z w)) (fun _ => FiniteDistribution.uniform)
            selectedErrors selectedWires z else 0) ≤
      ((Fintype.card A : ℝ)^9*ε)^errors.card *
        ((Fintype.card A : ℝ)^3*B^3*δ)^marked.card := by
  have hB0 : 0 ≤ B := by linarith
  have hraw := history_execution_marked_norm_le network
    (fun i h e a => data.trimmed B i h a e)
    (fun i h a => trimFactors (data.gate i h a).factors B)
    (fun i h a => data.trimmed_scoped B i h a)
    approximated errors wires marked (fun z w => law (label z w))
    (fun _ => FiniteDistribution.uniform) δ B hδ hB0 herrors hmarked hneighbors hD
    (fun i h a x => trimFactors_leftEnergy (data.gate i h a).factors B hB0 x)
    (fun i h a y => trimFactors_rightEnergy (data.gate i h a).factors B hB0 y)
  have hguard := history_guarded_product_bound data hports hdegree hrawε hleft hright
    label realization hvalid errors herrors marked hnonempty B ε (by linarith) hε hscale
  apply hraw.trans
  apply (mul_le_mul_of_nonneg_left hguard
    (mul_nonneg (pow_nonneg hδ _) (pow_nonneg hB0 _))).trans
  exact marked_activity_arithmetic (Fintype.card A : ℝ) B δ ε
    (by exact_mod_cast Fintype.card_pos (α := A)) hB hδ hε _ _ _ _
    (neighbors_card_le scope hdegree marked) (le_refl _)

end CompilerProof.DirectComposition
