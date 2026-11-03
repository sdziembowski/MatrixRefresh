import Proofs.Compiler.DirectComposition.ProductFactors
import Proofs.Compiler.DirectComposition.EncodingDifference
import Proofs.Compiler.DirectComposition.ExecutionExpansion
import Proofs.Compiler.DirectComposition.Adaptive

/-!
# Summing marked wire differences

Fix the ordinary encoding coordinates first. Scope locality makes every error and every true probability outside the marked-wire neighborhood constant on the marked coordinates. The remaining signed tables are multiplied through their chosen factor representations, then the tensor discrepancy gives one factor δ per marked wire. Only after bounding the absolute value of the whole signed weighted sum do we average the ordinary coordinates under their original encoding distributions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.DirectComposition

open Refresh MatrixRefresh CircuitCompiler.Composition
  CircuitCompiler.AveragedEnergyComparison

variable {W X I : Type*} [Fintype W] [DecidableEq W] [Fintype X] [Nonempty X]
  [Fintype I]

/-- Regroup a tuple of paired shares into its left and right coordinate tuples. -/
def pairedAssignmentEquiv (J : Type*) (E : Type*) :
    (J→E×E) ≃ (J→E)×(J→E) where
  toFun e := (fun j=>(e j).1,fun j=>(e j).2)
  invFun e := fun j=>(e.1 j,e.2 j)
  left_inv e := by funext j;exact Prod.eta (e j)
  right_inv e := by cases e;rfl

/-- Use signed kernels exactly at the marked wires and the original probability weights elsewhere. -/
def markedWireWeight (selected : Finset W) (μ : W→FiniteDistribution (X×X))
    (D : W→X→X→ℝ) (encoding : W→X×X) : ℝ :=
  ∏ w,if w∈selected then D w (encoding w).1 (encoding w).2
    else (μ w).weight (encoding w)

/-- Splitting marked and ordinary coordinates factors their weights exactly, including the signed weights. -/
theorem markedWireWeight_split (selected : Finset W) (μ : W→FiniteDistribution (X×X))
    (D : W→X→X→ℝ) (inside : selected→X×X)
    (outside : {w // w∉selected}→X×X) :
    markedWireWeight selected μ D (joinScope selected inside outside) =
      (∏ w : selected,D w (inside w).1 (inside w).2)*
        (independentDistribution (fun w : {w // w∉selected}=>μ w)).weight outside := by
  unfold markedWireWeight independentDistribution
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w=>w∈selected)]
  have hi : Finset.Subtype.fintype selected=Subtype.fintype (fun w=>w∈selected) :=
    Subsingleton.elim _ _
  rw [← hi]
  congr 1
  · apply Finset.prod_congr rfl
    intro w hw
    simp [joinScope_of_mem, w.property]
  · apply Finset.prod_congr rfl
    intro w hw
    simp [joinScope_of_not_mem, w.property]

/-- Grouping the marked shares commutes with fixing the outside coordinates separately for each party. -/
theorem joinScope_pair (selected : Finset W) (left right : selected→X)
    (outside : {w // w∉selected}→X×X) :
    joinScope selected (fun w=>(left w,right w)) outside =
      fun w=>(joinScope selected left (fun j=>(outside j).1) w,
        joinScope selected right (fun j=>(outside j).2) w) := by
  funext w
  by_cases hw : w∈selected
  · simp [joinScope_of_mem,hw]
  · simp [joinScope_of_not_mem,hw]

/-- Summing signed marked-wire weights against locally bounded factor tables and a remainder independent of those wires costs δ^|W|B^r. Every unmarked coordinate remains under its original unconditional encoding law. -/
theorem signed_tensor_integral_le
    (selected : Finset W) (μ : W→FiniteDistribution (X×X))
    (D : W→X→X→ℝ) (δ B : ℝ) (hδ : 0≤δ) (hB : 0≤B)
    (hD : ∀ w∈selected,∀ u v : X→ℝ,
      |∑ x,∑ y,D w x y*u x*v y|≤
        δ*Real.sqrt (FiniteDistribution.uniform.expect (fun x=>u x^2))*
          Real.sqrt (FiniteDistribution.uniform.expect (fun y=>v y^2)))
    (f : I→(W→X)→(W→X)→ℝ) (a : ∀ i,Factors (f i))
    (hleft : ∀ i x,(a i).leftEnergy x≤B)
    (hright : ∀ i y,(a i).rightEnergy y≤B)
    (remainder : (W→X×X)→ℝ) (hrest : Scoped selectedᶜ remainder) :
    |∑ encoding : W→X×X,markedWireWeight selected μ D encoding*remainder encoding*
      ∏ i,f i (fun w=>(encoding w).1) (fun w=>(encoding w).2)|≤
      δ^selected.card*B^Fintype.card I*
        (independentDistribution μ).expect (fun encoding=>|remainder encoding|) := by
  let ordinary := independentDistribution (fun w : {w // w∉selected}=>μ w)
  let base : selected→X×X := fun _=>
    (Classical.choice inferInstance,Classical.choice inferInstance)
  let rem : ({w // w∉selected}→X×X)→ℝ :=
    fun outside=>remainder (joinScope selected base outside)
  let inner : ({w // w∉selected}→X×X)→ℝ := fun outside=>
    ∑ inside : selected→X×X,(∏ w : selected,D w (inside w).1 (inside w).2)*
      ∏ i,f i (fun w=>(joinScope selected inside outside w).1)
        (fun w=>(joinScope selected inside outside w).2)
  have hconstant (inside : selected→X×X) (outside : {w // w∉selected}→X×X) :
      remainder (joinScope selected inside outside)=rem outside := by
    apply hrest
    intro w hw
    have hn : w∉selected := Finset.mem_compl.mp hw
    rw [joinScope_of_not_mem selected inside outside w hn,
      joinScope_of_not_mem selected base outside w hn]
  have hinner (outside : {w // w∉selected}→X×X) :
      |inner outside|≤δ^selected.card*B^Fintype.card I := by
    have h := tensor_productFactors_le
      (fun w : selected=>D w) δ B hδ hB (fun w=>hD w w.2) f a
      (fun left=>joinScope selected left (fun w=>(outside w).1))
      (fun right=>joinScope selected right (fun w=>(outside w).2)) hleft hright
    unfold inner
    rw [← Equiv.sum_comp (pairedAssignmentEquiv selected X).symm]
    simp only [Fintype.sum_prod_type,pairedAssignmentEquiv,Equiv.coe_fn_symm_mk]
    simp_rw [joinScope_pair]
    convert h using 1
    · congr 3
      · exact Subsingleton.elim _ _
      · funext l
        congr 3 <;> exact Subsingleton.elim _ _
    · simp only [Fintype.card_coe]
  have hsplit : (∑ encoding : W→X×X,
      markedWireWeight selected μ D encoding*remainder encoding*
        ∏ i,f i (fun w=>(encoding w).1) (fun w=>(encoding w).2)) =
      ordinary.expect (fun outside=>rem outside*inner outside) := by
    rw [← Equiv.sum_comp
      (Equiv.piEquivPiSubtypeProd (fun w=>w∈selected) (fun _=>X×X)).symm]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    unfold FiniteDistribution.expect ordinary inner
    apply Finset.sum_congr rfl
    intro outside ho
    dsimp only
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro inside hi
    change markedWireWeight selected μ D (joinScope selected inside outside)*
      remainder (joinScope selected inside outside)*_=_
    rw [markedWireWeight_split,hconstant]
    dsimp only [joinScope]
    ring
  have havg : ordinary.expect (fun outside=>|rem outside|)=
      (independentDistribution μ).expect (fun encoding=>|remainder encoding|) := by
    symm
    have hs := independentDistribution_split_reverse μ (fun w=>w∈selected)
    have hi : Finset.Subtype.fintype selected=Subtype.fintype (fun w=>w∈selected) :=
      Subsingleton.elim _ _
    rw [← hi] at hs
    rw [hs,expect_map,expect_prod]
    change (independentDistribution (fun w : selected=>μ w)).expect
      (fun inside=>ordinary.expect (fun outside=>|remainder
        (joinScope selected inside outside)|))=ordinary.expect (fun outside=>|rem outside|)
    simp_rw [hconstant]
    rw [FiniteDistribution.expect_const]
  rw [hsplit]
  calc
    _ ≤ ordinary.expect (fun outside=>|rem outside*inner outside|) :=
      abs_expect_le_expect_abs ordinary _
    _ ≤ ordinary.expect (fun outside=>|rem outside| * (δ^selected.card*B^Fintype.card I)) := by
      apply ordinary.expect_mono
      intro outside
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hinner outside) (abs_nonneg _)
    _ = _ := by rw [expect_mul_const,havg];ring

variable [DecidableEq I]

/-- Remove the neighboring approximation factors but retain the marked errors and every other true probability. -/
def markedRemainder (scope : I→Finset W) (errors : Finset I) (selected : Finset W)
    (p g : I→(W→X×X)→ℝ) (encoding : W→X×X) : ℝ :=
  ∏ i,if i∈errors then p i encoding-g i encoding
    else if i∈neighbors scope selected then 1 else p i encoding

/-- Operations outside the marked-wire neighborhood inspect only ordinary coordinates. -/
theorem scope_subset_marked_complement (scope : I→Finset W) (selected : Finset W)
    (i : I) (hi : i∉neighbors scope selected) : scope i⊆selectedᶜ := by
  have hd : Disjoint (scope i) selected := by
    by_contra hn
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)
  intro w hw
  exact Finset.mem_compl.mpr (fun hs=>(Finset.disjoint_left.mp hd) hw hs)

/-- An admissible marked remainder is independent of every marked wire. Its errors keep their full original scopes, all disjoint from the marked wire set. -/
theorem markedRemainder_scoped (scope : I→Finset W) (errors : Finset I)
    (selected : Finset W) (p g : I→(W→X×X)→ℝ)
    (hp : ∀ i,Scoped (scope i) (p i)) (hg : ∀ i,Scoped (scope i) (g i))
    (hd : Disjoint errors (neighbors scope selected)) :
    Scoped selectedᶜ (markedRemainder scope errors selected p g) := by
  intro first second he
  apply Finset.prod_congr rfl
  intro i hi
  by_cases herr : i∈errors
  · have hn : i∉neighbors scope selected :=
      fun hn=>(Finset.disjoint_left.mp hd) herr hn
    have he' : ∀ w∈scope i,first w=second w :=
      fun w hw=>he w (scope_subset_marked_complement scope selected i hn hw)
    simp only [if_pos herr]
    rw [hp i first second he',hg i first second he']
  · by_cases hn : i∈neighbors scope selected
    · simp [herr,hn]
    · simp only [if_neg herr,if_neg hn]
      exact hp i first second
        (fun w hw=>he w (scope_subset_marked_complement scope selected i hn hw))

/-- Factor the marked resummation into its neighboring approximations and the remainder that is constant on marked wires. -/
theorem marked_product_factorization (scope : I→Finset W) (errors : Finset I)
    (selected : Finset W) (p g : I→(W→X×X)→ℝ)
    (hd : Disjoint errors (neighbors scope selected)) (encoding : W→X×X) :
    (∏ i,if i∈errors then p i encoding-g i encoding
      else if i∈neighbors scope selected then g i encoding else p i encoding) =
      markedRemainder scope errors selected p g encoding*
        ∏ i : neighbors scope selected,g i encoding := by
  have hprod : (∏ i : neighbors scope selected,g i encoding)=
      ∏ i∈neighbors scope selected,g i encoding :=
    Finset.prod_coe_sort (neighbors scope selected) (fun i=>g i encoding)
  have hite : (∏ i∈neighbors scope selected,g i encoding)=
      ∏ i,if i∈neighbors scope selected then g i encoding else 1 :=
    (Fintype.prod_ite_mem (neighbors scope selected) (fun i=>g i encoding)).symm
  rw [hprod,hite]
  unfold markedRemainder
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases he : i∈errors
  · have hn : i∉neighbors scope selected :=
      fun hn=>(Finset.disjoint_left.mp hd) he hn
    simp [he,hn]
  · by_cases hn : i∈neighbors scope selected <;> simp [he,hn]

/-- One fixed-history marked resummation is bounded by tensor discrepancy times the ordinary-law remainder average. This is the analytic step between exact joint resummation and adaptive guard enumeration. -/
theorem marked_probability_integral_le
    (scope : I→Finset W) (errors : Finset I) (selected : Finset W)
    (μ : W→FiniteDistribution (X×X)) (D : W→X→X→ℝ)
    (δ B : ℝ) (hδ : 0≤δ) (hB : 0≤B)
    (hD : ∀ w∈selected,∀ u v : X→ℝ,
      |∑ x,∑ y,D w x y*u x*v y|≤
        δ*Real.sqrt (FiniteDistribution.uniform.expect (fun x=>u x^2))*
          Real.sqrt (FiniteDistribution.uniform.expect (fun y=>v y^2)))
    (p g : I→(W→X×X)→ℝ)
    (a : ∀ i,Factors (fun (left right : W→X)=>g i (fun w=>(left w,right w))))
    (hp : ∀ i,Scoped (scope i) (p i)) (hg : ∀ i,Scoped (scope i) (g i))
    (hleft : ∀ i x,(a i).leftEnergy x≤B)
    (hright : ∀ i y,(a i).rightEnergy y≤B)
    (hd : Disjoint errors (neighbors scope selected)) :
    |∑ encoding : W→X×X,
      (∏ i,if i∈errors then p i encoding-g i encoding
        else if i∈neighbors scope selected then g i encoding else p i encoding)*
      markedWireWeight selected μ D encoding|≤
      δ^selected.card*B^(neighbors scope selected).card*
        (independentDistribution μ).expect
          (fun encoding=>|markedRemainder scope errors selected p g encoding|) := by
  have h := signed_tensor_integral_le selected μ D δ B hδ hB hD
    (fun i : neighbors scope selected=>fun left right=>g i (fun w=>(left w,right w)))
    (fun i=>a i) (fun i=>hleft i) (fun i=>hright i)
    (markedRemainder scope errors selected p g)
    (markedRemainder_scoped scope errors selected p g hp hg hd)
  simp only [Fintype.card_coe,Prod.eta] at h
  convert h using 1
  apply congrArg abs
  apply Finset.sum_congr rfl
  intro encoding he
  rw [marked_product_factorization scope errors selected p g hd encoding]
  ring

variable {A : Type*} [Fintype A] {S : ℕ} {scope : Fin S→Finset W}

/-- Summing over marked-wire coordinates with their signed weights, before taking the full history norm, costs δ per marked wire and B per neighboring approximation. The remaining history sum is exactly the quantity controlled by the adaptive guard lemma. Incompatible error and wire marks contribute zero by the joint expansion identity. -/
theorem execution_marked_norm_le
    (network : ScopedProbabilities (E := X×X) (A := A) scope)
    (g : Fin S→List A→(W→X×X)→A→ℝ)
    (a : ∀ i h z,Factors (fun (left right : W→X)=>g i h (fun w=>(left w,right w)) z))
    (hg : ∀ i h z,Scoped (scope i) (fun encoding=>g i h encoding z))
    (operations required : Finset (Fin S)) (wires marked : Finset W)
    (μ ν : W→FiniteDistribution (X×X)) (δ B : ℝ) (hδ : 0≤δ) (hB : 0≤B)
    (hrequired : required⊆operations) (hmarked : marked⊆wires)
    (hneighbors : neighbors scope marked⊆operations)
    (hD : ∀ w∈marked,∀ u v : X→ℝ,
      |∑ x,∑ y,((μ w).weight (x,y)-(ν w).weight (x,y))*u x*v y|≤
        δ*Real.sqrt (FiniteDistribution.uniform.expect (fun x=>u x^2))*
          Real.sqrt (FiniteDistribution.uniform.expect (fun y=>v y^2)))
    (hleft : ∀ i h z x,(a i h z).leftEnergy x≤B)
    (hright : ∀ i h z y,(a i h z).rightEnergy y≤B) :
    variationNorm (fun z : Fin S→A=>
      ∑ errors∈operations.powerset,∑ selected∈wires.powerset,
        if required⊆errors ∧ marked⊆selected then
          executionTerm network g operations wires μ ν errors selected z else 0)≤
      δ^marked.card*B^(neighbors scope marked).card*
        ∑ z : Fin S→A,(independentDistribution μ).expect (fun encoding=>
          |∏ i,if i∈required then
            network.prob i ((List.ofFn z).take i.val) encoding (z i)-
              g i ((List.ofFn z).take i.val) encoding (z i)
            else if i∈neighbors scope marked then 1
            else network.prob i ((List.ofFn z).take i.val) encoding (z i)|) := by
  unfold variationNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  dsimp only
  rw [execution_marked_resummation network g operations required wires marked μ ν z
    hrequired hmarked hneighbors]
  by_cases hd : Disjoint required (neighbors scope marked)
  · rw [if_pos hd]
    exact marked_probability_integral_le scope required marked μ
      (fun w x y=>(μ w).weight (x,y)-(ν w).weight (x,y)) δ B hδ hB hD
      (fun i encoding=>network.prob i ((List.ofFn z).take i.val) encoding (z i))
      (fun i encoding=>g i ((List.ofFn z).take i.val) encoding (z i))
      (fun i=>a i _ _) (fun i=>network.locality i _ _) (fun i=>hg i _ _)
      (fun i=>hleft i _ _) (fun i=>hright i _ _) hd
  · rw [if_neg hd,abs_zero]
    exact mul_nonneg (mul_nonneg (pow_nonneg hδ _) (pow_nonneg hB _))
      ((independentDistribution μ).expect_nonneg _ (fun _=>abs_nonneg _))

end CompilerProof.DirectComposition
