import Proofs.Compiler.DirectComposition.InclusionExclusion
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Sum

/-!
# Summing marked activities

Inclusion–exclusion is applied before taking absolute values. A bound for each marked sum then gives the product of one plus each activity, minus one. When the total activity is small this is at most twice its sum; otherwise statistical distance is already at most one. The common empty term is an arbitrary signed weight and is never sampled.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.DirectComposition

open Refresh

variable {M V : Type*} [DecidableEq M] [Fintype V]

/-- Choosing marks of two different kinds is the same as choosing an independent subset of each kind. This converts the joint expansion's two indices into the single index used by marked inclusion–exclusion. -/
theorem sum_powerset_disjSum {N : Type*} [DecidableEq N]
    (left : Finset M) (right : Finset N) (f : Finset M → Finset N → ℝ) :
    (∑ U∈(left.disjSum right).powerset,f U.toLeft U.toRight) =
      ∑ A∈left.powerset,∑ B∈right.powerset,f A B := by
  rw [← Finset.sum_product']
  apply Finset.sum_bij (fun U _ => (U.toLeft,U.toRight))
  · intro U hU
    have h := Finset.subset_disjSum.mp (Finset.mem_powerset.mp hU)
    exact Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr h.1,
      Finset.mem_powerset.mpr h.2⟩
  · intro U hU U' hU' heq
    have hleft := congrArg Prod.fst heq
    have hright := congrArg Prod.snd heq
    change U.toLeft=U'.toLeft at hleft
    change U.toRight=U'.toRight at hright
    rw [← Finset.toLeft_disjSum_toRight (u:=U),
      ← Finset.toLeft_disjSum_toRight (u:=U')]
    rw [hleft,hright]
  · intro AB hAB
    obtain ⟨hA,hB⟩ := Finset.mem_product.mp hAB
    refine ⟨AB.1.disjSum AB.2,?_,?_⟩
    · apply Finset.mem_powerset.mpr
      simpa only [Finset.disjSum_subset,Finset.toLeft_disjSum,Finset.toRight_disjSum]
        using And.intro (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hB)
    · simp
  · intro U hU
    rfl

/-- The nonempty inclusion–exclusion coefficients all have absolute value one. -/
theorem abs_markSign {J : Finset M} (hJ : J≠∅) : |markSign J|=1 := by
  simp [markSign,hJ,abs_pow]

/-- Absolute mass is bounded after regrouping the expansion into its marked sums. No positivity or normalization is required of the terms. -/
theorem expansion_norm_le_activities (base : Finset M) (terms : Finset M → V → ℝ)
    (activity : M → ℝ)
    (hmarked : ∀ J,J⊆base → J≠∅ →
      variationNorm (fun v=>markedSum base (fun U=>terms U v) J) ≤ ∏ m∈J,activity m) :
    variationNorm (fun v=>(∑ U∈base.powerset,terms U v)-terms ∅ v) ≤
      (∏ m∈base,(1+activity m))-1 := by
  have hempty : (∅ : Finset M)∈base.powerset :=
    Finset.mem_powerset.mpr (Finset.empty_subset base)
  have hexp (v : V) : (∑ U∈base.powerset,terms U v)-terms ∅ v =
      ∑ J∈base.powerset.erase ∅,markSign J*markedSum base (fun U=>terms U v) J := by
    rw [marked_inclusion_exclusion]
    have h := Finset.sum_erase_add (s:=base.powerset)
      (f:=fun J=>markSign J*markedSum base (fun U=>terms U v) J) hempty
    simpa [markSign] using h.symm
  calc
    _ = ∑ v,|∑ J∈base.powerset.erase ∅,
        markSign J*markedSum base (fun U=>terms U v) J| := by
      simp only [variationNorm,hexp]
    _ ≤ ∑ v,∑ J∈base.powerset.erase ∅,
        |markSign J*markedSum base (fun U=>terms U v) J| := by
      apply Finset.sum_le_sum
      intro v _
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ J∈base.powerset.erase ∅,
        variationNorm (fun v=>markedSum base (fun U=>terms U v) J) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro J hJ
      have hJne : J≠∅ := (Finset.mem_erase.mp hJ).1
      simp only [variationNorm,abs_mul,abs_markSign hJne,one_mul]
    _ ≤ ∑ J∈base.powerset.erase ∅,∏ m∈J,activity m := by
      apply Finset.sum_le_sum
      intro J hJ
      exact hmarked J (Finset.mem_powerset.mp (Finset.mem_erase.mp hJ).2)
        (Finset.mem_erase.mp hJ).1
    _ = _ := sum_nonempty_activities base activity

/-- A finite product of one plus nonnegative activities is bounded by the exponential of their sum. -/
theorem prod_one_add_le_exp_sum (base : Finset M) (activity : M → ℝ)
    (ha : ∀ m∈base,0≤activity m) :
    (∏ m∈base,(1+activity m)) ≤ Real.exp (∑ m∈base,activity m) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro m hm
    linarith [ha m hm]
  · intro m hm
    linarith [Real.add_one_le_exp (activity m)]

/-- When total activity is at most one, the product remainder is at most twice that total. -/
theorem activities_remainder_le (base : Finset M) (activity : M → ℝ)
    (ha : ∀ m∈base,0≤activity m) (hsmall : (∑ m∈base,activity m)≤1) :
    (∏ m∈base,(1+activity m))-1 ≤ 2*(∑ m∈base,activity m) := by
  have h0 : 0≤∑ m∈base,activity m := Finset.sum_nonneg ha
  have he := Real.abs_exp_sub_one_le (x:=∑ m∈base,activity m)
    (by rwa [abs_of_nonneg h0])
  calc
    _ ≤ Real.exp (∑ m∈base,activity m)-1 :=
      sub_le_sub_right (prod_one_add_le_exp_sum base activity ha) 1
    _ ≤ |Real.exp (∑ m∈base,activity m)-1| := le_abs_self _
    _ ≤ 2*|∑ m∈base,activity m| := he
    _ = _ := by rw [abs_of_nonneg h0]

/-- Two probability distributions close to the same signed weight have distance at most the common absolute-mass error. -/
theorem statisticalDistance_le_common_signed (P Q : FiniteDistribution V)
    (common : V → ℝ) (R : ℝ)
    (hP : variationNorm (fun v=>P.weight v-common v)≤R)
    (hQ : variationNorm (fun v=>Q.weight v-common v)≤R) :
    statisticalDistance P Q≤R := by
  have h := variationNorm_sub_le P.weight common Q.weight
  have he : variationNorm (fun v=>common v-Q.weight v)=
      variationNorm (fun v=>Q.weight v-common v) := by
    simp only [variationNorm,abs_sub_comm]
  rw [he] at h
  unfold statisticalDistance
  linarith

/-- The small-activity estimate and the universal distance bound combine into one unconditional linear estimate. -/
theorem statisticalDistance_le_two_activity_sum (P Q : FiniteDistribution V)
    (common : V → ℝ) (base : Finset M) (activity : M → ℝ)
    (ha : ∀ m∈base,0≤activity m)
    (hP : variationNorm (fun v=>P.weight v-common v)≤(∏ m∈base,(1+activity m))-1)
    (hQ : variationNorm (fun v=>Q.weight v-common v)≤(∏ m∈base,(1+activity m))-1) :
    statisticalDistance P Q≤2*(∑ m∈base,activity m) := by
  by_cases hsmall : (∑ m∈base,activity m)≤1
  · exact (statisticalDistance_le_common_signed P Q common _ hP hQ).trans
      (activities_remainder_le base activity ha hsmall)
  · have h0 : 0≤∑ m∈base,activity m := Finset.sum_nonneg ha
    have h := statisticalDistance_le_one P Q
    linarith

/-- Joint expansions with a common empty term and a product bound for each marked sum yield the linear statistical-distance estimate. The empty term may be signed; only the two complete expansions are probability distributions. -/
theorem statisticalDistance_le_marked_activities (P Q : FiniteDistribution V)
    (base : Finset M) (termsP termsQ : Finset M → V → ℝ) (activity : M → ℝ)
    (ha : ∀ m∈base,0≤activity m)
    (hexpP : ∀ v,P.weight v=∑ U∈base.powerset,termsP U v)
    (hexpQ : ∀ v,Q.weight v=∑ U∈base.powerset,termsQ U v)
    (hcommon : ∀ v,termsP ∅ v=termsQ ∅ v)
    (hmarkedP : ∀ J,J⊆base → J≠∅ →
      variationNorm (fun v=>markedSum base (fun U=>termsP U v) J) ≤ ∏ m∈J,activity m)
    (hmarkedQ : ∀ J,J⊆base → J≠∅ →
      variationNorm (fun v=>markedSum base (fun U=>termsQ U v) J) ≤ ∏ m∈J,activity m) :
    statisticalDistance P Q≤2*(∑ m∈base,activity m) := by
  apply statisticalDistance_le_two_activity_sum P Q (termsP ∅) base activity ha
  · have h := expansion_norm_le_activities base termsP activity hmarkedP
    simpa only [hexpP] using h
  · have h := expansion_norm_le_activities base termsQ activity hmarkedQ
    simpa only [hexpQ,hcommon] using h

end CompilerProof.DirectComposition
