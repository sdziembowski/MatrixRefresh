import Proofs.Compiler.DirectComposition.Model
import Mathlib.Data.Nat.Choose.Sum

/-!
# Marked sums and their finite inclusion–exclusion identity

A term is indexed by the set of differences appearing in it. Its marked sum collects every term containing a prescribed mark set. Inclusion–exclusion recovers all nonempty terms from these marked sums. This finite identity is applied only after the analytic proof has bounded each marked sum; no term is interpreted as a probability distribution.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.DirectComposition

variable {M : Type*} [DecidableEq M]

/-- The inclusion–exclusion coefficient is zero on the empty mark set and (−1)^(|J|+1) otherwise. -/
def markSign (J : Finset M) : ℝ := if J=∅ then 0 else (-1:ℝ)^(J.card+1)

/-- The alternating nonempty-subset coefficients sum to one on a nonempty term and zero on the empty term. -/
theorem sum_markSign (U : Finset M) :
    (∑ J ∈ U.powerset, markSign J) = if U=∅ then 0 else 1 := by
  by_cases hU : U=∅
  · simp [hU,markSign]
  have hne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU
  have hsum : (∑ J ∈ U.powerset, (-1:ℝ)^J.card)=0 := by
    exact_mod_cast Finset.sum_powerset_neg_one_pow_card_of_nonempty hne
  have hempty : (∅ : Finset M)∈U.powerset := Finset.mem_powerset.mpr (Finset.empty_subset U)
  have hsplit := Finset.sum_erase_add (s:=U.powerset)
    (f:=fun J : Finset M => (-1:ℝ)^J.card) hempty
  have hrest : (∑ J ∈ U.powerset.erase ∅, (-1:ℝ)^J.card) = -1 := by
    simp only [Finset.card_empty,pow_zero,hsum] at hsplit
    linarith
  have hsign : (∑ J ∈ U.powerset,markSign J) =
      -(∑ J ∈ U.powerset.erase ∅,(-1:ℝ)^J.card) := by
    rw [← Finset.sum_erase_add (s:=U.powerset) (f:=markSign) hempty]
    simp only [markSign,ite_true,add_zero,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    have hJne : J≠∅ := (Finset.mem_erase.mp hJ).1
    simp [hJne,pow_succ]
  rw [hsign,hrest]
  simp [hU]

/-- Sum of all terms containing the specified marked differences, with an explicit finite ambient mark set. -/
def markedSum (base : Finset M) (terms : Finset M → ℝ) (J : Finset M) : ℝ :=
  ∑ U ∈ base.powerset, if J⊆U then terms U else 0

/-- Restricting a subset-sum to marks contained in U is exactly summing over the powerset of U. -/
theorem sum_subsets_restrict (base U : Finset M) (hU : U⊆base)
    (f : Finset M → ℝ) :
    (∑ J ∈ base.powerset,if J⊆U then f J else 0) = ∑ J ∈ U.powerset,f J := by
  symm
  calc
    _ = ∑ J ∈ U.powerset,if J⊆U then f J else 0 := by
      apply Finset.sum_congr rfl
      intro J hJ
      simp [Finset.mem_powerset.mp hJ]
    _ = _ := by
      apply Finset.sum_subset (Finset.powerset_mono.mpr hU)
      intro J hJbase hJU
      have hnot : ¬J⊆U := fun h => hJU (Finset.mem_powerset.mpr h)
      simp [hnot]

/-- Every nonempty term has total coefficient one in the alternating sum of marked sums; the empty common term has coefficient zero. -/
theorem marked_inclusion_exclusion (base : Finset M) (terms : Finset M → ℝ) :
    (∑ U ∈ base.powerset,terms U)-terms ∅ =
      ∑ J ∈ base.powerset,markSign J*markedSum base terms J := by
  have hempty : (∅ : Finset M)∈base.powerset := Finset.mem_powerset.mpr (Finset.empty_subset base)
  symm
  calc
    _ = ∑ U ∈ base.powerset,
        (∑ J ∈ base.powerset,if J⊆U then markSign J else 0)*terms U := by
      unfold markedSum
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro U hU
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro J hJ
      by_cases h : J⊆U <;> simp [h]
    _ = ∑ U ∈ base.powerset,(if U=∅ then 0 else 1)*terms U := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [sum_subsets_restrict base U (Finset.mem_powerset.mp hU),sum_markSign]
    _ = ∑ U ∈ base.powerset.erase ∅,terms U := by
      rw [← Finset.sum_erase_add (s:=base.powerset)
        (f:=fun U : Finset M => (if U=∅ then 0 else 1)*terms U) hempty]
      simp only [ite_true,zero_mul,add_zero]
      apply Finset.sum_congr rfl
      intro U hU
      simp [(Finset.mem_erase.mp hU).1]
    _ = (∑ U ∈ base.powerset,terms U)-terms ∅ := by
      have h := Finset.sum_erase_add (s:=base.powerset) (f:=terms) hempty
      linarith

/-- Summing all nonempty products of activities yields the product of (1+activity) minus one. -/
theorem sum_nonempty_activities (base : Finset M) (activity : M → ℝ) :
    (∑ J ∈ base.powerset.erase ∅,∏ m ∈ J,activity m) =
      (∏ m ∈ base,(1+activity m))-1 := by
  have hempty : (∅ : Finset M)∈base.powerset := Finset.mem_powerset.mpr (Finset.empty_subset base)
  have h := Finset.sum_erase_add (s:=base.powerset)
    (f:=fun J : Finset M => ∏ m ∈ J,activity m) hempty
  rw [Finset.prod_empty,← Finset.prod_one_add] at h
  linarith

end CompilerProof.DirectComposition
