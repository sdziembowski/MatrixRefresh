import Proofs.Compiler.DirectComposition.Model
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Finset.Sum

/-!
# Exact joint expansion with protected error scopes

The algebra below applies to arbitrary real coordinate weights, including signed weights. It never changes the encoding measures on the scope of an error factor. Marking and then summing the remaining differences restores the original measures away from the marked wires and the true answer probabilities away from their neighboring operations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.DirectComposition

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Choose μ−ν on marked coordinates, ν on other free coordinates, and μ everywhere protected. This formula permits signed μ and ν and is purely finite algebra. -/
def coordinateTerm (μ ν : W → ℝ) (free marked : Finset W) : ℝ :=
  ∏ w, if w∈marked then μ w-ν w else if w∈free then ν w else μ w

/-- Expanding only the free coordinate measures leaves every protected coordinate at its original μ weight. -/
theorem coordinate_expansion (μ ν : W → ℝ) (free : Finset W) :
    (∑ marked ∈ free.powerset,coordinateTerm μ ν free marked) = ∏ w,μ w := by
  induction free using Finset.induction with
  | empty => simp [coordinateTerm]
  | @insert a free ha ih =>
    rw [Finset.sum_powerset_insert ha,← Finset.sum_add_distrib]
    calc
      _ = ∑ marked ∈ free.powerset,coordinateTerm μ ν free marked := by
        apply Finset.sum_congr rfl
        intro marked hmarked
        have ham : a∉marked := fun h => ha (Finset.mem_powerset.mp hmarked h)
        apply Finset.prod_add_prod_eq (Finset.mem_univ a)
        · simp [ham,ha]
        · intro w hw hwa
          simp [Finset.mem_insert,hwa]
        · intro w hw hwa
          simp [Finset.mem_insert,hwa]
      _ = _ := ih

/-- Requiring every marked coordinate to occur in an expansion replaces its measure by μ−ν and sums every other free coordinate back to μ. -/
theorem coordinate_marked_resummation (μ ν : W → ℝ) (free required : Finset W)
    (hrequired : required⊆free) :
    (∑ marked ∈ free.powerset,
      if required⊆marked then coordinateTerm μ ν free marked else 0) =
      ∏ w,if w∈required then μ w-ν w else μ w := by
  let μ' : W → ℝ := fun w => if w∈required then μ w-ν w else μ w
  let ν' : W → ℝ := fun w => if w∈required then 0 else ν w
  have hterm (marked : Finset W) :
      coordinateTerm μ' ν' free marked =
        if required⊆marked then coordinateTerm μ ν free marked else 0 := by
    by_cases hm : required⊆marked
    · simp only [if_pos hm]
      apply Finset.prod_congr rfl
      intro w hw
      by_cases hr : w∈required
      · simp [μ',ν',hr,hm hr]
      · simp [μ',ν',hr]
    · simp only [if_neg hm]
      obtain ⟨w,hw,hn⟩ := Finset.not_subset.mp hm
      apply Finset.prod_eq_zero (Finset.mem_univ w)
      simp [μ',ν',hw,hn,hrequired hw]
  simpa only [hterm,μ'] using coordinate_expansion μ' ν' free

/-- Summing over subsets of a smaller finite set can be written as a filtered sum over a larger powerset. -/
theorem sum_powerset_restrict (small large : Finset W) (h : small⊆large)
    (f : Finset W → ℝ) :
    (∑ marked ∈ large.powerset,if marked⊆small then f marked else 0) =
      ∑ marked ∈ small.powerset,f marked := by
  symm
  calc
    _ = ∑ marked ∈ small.powerset,if marked⊆small then f marked else 0 := by
      apply Finset.sum_congr rfl
      intro marked hm
      simp [Finset.mem_powerset.mp hm]
    _ = _ := by
      apply Finset.sum_subset (Finset.powerset_mono.mpr h)
      intro marked hm hn
      have hnot : ¬marked⊆small := fun hs => hn (Finset.mem_powerset.mpr hs)
      simp [hnot]

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The protected wires are the full union of the scopes carrying local error factors. -/
def errorScope (scope : I → Finset W) (errors : Finset I) : Finset W := errors.biUnion scope

/-- Neighbors of marked wires are exactly the operations whose scopes touch them. -/
def neighbors (scope : I → Finset W) (wires : Finset W) : Finset I :=
  Finset.univ.filter (fun i => ¬Disjoint (scope i) wires)

/-- Marked wires avoid every protected error scope exactly when the error positions avoid every marked-wire neighbor. -/
theorem errors_disjoint_neighbors (scope : I → Finset W) (errors : Finset I) (wires : Finset W) :
    Disjoint wires (errorScope scope errors) ↔ Disjoint errors (neighbors scope wires) := by
  constructor
  · intro h
    apply Finset.disjoint_left.mpr
    intro i hi hneighbor
    have htouch := (Finset.mem_filter.mp hneighbor).2
    obtain ⟨w,hwi,hww⟩ := Finset.not_disjoint_iff.mp htouch
    exact (Finset.disjoint_left.mp h) hww (Finset.mem_biUnion.mpr ⟨i,hi,hwi⟩)
  · intro h
    apply Finset.disjoint_left.mpr
    intro w hw he
    obtain ⟨i,hi,hwi⟩ := Finset.mem_biUnion.mp he
    apply (Finset.disjoint_left.mp h) hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.not_disjoint_iff.mpr ⟨w,hwi,hw⟩⟩

/-- The pointwise term with marked error operations and signed wire differences. Wire expansion is restricted to the complement of every error scope. -/
def jointTerm (scope : I → Finset W) (operations : Finset I) (wires : Finset W)
    (μ ν : W → ℝ) (p g : I → ℝ) (errors : Finset I) (marked : Finset W) : ℝ :=
  if marked⊆wires\errorScope scope errors then
    coordinateTerm p g operations errors *
      coordinateTerm μ ν (wires\errorScope scope errors) marked else 0

/-- All terms in the joint expansion sum exactly to the original encoding-weight product times the original probability-factor product. -/
theorem joint_expansion (scope : I → Finset W) (operations : Finset I) (wires : Finset W)
    (μ ν : W → ℝ) (p g : I → ℝ) :
    (∑ errors ∈ operations.powerset,∑ marked ∈ wires.powerset,
      jointTerm scope operations wires μ ν p g errors marked) =
      (∏ i,p i)*(∏ w,μ w) := by
  have hinner (errors : Finset I) :
      (∑ marked ∈ wires.powerset,jointTerm scope operations wires μ ν p g errors marked) =
        coordinateTerm p g operations errors*(∏ w,μ w) := by
    unfold jointTerm
    calc
      _ = coordinateTerm p g operations errors *
          ∑ marked ∈ wires.powerset,
            if marked⊆wires\errorScope scope errors then
              coordinateTerm μ ν (wires\errorScope scope errors) marked else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro marked hm
        split_ifs <;> simp
      _ = _ := by
        rw [sum_powerset_restrict _ wires Finset.sdiff_subset,
          coordinate_expansion]
  simp_rw [hinner]
  rw [← Finset.sum_mul,coordinate_expansion]

/-- Marked wires can be expanded outside every error scope exactly when the error operations avoid their neighbors. -/
theorem marked_subset_free_iff (scope : I → Finset W) (wires marked : Finset W)
    (hmarked : marked⊆wires) (errors : Finset I) :
    marked⊆wires\errorScope scope errors ↔ Disjoint errors (neighbors scope marked) := by
  rw [← errors_disjoint_neighbors]
  constructor
  · intro h
    apply Finset.disjoint_left.mpr
    intro w hw he
    exact (Finset.mem_sdiff.mp (h hw)).2 he
  · intro h w hw
    exact Finset.mem_sdiff.mpr ⟨hmarked hw,fun he => (Finset.disjoint_left.mp h) hw he⟩

/-- Summing all unmarked wire differences at fixed error operations restores the original measures at every unmarked wire. -/
theorem joint_marked_wires (scope : I → Finset W) (operations : Finset I)
    (wires marked : Finset W) (hmarked : marked⊆wires)
    (μ ν : W → ℝ) (p g : I → ℝ) (errors : Finset I) :
    (∑ selected ∈ wires.powerset,
      if marked⊆selected then jointTerm scope operations wires μ ν p g errors selected else 0) =
      if Disjoint errors (neighbors scope marked) then
        coordinateTerm p g operations errors *
          (∏ w,if w∈marked then μ w-ν w else μ w) else 0 := by
  by_cases hfree : marked⊆wires\errorScope scope errors
  · have hdis := (marked_subset_free_iff scope wires marked hmarked errors).1 hfree
    rw [if_pos hdis]
    unfold jointTerm
    calc
      _ = coordinateTerm p g operations errors *
          ∑ selected ∈ wires.powerset,
            if selected⊆wires\errorScope scope errors then
              (if marked⊆selected then coordinateTerm μ ν (wires\errorScope scope errors) selected else 0)
            else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro selected hs
        split_ifs <;> simp_all
      _ = _ := by
        rw [sum_powerset_restrict _ wires Finset.sdiff_subset,
          coordinate_marked_resummation μ ν _ marked hfree]
  · have hdis : ¬Disjoint errors (neighbors scope marked) :=
      fun h => hfree ((marked_subset_free_iff scope wires marked hmarked errors).2 h)
    rw [if_neg hdis]
    apply Finset.sum_eq_zero
    intro selected hs
    unfold jointTerm
    split_ifs with hselect hsubset
    · exact False.elim (hfree (hselect.trans hsubset))
    all_goals rfl

/-- Suppressing errors at a forbidden set of operations is equivalent to replacing their original factor by their approximation before expanding. -/
theorem coordinate_avoid (p g : I → ℝ) (operations forbidden errors : Finset I)
    (hforbidden : forbidden⊆operations) :
    coordinateTerm (fun i => if i∈forbidden then g i else p i) g operations errors =
      if Disjoint errors forbidden then coordinateTerm p g operations errors else 0 := by
  by_cases hdis : Disjoint errors forbidden
  · rw [if_pos hdis]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases he : i∈errors
    · have hf : i∉forbidden := fun h => (Finset.disjoint_left.mp hdis) he h
      simp [he,hf]
    · by_cases hf : i∈forbidden
      · simp [he,hf,hforbidden hf]
      · simp [he,hf]
  · rw [if_neg hdis]
    obtain ⟨i,hi,hf⟩ := Finset.not_disjoint_iff.mp hdis
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi,hf]

/-- Sum all unmarked operation errors while retaining the forbidden approximation factors and the required error factors. -/
theorem operation_marked_resummation (p g : I → ℝ) (operations required forbidden : Finset I)
    (hrequired : required⊆operations) (hforbidden : forbidden⊆operations)
    (hdisjoint : Disjoint required forbidden) :
    (∑ errors ∈ operations.powerset,
      if required⊆errors then (if Disjoint errors forbidden then coordinateTerm p g operations errors else 0)
        else 0) =
      ∏ i,if i∈required then p i-g i else if i∈forbidden then g i else p i := by
  have h := coordinate_marked_resummation
    (fun i => if i∈forbidden then g i else p i) g operations required hrequired
  have hsum : (∑ errors ∈ operations.powerset,
      if required⊆errors then coordinateTerm (fun i => if i∈forbidden then g i else p i) g operations errors else 0) =
      ∑ errors ∈ operations.powerset,
      if required⊆errors then (if Disjoint errors forbidden then coordinateTerm p g operations errors else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro errors he
    rw [coordinate_avoid p g operations forbidden errors hforbidden]
  rw [← hsum, h]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hr : i∈required
  · have hf : i∉forbidden := fun h => (Finset.disjoint_left.mp hdisjoint) hr h
    simp [hr,hf]
  · simp [hr]

/-- The marked sum restores every unmarked true probability and encoding law. Only marked local errors and neighbors of marked wires remain signed; error scopes remain protected throughout. -/
theorem joint_marked_resummation (scope : I → Finset W) (operations required : Finset I)
    (wires marked : Finset W) (μ ν : W → ℝ) (p g : I → ℝ)
    (hrequired : required⊆operations) (hmarked : marked⊆wires)
    (hneighbors : neighbors scope marked⊆operations) :
    (∑ errors ∈ operations.powerset, ∑ selected ∈ wires.powerset,
      if required⊆errors ∧ marked⊆selected then
        jointTerm scope operations wires μ ν p g errors selected else 0) =
      if Disjoint required (neighbors scope marked) then
        (∏ i,if i∈required then p i-g i else if i∈neighbors scope marked then g i else p i) *
          (∏ w,if w∈marked then μ w-ν w else μ w)
      else 0 := by
  have hinner (errors : Finset I) :
      (∑ selected ∈ wires.powerset,
        if required⊆errors ∧ marked⊆selected then
          jointTerm scope operations wires μ ν p g errors selected else 0) =
      if required⊆errors then
        (if Disjoint errors (neighbors scope marked) then
          coordinateTerm p g operations errors *
            (∏ w,if w∈marked then μ w-ν w else μ w) else 0) else 0 := by
    by_cases he : required⊆errors
    · simp only [he,true_and,if_true]
      exact joint_marked_wires scope operations wires marked hmarked μ ν p g errors
    · simp [he]
  simp_rw [hinner]
  by_cases hd : Disjoint required (neighbors scope marked)
  · rw [if_pos hd]
    calc
      _ = (∑ errors ∈ operations.powerset,
          if required⊆errors then
            (if Disjoint errors (neighbors scope marked) then coordinateTerm p g operations errors else 0)
          else 0) * (∏ w,if w∈marked then μ w-ν w else μ w) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro errors he
            split_ifs <;> simp
      _ = _ := by rw [operation_marked_resummation p g operations required _ hrequired hneighbors hd]
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro errors he
    by_cases hr : required⊆errors
    · have hbad : ¬Disjoint errors (neighbors scope marked) :=
        fun hh => hd (Finset.disjoint_of_subset_left hr hh)
      simp [hr,hbad]
    · simp [hr]

end CompilerProof.DirectComposition
