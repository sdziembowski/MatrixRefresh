import Proofs.Compiler.DirectComposition.Expansion

/-!
# The closed marked neighborhood

Every operation has at most three wire ports and every wire has at most three incident operations. A marked error therefore creates at most nine guard positions, and a marked wire creates at most three. These counts allow arbitrary fanout in the source circuit because refresh chains enforce the incidence bound in the physical execution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.DirectComposition

open CircuitCompiler.Composition

variable {W I : Type*} [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]

/-- The neighbors of a wire set are the union of the individual incidence sets. -/
theorem neighbors_eq_biUnion (scope : I→Finset W) (wires : Finset W) :
    neighbors scope wires=wires.biUnion (fun w=>Finset.univ.filter (fun i=>w∈scope i)) := by
  ext i
  simp only [neighbors,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_biUnion]
  constructor
  · intro h
    by_contra hn
    apply h
    apply Finset.disjoint_left.mpr
    intro w hw hs
    exact hn ⟨w,hs,hw⟩
  · rintro ⟨w,hw,hi⟩ hd
    exact (Finset.disjoint_left.mp hd) hi hw

/-- At incidence three, a set of marked wires has at most three times as many neighboring operations. -/
theorem neighbors_card_le (scope : I→Finset W)
    (hdegree : ∀ w,(Finset.univ.filter (fun i=>w∈scope i)).card≤3) (wires : Finset W) :
    (neighbors scope wires).card≤3*wires.card := by
  rw [neighbors_eq_biUnion]
  calc
    _ ≤ ∑ w∈wires,(Finset.univ.filter (fun i=>w∈scope i)).card := Finset.card_biUnion_le
    _ ≤ ∑ _w∈wires,3 := Finset.sum_le_sum (fun w hw=>hdegree w)
    _ = _ := by simp [Nat.mul_comm]

/-- Three-port operations expose at most three wires per marked local error. -/
theorem errorScope_card_le (scope : I→Finset W) (hports : ∀ i,(scope i).card≤3)
    (errors : Finset I) : (errorScope scope errors).card≤3*errors.card := by
  calc
    _ ≤ ∑ i∈errors,(scope i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i∈errors,3 := Finset.sum_le_sum (fun i hi=>hports i)
    _ = _ := by simp [Nat.mul_comm]

/-- Every nonempty marked operation touches the union of the marked error scopes. -/
theorem errors_subset_neighbors (scope : I→Finset W) (errors : Finset I)
    (hnonempty : ∀ i∈errors,(scope i).Nonempty) :
    errors⊆neighbors scope (errorScope scope errors) := by
  intro i hi
  obtain ⟨w,hw⟩ := hnonempty i hi
  simp only [neighbors,Finset.mem_filter,Finset.mem_univ,true_and]
  intro hd
  exact (Finset.disjoint_left.mp hd) hw (Finset.mem_biUnion.mpr ⟨i,hi,hw⟩)

/-- The signed positions together with the unsigned guards form a closed neighborhood of size at most 9a+3w. No loss depends on the total number of operations. -/
theorem closed_guard_card_le (scope : I→Finset W)
    (hports : ∀ i,(scope i).card≤3)
    (hdegree : ∀ w,(Finset.univ.filter (fun i=>w∈scope i)).card≤3)
    (errors : Finset I) (wires : Finset W)
    (hnonempty : ∀ i∈errors,(scope i).Nonempty) :
    (errors∪neighbors scope wires).card+
      (neighbors scope (errorScope scope errors)\(errors∪neighbors scope wires)).card ≤
        9*errors.card+3*wires.card := by
  let signed := errors∪neighbors scope wires
  let closed := neighbors scope (errorScope scope errors)
  have hcover := errors_subset_neighbors scope errors hnonempty
  have hcard : signed.card+(closed\signed).card=(signed∪closed).card := by
    have h := Finset.card_union_add_card_inter signed closed
    have h' := Finset.card_sdiff_add_card_inter closed signed
    rw [Finset.inter_comm closed signed] at h'
    omega
  change signed.card+(closed\signed).card≤_
  rw [hcard]
  have hunion : signed∪closed=neighbors scope wires∪closed := by
    ext i
    simp only [signed,Finset.mem_union]
    constructor
    · rintro ((h|h)|h)
      · exact Or.inr (hcover h)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h|h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  rw [hunion]
  have hc : closed.card≤9*errors.card :=
    (neighbors_card_le scope hdegree _).trans
      (by have h:=errorScope_card_le scope hports errors;omega)
  have hw := neighbors_card_le scope hdegree wires
  have hu := Finset.card_union_le (neighbors scope wires) closed
  omega

/-- The paper's neighborhood notation coincides with the generic adaptive execution's guard notation. -/
theorem neighbors_eq_touching {S : ℕ} (scope : Fin S→Finset W) (selected : Finset W) :
    neighbors scope selected=touching scope selected := by
  rfl

/-- Only active nonpublic wires need wire-difference marks. Unused private inputs stay outside the expansion and are marginalized exactly. -/
def dynamicWires (scope : I→Finset W) (publicWires : Finset W) : Finset W :=
  Finset.univ.biUnion scope\publicWires

/-- Three ports per operation give at most 3S dynamic wires independently of the number of unused source inputs. -/
theorem dynamicWires_card_le (scope : I→Finset W) (publicWires : Finset W)
    (hports : ∀ i,(scope i).card≤3) :
    (dynamicWires scope publicWires).card≤3*Fintype.card I := by
  exact (Finset.card_le_card Finset.sdiff_subset).trans
    (by simpa only [errorScope,Finset.card_univ] using errorScope_card_le scope hports Finset.univ)

/-- A public sampler cannot neighbor a marked dynamic wire, so every neighbor has a chosen signed approximation. -/
theorem dynamic_neighbors_subset (scope : I→Finset W) (publicWires : Finset W)
    (operations : Finset I) (hpublicWires : ∀ i,i∉operations→scope i⊆publicWires)
    (marked : Finset W) (hmarked : marked⊆dynamicWires scope publicWires) :
    neighbors scope marked⊆operations := by
  intro i hi
  by_contra hn
  have hdis : Disjoint (scope i) marked := by
    apply Finset.disjoint_left.mpr
    intro w hw hm
    have hnot := (Finset.mem_sdiff.mp (hmarked hm)).2
    exact hnot (hpublicWires i hn hw)
  exact (Finset.mem_filter.mp hi).2 hdis

/-- Every active wire outside the expansion is public. -/
theorem active_not_dynamic_public (scope : I→Finset W) (publicWires : Finset W)
    (w : W) (hactive : w∈Finset.univ.biUnion scope)
    (hdynamic : w∉dynamicWires scope publicWires) : w∈publicWires := by
  by_contra hn
  exact hdynamic (Finset.mem_sdiff.mpr ⟨hactive,hn⟩)

end CompilerProof.DirectComposition
