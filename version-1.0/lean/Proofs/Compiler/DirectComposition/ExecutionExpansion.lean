import Proofs.Compiler.DirectComposition.Expansion
import Proofs.Compiler.LocalComparisons.PatchMarginals

/-!
# Expansion of unconditional transcript weights

The finite algebra is applied before conditioning on any leakage prefix. Hidden encoding variables are summed only after the joint expansion. The empty term is shared by labelings that agree on public active wires; unused input probability weights sum to one and impose no equality requirement.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.DirectComposition

open Refresh MatrixRefresh CircuitCompiler.Composition
  CircuitCompiler.AveragedEnergyComparison

variable {W E A : Type*} [Fintype W] [DecidableEq W] [Fintype E] [Nonempty E]
  [Fintype A] {S : ℕ} {scope : Fin S→Finset W}

/-- The signed joint coefficient for a complete formal history, with every error scope protected from wire expansion. -/
def executionTerm (network : ScopedProbabilities (E := E) (A := A) scope)
    (g : Fin S→List A→(W→E)→A→ℝ) (operations : Finset (Fin S)) (wires : Finset W)
    (μ ν : W→FiniteDistribution E) (errors : Finset (Fin S)) (marked : Finset W)
    (z : Fin S→A) : ℝ :=
  ∑ encoding : W→E,jointTerm scope operations wires
    (fun w=>(μ w).weight (encoding w)) (fun w=>(ν w).weight (encoding w))
    (fun i=>network.prob i ((List.ofFn z).take i.val) encoding (z i))
    (fun i=>g i ((List.ofFn z).take i.val) encoding (z i)) errors marked

/-- Summing all signed coefficients gives exactly the original canonical transcript weight. -/
theorem execution_expansion (network : ScopedProbabilities (E := E) (A := A) scope)
    (g : Fin S→List A→(W→E)→A→ℝ) (operations : Finset (Fin S)) (wires : Finset W)
    (μ ν : W→FiniteDistribution E) (z : Fin S→A) :
    (∑ errors∈operations.powerset,∑ marked∈wires.powerset,
      executionTerm network g operations wires μ ν errors marked z) =
    (independentDistribution μ).expect (fun encoding=>
      ∏ i,network.prob i ((List.ofFn z).take i.val) encoding (z i)) := by
  simp only [executionTerm,FiniteDistribution.expect,independentDistribution]
  simp_rw [Finset.sum_comm (s:=wires.powerset) (t:=Finset.univ)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro encoding he
  rw [joint_expansion]
  ring

/-- Marking and summing preserves exact equality after the finite weighted sum over the hidden encoding tuple. -/
theorem execution_marked_resummation (network : ScopedProbabilities (E := E) (A := A) scope)
    (g : Fin S→List A→(W→E)→A→ℝ) (operations required : Finset (Fin S))
    (wires marked : Finset W) (μ ν : W→FiniteDistribution E) (z : Fin S→A)
    (hrequired : required⊆operations) (hmarked : marked⊆wires)
    (hneighbors : neighbors scope marked⊆operations) :
    (∑ errors∈operations.powerset,∑ selected∈wires.powerset,
      if required⊆errors ∧ marked⊆selected then
        executionTerm network g operations wires μ ν errors selected z else 0) =
    if Disjoint required (neighbors scope marked) then
      ∑ encoding : W→E,
        (∏ i,if i∈required then
          network.prob i ((List.ofFn z).take i.val) encoding (z i)-
            g i ((List.ofFn z).take i.val) encoding (z i)
          else if i∈neighbors scope marked then g i ((List.ofFn z).take i.val) encoding (z i)
          else network.prob i ((List.ofFn z).take i.val) encoding (z i)) *
        (∏ w,if w∈marked then (μ w).weight (encoding w)-(ν w).weight (encoding w)
          else (μ w).weight (encoding w))
    else 0 := by
  have hif (errors : Finset (Fin S)) (selected : Finset W) :
      (if required⊆errors ∧ marked⊆selected then
        executionTerm network g operations wires μ ν errors selected z else 0) =
      ∑ encoding : W→E,if required⊆errors ∧ marked⊆selected then
        jointTerm scope operations wires (fun w=>(μ w).weight (encoding w))
          (fun w=>(ν w).weight (encoding w))
          (fun i=>network.prob i ((List.ofFn z).take i.val) encoding (z i))
          (fun i=>g i ((List.ofFn z).take i.val) encoding (z i)) errors selected else 0 := by
    by_cases h : required⊆errors ∧ marked⊆selected <;> simp [h,executionTerm]
  simp_rw [hif]
  simp_rw [Finset.sum_comm (s:=wires.powerset) (t:=Finset.univ)]
  rw [Finset.sum_comm]
  simp_rw [joint_marked_resummation scope operations required wires marked _ _ _ _
    hrequired hmarked hneighbors]
  by_cases h : Disjoint required (neighbors scope marked) <;> simp [h]

/-- A scoped function has the same independent expectation under laws agreeing on its scope. This allows unused private wire labels to differ freely. -/
theorem scoped_expect_eq_of_laws (μ ν : W→FiniteDistribution E) (selected : Finset W)
    (h : ∀ w∈selected,μ w=ν w) (f : (W→E)→ℝ) (hf : Scoped selected f) :
    (independentDistribution μ).expect f=(independentDistribution ν).expect f := by
  let outside : {w // w∉selected}→E := fun _=>Classical.choice inferInstance
  rw [← expect_scope_eq_global μ selected f hf outside,
    ← expect_scope_eq_global ν selected f hf outside]
  congr 1
  congr 1
  funext w
  exact h w w.2

/-- The empty joint coefficient is an independent expectation: approximate designated operations, retain true public samplers, and use ν exactly on the expanded wires. -/
theorem execution_empty (network : ScopedProbabilities (E := E) (A := A) scope)
    (g : Fin S→List A→(W→E)→A→ℝ) (operations : Finset (Fin S)) (wires : Finset W)
    (μ ν : W→FiniteDistribution E) (z : Fin S→A) :
    executionTerm network g operations wires μ ν ∅ ∅ z =
      (independentDistribution (fun w=>if w∈wires then ν w else μ w)).expect (fun encoding=>
        ∏ i,if i∈operations then g i ((List.ofFn z).take i.val) encoding (z i)
          else network.prob i ((List.ofFn z).take i.val) encoding (z i)) := by
  simp only [executionTerm,jointTerm,Finset.empty_subset,if_true,errorScope,
    Finset.biUnion_empty,Finset.sdiff_empty,coordinateTerm,Finset.notMem_empty,if_false,
    FiniteDistribution.expect,independentDistribution]
  apply Finset.sum_congr rfl
  intro encoding he
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro w hw
  split_ifs <;> rfl

/-- The empty term is common when the original encoding laws agree on active wires outside the expanded set. Inactive private inputs need not agree because their independent probability weights sum to one. -/
theorem execution_empty_eq (network : ScopedProbabilities (E := E) (A := A) scope)
    (g : Fin S→List A→(W→E)→A→ℝ)
    (hglocal : ∀ i h a,Scoped (scope i) (fun e=>g i h e a))
    (operations : Finset (Fin S)) (wires : Finset W)
    (μ μ' ν : W→FiniteDistribution E) (z : Fin S→A)
    (hpublic : ∀ w∈Finset.univ.biUnion scope,w∉wires→μ w=μ' w) :
    executionTerm network g operations wires μ ν ∅ ∅ z =
      executionTerm network g operations wires μ' ν ∅ ∅ z := by
  rw [execution_empty,execution_empty]
  apply scoped_expect_eq_of_laws _ _ (Finset.univ.biUnion scope)
  · intro w hw
    by_cases hm : w∈wires
    · simp [hm]
    · simp only [hm,if_false]
      exact hpublic w hw hm
  · intro first second he
    apply Finset.prod_congr rfl
    intro i hi
    have hs : ∀ w∈scope i,first w=second w :=
      fun w hw=>he w (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hw⟩)
    by_cases hm : i∈operations
    · simpa only [hm,if_true] using hglocal i _ _ first second hs
    · simpa only [hm,if_false] using network.locality i _ _ first second hs

end CompilerProof.DirectComposition
