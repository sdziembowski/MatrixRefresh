import Mathlib.Tactic.FinCases
import Proofs.Compiler.LocalComparisons.Framework.NetworkExecution
import Proofs.Compiler.Foundations.LinearAlgebra.FiniteCarrier



/-!
# Ordered three-port tables and circuit wire scopes
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace CircuitCompiler.Composition

open Refresh TableAnalysis

variable {W X : Type*} [DecidableEq W]

/-- Three distinct physical wires form an ordered three-element local scope. -/
/- Mathematical definition (normal notation): For distinct left, right, and output wires, identify indices 0,1,2 with those three wires in that order. This is a bijection onto the gate's scope. -/
noncomputable def threePortEquiv (left right output : W)
    (hlr : left ≠ right) (hlo : left ≠ output) (hro : right ≠ output) :
    Fin 3 ≃ {w // w ∈ ({left, right, output} : Finset W)} :=
  Equiv.ofBijective (fun i => ⟨![left, right, output] i, by fin_cases i <;> simp⟩) (by
    constructor
    · intro i j hij
      have hval := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;> simp_all [Ne.symm hlr, Ne.symm hlo, Ne.symm hro]
    · intro w
      have hw := w.property
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with h | h | h
      · exact ⟨0, Subtype.ext (by simpa using h.symm)⟩
      · exact ⟨1, Subtype.ext (by simpa using h.symm)⟩
      · exact ⟨2, Subtype.ext (by simpa using h.symm)⟩)

/-- The ordered `(left,right,output)` data used by the gate analysis and the scope-indexed data used by composition are exactly equivalent. -/
/- Mathematical definition (normal notation): For distinct gate ports, identify the ordered data triple (x_L,x_R,x_O) with the function assigning these values to the left, right, and output wires in the gate's scope. -/
def tripleScopeEquiv (left right output : W)
    (hlr : left ≠ right) (hlo : left ≠ output) (hro : right ≠ output) :
    ((X × X) × X) ≃ ({w // w ∈ ({left, right, output} : Finset W)} → X) where
  toFun value w := if w.val = left then value.1.1 else if w.val = right then value.1.2 else value.2
  invFun value := ((value ⟨left, by simp⟩, value ⟨right, by simp⟩), value ⟨output, by simp⟩)
  left_inv value := by simp [hlr, hlo, hro, Ne.symm hlr, Ne.symm hlo, Ne.symm hro]
  right_inv value := by
    funext w
    have hw := w.property
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with h | h | h
    · have heq : w = ⟨left, by simp⟩ := Subtype.ext h
      subst w
      simp
    · have heq : w = ⟨right, by simp⟩ := Subtype.ext h
      subst w
      simp [Ne.symm hlr]
    · have heq : w = ⟨output, by simp⟩ := Subtype.ext h
      subst w
      simp [Ne.symm hlo, Ne.symm hro]

/-- The circuit-scope and ordered-port approximations have the same normalized nuclear norm. In particular no dimension factor is incurred by this adapter. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For left, right, output ∈ W; G ∈ ℝ^(((X × X) × X) × ((X × X) × X)), assume X is finite; left ≠ right; left ≠ output; right ≠ output. Then

‖ reindexTable(G, tripleScopeEquiv(left, right, output), tripleScopeEquiv(left, right, output))‖_* = ‖ G‖_*.
-/
theorem tripleScope_tableNuclearNorm [Fintype X] [DecidableEq X]
    (left right output : W) (hlr : left ≠ right) (hlo : left ≠ output) (hro : right ≠ output)
    (G : Matrix ((X × X) × X) ((X × X) × X) ℝ) :
    tableNuclearNorm (reindexTable G (tripleScopeEquiv left right output hlr hlo hro)
      (tripleScopeEquiv left right output hlr hlo hro)) = tableNuclearNorm G :=
  reindexTable_tableNuclearNorm G _ _

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For left, right, output ∈ W; G ∈ ℝ^(((X × X) × X) × ((X × X) × X)), assume X is finite; left ≠ right; left ≠ output; right ≠ output. Then

tableL1(reindexTable(G, tripleScopeEquiv(left, right, output), tripleScopeEquiv(left, right, output))) = tableL1(G).
-/
theorem tripleScope_tableL1 [Fintype X]
    (left right output : W) (hlr : left ≠ right) (hlo : left ≠ output) (hro : right ≠ output)
    (G : Matrix ((X × X) × X) ((X × X) × X) ℝ) :
    tableL1 (reindexTable G (tripleScopeEquiv left right output hlr hlo hro)
      (tripleScopeEquiv left right output hlr hlo hro)) = tableL1 G :=
  reindexTable_tableL1 G _ _

/-- Independent encodings on the three scoped wires are exactly the ordered product distribution used by the full gate approximation. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For left, right, output ∈ W; wireDistribution ∈ W → 𝒟(X), assume X is finite; left ≠ right; left ≠ output; right ≠ output. Then

((tripleScopeEquiv(left, right, output))⁻¹_*independentDistribution(((w ∈ {w | w ∈ {left, right, output}} ↦ wireDistribution(w))))) = ((wireDistribution(left) ⊗ wireDistribution(right)) ⊗ wireDistribution(output)).
-/
theorem tripleScope_product_distribution [Fintype X]
    (left right output : W) (hlr : left ≠ right) (hlo : left ≠ output) (hro : right ≠ output)
    (wireDistribution : W → FiniteDistribution X) :
    (independentDistribution (fun w : {w // w ∈ ({left, right, output} : Finset W)} => wireDistribution w)).map
      (tripleScopeEquiv left right output hlr hlo hro).symm =
      ((wireDistribution left).prod (wireDistribution right)).prod (wireDistribution output) := by
  ext value
  rw [map_equiv_weight]
  change (∏ w : {w // w ∈ ({left, right, output} : Finset W)},
      (wireDistribution w).weight (tripleScopeEquiv left right output hlr hlo hro value w)) =
    ((wireDistribution left).weight value.1.1 * (wireDistribution right).weight value.1.2) *
      (wireDistribution output).weight value.2
  rw [← Equiv.prod_comp (threePortEquiv left right output hlr hlo hro)]
  simp [Fin.prod_univ_three, threePortEquiv, tripleScopeEquiv,
    hlr, hlo, hro, Ne.symm hlr, Ne.symm hlo, Ne.symm hro]

end CircuitCompiler.Composition
