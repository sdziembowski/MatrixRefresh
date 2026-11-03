import Proofs.Compiler.DirectComposition.Activities
import Proofs.Compiler.DirectComposition.ExecutionExpansion

/-!
# Local-error marks and wire marks

The two kinds of marks share one finite index type only for inclusion–exclusion. Splitting that index recovers exactly the protected joint expansion, without identifying operation errors with wire differences.
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

/-- Inclusion of mixed marks is equivalent to the two separate inclusions. -/
theorem mixed_marks_subset (J U : Finset (Fin S⊕W)) :
    J⊆U ↔ J.toLeft⊆U.toLeft ∧ J.toRight⊆U.toRight := by
  calc
    J⊆U ↔ J⊆U.toLeft.disjSum U.toRight := by rw [Finset.toLeft_disjSum_toRight]
    _ ↔ _ := Finset.subset_disjSum

/-- A mixed marked sum is exactly the double marked sum of operation errors and encoding differences. -/
theorem mixed_marked_sum (operations : Finset (Fin S)) (wires : Finset W)
    (term : Finset (Fin S)→Finset W→ℝ) (J : Finset (Fin S⊕W)) :
    markedSum (operations.disjSum wires) (fun U=>term U.toLeft U.toRight) J =
      ∑ errors∈operations.powerset,∑ marked∈wires.powerset,
        if J.toLeft⊆errors ∧ J.toRight⊆marked then term errors marked else 0 := by
  unfold markedSum
  simp_rw [mixed_marks_subset]
  exact sum_powerset_disjSum operations wires
    (fun errors marked=>if J.toLeft⊆errors ∧ J.toRight⊆marked then term errors marked else 0)

/-- The product of mixed activities is the local-error activity to its number of marks times the wire activity to its number of marks. -/
theorem mixed_activity_product (errorActivity wireActivity : ℝ) (J : Finset (Fin S⊕W)) :
    (∏ m∈J,Sum.elim (fun _=>errorActivity) (fun _=>wireActivity) m) =
      errorActivity^J.toLeft.card*wireActivity^J.toRight.card := by
  calc
    _ = (∏ m∈J.toLeft.disjSum J.toRight,
      Sum.elim (fun _=>errorActivity) (fun _=>wireActivity) m) := by
        rw [Finset.toLeft_disjSum_toRight]
    _ = _ := by rw [Finset.prod_disjSum];simp

/-- The sum of mixed activities counts each approximated operation and each active nonpublic wire exactly once. -/
theorem mixed_activity_sum (operations : Finset (Fin S)) (wires : Finset W)
    (errorActivity wireActivity : ℝ) :
    (∑ m∈operations.disjSum wires,Sum.elim (fun _=>errorActivity) (fun _=>wireActivity) m) =
      operations.card*errorActivity+wires.card*wireActivity := by
  rw [Finset.sum_disjSum]
  simp

/-- The expansion indexed by mixed marks equals the original canonical history weight. -/
theorem mixed_execution_expansion (network : ScopedProbabilities (E := E) (A := A) scope)
    (g : Fin S→List A→(W→E)→A→ℝ) (operations : Finset (Fin S)) (wires : Finset W)
    (μ ν : W→FiniteDistribution E) (z : Fin S→A) :
    (∑ U∈(operations.disjSum wires).powerset,
      executionTerm network g operations wires μ ν U.toLeft U.toRight z) =
    (independentDistribution μ).expect (fun encoding=>
      ∏ i,network.prob i ((List.ofFn z).take i.val) encoding (z i)) := by
  exact (sum_powerset_disjSum operations wires
    (fun errors marked=>executionTerm network g operations wires μ ν errors marked z)).trans
      (execution_expansion network g operations wires μ ν z)

end CompilerProof.DirectComposition
