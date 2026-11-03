import Proofs.Compiler.Direct.Canonical
import Proofs.Compiler.DirectComposition.Model

/-!
# The normalized physical canonical transcript

A complete chronological answer vector is only a bijective presentation of the existing recursive answer history. Its probability is the independent-wire expectation of the adaptive product of the actual conditional answer tables. This connects the generic composition theorem to a normalized distribution obtained from the physical protocol.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.Direct
open Refresh MatrixRefresh CircuitCompiler CircuitCompiler.Operations
  CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution
  CircuitCompiler.AveragedEnergyComparison CompilerProof.DirectComposition

variable {F E A : Type*} [Mul F] [Sub F] [Fintype E] [DecidableEq E]
  [Fintype A] {P S : ℕ}

/-- The true normalized canonical experiment returns just the chronological answer vector and hides every sampled wire encoding. -/
def flatCanonical (protocol : Operations.Protocol F E A P) (hlocal : protocol.Local)
    (defaultAnswer : A) (program : Operations.Program F P S) (law : F → FiniteDistribution E)
    (label : Fin (P+S) → F) : FiniteDistribution (Fin S → A) :=
  protocol.canonicalNetworkView hlocal defaultAnswer program law label
    (fun state=>(answersEquiv A S) state.1)

/-- At a complete vector, the recursive canonical answer table is exactly the product with its true chronological prefixes. -/
theorem canonical_product (protocol : Operations.Protocol F E A P) (hlocal : protocol.Local)
    (defaultAnswer : A) (program : Operations.Program F P S)
    (z : Fin S → A) (encoding : Fin (P+S) → E) :
    (ErrorProcess.fromTables
      ((protocol.probabilities hlocal defaultAnswer program).mixed (fun _ _ _ _=>0) ∅)
      (fun _ _=>1) S []).weight ((answersEquiv A S).symm z) encoding=
      ∏ i, ((protocol.probabilities hlocal defaultAnswer program).prob
        i ((List.ofFn z).take i.val) encoding (z i)) := by
  rw [ErrorProcess.fromTables_product]
  apply Finset.prod_congr rfl
  intro i hi
  have hlen : ((List.ofFn z).take i.val).length=i.val := by
    simp only [List.length_take,List.length_ofFn,min_eq_left (Nat.le_of_lt i.isLt)]
  simp [List.nil_append,ScopedProbabilities.mixed,hlen,i.isLt]

/-- The weight of the normalized physical canonical transcript is precisely the scalar independent-wire weight used by direct composition. -/
theorem flatCanonical_weight {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (protocol : Operations.Protocol F (X×X) A P) (hlocal : protocol.Local)
    (defaultAnswer : A) (program : Operations.Program F P S)
    (law : F → FiniteDistribution (X×X)) (label : Fin (P+S) → F) (z : Fin S → A) :
    (flatCanonical protocol hlocal defaultAnswer program law label).weight z=
      canonicalWeight program.scope (protocol.probabilities hlocal defaultAnswer program) law label z := by
  unfold flatCanonical
  rw [protocol.canonicalNetworkView_weight hlocal defaultAnswer program law label _ (fun _ _ _ _=>0)]
  rw [ErrorProcess.observedWeight_history]
  have he (x : Answers A S) : z=(answersEquiv A S) x ↔ x=(answersEquiv A S).symm z := by
    constructor
    · intro h
      simpa using (congrArg (answersEquiv A S).symm h).symm
    · intro h
      rw [h,Equiv.apply_symm_apply]
  simp only [FiniteDistribution.pure,mul_ite,mul_one,mul_zero,he,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true]
  unfold canonicalWeight historyWeight
  congr 1
  funext encoding
  exact canonical_product protocol hlocal defaultAnswer program z encoding

/-- Observing a canonical transcript as a vector or as a recursive history gives exactly the same distribution under the canonical answer bijection. -/
theorem flatCanonical_eq_map (protocol : Operations.Protocol F E A P) (hlocal : protocol.Local)
    (defaultAnswer : A) (program : Operations.Program F P S) (law : F → FiniteDistribution E)
    (label : Fin (P+S) → F) :
    flatCanonical protocol hlocal defaultAnswer program law label=
      (protocol.canonicalNetworkView hlocal defaultAnswer program law label Prod.fst).map
        (answersEquiv A S) := by
  unfold flatCanonical Operations.Protocol.canonicalNetworkView ScopedTables.canonicalDistribution
  rw [FiniteDistribution.map_map]
  rfl

end CompilerProof.Direct
