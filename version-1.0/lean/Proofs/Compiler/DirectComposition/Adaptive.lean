import Proofs.Compiler.DirectComposition.Model
import Proofs.Compiler.DirectComposition.Holder
import Proofs.Compiler.LocalComparisons.PatchMarginals

/-!
# Adaptive guard enumeration

All unsigned positions retain their true, normalized adaptive probabilities. Only marked errors and neighbors of marked wire differences are enumerated. Consequently the alphabet loss is controlled by the closed marked neighborhood rather than by the execution length.
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
  [Fintype A] {S : ℕ}

/-- Observing both the history and its hidden sample preserves the full absolute mass of a finite signed execution. -/
theorem observed_identity_norm (P : FiniteDistribution E) (process : ErrorProcess A E S) :
    variationNorm (ErrorProcess.observedWeight P process id) =
      ∑ history, P.expect (fun e => |process.weight history e|) := by
  have hpoint (v : Answers A S × E) :
      ErrorProcess.observedWeight P process id v = P.weight v.2 * process.weight v.1 v.2 := by
    simp [ErrorProcess.observedWeight,FiniteDistribution.pure]
  unfold variationNorm
  simp_rw [hpoint]
  simp only [Fintype.sum_prod_type,FiniteDistribution.expect,abs_mul,
    abs_of_nonneg (P.nonneg _)]

/-- The adaptive guard lemma also controls absolute mass before hidden encodings are discarded. It is the existing scoped isolation theorem with the identity observation. -/
theorem guarded_execution_bound {scope : Fin S → Finset W}
    (network : ScopedProbabilities (E := E) (A := A) scope)
    (table : Fin S → List A → (W → E) → A → ℝ)
    (signed : Finset (Fin S)) (μ : W → FiniteDistribution E)
    (selected : Finset W) (error : ℝ) (herror : 0≤error)
    (hlocal : ∀ outside, ∀ history : Answers A S,
      (independentDistribution (fun w : {w // w∈selected} => μ w)).expect
        (fun inside => |(network.split table signed selected outside).localPart.weight history inside|) ≤ error) :
    (∑ history : Answers A S,
      (independentDistribution μ).expect (fun encoding =>
        |(ErrorProcess.fromTables (network.mixed table signed) (fun _ _ => 1) S []).weight
          history encoding|)) ≤
      (Fintype.card A : ℝ)^(signed.card+(touching scope selected\signed).card)*error := by
  have h := network.observed_network_bound table signed μ selected error herror hlocal id
  rw [observed_identity_norm] at h
  exact h

/-- Replacing the auxiliary signed positions by one leaves precisely the marked error factors in the isolated local product. -/
theorem guarded_local_product {scope : Fin S → Finset W}
    (network : ScopedProbabilities (E := E) (A := A) scope)
    (error : Fin S → List A → (W → E) → A → ℝ)
    (marked erased : Finset (Fin S)) (selected : Finset W)
    (outside : {w // w∉selected}→E) (z : Fin S→A)
    (inside : {w // w∈selected}→E) :
    (network.split (fun i h e a => if i∈marked then error i h e a else 1)
      (marked∪erased) selected outside).localPart.weight ((answersEquiv A S).symm z) inside =
      ∏ i∈marked,error i ((List.ofFn z).take i.val) (joinScope selected inside outside) (z i) := by
  rw [network.split_localPart_product]
  simp

/-- The isolated marked-error product can be bounded under the original independent law because it depends only on the union of the marked scopes. -/
theorem marked_error_local_average {scope : Fin S → Finset W}
    (μ : W → FiniteDistribution E) (marked : Finset (Fin S)) (selected : Finset W)
    (f : Fin S→(W→E)→ℝ) (hlocal : ∀ i,Scoped (scope i) (f i))
    (hcover : ∀ i∈marked,scope i⊆selected)
    (outside : {w // w∉selected}→E) :
    (independentDistribution (fun w : {w // w∈selected}=>μ w)).expect
      (fun inside=>|∏ i∈marked,f i (joinScope selected inside outside)|) =
      (independentDistribution μ).expect (fun encoding=>|∏ i∈marked,f i encoding|) := by
  apply expect_scope_eq_global μ selected (fun encoding=>|∏ i∈marked,f i encoding|) _ outside
  intro first second he
  apply congrArg abs
  apply Finset.prod_congr rfl
  intro i hi
  exact hlocal i first second (fun w hw=>he w (hcover i hi hw))

/-- Incidence-three Hölder applies to any selected set of signed local errors. The number of factors is the number of marks, including the empty marked set. -/
theorem marked_error_holder {scope : Fin S→Finset W}
    (μ : W→FiniteDistribution E) (marked : Finset (Fin S))
    (f : Fin S→(W→E)→ℝ) (hlocal : ∀ i,Scoped (scope i) (f i))
    (hdegree : ∀ w,(Finset.univ.filter (fun i=>w∈scope i)).card≤3)
    (ε : ℝ) (hε : 0≤ε)
    (hmoment : ∀ i∈marked,(independentDistribution μ).expect (fun e=>|f i e|^3)≤ε^3) :
    (independentDistribution μ).expect (fun e=>|∏ i∈marked,f i e|) ≤ ε^marked.card := by
  have hdegree' (w : W) :
      (Finset.univ.filter (fun i : marked=>w∈scope i)).card≤3 := by
    rw [← Fintype.card_subtype]
    calc
      Fintype.card {i : marked // w∈scope i} ≤ Fintype.card {i : Fin S // w∈scope i} :=
        Fintype.card_le_of_injective (fun i=>⟨i.1.1,i.2⟩)
          (by
            intro a b he
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg (fun i : {i : Fin S // w∈scope i}=>i.val) he)
      _ ≤ 3 := by rw [Fintype.card_subtype];exact hdegree w
  have h := scoped_product_le_pow μ (fun i : marked=>scope i)
    (fun i : marked=>fun e=>|f i e|) (fun _ _=>abs_nonneg _)
    (fun i first second he=>congrArg abs (hlocal i first second he)) hdegree' ε hε
    (fun i=>hmoment i i.2)
  simp_rw [← Finset.abs_prod] at h
  have hprod (e : W→E) : (∏ i : marked,f i e)=∏ i∈marked,f i e :=
    Finset.prod_coe_sort marked (fun i=>f i e)
  simp_rw [hprod] at h
  simpa only [Fintype.card_coe] using h

/-- Along a fixed formal answer vector, the mixed execution contains the chosen signed table exactly at its signed positions. -/
theorem mixed_history_product {scope : Fin S→Finset W}
    (network : ScopedProbabilities (E := E) (A := A) scope)
    (table : Fin S→List A→(W→E)→A→ℝ) (signed : Finset (Fin S))
    (z : Fin S→A) (encoding : W→E) :
    (ErrorProcess.fromTables (network.mixed table signed) (fun _ _=>1) S []).weight
      ((answersEquiv A S).symm z) encoding =
      ∏ i,if i∈signed then table i ((List.ofFn z).take i.val) encoding (z i)
        else network.prob i ((List.ofFn z).take i.val) encoding (z i) := by
  rw [ErrorProcess.fromTables_product]
  apply Finset.prod_congr rfl
  intro i hi
  have hp : ((List.ofFn z).take i.val).length=i.val := by
    simp only [List.length_take,List.length_ofFn,min_eq_left (Nat.le_of_lt i.isLt)]
  simp only [List.nil_append,ScopedProbabilities.mixed,hp,dif_pos i.isLt]

/-- Enumerating marked errors and erased neighboring positions costs only their closed guard neighborhood. The third-moment input is local, and every other adaptive answer still sums as a genuine probability. -/
theorem guarded_error_product_bound {scope : Fin S→Finset W}
    (network : ScopedProbabilities (E := E) (A := A) scope)
    (μ : W→FiniteDistribution E) (marked erased : Finset (Fin S))
    (selected : Finset W) (error : Fin S→List A→(W→E)→A→ℝ)
    (hlocal : ∀ i h a,Scoped (scope i) (fun e=>error i h e a))
    (hcover : ∀ i∈marked,scope i⊆selected)
    (hdegree : ∀ w,(Finset.univ.filter (fun i=>w∈scope i)).card≤3)
    (ε : ℝ) (hε : 0≤ε)
    (hmoment : ∀ i∈marked,∀ h a,
      (independentDistribution μ).expect (fun e=>|error i h e a|^3)≤ε^3) :
    (∑ z : Fin S→A,(independentDistribution μ).expect (fun encoding=>
      |∏ i,if i∈marked then error i ((List.ofFn z).take i.val) encoding (z i)
        else if i∈erased then 1 else network.prob i ((List.ofFn z).take i.val) encoding (z i)|)) ≤
      (Fintype.card A : ℝ)^((marked∪erased).card+
        (touching scope selected\(marked∪erased)).card)*ε^marked.card := by
  have hleaf (outside) (history : Answers A S) :
      (independentDistribution (fun w : {w // w∈selected}=>μ w)).expect (fun inside=>
        |(network.split (fun i h e a=>if i∈marked then error i h e a else 1)
          (marked∪erased) selected outside).localPart.weight history inside|)≤ε^marked.card := by
    let z := answersEquiv A S history
    have he : history=(answersEquiv A S).symm z := by simp [z]
    rw [he]
    simp_rw [guarded_local_product]
    rw [marked_error_local_average μ marked selected
      (fun i e=>error i ((List.ofFn z).take i.val) e (z i))
      (fun i=>hlocal i _ _) hcover outside]
    exact marked_error_holder μ marked _ (fun i=>hlocal i _ _) hdegree ε hε
      (fun i hi=>hmoment i hi _ _)
  have h := guarded_execution_bound network
    (fun i h e a=>if i∈marked then error i h e a else 1)
    (marked∪erased) μ selected (ε^marked.card) (pow_nonneg hε _) hleaf
  rw [← Equiv.sum_comp (answersEquiv A S).symm] at h
  simp_rw [mixed_history_product] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro z hz
  apply congrArg (independentDistribution μ).expect
  funext encoding
  apply congrArg abs
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hm : i∈marked <;> by_cases he : i∈erased <;> simp [hm,he]

end CompilerProof.DirectComposition
