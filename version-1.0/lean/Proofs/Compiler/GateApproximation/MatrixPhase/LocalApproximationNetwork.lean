import Proofs.Compiler.LocalComparisons.Framework.CutoffProbabilityFacts
import Proofs.Compiler.LocalComparisons.Framework.ScopedNetwork



/-!
# Building a scoped network from local gate tables and common factors
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler.Composition

open Refresh CommonTruncation

variable {W X Y A : Type*} [Fintype W] [DecidableEq W]
  [Fintype X] [Fintype Y] [Fintype A] {T : ℕ}

/-- Local data before common truncation. Both original and approximating tables read precisely the local port encodings; factors are chosen independently of the plaintext labels. -/
/- Mathematical definition (normal notation): For each gate i, answer prefix h, and next answer z, specify an original conditional probability p_(i,h,z) and a real approximation G_(i,h,z), both depending only on the gate's local left and right shares. The probabilities are nonnegative and sum to one over z; the approximations come with explicit factors G_(i,h,z) = ∑ⱼ a_(i,h,z,j)b_(i,h,z,j)ᵀ. This record does not itself impose approximation-error or energy bounds. -/
structure LocalApproximationData (scope : Fin T → Finset W) where
  original : (i : Fin T) → List A → A → ({w // w ∈ scope i} → X) →
    ({w // w ∈ scope i} → Y) → ℝ
  approximation : (i : Fin T) → List A → A → ({w // w ∈ scope i} → X) →
    ({w // w ∈ scope i} → Y) → ℝ
  rank : Fin T → List A → ℕ
  left : (i : Fin T) → (history : List A) → A → ({w // w ∈ scope i} → X) →
    Fin (rank i history) → ℝ
  right : (i : Fin T) → (history : List A) → A → ({w // w ∈ scope i} → Y) →
    Fin (rank i history) → ℝ
  original_nonneg : ∀ i history a x y, 0 ≤ original i history a x y
  original_total : ∀ i history x y, (∑ a, original i history a x y) = 1
  reconstruct : ∀ i history a x y,
    approximation i history a x y = ∑ j, left i history a x j * right i history a y j

namespace LocalApproximationData

variable {scope : Fin T → Finset W}

/-- The gate reads left and right coordinates of the same complete encodings. -/
/-
Mathematical definition (normal notation): For i ∈ {0,…,T-1}; encoding ∈ W → X × Y, define

leftPort(i, encoding) := (w ↦ (encoding(w))₁).
-/
def leftPort (i : Fin T) (encoding : W → X × Y) : {w // w ∈ scope i} → X :=
  fun w => (encoding w).1

/-
Mathematical definition (normal notation): For i ∈ {0,…,T-1}; encoding ∈ W → X × Y, define

rightPort(i, encoding) := (w ↦ (encoding(w))₂).
-/
def rightPort (i : Fin T) (encoding : W → X × Y) : {w // w ∈ scope i} → Y :=
  fun w => (encoding w).2

/-- Restricting a local two-sided table to its port coordinates gives an explicitly scoped global answer table. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For i ∈ {0,…,T-1}; table ∈ ({w | w ∈ scope(i)} → X) → ({w | w ∈ scope(i)} → Y) → ℝ, we have

Scoped(scope(i), ((encoding ↦ table(leftPort(i, encoding), rightPort(i, encoding))))).
-/
theorem port_scoped (i : Fin T)
    (table : ({w // w ∈ scope i} → X) → ({w // w ∈ scope i} → Y) → ℝ) :
    Scoped (scope i) (fun encoding => table (leftPort i encoding) (rightPort i encoding)) := by
  intro first second heq
  have hl : leftPort (scope := scope) i first = leftPort (scope := scope) i second :=
    funext (fun w => congrArg Prod.fst (heq w w.property))
  have hr : rightPort (scope := scope) i first = rightPort (scope := scope) i second :=
    funext (fun w => congrArg Prod.snd (heq w w.property))
  change table (leftPort i first) (rightPort i first) = table (leftPort i second) (rightPort i second)
  rw [hl, hr]

/-- Common truncation creates the three actual answer tables used in the network. Every locality and pointwise answer-budget property is proved here. -/
/- Mathematical definition (normal notation): Turn local probabilities and chosen product approximations into three scoped families: the original probability p, its common-cutoff version χ p, and the signed approximation χ G. The cutoff retains only rows and columns with total factor energy at most B ≥ 0. The resulting network records locality, normalization of p, subnormalization of χ p, and the signed-answer budget for χ G. -/
noncomputable def network (data : LocalApproximationData (X := X) (Y := Y) (A := A) scope)
    (B : ℝ) (hB : 0 ≤ B) : ScopedTables (E := X × Y) (A := A) scope B where
  original i history encoding a := data.original i history a (leftPort i encoding) (rightPort i encoding)
  real i history encoding a := cut (data.left i history) (data.right i history) B
    (data.original i history a) (leftPort i encoding) (rightPort i encoding)
  signed i history encoding a := cut (data.left i history) (data.right i history) B
    (data.approximation i history a) (leftPort i encoding) (rightPort i encoding)
  original_nonneg i history encoding a := data.original_nonneg i history a _ _
  original_total i history encoding := data.original_total i history _ _
  real_nonneg i history encoding a := cut_nonneg (data.left i history) (data.right i history) B
    (data.original i history) (data.original_nonneg i history) a _ _
  real_total_le i history encoding := cut_total_le (data.left i history) (data.right i history) B
    (data.original i history) (data.original_total i history) _ _
  signed_budget i history encoding := cut_answer_sum_le (data.left i history) (data.right i history)
    (data.approximation i history) (data.reconstruct i history) B hB _ _
  original_scoped i history a := port_scoped i (data.original i history a)
  real_scoped i history a := port_scoped i
    (cut (data.left i history) (data.right i history) B (data.original i history a))
  signed_scoped i history a := port_scoped i
    (cut (data.left i history) (data.right i history) B (data.approximation i history a))

/-- The global signed table certificate is the restriction of the common-cut local certificate; its budget does not depend on the number of wires. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For data ∈ LocalApproximationData(X = X, Y = Y, A = A, scope); B ∈ ℝ; i ∈ {0,…,T-1}; history ∈ A*; a ∈ A, assume 0 ≤ B. Then

BoundedFactorization(((left ∈ W → X, right ∈ W → Y ↦ signed(data.network(B))(i, history, ((w ↦ (left(w), right(w)))), a))), B) ≠ ∅.
-/
theorem network_factorization
    (data : LocalApproximationData (X := X) (Y := Y) (A := A) scope) (B : ℝ) (hB : 0 ≤ B)
    (i : Fin T) (history : List A) (a : A) :
    Nonempty (BoundedFactorization
      (fun (left : W → X) (right : W → Y) =>
        (data.network B hB).signed i history (fun w => (left w, right w)) a) B) := by
  exact ⟨(cut_factorization (data.left i history) (data.right i history)
    (data.approximation i history) (data.reconstruct i history) B hB a).restrict
      (fun (left : W → X) (w : {w // w ∈ scope i}) => left w)
      (fun (right : W → Y) (w : {w // w ∈ scope i}) => right w)⟩

/-- Fixing encodings outside a gate leaves exactly the supplied local ports. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For i ∈ {0,…,T-1}; inside ∈ {w | w ∈ scope(i)} → X × Y; outside ∈ {w | w ∉ scope(i)} → X × Y, we have

leftPort(i, joinScope(scope(i), inside, outside)) = (w ↦ (inside(w))₁).
-/
theorem leftPort_joinScope (i : Fin T) (inside : {w // w ∈ scope i} → X × Y)
    (outside : {w // w ∉ scope i} → X × Y) :
    leftPort i (joinScope (scope i) inside outside) = fun w => (inside w).1 := by
  funext w
  simp [leftPort, joinScope_of_mem, w.property]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For i ∈ {0,…,T-1}; inside ∈ {w | w ∈ scope(i)} → X × Y; outside ∈ {w | w ∉ scope(i)} → X × Y, we have

rightPort(i, joinScope(scope(i), inside, outside)) = (w ↦ (inside(w))₂).
-/
theorem rightPort_joinScope (i : Fin T) (inside : {w // w ∈ scope i} → X × Y)
    (outside : {w // w ∉ scope i} → X × Y) :
    rightPort i (joinScope (scope i) inside outside) = fun w => (inside w).2 := by
  funext w
  simp [rightPort, joinScope_of_mem, w.property]

/-- Independent complete port encodings grouped into their left and right share vectors. -/
/-
Mathematical definition (normal notation): For wireDistribution ∈ W → 𝒟((X × Y)); i ∈ {0,…,T-1}, define

portDistribution(wireDistribution, i) := (((encoding ↦ ((w ↦ (encoding(w))₁), (w ↦ (encoding(w))₂))))_*independentDistribution(((w ∈ {w | w ∈ scope(i)} ↦ wireDistribution(w))))).
-/
noncomputable def portDistribution (wireDistribution : W → FiniteDistribution (X × Y)) (i : Fin T) :
    FiniteDistribution (({w // w ∈ scope i} → X) × ({w // w ∈ scope i} → Y)) :=
  (independentDistribution (fun w : {w // w ∈ scope i} => wireDistribution w)).map
    (fun encoding => (fun w => (encoding w).1, fun w => (encoding w).2))

/-- Original local approximation error supplies the fixed-answer forcing error of the actual network after applying the common mask. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For data ∈ LocalApproximationData(X = X, Y = Y, A = A, scope); B ∈ ℝ; wireDistribution ∈ W → 𝒟((X × Y)); i ∈ {0,…,T-1}; history ∈ A*; η ∈ ℝ; outside ∈ {w | w ∉ scope(i)} → X × Y; a ∈ A, assume 0 ≤ B; (∑ₐ (𝔼_(xy ← portDistribution(wireDistribution, i)) [|data.original(i, history, a, (xy)₁, (xy)₂) - data.approximation(i, history, a, (xy)₁, (xy)₂)|])) ≤ η. Then

𝔼_(inside ← independentDistribution(((w ∈ {w | w ∈ scope(i)} ↦ wireDistribution(w))))) [|signed(data.network(B))(i, history, joinScope(scope(i), inside, outside), a) - real(data.network(B))(i, history, joinScope(scope(i), inside, outside), a)|] ≤ η.
-/
theorem network_approximation_error
    (data : LocalApproximationData (X := X) (Y := Y) (A := A) scope) (B : ℝ) (hB : 0 ≤ B)
    (wireDistribution : W → FiniteDistribution (X × Y)) (i : Fin T) (history : List A) (η : ℝ)
    (herror : (∑ a, (portDistribution wireDistribution i).expect (fun xy =>
      |data.original i history a xy.1 xy.2 - data.approximation i history a xy.1 xy.2|)) ≤ η)
    (outside : {w // w ∉ scope i} → X × Y) (a : A) :
    (independentDistribution (fun w : {w // w ∈ scope i} => wireDistribution w)).expect (fun inside =>
      |(data.network B hB).signed i history (joinScope (scope i) inside outside) a -
        (data.network B hB).real i history (joinScope (scope i) inside outside) a|) ≤ η := by
  have h := (cut_fixed_answer_error_le (data.left i history) (data.right i history) B
    (data.original i history) (data.approximation i history) (portDistribution wireDistribution i) a).trans herror
  simpa only [network, leftPort_joinScope, rightPort_joinScope, portDistribution, MatrixRefresh.expect_map] using h

/-- A local common-mask failure bound gives exactly the truncation error required by the concrete canonical-network composition theorem. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For data ∈ LocalApproximationData(X = X, Y = Y, A = A, scope); B ∈ ℝ; wireDistribution ∈ W → 𝒟((X × Y)); i ∈ {0,…,T-1}; history ∈ A*; β ∈ ℝ; outside ∈ {w | w ∉ scope(i)} → X × Y; a ∈ A, assume 0 ≤ B; 𝔼_(xy ← portDistribution(wireDistribution, i)) [{ 0 if energy(data.left(i, history), (xy)₁) ≤ B ∧ energy(data.right(i, history), (xy)₂) ≤ B,; 1 otherwise }] ≤ β. Then

𝔼_(inside ← independentDistribution(((w ∈ {w | w ∈ scope(i)} ↦ wireDistribution(w))))) [|original(data.network(B))(i, history, joinScope(scope(i), inside, outside), a) - real(data.network(B))(i, history, joinScope(scope(i), inside, outside), a)|] ≤ β.
-/
theorem network_truncation_error
    (data : LocalApproximationData (X := X) (Y := Y) (A := A) scope) (B : ℝ) (hB : 0 ≤ B)
    (wireDistribution : W → FiniteDistribution (X × Y)) (i : Fin T) (history : List A) (β : ℝ)
    (hbad : (portDistribution wireDistribution i).expect (fun xy =>
      if energy (data.left i history) xy.1 ≤ B ∧ energy (data.right i history) xy.2 ≤ B
      then 0 else 1) ≤ β)
    (outside : {w // w ∉ scope i} → X × Y) (a : A) :
    (independentDistribution (fun w : {w // w ∈ scope i} => wireDistribution w)).expect (fun inside =>
      |(data.network B hB).original i history (joinScope (scope i) inside outside) a -
        (data.network B hB).real i history (joinScope (scope i) inside outside) a|) ≤ β := by
  have h := (cut_original_answer_error_le_bad (data.left i history) (data.right i history) B
    (data.original i history) (data.original_nonneg i history) (data.original_total i history)
      (portDistribution wireDistribution i) a).trans hbad
  simpa only [network, leftPort_joinScope, rightPort_joinScope, portDistribution, MatrixRefresh.expect_map] using h

end LocalApproximationData

end CircuitCompiler.Composition
