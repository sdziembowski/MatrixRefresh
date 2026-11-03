import Proofs.Compiler.LocalComparisons.GateInterface
import Proofs.Compiler.LocalComparisons.Framework.NetworkExecution
import Proofs.Compiler.Foundations.MatrixRefreshing.Protocol.Endpoints



/-!
# Lifting the local gate estimates to independent network encodings
-/
set_option autoImplicit false

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace CircuitCompiler.AveragedEnergyComparison

open Refresh MatrixRefresh Composition

noncomputable section

-- Auxiliary lemma (hybrid comparison); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X,Y a set; P ∈ 𝒟(X); Q ∈ 𝒟(Y), assume X is finite; Y is finite. Then

((Prod)₁_*(P ⊗ Q)) = P.
-/
private theorem prod_map_fst {X Y : Type*} [Fintype X] [Fintype Y]
    (P : FiniteDistribution X) (Q : FiniteDistribution Y) : (P.prod Q).map Prod.fst = P := by
  classical
  ext x
  rw [map_fst_weight]
  simp only [FiniteDistribution.prod, FiniteDistribution.joint]
  rw [← Finset.mul_sum, Q.total, mul_one]

-- Auxiliary lemma (hybrid comparison); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For W,E a set; distributions ∈ W → 𝒟(E); p ∈ W → Prop, assume W is finite; E is finite; DecidablePred(p). Then

(((x ↦ (w ∈ {w | p(w)} ↦ x(w))))_*independentDistribution(distributions)) = independentDistribution(((w ∈ {w | p(w)} ↦ distributions(w)))).
-/
theorem independentDistribution_select {W E : Type*} [Fintype W] [DecidableEq W]
    [Fintype E] (laws : W → FiniteDistribution E) (p : W → Prop) [DecidablePred p] :
    (independentDistribution laws).map (fun x => fun w : {w // p w} => x w) =
      independentDistribution (fun w : {w // p w} => laws w) := by
  have h := congrArg (fun Q : FiniteDistribution (({w // p w} → E) × ({w // ¬ p w} → E)) =>
    Q.map Prod.fst) (independentDistribution_split laws p)
  rw [FiniteDistribution.map_map, prod_map_fst] at h
  exact h

-- Auxiliary lemma (hybrid comparison); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For W,E a set; distributions ∈ W → 𝒟(E); selected ∈ Finset(W), assume W is finite; E is finite. Then

(((x ↦ (w ∈ {w | w ∈ selected} ↦ x(w))))_*independentDistribution(distributions)) = independentDistribution(((w ∈ {w | w ∈ selected} ↦ distributions(w)))).
-/
theorem independentDistribution_restrict {W E : Type*} [Fintype W] [DecidableEq W]
    [Fintype E] (laws : W → FiniteDistribution E) (selected : Finset W) :
    (independentDistribution laws).map (fun x => fun w : {w // w ∈ selected} => x w) =
      independentDistribution (fun w : {w // w ∈ selected} => laws w) := by
  have h := independentDistribution_select laws (fun w => w ∈ selected)
  have hi : Finset.Subtype.fintype selected = Subtype.fintype (fun w => w ∈ selected) :=
    Subsingleton.elim _ _
  rw [← hi] at h
  exact h

-- Auxiliary lemma (hybrid comparison); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For W,X a set; selected ∈ Finset(W), assume W is finite; X is finite; X ≠ ∅. Then

(((x ↦ (w ∈ {w | w ∈ selected} ↦ x(w))))_*𝒰_(W → X)) = FiniteDistribution.uniform.
-/
theorem uniform_restrict {W X : Type*} [Fintype W] [DecidableEq W]
    [Fintype X] [Nonempty X] (selected : Finset W) :
    (FiniteDistribution.uniform : FiniteDistribution (W → X)).map
      (fun x => fun w : {w // w ∈ selected} => x w) = FiniteDistribution.uniform := by
  rw [← independentDistribution_uniform (W := W)]
  rw [independentDistribution_restrict, independentDistribution_uniform]

-- Auxiliary lemma (hybrid comparison); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For W,X a set; distributions ∈ W → 𝒟((X × X)); selected ∈ Finset(W), assume W is finite; X is finite. Then

(((xy ↦ (((w ∈ {w | w ∈ selected} ↦ (xy)₁(w))), ((w ∈ {w | w ∈ selected} ↦ (xy)₂(w))))))_*groupedDistribution(distributions, (Prod)₁, (Prod)₂)) = groupedDistribution(((w ∈ {w | w ∈ selected} ↦ distributions(w))), (Prod)₁, (Prod)₂).
-/
theorem groupedDistribution_restrict {W X : Type*} [Fintype W] [DecidableEq W]
    [Fintype X] (laws : W → FiniteDistribution (X × X)) (selected : Finset W) :
    (groupedDistribution laws Prod.fst Prod.snd).map
      (fun xy => ((fun w : {w // w ∈ selected} => xy.1 w),
        (fun w : {w // w ∈ selected} => xy.2 w))) =
      groupedDistribution (fun w : {w // w ∈ selected} => laws w) Prod.fst Prod.snd := by
  unfold groupedDistribution
  rw [FiniteDistribution.map_map, ← independentDistribution_restrict laws selected, FiniteDistribution.map_map]
  rfl

variable {W I X A S : Type*} [Fintype W] [DecidableEq W]
  [Fintype X] [Nonempty X]

/- Mathematical definition (normal notation): For label assignment s and gate i, independently sample each encoding on the scope Sᵢ from its wire distribution. Group all left shares into one tuple and all right shares into another. This is the gate's reference port distribution. -/
def networkPortDistribution (scope : I → Finset W) (laws : S → W → FiniteDistribution (X × X))
    (s : S) (i : I) : FiniteDistribution (({w // w ∈ scope i} → X) × ({w // w ∈ scope i} → X)) :=
  groupedDistribution (fun w : {w // w ∈ scope i} => laws s w) Prod.fst Prod.snd

/-- Each per-history, per-answer local table has the concrete gate certificate. Scope embedding, overlap, and arbitrary invalid companion labels are handled by the lifting theorems below, not assumed independent. -/

/- Mathematical definition (normal notation): For every gate i, prefix history h, and answer z, supply a local approximation certificate for the table A_(i,h,z) on the gate's wire scope Sᵢ. The reference distribution samples each scoped wire independently from its label-conditioned encoding distribution. All certificates have the same parameters β,ε, and each chosen signed table and its factors are shared across labels. -/
structure NetworkLocalInterface (scope : I → Finset W)
    (laws : S → W → FiniteDistribution (X × X)) (valid : S → I → Prop)
    (original : (s : S) → (i : I) → List A → A →
      ({w // w ∈ scope i} → X) → ({w // w ∈ scope i} → X) → ℝ)
    (β ε : ℝ) where
  gate : ∀ i h z, GateLocalEstimates (fun s => networkPortDistribution scope laws s i)
    (fun s => valid s i) (fun s => original s i h z) β ε

namespace NetworkLocalInterface

variable {scope : I → Finset W} {laws : S → W → FiniteDistribution (X × X)}
  {valid : S → I → Prop}
  {original : (s : S) → (i : I) → List A → A →
    ({w // w ∈ scope i} → X) → ({w // w ∈ scope i} → X) → ℝ}
  {β ε : ℝ}

/-- Lift to all wires. Product distributions retain overlapping local scopes exactly. -/
/-
Mathematical definition (normal notation): For data ∈ NetworkLocalInterface(scope, distributions, valid, original, β, ε); i ∈ I; h ∈ A*; z ∈ A, define

global(data, i, h, z) := pullback(data.gate(i, h, z))(((s ↦ groupedDistribution(distributions(s), (Prod)₁, (Prod)₂))), ((x ∈ W → X, w ∈ {w | w ∈ scope(i)} ↦ x(w))), ((y ∈ W → X, w ∈ {w | w ∈ scope(i)} ↦ y(w))), ((s ↦ groupedDistribution_restrict(distributions(s), scope(i))))).
-/
def global (data : NetworkLocalInterface scope laws valid original β ε)
    (i : I) (h : List A) (z : A) :
    GateLocalEstimates (fun s => groupedDistribution (laws s) Prod.fst Prod.snd)
      (fun s => valid s i)
      (fun s x y => original s i h z (fun w => x w) (fun w => y w)) β ε :=
  (data.gate i h z).pullback (fun s => groupedDistribution (laws s) Prod.fst Prod.snd)
    (fun (x : W → X) (w : {w // w ∈ scope i}) => x w)
    (fun (y : W → X) (w : {w // w ∈ scope i}) => y w)
    (uniform_restrict (scope i)) (uniform_restrict (scope i))
    (fun s => groupedDistribution_restrict (laws s) (scope i))

end NetworkLocalInterface

end

end CircuitCompiler.AveragedEnergyComparison
