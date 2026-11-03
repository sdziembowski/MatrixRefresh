import Proofs.Compiler.LocalComparisons.NetworkInterface
import Proofs.Compiler.LocalComparisons.Framework.ScopedNetwork



/-!
# Independent patch marginals with the complementary encodings fixed
-/
set_option autoImplicit false

set_option maxHeartbeats 1200000

open scoped BigOperators

namespace CircuitCompiler.AveragedEnergyComparison

open Refresh MatrixRefresh Composition

noncomputable section

variable {W E : Type*} [Fintype W] [DecidableEq W] [Fintype E]

/-- A function supported on a patch has exactly the same average when the complement is fixed arbitrarily as when every wire is sampled independently. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For distributions ∈ W → 𝒟(E); selected ∈ Finset(W); f ∈ (W → E) → ℝ; outside ∈ {w | w ∉ selected} → E, assume Scoped(selected, f). Then

𝔼_(inside ← independentDistribution(((w ∈ {w | w ∈ selected} ↦ distributions(w))))) [f(joinScope(selected, inside, outside))] = 𝔼_(v ← independentDistribution(distributions)) [f(v)] .
-/
theorem expect_scope_eq_global (laws : W → FiniteDistribution E) (selected : Finset W)
    (f : (W → E) → ℝ) (hf : Scoped selected f)
    (outside : {w // w ∉ selected} → E) :
    (independentDistribution (fun w : {w // w ∈ selected} => laws w)).expect
      (fun inside => f (joinScope selected inside outside)) =
      (independentDistribution laws).expect f := by
  have hs := independentDistribution_split_reverse laws (fun w => w ∈ selected)
  have hi : Finset.Subtype.fintype selected = Subtype.fintype (fun w => w ∈ selected) :=
    Subsingleton.elim _ _
  rw [← hi] at hs
  rw [hs, expect_map, expect_prod]
  apply congrArg (independentDistribution (fun w : {w // w ∈ selected} => laws w)).expect
  funext inside
  have he (other : {w // w ∉ selected} → E) :
      f (joinScope selected inside other) = f (joinScope selected inside outside) := by
    apply hf
    intro w hw
    rw [joinScope_of_mem selected inside other w hw,
      joinScope_of_mem selected inside outside w hw]
  change f (joinScope selected inside outside) =
    (independentDistribution (fun w : {w // w ∉ selected} => laws w)).expect
      (fun other => f (joinScope selected inside other))
  simp_rw [he]
  rw [FiniteDistribution.expect_const]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For distributions ∈ W → 𝒟(E); selected ∈ Finset(W); f ∈ (W → E) → ℝ; outside ∈ {w | w ∉ selected} → E, assume Scoped(selected, f). Then

‖ ((inside ↦ f(joinScope(selected, inside, outside))))‖_(2,independentDistribution(((w ∈ {w | w ∈ selected} ↦ distributions(w))))) = ‖ f‖_(2,independentDistribution(distributions)).
-/
theorem rms_scope_eq_global (laws : W → FiniteDistribution E) (selected : Finset W)
    (f : (W → E) → ℝ) (hf : Scoped selected f)
    (outside : {w // w ∉ selected} → E) :
    rms (independentDistribution (fun w : {w // w ∈ selected} => laws w))
      (fun inside => f (joinScope selected inside outside)) =
      rms (independentDistribution laws) f := by
  unfold rms
  rw [expect_scope_eq_global laws selected (fun x => f x ^ 2)
    (fun x y h => congrArg (fun t : ℝ => t^2) (hf x y h)) outside]

/-- Grouping the left and right shares only changes coordinates. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X a set; distributions ∈ W → 𝒟((X × X)); f ∈ (W → X) → (W → X) → ℝ, assume X is finite. Then

‖ ((xy ↦ f((xy)₁, (xy)₂)))‖_(2,groupedDistribution(distributions, (Prod)₁, (Prod)₂)) = ‖ ((x ↦ f(((w ↦ (x(w))₁)), ((w ↦ (x(w))₂)))))‖_(2,independentDistribution(distributions)) .
-/
theorem grouped_rms_eq {X : Type*} [Fintype X]
    (laws : W → FiniteDistribution (X × X)) (f : (W → X) → (W → X) → ℝ) :
    rms (groupedDistribution laws Prod.fst Prod.snd) (fun xy => f xy.1 xy.2) =
      rms (independentDistribution laws) (fun x => f (fun w => (x w).1) (fun w => (x w).2)) := by
  simp only [rms, groupedDistribution, expect_map]

end

end CircuitCompiler.AveragedEnergyComparison
