import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.LocalComparisons.FactorEnergies
/-!
# Local approximation and factor-energy certificates

All quantitative fields are conclusions of the concrete matrix and shortening analysis. The interface retains one chosen representation for all labels; only the reference encoding distribution and the true answer table depend on labels.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace CircuitCompiler.AveragedEnergyComparison
open Refresh MatrixRefresh TableAnalysis
noncomputable section
namespace Factors
variable {X Y : Type*} {f : X → Y → ℝ}
def one : Factors (fun (_ : X) (_ : Y) => (1 : ℝ)) where
  rank := 1
  left _ _ := 1
  right _ _ := 1
  reconstruct _ _ := by simp
@[simp] theorem one_leftEnergy (x : X) : (one (X := X) (Y := Y)).leftEnergy x = 1 := by
  simp [one, leftEnergy, Finset.card_univ, Fintype.card_fin]
@[simp] theorem one_rightEnergy (y : Y) : (one (X := X) (Y := Y)).rightEnergy y = 1 := by
  simp [one, rightEnergy, Finset.card_univ, Fintype.card_fin]
theorem abs_le_energy (a : Factors f) (x : X) (y : Y) :
    |f x y| ≤ Real.sqrt (a.leftEnergy x) * Real.sqrt (a.rightEnergy y) := by
  rw [a.reconstruct]
  exact abs_sum_mul_le (a.left x) (a.right y)
theorem abs_le_of_energy (a : Factors f) (H : ℝ) (hH : 0 ≤ H)
    (hl : ∀ x, a.leftEnergy x ≤ H) (hr : ∀ y, a.rightEnergy y ≤ H)
    (x : X) (y : Y) : |f x y| ≤ H := by
  apply (a.abs_le_energy x y).trans
  calc
    _ ≤ Real.sqrt H * Real.sqrt H := mul_le_mul
      (Real.sqrt_le_sqrt (hl x)) (Real.sqrt_le_sqrt (hr y))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = H := Real.mul_self_sqrt hH
end Factors
namespace GateLocalEstimates
variable {X Y S : Type*} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    {laws : S → FiniteDistribution (X × X)} {valid : S → Prop}
    {original : S → X → X → ℝ} {β ε : ℝ}
/-- Lifting a gate to a larger wire set preserves its estimates whenever the selected ports have their original distributions. This also applies after fixing all encodings outside a patch containing those ports. -/
/- Mathematical definition (normal notation): Pull a local certificate back along left/right maps preserving uniform marginals and the label-conditioned joint distributions. The new approximation is G'(x,y) = G(ℓ(x),r(y)), with composed factors; the parameters β,ε and all energy bounds remain the same. -/
def pullback (data : GateLocalEstimates laws valid original β ε)
    (target : S → FiniteDistribution (Y × Y)) (left right : Y → X)
    (hl : (FiniteDistribution.uniform : FiniteDistribution Y).map left = FiniteDistribution.uniform)
    (hr : (FiniteDistribution.uniform : FiniteDistribution Y).map right = FiniteDistribution.uniform)
    (hjoint : ∀ s, (target s).map (fun xy => (left xy.1,right xy.2)) = laws s) :
    GateLocalEstimates target valid
      (fun s x y => original s (left x) (right y)) β ε where
  approximation x y := data.approximation (left x) (right y)
  factors := data.factors.restrict left right
  left_max x := data.left_max _
  right_max y := data.right_max _
  left_mean := by
    change FiniteDistribution.uniform.expect (fun x => data.factors.leftEnergy (left x)) ≤ 8
    rw [← expect_map, hl]
    exact data.left_mean
  right_mean := by
    change FiniteDistribution.uniform.expect (fun y => data.factors.rightEnergy (right y)) ≤ 8
    rw [← expect_map, hr]
    exact data.right_mean
  all_labels_rms s := by
    have h := data.all_labels_rms s
    rw [← hjoint s] at h
    simpa only [rms, expect_map] using h
  valid_error_rms s hv := by
    have h := data.valid_error_rms s hv
    rw [← hjoint s] at h
    simpa only [rms, expect_map] using h
theorem abs_le (data : GateLocalEstimates laws valid original β ε)
    (hβ : 0 < β) (x y : X) : |data.approximation x y| ≤ 2 / β :=
  data.factors.abs_le_of_energy _ (by positivity) data.left_max data.right_max x y
end GateLocalEstimates
end
end CircuitCompiler.AveragedEnergyComparison
