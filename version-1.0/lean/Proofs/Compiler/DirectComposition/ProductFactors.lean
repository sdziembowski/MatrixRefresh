import Proofs.Compiler.DirectComposition.TensorDiscrepancy

/-!
# Products of chosen local factor representations

Multiply the local product representations before summing over marked-wire coordinates with their signed weights. Their left and right energies multiply exactly, even when scopes overlap. Fixing outside coordinates is only a pullback of those same factors, so a pointwise energy bound survives that restriction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.DirectComposition

open CircuitCompiler.AveragedEnergyComparison

variable {I X Y : Type*} [Fintype I]

/-- Tensor the finite factor indices to represent the pointwise product of all local tables. -/
def productFactors (f : I → X → Y → ℝ) (a : ∀ i, Factors (f i)) :
    Factors (fun x y => ∏ i, f i x y) where
  rank := Fintype.card (∀ i, Fin (a i).rank)
  left x j := ∏ i, (a i).left x ((Fintype.equivFin (∀ i, Fin (a i).rank)).symm j i)
  right y j := ∏ i, (a i).right y ((Fintype.equivFin (∀ i, Fin (a i).rank)).symm j i)
  reconstruct x y := by
    simp_rw [(a _).reconstruct]
    rw [Fintype.prod_sum]
    rw [← Equiv.sum_comp (Fintype.equivFin (∀ i, Fin (a i).rank))]
    simp only [Equiv.symm_apply_apply,← Finset.prod_mul_distrib]

/-- The left energy of the multiplied representation is the product of the individual left energies. -/
theorem productFactors_leftEnergy (f : I → X → Y → ℝ) (a : ∀ i, Factors (f i)) (x : X) :
    (productFactors f a).leftEnergy x = ∏ i, (a i).leftEnergy x := by
  unfold Factors.leftEnergy productFactors
  rw [← Equiv.sum_comp (Fintype.equivFin (∀ i, Fin (a i).rank))]
  simp only [Equiv.symm_apply_apply]
  simp_rw [← Finset.prod_pow]
  exact (Fintype.prod_sum (fun i j => (a i).left x j ^ 2)).symm

/-- The right energy obeys the same product identity. -/
theorem productFactors_rightEnergy (f : I → X → Y → ℝ) (a : ∀ i, Factors (f i)) (y : Y) :
    (productFactors f a).rightEnergy y = ∏ i, (a i).rightEnergy y := by
  unfold Factors.rightEnergy productFactors
  rw [← Equiv.sum_comp (Fintype.equivFin (∀ i, Fin (a i).rank))]
  simp only [Equiv.symm_apply_apply]
  simp_rw [← Finset.prod_pow]
  exact (Fintype.prod_sum (fun i j => (a i).right y j ^ 2)).symm

/-- Fixing outside coordinates preserves the uniform pointwise left-energy budget of the product. -/
theorem productFactors_restrict_left_le {X' Y' : Type*}
    (f : I → X → Y → ℝ) (a : ∀ i, Factors (f i))
    (left : X' → X) (right : Y' → Y) (B : ℝ)
    (h : ∀ i x, (a i).leftEnergy x ≤ B) (x : X') :
    ((productFactors f a).restrict left right).leftEnergy x ≤ B ^ Fintype.card I := by
  change (productFactors f a).leftEnergy (left x) ≤ _
  rw [productFactors_leftEnergy]
  calc
    _ ≤ ∏ _ : I, B := Finset.prod_le_prod₀
      (fun i _ => (a i).leftEnergy_nonneg (left x)) (fun i _ => h i (left x))
    _ = _ := by simp

/-- Fixing outside coordinates also preserves the right-energy budget. -/
theorem productFactors_restrict_right_le {X' Y' : Type*}
    (f : I → X → Y → ℝ) (a : ∀ i, Factors (f i))
    (left : X' → X) (right : Y' → Y) (B : ℝ)
    (h : ∀ i y, (a i).rightEnergy y ≤ B) (y : Y') :
    ((productFactors f a).restrict left right).rightEnergy y ≤ B ^ Fintype.card I := by
  change (productFactors f a).rightEnergy (right y) ≤ _
  rw [productFactors_rightEnergy]
  calc
    _ ≤ ∏ _ : I, B := Finset.prod_le_prod₀
      (fun i _ => (a i).rightEnergy_nonneg (right y)) (fun i _ => h i (right y))
    _ = _ := by simp

/-- The signed weighted sum of the marked-wire tensor against a product of r locally bounded tables costs at most δ^|W| · B^r, for every fixed outside assignment. -/
theorem tensor_productFactors_le {E W : Type*} [Fintype E] [Nonempty E] [Fintype W]
    (D : W → E → E → ℝ) (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hD : ∀ w (u v : E → ℝ),
      |∑ x, ∑ y, D w x y * u x * v y| ≤
        δ * Real.sqrt ((Refresh.FiniteDistribution.uniform : Refresh.FiniteDistribution E).expect
          (fun x => u x ^ 2)) *
          Real.sqrt ((Refresh.FiniteDistribution.uniform : Refresh.FiniteDistribution E).expect
            (fun x => v x ^ 2)))
    (f : I → X → Y → ℝ) (a : ∀ i, Factors (f i))
    (left : (W → E) → X) (right : (W → E) → Y)
    (hleft : ∀ i x, (a i).leftEnergy x ≤ B)
    (hright : ∀ i y, (a i).rightEnergy y ≤ B) :
    |∑ l, ∑ r, (∏ w, D w (l w) (r w)) * ∏ i, f i (left l) (right r)| ≤
      δ ^ Fintype.card W * B ^ Fintype.card I := by
  exact tensor_factors_pairing_le D δ (B ^ Fintype.card I) hδ (pow_nonneg hB _) hD _
    ((productFactors f a).restrict left right)
    (productFactors_restrict_left_le f a left right B hleft)
    (productFactors_restrict_right_le f a left right B hright)

end CompilerProof.DirectComposition
