import Proofs.Refreshing.FiniteExpectation

/-!
# Factor-energy bounds for neighboring signed rounds
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RefreshingProof

/-- The expectation of a constant under a finite PMF is that constant. -/
@[simp] theorem pmfMean_const {X : Type*} [Fintype X] (p : PMF X) (c : ℝ) :
    pmfMean p (fun _ => c) = c := by
  unfold pmfMean
  rw [← Finset.sum_mul, sum_pmf_real, one_mul]

/-- The expectation of a pointwise nonnegative real function is nonnegative. -/
theorem pmfMean_nonneg {X : Type*} [Fintype X] (p : PMF X) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ pmfMean p f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg ENNReal.toReal_nonneg (hf x))

/-- Sum factor-index energies before averaging over the common coordinate. -/
theorem product_energy_identity {A B X I J : Type*}
    [Fintype X] [Fintype I] [Fintype J] (μX : PMF X)
    (f : I → A → X → ℝ) (g : J → X → B → ℝ) (a : A) (b : B) :
    (∑ ij : I × J, pmfMean μX (fun x => (f ij.1 a x * g ij.2 x b) ^ 2)) =
      pmfMean μX (fun x => (∑ i, f i a x ^ 2) * (∑ j, g j x b ^ 2)) := by
  rw [← pmfMean_sum]
  apply congrArg (pmfMean μX)
  funext x
  simp only [Fintype.sum_prod_type, mul_pow, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- One pointwise factor-energy bound and the other factor's mean bound control the entire product representation, averaged over both outer states. -/
theorem product_energy_sum_bound {A B X I J : Type*}
    [Fintype A] [Fintype B] [Fintype X] [Fintype I] [Fintype J]
    (μA : PMF A) (μB : PMF B) (μX : PMF X)
    (f : I → A → X → ℝ) (g : J → X → B → ℝ) (P M : ℝ) (hP : 0 ≤ P)
    (hpoint : ∀ a x, (∑ i, f i a x ^ 2) ≤ P)
    (hmean : pmfMean μX (fun x => pmfMean μB (fun b => ∑ j, g j x b ^ 2)) ≤ M) :
    pmfMean μA (fun a => pmfMean μB (fun b =>
      ∑ ij : I × J, pmfMean μX (fun x => (f ij.1 a x * g ij.2 x b) ^ 2))) ≤ P * M := by
  simp_rw [product_energy_identity]
  have hpoint' (a : A) (b : B) :
      pmfMean μX (fun x => (∑ i, f i a x ^ 2) * (∑ j, g j x b ^ 2)) ≤
        P * pmfMean μX (fun x => ∑ j, g j x b ^ 2) := by
    rw [← pmfMean_const_mul]
    apply pmfMean_mono
    intro x
    exact mul_le_mul_of_nonneg_right (hpoint a x) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  calc
    _ ≤ pmfMean μA (fun _ => pmfMean μB (fun b =>
        P * pmfMean μX (fun x => ∑ j, g j x b ^ 2))) :=
      pmfMean_mono _ _ _ (fun a => pmfMean_mono _ _ _ (hpoint' a))
    _ = P * pmfMean μX (fun x => pmfMean μB (fun b => ∑ j, g j x b ^ 2)) := by
      rw [pmfMean_const, pmfMean_const_mul, pmfMean_comm]
    _ ≤ P * M := mul_le_mul_of_nonneg_left hmean hP

/-- Encoding the outer averages and the factor-index sum as one weighted mean. -/
theorem weightedMean_outer_index {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
    (μA : PMF A) (μB : PMF B) (F : A × B × I → ℝ) :
    weightedMean (fun abi : A × B × I => (μA abi.1).toReal * (μB abi.2.1).toReal) F =
      pmfMean μA (fun a => pmfMean μB (fun b => ∑ i, F (a, b, i))) := by
  simp [weightedMean, pmfMean, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- One weighted Cauchy–Schwarz inequality simultaneously averages over the outer encodings and sums over all factors. -/
theorem averaged_factor_cost_le {A B I : Type*}
    [Fintype A] [Fintype B] [Fintype I] (μA : PMF A) (μB : PMF B)
    (u v : I → A → B → ℝ) (hu : ∀ i a b, 0 ≤ u i a b) (hv : ∀ i a b, 0 ≤ v i a b)
    (C : ℝ) (hC : 0 ≤ C)
    (hU : pmfMean μA (fun a => pmfMean μB (fun b => ∑ i, u i a b)) ≤ C)
    (hV : pmfMean μA (fun a => pmfMean μB (fun b => ∑ i, v i a b)) ≤ C) :
    pmfMean μA (fun a => pmfMean μB (fun b =>
      ∑ i, Real.sqrt (u i a b) * Real.sqrt (v i a b))) ≤ C := by
  let w : A × B × I → ℝ := fun abi => (μA abi.1).toReal * (μB abi.2.1).toReal
  let f : A × B × I → ℝ := fun abi => Real.sqrt (u abi.2.2 abi.1 abi.2.1)
  let g : A × B × I → ℝ := fun abi => Real.sqrt (v abi.2.2 abi.1 abi.2.1)
  have hw : ∀ abi, 0 ≤ w abi := fun _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hcs := weighted_cauchy_schwarz w f g hw
  have habs (abi : A × B × I) : |f abi * g abi| = f abi * g abi :=
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hf (abi : A × B × I) : f abi ^ 2 = u abi.2.2 abi.1 abi.2.1 := Real.sq_sqrt (hu _ _ _)
  have hg (abi : A × B × I) : g abi ^ 2 = v abi.2.2 abi.1 abi.2.1 := Real.sq_sqrt (hv _ _ _)
  simp_rw [habs, hf, hg] at hcs
  simp only [w, weightedMean_outer_index] at hcs
  calc
    _ ≤ Real.sqrt (pmfMean μA (fun a => pmfMean μB (fun b => ∑ i, u i a b))) *
        Real.sqrt (pmfMean μA (fun a => pmfMean μB (fun b => ∑ i, v i a b))) := hcs
    _ ≤ Real.sqrt C * Real.sqrt C := mul_le_mul (Real.sqrt_le_sqrt hU) (Real.sqrt_le_sqrt hV)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = C := Real.mul_self_sqrt hC

/-- Product of two local finite representations: a pointwise energy bound P for the first table and mean energy bound M for the second give total averaged factor cost at most P·M. Applied with P=2/β and M=4 this is the paper's 8/β. -/
theorem two_round_factor_cost_bound {A B L R I J : Type*}
    [Fintype A] [Fintype B] [Fintype L] [Fintype R] [Fintype I] [Fintype J]
    (μA : PMF A) (μB : PMF B) (μL : PMF L) (μR : PMF R)
    (l₁ : I → A → L → ℝ) (l₂ : J → L → B → ℝ)
    (r₁ : I → A → R → ℝ) (r₂ : J → R → B → ℝ)
    (P M : ℝ) (hP : 0 ≤ P) (hM : 0 ≤ M)
    (hpointL : ∀ a l, (∑ i, l₁ i a l ^ 2) ≤ P)
    (hpointR : ∀ a r, (∑ i, r₁ i a r ^ 2) ≤ P)
    (hmeanL : pmfMean μL (fun l => pmfMean μB (fun b => ∑ j, l₂ j l b ^ 2)) ≤ M)
    (hmeanR : pmfMean μR (fun r => pmfMean μB (fun b => ∑ j, r₂ j r b ^ 2)) ≤ M) :
    pmfMean μA (fun a => pmfMean μB (fun b => ∑ ij : I × J,
      Real.sqrt (pmfMean μL (fun l => (l₁ ij.1 a l * l₂ ij.2 l b) ^ 2)) *
        Real.sqrt (pmfMean μR (fun r => (r₁ ij.1 a r * r₂ ij.2 r b) ^ 2)))) ≤ P * M := by
  apply averaged_factor_cost_le μA μB _ _
    (fun _ _ _ => pmfMean_nonneg _ _ (fun _ => sq_nonneg _))
    (fun _ _ _ => pmfMean_nonneg _ _ (fun _ => sq_nonneg _)) (P * M) (mul_nonneg hP hM)
  · exact product_energy_sum_bound μA μB μL l₁ l₂ P M hP hpointL hmeanL
  · exact product_energy_sum_bound μA μB μR r₁ r₂ P M hP hpointR hmeanR

end RefreshingProof
