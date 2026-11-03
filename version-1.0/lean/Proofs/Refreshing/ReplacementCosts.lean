import Proofs.Refreshing.FactorEnergy

/-!
# Local L₂ replacement estimates on actual product probability spaces
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RefreshingProof

/-- The absolute value of a finite PMF expectation is at most the expectation of the absolute value. -/
theorem pmfMean_abs_le {X : Type*} [Fintype X] (p : PMF X) (f : X → ℝ) :
    |pmfMean p f| ≤ pmfMean p (fun x => |f x|) := by
  unfold pmfMean
  calc
    _ ≤ ∑ x, |(p x).toReal * f x| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]

/-- A weighted mean with product PMF weights equals two iterated independent expectations. -/
theorem weightedMean_two {A B : Type*} [Fintype A] [Fintype B]
    (μA : PMF A) (μB : PMF B) (F : A × B → ℝ) :
    weightedMean (fun ab : A × B => (μA ab.1).toReal * (μB ab.2).toReal) F =
      pmfMean μA (fun a => pmfMean μB (fun b => F (a, b))) := by
  simp [weightedMean, pmfMean, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- A weighted mean with three product PMF weights equals three iterated independent expectations. -/
theorem weightedMean_three {A X B : Type*} [Fintype A] [Fintype X] [Fintype B]
    (μA : PMF A) (μX : PMF X) (μB : PMF B) (F : A × X × B → ℝ) :
    weightedMean (fun axb : A × X × B =>
      (μA axb.1).toReal * (μX axb.2.1).toReal * (μB axb.2.2).toReal) F =
      pmfMean μA (fun a => pmfMean μX (fun x => pmfMean μB (fun b => F (a, x, b)))) := by
  simp [weightedMean, pmfMean, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- Replace the second round while the first is a signed companion. -/
theorem replacement_second_table {A X B : Type*} [Fintype A] [Fintype X] [Fintype B]
    (μA : PMF A) (μX : PMF X) (μB : PMF B) (e : X → B → ℝ) (g : A → X → ℝ)
    (ε : ℝ)
    (he : Real.sqrt (pmfMean μX (fun x => pmfMean μB (fun b => e x b ^ 2))) ≤ ε)
    (hg : Real.sqrt (pmfMean μA (fun a => pmfMean μX (fun x => g a x ^ 2))) ≤ 6) :
    pmfMean μA (fun a => pmfMean μB (fun b =>
      |pmfMean μX (fun x => e x b * g a x)|)) ≤ 6 * ε := by
  let w : A × X × B → ℝ := fun axb =>
    (μA axb.1).toReal * (μX axb.2.1).toReal * (μB axb.2.2).toReal
  have hw : ∀ axb, 0 ≤ w axb := fun _ => by dsimp [w]; positivity
  have he' : Real.sqrt (weightedMean w (fun axb => e axb.2.1 axb.2.2 ^ 2)) ≤ ε := by
    simpa only [w, weightedMean_three, pmfMean_const] using he
  have hg' : Real.sqrt (weightedMean w (fun axb => g axb.1 axb.2.1 ^ 2)) ≤ 6 := by
    simpa only [w, weightedMean_three, pmfMean_const] using hg
  have hcs := replacement_with_companion w (fun axb => e axb.2.1 axb.2.2)
    (fun axb => g axb.1 axb.2.1) ε hw he' hg'
  have hcost : pmfMean μA (fun a => pmfMean μX (fun x => pmfMean μB (fun b =>
      |e x b * g a x|))) ≤ 6 * ε := by
    simpa only [w, weightedMean_three] using hcs
  have hj := pmfMean_mono μA _ _ (fun a => pmfMean_mono μB _ _
    (fun b => pmfMean_abs_le μX (fun x => e x b * g a x)))
  simp_rw [pmfMean_comm μB μX] at hj
  exact hj.trans hcost

/-- Replace the first round while the second is a signed companion. -/
theorem replacement_first_table {A X B : Type*} [Fintype A] [Fintype X] [Fintype B]
    (μA : PMF A) (μX : PMF X) (μB : PMF B) (e : A → X → ℝ) (g : X → B → ℝ)
    (ε : ℝ)
    (he : Real.sqrt (pmfMean μA (fun a => pmfMean μX (fun x => e a x ^ 2))) ≤ ε)
    (hg : Real.sqrt (pmfMean μX (fun x => pmfMean μB (fun b => g x b ^ 2))) ≤ 6) :
    pmfMean μA (fun a => pmfMean μB (fun b =>
      |pmfMean μX (fun x => e a x * g x b)|)) ≤ 6 * ε := by
  let w : A × X × B → ℝ := fun axb =>
    (μA axb.1).toReal * (μX axb.2.1).toReal * (μB axb.2.2).toReal
  have hw : ∀ axb, 0 ≤ w axb := fun _ => by dsimp [w]; positivity
  have he' : Real.sqrt (weightedMean w (fun axb => e axb.1 axb.2.1 ^ 2)) ≤ ε := by
    simpa only [w, weightedMean_three, pmfMean_const] using he
  have hg' : Real.sqrt (weightedMean w (fun axb => g axb.2.1 axb.2.2 ^ 2)) ≤ 6 := by
    simpa only [w, weightedMean_three, pmfMean_const] using hg
  have hcs := replacement_with_companion w (fun axb => e axb.1 axb.2.1)
    (fun axb => g axb.2.1 axb.2.2) ε hw he' hg'
  have hcost : pmfMean μA (fun a => pmfMean μX (fun x => pmfMean μB (fun b =>
      |e a x * g x b|))) ≤ 6 * ε := by
    simpa only [w, weightedMean_three] using hcs
  have hj := pmfMean_mono μA _ _ (fun a => pmfMean_mono μB _ _
    (fun b => pmfMean_abs_le μX (fun x => e a x * g x b)))
  simp_rw [pmfMean_comm μB μX] at hj
  exact hj.trans hcost

/-- Endpoint replacement with no signed companion. -/
theorem replacement_no_companion {A B : Type*} [Fintype A] [Fintype B]
    (μA : PMF A) (μB : PMF B) (e : A → B → ℝ) (ε : ℝ)
    (he : Real.sqrt (pmfMean μA (fun a => pmfMean μB (fun b => e a b ^ 2))) ≤ ε) :
    pmfMean μB (fun b => |pmfMean μA (fun a => e a b)|) ≤ ε := by
  let w : A × B → ℝ := fun ab => (μA ab.1).toReal * (μB ab.2).toReal
  have hw : ∀ ab, 0 ≤ w ab := fun _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have he' : Real.sqrt (weightedMean w (fun ab => e ab.1 ab.2 ^ 2)) ≤ ε := by
    simpa only [w, weightedMean_two] using he
  have hn : weightedMean w (fun _ => 1) = 1 := by
    simp only [w, weightedMean_two, pmfMean_const]
  have hcs := replacement_without_companion w (fun ab => e ab.1 ab.2) ε hw hn he'
  have hcost : pmfMean μA (fun a => pmfMean μB (fun b => |e a b|)) ≤ ε := by
    simpa only [w, weightedMean_two] using hcs
  have hj := pmfMean_mono μB _ _ (fun b => pmfMean_abs_le μA (fun a => e a b))
  rw [pmfMean_comm μB μA] at hj
  exact hj.trans hcost

end RefreshingProof
