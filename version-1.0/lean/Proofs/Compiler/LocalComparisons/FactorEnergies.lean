import Proofs.EfficientSimulaiton.PublicModel
import Proofs.Compiler.GateApproximation.MatrixPhase.Factorization
import Proofs.Compiler.GateApproximation.Shortening.ShorteningNuclear
/-!
# Averaged energies and local replacements without cutoffs

The signed factors in a patch are multiplied before averaging.  A single factor can have large pointwise energy: only its mean energy is needed when the remaining factors have pointwise bounds.  All estimates use one common probability distribution and do not assume independence of overlapping gate tables.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace CircuitCompiler.AveragedEnergyComparison
open Refresh MatrixRefresh TableAnalysis
namespace Factors
variable {X Y X' Y' : Type*} {f g : X → Y → ℝ}
theorem leftEnergy_nonneg (a : Factors f) (x : X) : 0 ≤ a.leftEnergy x := by
  unfold leftEnergy
  positivity
theorem rightEnergy_nonneg (a : Factors f) (y : Y) : 0 ≤ a.rightEnergy y := by
  unfold rightEnergy
  positivity
def restrict (a : Factors f) (l : X' → X) (r : Y' → Y) :
    Factors (fun x y => f (l x) (r y)) where
  rank := a.rank
  left x := a.left (l x)
  right y := a.right (r y)
  reconstruct x y := a.reconstruct (l x) (r y)
/-- Tensoring the representations also tensors their energies exactly. -/
/-
Mathematical definition (normal notation): If F = ∑ⱼ aⱼ bⱼᵀ and G = ∑ₖ cₖ dₖᵀ, represent their pointwise product using factor pairs

(aⱼ · cₖ, bⱼ · dₖ),

indexed by (j,k). Thus the factors are tensor products of the two factor families.
-/
def mul (a : Factors f) (b : Factors g) : Factors (fun x y => f x y * g x y) where
  rank := a.rank * b.rank
  left x j := a.left x (finProdFinEquiv.symm j).1 * b.left x (finProdFinEquiv.symm j).2
  right y j := a.right y (finProdFinEquiv.symm j).1 * b.right y (finProdFinEquiv.symm j).2
  reconstruct x y := by
    rw [a.reconstruct, b.reconstruct, ← Equiv.sum_comp finProdFinEquiv]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
theorem mul_leftEnergy (a : Factors f) (b : Factors g) (x : X) :
    (a.mul b).leftEnergy x = a.leftEnergy x * b.leftEnergy x := by
  unfold leftEnergy mul
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, mul_pow]
  exact (Finset.sum_mul_sum _ _ _ _).symm
theorem mul_rightEnergy (a : Factors f) (b : Factors g) (y : Y) :
    (a.mul b).rightEnergy y = a.rightEnergy y * b.rightEnergy y := by
  unfold rightEnergy mul
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, mul_pow]
  exact (Finset.sum_mul_sum _ _ _ _).symm
variable [Fintype X] [Fintype Y]
/-- Product cost is controlled by separate mean energies, without any pointwise energy bound. -/

/-
Mathematical statement (normal notation): For a product representation F(x,y) = ∑ⱼ aⱼ(x) · bⱼ(y) and probability distributions L,R, put Φ(x) = ∑ⱼ aⱼ(x)² and Ψ(y) = ∑ⱼ bⱼ(y)². Then

∑ⱼ ‖aⱼ‖_(2,L) · ‖bⱼ‖_(2,R) ≤ √(𝔼_L [Φ]) · √(𝔼_R [Ψ]).
-/
theorem cost_le (a : Factors f) (L : FiniteDistribution X) (R : FiniteDistribution Y) :
    (∑ j, rms L (fun x => a.left x j) * rms R (fun y => a.right y j)) ≤
      Real.sqrt (L.expect a.leftEnergy) * Real.sqrt (R.expect a.rightEnergy) := by
  have hl (j) : 0 ≤ L.expect (fun x => a.left x j ^ 2) :=
    L.expect_nonneg _ (fun _ => sq_nonneg _)
  have hr (j) : 0 ≤ R.expect (fun y => a.right y j ^ 2) :=
    R.expect_nonneg _ (fun _ => sq_nonneg _)
  have h := Real.sum_sqrt_mul_sqrt_le Finset.univ hl hr
  change (∑ j, rms L (fun x => a.left x j) * rms R (fun y => a.right y j)) ≤
    Real.sqrt (L.expect (fun x => ∑ j, a.left x j ^ 2)) *
      Real.sqrt (R.expect (fun y => ∑ j, a.right y j ^ 2))
  simpa only [rms, expect_sum] using h
/-- Scalar product discrepancy extends to the whole signed patch, retaining the two mean energies rather than replacing them by maxima. -/

/-
Mathematical statement (normal notation): Suppose two distributions P,Q on X × Y satisfy

|𝔼_P [u · v]-𝔼_Q [u · v]| ≤ δ · ‖u‖_(2,L) · ‖v‖_(2,R)

for every real u:X → ℝ, v:Y → ℝ, with δ ≥ 0. For every chosen product representation of F, with energies Φ,Ψ,

|𝔼_P [F]-𝔼_Q [F]| ≤ δ · √(𝔼_L [Φ]) · √(𝔼_R [Ψ]).
-/
theorem discrepancy (a : Factors f) (P Q : FiniteDistribution (X × Y))
    (L : FiniteDistribution X) (R : FiniteDistribution Y) (δ : ℝ) (hδ : 0 ≤ δ)
    (hscalar : ∀ u : X → ℝ, ∀ v : Y → ℝ,
      |P.expect (fun xy => u xy.1 * v xy.2) -
        Q.expect (fun xy => u xy.1 * v xy.2)| ≤ δ * rms L u * rms R v) :
    |P.expect (fun xy => f xy.1 xy.2) - Q.expect (fun xy => f xy.1 xy.2)| ≤
      δ * (Real.sqrt (L.expect a.leftEnergy) * Real.sqrt (R.expect a.rightEnergy)) := by
  have he (S : FiniteDistribution (X × Y)) :
      S.expect (fun xy => f xy.1 xy.2) =
        ∑ j, S.expect (fun xy => a.left xy.1 j * a.right xy.2 j) := by
    simp only [a.reconstruct, expect_sum]
  rw [he, he, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, |P.expect (fun xy => a.left xy.1 j * a.right xy.2 j) -
        Q.expect (fun xy => a.left xy.1 j * a.right xy.2 j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, δ * rms L (fun x => a.left x j) * rms R (fun y => a.right y j) :=
      Finset.sum_le_sum (fun j _ => hscalar (fun x => a.left x j) (fun y => a.right y j))
    _ = δ * ∑ j, rms L (fun x => a.left x j) * rms R (fun y => a.right y j) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (a.cost_le L R) hδ
end Factors
variable {X : Type*} [Fintype X]
/-- One coarse replacement with a possibly overlapping signed companion. -/

/-
Mathematical statement (normal notation): For a probability distribution P, real functions e,g, and ε ≥ 0, if ‖e‖_(2,P) ≤ ε and ‖g‖_(2,P) ≤ C₀, then

𝔼_(x ← P) [|e(x) · g(x)|] ≤ ε · C₀.

The two functions are averaged under the same distribution; independence is not assumed.
-/
theorem coarse_replacement (P : FiniteDistribution X) (error companion : X → ℝ)
    (ε C0 : ℝ) (hε : 0 ≤ ε)
    (herr : rms P error ≤ ε) (hcompanion : rms P companion ≤ C0) :
    P.expect (fun x => |error x * companion x|) ≤ ε * C0 := by
  exact (expect_abs_mul_le_rms_mul_rms P error companion).trans
    (mul_le_mul herr hcompanion (rms_nonneg _ _) hε)
/-- With two coarse companions, bound one pointwise and average the other. No pointwise bound on the finer approximation or its residual is used. -/
-- Auxiliary lemma (hybrid comparison); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(X); error, first, second ∈ X → ℝ; ε, C0, H ∈ ℝ, assume 0 ≤ ε; 0 ≤ H; ‖ error‖_(2,P) ≤ ε; ‖ second‖_(2,P) ≤ C0; ∀ x, |first(x)| ≤ H. Then

𝔼_(x ← P) [|error(x) · first(x) · second(x)|] ≤ H · (ε · C0).
-/
theorem fine_replacement (P : FiniteDistribution X) (error first second : X → ℝ)
    (ε C0 H : ℝ) (hε : 0 ≤ ε) (hH : 0 ≤ H)
    (herr : rms P error ≤ ε) (hsecond : rms P second ≤ C0)
    (hfirst : ∀ x, |first x| ≤ H) :
    P.expect (fun x => |error x * first x * second x|) ≤ H * (ε * C0) := by
  calc
    _ ≤ P.expect (fun x => H * |error x * second x|) := by
      apply P.expect_mono
      intro x
      rw [abs_mul, abs_mul, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hfirst x)
        (mul_nonneg (abs_nonneg (error x)) (abs_nonneg (second x)))]
    _ = H * P.expect (fun x => |error x * second x|) := expect_smul _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (coarse_replacement P error second ε C0 hε herr hsecond) hH
/-- Average the fine energy and bound only the coarse energies pointwise. -/
-- Auxiliary lemma (hybrid comparison); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(X); fine, first, second ∈ X → ℝ; B, H ∈ ℝ, assume 0 ≤ H; ∀ x, 0 ≤ fine(x); ∀ x, 0 ≤ second(x); ∀ x, first(x) ≤ H; ∀ x, second(x) ≤ H; 𝔼_(u ← P) [fine(u)] ≤ B. Then

𝔼_(x ← P) [fine(x) · first(x) · second(x)] ≤ B · H².
-/
theorem mean_product_energy_three (P : FiniteDistribution X) (fine first second : X → ℝ)
    (B H : ℝ) (hH : 0 ≤ H)
    (hf : ∀ x, 0 ≤ fine x)
    (hsecond0 : ∀ x, 0 ≤ second x)
    (hfirst : ∀ x, first x ≤ H) (hsecond : ∀ x, second x ≤ H)
    (hmean : P.expect fine ≤ B) :
    P.expect (fun x => fine x * first x * second x) ≤ B * H^2 := by
  calc
    _ ≤ P.expect (fun x => fine x * H^2) := by
      apply P.expect_mono
      intro x
      have h := mul_le_mul (hfirst x) (hsecond x) (hsecond0 x) hH
      simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_left h (hf x)
    _ = P.expect fine * H^2 := expect_mul_const _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hmean (sq_nonneg H)
/-- The corresponding bound with only two coarse energies. -/

/-
Mathematical statement (normal notation): Let P be a probability distribution. If e(x) ≥ 0, f(x) ≤ H everywhere, H ≥ 0, and 𝔼_P [e] ≤ B, then

𝔼_P [e · f] ≤ B · H.

No independence between e and f is required.
-/
theorem mean_product_energy_two (P : FiniteDistribution X) (first second : X → ℝ)
    (B H : ℝ) (hH : 0 ≤ H) (hfirst : ∀ x, 0 ≤ first x)
    (hsecond : ∀ x, second x ≤ H) (hmean : P.expect first ≤ B) :
    P.expect (fun x => first x * second x) ≤ B * H := by
  calc
    _ ≤ P.expect (fun x => first x * H) :=
      P.expect_mono (fun x => mul_le_mul_of_nonneg_left (hsecond x) (hfirst x))
    _ = P.expect first * H := expect_mul_const _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hmean hH
variable {Ω Y : Type*} [Fintype Ω] [Fintype Y]
/-- Average over all other encodings after taking the absolute changed-wire discrepancy.  The outer distribution may correlate its left and right shares. -/

/-
Mathematical statement (normal notation): Suppose two distributions P,Q on X × Y satisfy

|𝔼_P [u · v]-𝔼_Q [u · v]| ≤ δ · ‖u‖_(2,L) · ‖v‖_(2,R)

for every real u:X → ℝ, v:Y → ℝ, with δ ≥ 0. Let F_ω have chosen product factors with energies Φ_ω,Ψ_ω, where ω is sampled from a probability distribution O. If both 𝔼_ω [𝔼_L [Φ_ω]] and 𝔼_ω [𝔼_R [Ψ_ω]] are at most B ≥ 0, then

𝔼_ω [|𝔼_P [F_ω]-𝔼_Q [F_ω]|] ≤ δ · B.
-/
theorem averaged_discrepancy (O : FiniteDistribution Ω) (P Q : FiniteDistribution (X × Y))
    (L : FiniteDistribution X) (R : FiniteDistribution Y) (f : Ω → X → Y → ℝ)
    (factor : ∀ ω, Factors (f ω)) (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hscalar : ∀ u : X → ℝ, ∀ v : Y → ℝ,
      |P.expect (fun xy => u xy.1 * v xy.2) -
        Q.expect (fun xy => u xy.1 * v xy.2)| ≤ δ * rms L u * rms R v)
    (hleft : O.expect (fun ω => L.expect (factor ω).leftEnergy) ≤ B)
    (hright : O.expect (fun ω => R.expect (factor ω).rightEnergy) ≤ B) :
    O.expect (fun ω => |P.expect (fun xy => f ω xy.1 xy.2) -
      Q.expect (fun xy => f ω xy.1 xy.2)|) ≤ δ * B := by
  let a : Ω → ℝ := fun ω => L.expect (factor ω).leftEnergy
  let b : Ω → ℝ := fun ω => R.expect (factor ω).rightEnergy
  have ha (ω) : 0 ≤ a ω := L.expect_nonneg _ (factor ω).leftEnergy_nonneg
  have hb (ω) : 0 ≤ b ω := R.expect_nonneg _ (factor ω).rightEnergy_nonneg
  have hcs : O.expect (fun ω => Real.sqrt (a ω) * Real.sqrt (b ω)) ≤ B := by
    have h := expect_abs_mul_le_rms_mul_rms O
      (fun ω => Real.sqrt (a ω)) (fun ω => Real.sqrt (b ω))
    simp only [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), rms,
      Real.sq_sqrt (ha _), Real.sq_sqrt (hb _)] at h
    apply h.trans
    calc
      _ ≤ Real.sqrt B * Real.sqrt B :=
        mul_le_mul (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = B := Real.mul_self_sqrt hB
  calc
    _ ≤ O.expect (fun ω => δ * (Real.sqrt (a ω) * Real.sqrt (b ω))) :=
      O.expect_mono (fun ω => (factor ω).discrepancy P Q L R δ hδ hscalar)
    _ = δ * O.expect (fun ω => Real.sqrt (a ω) * Real.sqrt (b ω)) := expect_smul _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hcs hδ
end CircuitCompiler.AveragedEnergyComparison
