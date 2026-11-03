import Proofs.Compiler.LocalComparisons.GateInterface

/-!
# Transporting the local approximation to the full retry experiment

If two conditional answer tables differ by at most ρ on the support of every valid encoding distribution, the same chosen product factors approximate the second table with error ε + ρ. Their pointwise energies, mean energies, and bounds under arbitrary labelings are unchanged. This is the local triangle inequality used to include all shortening retries in the paper's exact canonical experiment.
-/

noncomputable section
open scoped BigOperators

namespace CompilerProof.LocalApproximation

open Refresh MatrixRefresh CircuitCompiler.AveragedEnergyComparison

/-- A bound |f(x)| ≤ ρ at all positive-mass points implies ‖f‖₂ ≤ ρ. Zero-mass points contribute nothing to the weighted square sum. -/
theorem rms_le_of_support_bound {X : Type*} [Fintype X]
    (P : FiniteDistribution X) (f : X → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hbound : ∀ x, 0 < P.weight x → |f x| ≤ ρ) : rms P f ≤ ρ := by
  apply (sq_le_sq₀ (rms_nonneg P f) hρ).mp
  rw [rms_sq]
  calc
    P.expect (fun x => f x ^ 2) ≤ P.expect (fun _ => ρ ^ 2) := by
      unfold FiniteDistribution.expect
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : P.weight x = 0
      · simp only [hx, zero_mul, le_refl]
      · have hp : 0 < P.weight x := lt_of_le_of_ne (P.nonneg x) (Ne.symm hx)
        have hs := (sq_le_sq₀ (abs_nonneg (f x)) hρ).2 (hbound x hp)
        exact mul_le_mul_of_nonneg_left (by simpa only [sq_abs] using hs) (P.nonneg x)
    _ = ρ ^ 2 := FiniteDistribution.expect_const _ _

/-- Retain one approximation and its factors when a valid true answer changes pointwise by at most ρ. The error becomes ε + ρ, uniformly over all valid labelings. -/
def changeOriginal {X S : Type*} [Fintype X] [Nonempty X]
    {laws : S → FiniteDistribution (X × X)} {valid : S → Prop}
    {original : S → X → X → ℝ} {β ε : ℝ}
    (data : GateLocalEstimates laws valid original β ε)
    (newOriginal : S → X → X → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hbound : ∀ s, valid s → ∀ x y, 0 < (laws s).weight (x,y) →
      |newOriginal s x y - original s x y| ≤ ρ) :
    GateLocalEstimates laws valid newOriginal β (ε + ρ) where
  approximation := data.approximation
  factors := data.factors
  left_max := data.left_max
  right_max := data.right_max
  left_mean := data.left_mean
  right_mean := data.right_mean
  all_labels_rms := data.all_labels_rms
  valid_error_rms s hv := by
    have hd := rms_le_of_support_bound (laws s)
      (fun xy => newOriginal s xy.1 xy.2 - original s xy.1 xy.2) hρ
      (fun xy hp => hbound s hv xy.1 xy.2 hp)
    have ht := rms_add_le (laws s)
      (fun xy => original s xy.1 xy.2 - data.approximation xy.1 xy.2)
      (fun xy => newOriginal s xy.1 xy.2 - original s xy.1 xy.2)
    have he : (fun xy : X × X =>
        (original s xy.1 xy.2 - data.approximation xy.1 xy.2) +
          (newOriginal s xy.1 xy.2 - original s xy.1 xy.2)) =
        (fun xy => newOriginal s xy.1 xy.2 - data.approximation xy.1 xy.2) := by
      funext xy
      ring
    rw [he] at ht
    exact ht.trans (add_le_add (data.valid_error_rms s hv) hd)

end CompilerProof.LocalApproximation
