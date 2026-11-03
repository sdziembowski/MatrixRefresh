import Proofs.Refreshing.FiniteExpectation

/-!
# Fubini identity for the local adaptive block
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RefreshingProof

/-- Move exactly three enumerated answers before the independently sampled outer states. This is finite Fubini; no positivity or independence is assumed of the integrand itself. -/
theorem finite_block_fubini {C Z A B : Type*}
    [Fintype C] [Fintype Z] [Fintype A] [Fintype B]
    (F : C → Z → Z → Z → A → B → ℝ) :
    (∑ c, ∑ a, ∑ z₀, ∑ z₁, ∑ b, ∑ z₂, F c z₀ z₁ z₂ a b) =
      ∑ c, ∑ z₀, ∑ z₁, ∑ z₂, ∑ a, ∑ b, F c z₀ z₁ z₂ a b := by
  apply Finset.sum_congr rfl
  intro c _
  calc
    _ = ∑ z₀, ∑ a, ∑ z₁, ∑ b, ∑ z₂, F c z₀ z₁ z₂ a b := Finset.sum_comm
    _ = ∑ z₀, ∑ z₁, ∑ a, ∑ b, ∑ z₂, F c z₀ z₁ z₂ a b := by
      apply Finset.sum_congr rfl
      intro z₀ _
      exact Finset.sum_comm
    _ = ∑ z₀, ∑ z₁, ∑ a, ∑ z₂, ∑ b, F c z₀ z₁ z₂ a b := by
      apply Finset.sum_congr rfl
      intro z₀ _
      apply Finset.sum_congr rfl
      intro z₁ _
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z₀ _
      apply Finset.sum_congr rfl
      intro z₁ _
      exact Finset.sum_comm

/-- The signed-kernel local error is exactly its natural sequential expectation: context, first outer state, preceding answer, first block answer, second outer state, second block answer, then the true suffix. -/
theorem blockFinal_as_pmfMean {C Z A B R : Type*}
    [Fintype C] [Fintype Z] [Fintype A] [Fintype B]
    (P : PMF C) (μA : PMF A) (μB : PMF B) (p : C → A → PMF Z)
    (E : C → ThreeAnswers Z → A → B → ℝ)
    (suffix : BlockIndex C Z A B → PMF R) (r : R) :
    signedKernelApply (blockBaseMass P μA μB p E)
      (fun v r => (suffix v r).toReal) r =
      pmfMean P (fun c => pmfMean μA (fun a => pmfMean (p c a) (fun z₀ =>
        ∑ z₁, pmfMean μB (fun b => ∑ z₂,
          E c (z₀, z₁, z₂) a b * (suffix (c, (z₀, z₁, z₂), a, b) r).toReal)))) := by
  unfold signedKernelApply blockBaseMass pmfMean
  simp only [Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  conv_rhs => rw [finite_block_fubini]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro z₀ _
  apply Finset.sum_congr rfl
  intro z₁ _
  apply Finset.sum_congr rfl
  intro z₂ _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end RefreshingProof
