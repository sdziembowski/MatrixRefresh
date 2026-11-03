import Proofs.Refreshing.BlockExpectation

/-!
# Boundary versions of adaptive block accounting

Dummy answers account for absent preceding or incident rounds. They preserve exact mass identities and keep the uniform K³ bound, including one-round runs.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RefreshingProof

/-- Expectation under a point-mass distribution evaluates the function at that point. -/
@[simp] theorem pmfMean_pure {X : Type*} [Fintype X] (x : X) (f : X → ℝ) :
    pmfMean (PMF.pure x) f = f x := by
  classical
  simp [pmfMean, PMF.pure_apply, apply_ite ENNReal.toReal]

/-- Two real block answers, with no preceding real round. -/
theorem noPrefixTwoRound_l1_bound {Z A B R : Type*}
    [Fintype Z] [Inhabited Z] [Fintype A] [Fintype B] [Fintype R]
    (μA : PMF A) (μB : PMF B) (E : Z → B → Z → A → ℝ)
    (tail : Z → B → Z → PMF R) (δ : ℝ)
    (hlocal : ∀ z₁ z₂, pmfMean μA (fun a => pmfMean μB (fun b => |E z₁ b z₂ a|)) ≤ δ) :
    (∑ r, |pmfMean μA (fun a => ∑ z₁, pmfMean μB (fun b => ∑ z₂,
      E z₁ b z₂ a * (tail z₁ b z₂ r).toReal))|) ≤ (Fintype.card Z : ℝ) ^ 3 * δ := by
  have h := adaptive_block_K3 (PMF.pure Unit.unit) μA μB
    (fun _ _ => PMF.pure (default : Z))
    (fun _ z a b => E z.2.1 b z.2.2 a)
    (fun v => tail v.2.1.2.1 v.2.2.2 v.2.1.2.2) δ
    (fun _ z => hlocal z.2.1 z.2.2)
  simpa only [blockFinal_as_pmfMean, pmfMean_pure] using h

/-- One real block answer, preceded by a true round. The absent second block answer is a fixed dummy, selected by an indicator in the local error table. -/
theorem oneRoundPrefix_l1_bound {C Z A R : Type*}
    [Fintype C] [Fintype Z] [Inhabited Z] [Fintype A] [Fintype R]
    (P : PMF C) (μA : PMF A) (p : C → A → PMF Z)
    (E : C → Z → Z → A → ℝ) (tail : C → Z → A → Z → PMF R)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hlocal : ∀ c z₀ z₁, pmfMean μA (fun a => |E c z₀ z₁ a|) ≤ δ) :
    (∑ r, |pmfMean P (fun c => pmfMean μA (fun a => pmfMean (p c a) (fun z₀ =>
      ∑ z₁, E c z₀ z₁ a * (tail c z₀ a z₁ r).toReal)))|) ≤
      (Fintype.card Z : ℝ) ^ 3 * δ := by
  classical
  let E' : C → ThreeAnswers Z → A → Unit → ℝ :=
    fun c z a _ => if z.2.2 = default then E c z.1 z.2.1 a else 0
  have hl : ∀ c z, (∑ a, (μA a).toReal *
      (∑ b, (PMF.pure Unit.unit b).toReal * |E' c z a b|)) ≤ δ := by
    intro c z
    by_cases hz : z.2.2 = default
    · simpa [pmfMean, E', hz] using hlocal c z.1 z.2.1
    · simpa [E', hz] using hδ
  have h := adaptive_block_K3 P μA (PMF.pure Unit.unit) p E'
    (fun v => tail v.1 v.2.1.1 v.2.2.1 v.2.1.2.1) δ hl
  simpa [blockFinal_as_pmfMean, E', ite_mul] using h

/-- One real block answer with no preceding real round. -/
theorem oneRoundNoPrefix_l1_bound {Z A R : Type*}
    [Fintype Z] [Inhabited Z] [Fintype A] [Fintype R]
    (μA : PMF A) (E : Z → A → ℝ) (tail : A → Z → PMF R)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hlocal : ∀ z, pmfMean μA (fun a => |E z a|) ≤ δ) :
    (∑ r, |pmfMean μA (fun a => ∑ z, E z a * (tail a z r).toReal)|) ≤
      (Fintype.card Z : ℝ) ^ 3 * δ := by
  have h := oneRoundPrefix_l1_bound (PMF.pure Unit.unit) μA
    (fun _ _ => PMF.pure (default : Z)) (fun _ _ z a => E z a)
    (fun _ _ a z => tail a z) δ hδ (fun _ _ z => hlocal z)
  simpa only [pmfMean_pure] using h

end RefreshingProof
