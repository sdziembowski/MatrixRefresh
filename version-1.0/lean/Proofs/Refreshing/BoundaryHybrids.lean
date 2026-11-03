import Proofs.Refreshing.InteriorHybrids
import Proofs.Refreshing.ShortBlock

/-!
# Boundary signed-hybrid steps, including one-round executions
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RefreshingProof
open Refreshing

/-- The zero-round prefix contains just its uniformly sampled initial state. -/
theorem pmfMean_canonicalPrefix_zero {n T leakage : ℕ} (s : Bit)
    [Nonempty (Encoding n s)] (A : Strategy n T leakage)
    (F : Encoding n s × History leakage 0 → ℝ) :
    pmfMean (canonicalPrefix s A 0 (by omega)) F =
      pmfMean (uniformPMF (Encoding n s)) (fun x => F (x, Fin.elim0)) := by
  unfold canonicalPrefix
  rw [pmfMean_bind]
  apply congrArg (pmfMean (uniformPMF (Encoding n s)))
  funext x
  exact pmfMean_pure _ _

/-- First two rounds, with the first signed and common-state label zero. -/
def initialWindowLeft {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (G : SignedTables n T leakage) (hT : 2 ≤ T)
    (z₁ : Answer leakage) (b : Encoding n (0 : Bit)) (z₂ : Answer leakage)
    (a : Encoding n (1 : Bit)) : ℝ :=
  pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun x =>
    G ⟨0, by omega⟩ Fin.elim0 z₁ a.val x.val *
      (conditionalAnswer (A ⟨1, by omega⟩ (appendAnswer Fin.elim0 z₁)) x b z₂).toReal)

/-- First two rounds, with the second signed and common-state label one. -/
def initialWindowRight {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (G : SignedTables n T leakage) (hT : 2 ≤ T)
    (z₁ : Answer leakage) (b : Encoding n (0 : Bit)) (z₂ : Answer leakage)
    (a : Encoding n (1 : Bit)) : ℝ :=
  pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun x =>
    (conditionalAnswer (A ⟨0, by omega⟩ Fin.elim0) a x z₁).toReal *
      G ⟨1, by omega⟩ (appendAnswer Fin.elim0 z₁) z₂ x.val b.val)

/-- Exact signed two-round window contribution at the beginning of execution. -/
def initialBlockDifference {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (hT : 2 ≤ T)
    (E : Answer leakage → Encoding n (0 : Bit) → Answer leakage → Encoding n (1 : Bit) → ℝ)
    (final : History leakage T) : ℝ :=
  pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun a =>
    ∑ z₁, pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun b => ∑ z₂,
      E z₁ b z₂ a * (canonicalContinuation A 2 hT b
        (appendAnswer (appendAnswer Fin.elim0 z₁) z₂) final).toReal))

/-- The first signed hybrid is the initial two-round window with its left signed factor. -/
theorem signedHybrid_initial_left_window {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (G : SignedTables n T leakage) (hT : 2 ≤ T)
    (final : History leakage T) :
    signedHybrid A G ⟨0, by omega⟩ final =
      initialBlockDifference A hT (initialWindowLeft A G hT) final := by
  rw [signedHybrid_as_pmfMean, pmfMean_canonicalPrefix_zero]
  unfold initialBlockDifference
  apply congrArg (pmfMean (uniformPMF (Encoding n (1 : Bit))))
  funext a
  simp_rw [canonicalContinuation_toReal_step A 1 (by omega)]
  exact two_round_window_factorization
    (uniformPMF (Encoding n (0 : Bit))) (uniformPMF (Encoding n (0 : Bit)))
    (fun x z₁ => G ⟨0, by omega⟩ Fin.elim0 z₁ a.val x.val)
    (fun x z₁ b z₂ => (conditionalAnswer
      (A ⟨1, by omega⟩ (appendAnswer Fin.elim0 z₁)) x b z₂).toReal)
    (fun z₁ b z₂ => (canonicalContinuation A 2 hT b
      (appendAnswer (appendAnswer Fin.elim0 z₁) z₂) final).toReal)

/-- The second signed hybrid is the same initial window with its right signed factor. -/
theorem signedHybrid_initial_right_window {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (G : SignedTables n T leakage) (hT : 2 ≤ T)
    (final : History leakage T) :
    signedHybrid A G ⟨1, by omega⟩ final =
      initialBlockDifference A hT (initialWindowRight A G hT) final := by
  rw [signedHybrid_as_pmfMean, pmfMean_canonicalPrefix_succ 1 A 0 (by omega),
    pmfMean_canonicalPrefix_zero]
  unfold initialBlockDifference
  apply congrArg (pmfMean (uniformPMF (Encoding n (1 : Bit))))
  funext a
  exact two_round_window_factorization
    (uniformPMF (Encoding n (1 : Bit))) (uniformPMF (Encoding n (0 : Bit)))
    (fun x z₁ => (conditionalAnswer (A ⟨0, by omega⟩ Fin.elim0) a x z₁).toReal)
    (fun x z₁ b z₂ => G ⟨1, by omega⟩ (appendAnswer Fin.elim0 z₁) z₂ x.val b.val)
    (fun z₁ b z₂ => (canonicalContinuation A 2 hT b
      (appendAnswer (appendAnswer Fin.elim0 z₁) z₂) final).toReal)

/-- The initial-window continuation is linear in the difference of its two local kernels. -/
theorem initialBlockDifference_sub {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (hT : 2 ≤ T)
    (E F : Answer leakage → Encoding n (0 : Bit) → Answer leakage → Encoding n (1 : Bit) → ℝ)
    (final : History leakage T) :
    initialBlockDifference A hT (fun z₁ b z₂ a => E z₁ b z₂ a - F z₁ b z₂ a) final =
      initialBlockDifference A hT E final - initialBlockDifference A hT F final := by
  unfold initialBlockDifference
  simp only [sub_mul, Finset.sum_sub_distrib, pmfMean_sub]

/-- The first adjacent signed hybrids need no preceding real round. -/
theorem signedHybrid_first_neighbor_l1_le {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (G : SignedTables n T leakage) (hT : 2 ≤ T) (δ : ℝ)
    (hlocal : ∀ z₁ z₂, pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun a =>
      pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun b =>
        |initialWindowLeft A G hT z₁ b z₂ a - initialWindowRight A G hT z₁ b z₂ a|)) ≤ δ) :
    massL1 (signedHybrid A G ⟨0, by omega⟩) (signedHybrid A G ⟨1, by omega⟩) ≤
      (K leakage : ℝ) ^ 3 * δ := by
  have heq (final : History leakage T) :
      signedHybrid A G ⟨0, by omega⟩ final - signedHybrid A G ⟨1, by omega⟩ final =
        initialBlockDifference A hT
          (fun z₁ b z₂ a => initialWindowLeft A G hT z₁ b z₂ a -
            initialWindowRight A G hT z₁ b z₂ a) final := by
    rw [signedHybrid_initial_left_window A G hT, signedHybrid_initial_right_window A G hT]
    exact (initialBlockDifference_sub A hT _ _ final).symm
  unfold massL1
  simp_rw [heq]
  have hb := noPrefixTwoRound_l1_bound
    (uniformPMF (Encoding n (1 : Bit))) (uniformPMF (Encoding n (0 : Bit)))
    (fun z₁ b z₂ a => initialWindowLeft A G hT z₁ b z₂ a - initialWindowRight A G hT z₁ b z₂ a)
    (fun z₁ b z₂ => canonicalContinuation A 2 hT b
      (appendAnswer (appendAnswer Fin.elim0 z₁) z₂)) δ hlocal
  simpa only [initialBlockDifference, answer_card_eq_K] using hb

end RefreshingProof
