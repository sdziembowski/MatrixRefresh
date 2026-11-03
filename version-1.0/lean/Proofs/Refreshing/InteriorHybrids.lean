import Proofs.Refreshing.HybridAlgebra
import Proofs.Refreshing.BlockExpectation

/-!
# Actual interior signed-hybrid steps

These identities derive the complete adaptive hybrid step from its two-round local window. They do not assume a bound on the full hybrid step.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RefreshingProof
open Refreshing

/-- Expose a true preceding round and the first true suffix round around the left-signed window. -/
theorem signedHybrid_left_window {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (G : SignedTables n T leakage)
    (i : ℕ) (hi : i + 3 ≤ T) (final : History leakage T) :
    signedHybrid A G ⟨i + 1, by omega⟩ final =
      canonicalBlockDifference A i hi (windowLeftSigned A G i hi) final := by
  let : Fintype (Encoding n (1 : Bit)) := inferInstance
  let : Fintype (Encoding n (0 : Bit)) := inferInstance
  let : Fintype (ThreeAnswers (Answer leakage)) := inferInstance
  let : Fintype (Encoding n (1 : Bit) × History leakage i) := inferInstance
  unfold canonicalBlockDifference
  rw [blockFinal_as_pmfMean, signedHybrid_prefix_succ A G i (by omega)]
  apply congrArg (pmfMean (canonicalPrefix 1 A i (by omega)))
  funext c
  apply congrArg (pmfMean (uniformPMF (Encoding n (1 : Bit))))
  funext a
  apply congrArg (pmfMean (conditionalAnswer (A ⟨i, by omega⟩ c.2) c.1 a))
  funext z₀
  simp_rw [canonicalContinuation_toReal_step A (i + 2) (by omega)]
  exact two_round_window_factorization
    (uniformPMF (Encoding n (0 : Bit))) (uniformPMF (Encoding n (0 : Bit)))
    (fun x z₁ => G ⟨i + 1, by omega⟩ (appendAnswer c.2 z₀) z₁ a.val x.val)
    (fun x z₁ b z₂ => (conditionalAnswer
      (A ⟨i + 2, by omega⟩ (appendAnswer (appendAnswer c.2 z₀) z₁)) x b z₂).toReal)
    (fun z₁ b z₂ => (canonicalContinuation A (i + 3) hi b
      (appendAnswer (appendAnswer (appendAnswer c.2 z₀) z₁) z₂) final).toReal)

/-- Expose the two true prefix rounds around the right-signed window. -/
theorem signedHybrid_right_window {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (G : SignedTables n T leakage)
    (i : ℕ) (hi : i + 3 ≤ T) (final : History leakage T) :
    signedHybrid A G ⟨i + 2, by omega⟩ final =
      canonicalBlockDifference A i hi (windowRightSigned A G i hi) final := by
  let : Fintype (Encoding n (1 : Bit)) := inferInstance
  let : Fintype (Encoding n (0 : Bit)) := inferInstance
  let : Fintype (ThreeAnswers (Answer leakage)) := inferInstance
  let : Fintype (Encoding n (1 : Bit) × History leakage i) := inferInstance
  unfold canonicalBlockDifference
  rw [blockFinal_as_pmfMean, signedHybrid_as_pmfMean,
    pmfMean_canonicalPrefix_succ 1 A (i + 1) (by omega),
    pmfMean_canonicalPrefix_succ 1 A i (by omega)]
  apply congrArg (pmfMean (canonicalPrefix 1 A i (by omega)))
  funext c
  apply congrArg (pmfMean (uniformPMF (Encoding n (1 : Bit))))
  funext a
  apply congrArg (pmfMean (conditionalAnswer (A ⟨i, by omega⟩ c.2) c.1 a))
  funext z₀
  exact two_round_window_factorization
    (uniformPMF (Encoding n (1 : Bit))) (uniformPMF (Encoding n (0 : Bit)))
    (fun x z₁ => (conditionalAnswer (A ⟨i + 1, by omega⟩ (appendAnswer c.2 z₀)) a x z₁).toReal)
    (fun x z₁ b z₂ => G ⟨i + 2, by omega⟩
      (appendAnswer (appendAnswer c.2 z₀) z₁) z₂ x.val b.val)
    (fun z₁ b z₂ => (canonicalContinuation A (i + 3) hi b
      (appendAnswer (appendAnswer (appendAnswer c.2 z₀) z₁) z₂) final).toReal)

/-- The global block-error expression is linear in its local table. -/
theorem canonicalBlockDifference_sub {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (i : ℕ) (hi : i + 3 ≤ T)
    (E F : (Encoding n (1 : Bit) × History leakage i) → ThreeAnswers (Answer leakage) →
      Encoding n (1 : Bit) → Encoding n (0 : Bit) → ℝ) (final : History leakage T) :
    canonicalBlockDifference A i hi (fun c z a b => E c z a b - F c z a b) final =
      canonicalBlockDifference A i hi E final - canonicalBlockDifference A i hi F final := by
  unfold canonicalBlockDifference signedKernelApply blockBaseMass
  simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]

/-- Exact adjacent-hybrid difference, with all preceding and future rounds accounted for by their actual canonical probability distributions. -/
theorem signedHybrid_neighbor_difference {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (G : SignedTables n T leakage)
    (i : ℕ) (hi : i + 3 ≤ T) (final : History leakage T) :
    signedHybrid A G ⟨i + 1, by omega⟩ final -
        signedHybrid A G ⟨i + 2, by omega⟩ final =
      canonicalBlockDifference A i hi (twoRoundWindowError A G i hi) final := by
  rw [signedHybrid_left_window A G i hi, signedHybrid_right_window A G i hi]
  exact (canonicalBlockDifference_sub A i hi _ _ final).symm

/-- The actual interior hybrid-step bound, obtained from local per-answer replacement and label-change data, rather than assumed for the whole view. -/
theorem signedHybrid_neighbor_l1_le {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (G : SignedTables n T leakage)
    (i : ℕ) (hi : i + 3 ≤ T) (ε d : ℝ)
    (hlocal : ∀ c z,
      pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun a =>
        pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun b =>
          |twoRoundWindowError A G i hi c z a b|)) ≤ 12 * ε + 8 * d) :
    massL1 (signedHybrid A G ⟨i + 1, by omega⟩)
        (signedHybrid A G ⟨i + 2, by omega⟩) ≤
      (K leakage : ℝ) ^ 3 * (12 * ε + 8 * d) := by
  unfold massL1
  simp_rw [signedHybrid_neighbor_difference A G i hi]
  exact twoRoundWindowError_global_bound A G i hi ε d hlocal

end RefreshingProof
