import Proofs.Refreshing.Hybrids
import Proofs.Refreshing.FiniteExpectation

/-!
# Local two-round windows of neighboring signed hybrids
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RefreshingProof
open Refreshing

/-- Expose the first true round of a suffix at the level of real point masses. -/
theorem canonicalContinuation_toReal_step {n T leakage : ℕ} {s : Bit}
    [Nonempty (Encoding n s)] (A : Strategy n T leakage) (i : ℕ) (hi : i < T)
    (x : Encoding n s) (h : History leakage i) (final : History leakage T) :
    (canonicalContinuation A i (by omega) x h final).toReal =
      pmfMean (uniformPMF (Encoding n s)) (fun y =>
        pmfMean (conditionalAnswer (A ⟨i, hi⟩ h) x y) (fun z =>
          (canonicalContinuation A (i + 1) (by omega) y (appendAnswer h z) final).toReal)) := by
  rw [canonicalContinuation_step A i hi]
  simp only [pmf_bind_toReal, pmfMean]

/-- Expose the last true round of a prefix inside an arbitrary signed test. -/
theorem pmfMean_canonicalPrefix_succ {n T leakage : ℕ} (s : Bit)
    [Nonempty (Encoding n s)] (A : Strategy n T leakage) (i : ℕ) (hi : i + 1 ≤ T)
    (F : Encoding n s × History leakage (i + 1) → ℝ) :
    pmfMean (canonicalPrefix s A (i + 1) hi) F =
      pmfMean (canonicalPrefix s A i (by omega)) (fun c =>
        pmfMean (uniformPMF (Encoding n s)) (fun y =>
          pmfMean (conditionalAnswer (A ⟨i, by omega⟩ c.2) c.1 y) (fun z =>
            F (y, appendAnswer c.2 z)))) := by
  rw [canonicalPrefix_succ, pmfMean_bind]
  apply congrArg (pmfMean (canonicalPrefix s A i (by omega)))
  funext c
  rw [pmfMean_bind]
  apply congrArg (pmfMean (uniformPMF (Encoding n s)))
  funext y
  rw [pmfMean_map]

/-- A signed hybrid is the expectation of its signed local table and actual suffix over the canonical secret-one prefix. -/
theorem signedHybrid_as_pmfMean {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (G : SignedTables n T leakage) (k : Fin T)
    (final : History leakage T) :
    signedHybrid A G k final =
      pmfMean (canonicalPrefix 1 A k.val (by omega)) (fun c =>
        pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun y =>
          ∑ z : Answer leakage, G k c.2 z c.1.val y.val *
            (canonicalContinuation A (k.val + 1) (by omega) y (appendAnswer c.2 z) final).toReal)) := rfl

/-- Expand the preceding unsigned round of an interior one-signed-round hybrid. -/
theorem signedHybrid_prefix_succ {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (G : SignedTables n T leakage)
    (i : ℕ) (hi : i + 2 ≤ T) (final : History leakage T) :
    signedHybrid A G ⟨i + 1, by omega⟩ final =
      pmfMean (canonicalPrefix 1 A i (by omega)) (fun c =>
        pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun a =>
          pmfMean (conditionalAnswer (A ⟨i, by omega⟩ c.2) c.1 a) (fun z₀ =>
            pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun x =>
              ∑ z₁ : Answer leakage,
                G ⟨i + 1, by omega⟩ (appendAnswer c.2 z₀) z₁ a.val x.val *
                  (canonicalContinuation A (i + 2) (by omega) x
                    (appendAnswer (appendAnswer c.2 z₀) z₁) final).toReal)))) := by
  rw [signedHybrid_as_pmfMean, pmfMean_canonicalPrefix_succ]

/-- First block round signed, second block round true, with middle secret zero. -/
def windowLeftSigned {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (G : SignedTables n T leakage)
    (i : ℕ) (hi : i + 3 ≤ T)
    (c : Encoding n (1 : Bit) × History leakage i) (z : ThreeAnswers (Answer leakage))
    (a : Encoding n (1 : Bit)) (b : Encoding n (0 : Bit)) : ℝ :=
  let h₁ := appendAnswer c.2 z.1
  let h₂ := appendAnswer h₁ z.2.1
  pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun x =>
    G ⟨i + 1, by omega⟩ h₁ z.2.1 a.val x.val *
      (conditionalAnswer (A ⟨i + 2, by omega⟩ h₂) x b z.2.2).toReal)

/-- Both block rounds signed, with an arbitrary label for their common state. -/
def windowBothSigned {n T leakage : ℕ} (s : Bit) [Nonempty (Encoding n s)]
    (G : SignedTables n T leakage) (i : ℕ) (hi : i + 3 ≤ T)
    (c : Encoding n (1 : Bit) × History leakage i) (z : ThreeAnswers (Answer leakage))
    (a : Encoding n (1 : Bit)) (b : Encoding n (0 : Bit)) : ℝ :=
  let h₁ := appendAnswer c.2 z.1
  let h₂ := appendAnswer h₁ z.2.1
  pmfMean (uniformPMF (Encoding n s)) (fun x =>
    G ⟨i + 1, by omega⟩ h₁ z.2.1 a.val x.val *
      G ⟨i + 2, by omega⟩ h₂ z.2.2 x.val b.val)

/-- First block round true, second block round signed, with middle secret one. -/
def windowRightSigned {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (G : SignedTables n T leakage)
    (i : ℕ) (hi : i + 3 ≤ T)
    (c : Encoding n (1 : Bit) × History leakage i) (z : ThreeAnswers (Answer leakage))
    (a : Encoding n (1 : Bit)) (b : Encoding n (0 : Bit)) : ℝ :=
  let h₁ := appendAnswer c.2 z.1
  let h₂ := appendAnswer h₁ z.2.1
  pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun x =>
    (conditionalAnswer (A ⟨i + 1, by omega⟩ h₁) a x z.2.1).toReal *
      G ⟨i + 2, by omega⟩ h₂ z.2.2 x.val b.val)

/-- The local difference between the two neighboring signed-hybrid windows. -/
def twoRoundWindowError {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (G : SignedTables n T leakage) (i : ℕ) (hi : i + 3 ≤ T)
    (c : Encoding n (1 : Bit) × History leakage i) (z : ThreeAnswers (Answer leakage))
    (a : Encoding n (1 : Bit)) (b : Encoding n (0 : Bit)) : ℝ :=
  windowLeftSigned A G i hi c z a b - windowRightSigned A G i hi c z a b

/-- The local replacement and label-change estimates imply the per-answer outer-state bound required by the actual adaptive block accounting theorem. -/
theorem twoRoundWindowError_local_bound {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (G : SignedTables n T leakage) (i : ℕ) (hi : i + 3 ≤ T)
    (ε d : ℝ) (c : Encoding n (1 : Bit) × History leakage i)
    (z : ThreeAnswers (Answer leakage))
    (hinsert : pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun a =>
      pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun b =>
        |windowLeftSigned A G i hi c z a b - windowBothSigned 0 G i hi c z a b|)) ≤ 6 * ε)
    (hlabel : pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun a =>
      pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun b =>
        |windowBothSigned 0 G i hi c z a b - windowBothSigned 1 G i hi c z a b|)) ≤ 8 * d)
    (hrestore : pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun a =>
      pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun b =>
        |windowBothSigned 1 G i hi c z a b - windowRightSigned A G i hi c z a b|)) ≤ 6 * ε) :
    pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun a =>
      pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun b =>
        |twoRoundWindowError A G i hi c z a b|)) ≤ 12 * ε + 8 * d :=
  local_three_move_bound _ _ _ _ _ _ ε d hinsert hlabel hrestore

/-- Complete global K³ loss for these actual two-round window errors, with only local per-answer estimates as hypotheses. -/
theorem twoRoundWindowError_global_bound {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (G : SignedTables n T leakage) (i : ℕ) (hi : i + 3 ≤ T)
    (ε d : ℝ)
    (hlocal : ∀ c z,
      pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun a =>
        pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun b =>
          |twoRoundWindowError A G i hi c z a b|)) ≤ 12 * ε + 8 * d) :
    ∑ h, |canonicalBlockDifference A i hi (twoRoundWindowError A G i hi) h| ≤
      (K leakage : ℝ) ^ 3 * (12 * ε + 8 * d) :=
  canonicalBlockDifference_l1_le A i hi _ _ hlocal

end RefreshingProof
