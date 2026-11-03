import Proofs.Refreshing.ActualEndpoints

/-!
# Transcript comparison from local signed approximation estimates

All hypotheses below are per-answer local state averages. Full transcript and full hybrid-step bounds are derived, including both actual endpoints.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RefreshingProof
open Refreshing

/-- The complete positive-horizon comparison theorem. The true initial and final probability distributions are endpoints of a chain with one signed round at a time. No global security estimate is a hypothesis. -/
theorem security_of_window_bounds {n t leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (hn : 2 ≤ n) (A : Strategy n (t + 1) leakage) (G : SignedTables n (t + 1) leakage)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hfirst : ∀ z, pmfMean (uniformPMF (Encoding n (0 : Bit)))
      (fun b => |firstKernelError A G (by omega) z b|) ≤ δ)
    (hlast : ∀ h z, pmfMean (uniformPMF (Encoding n (1 : Bit)))
      (fun a => |lastKernelError A G h a z|) ≤ δ)
    (hinitial : ∀ hT : 2 ≤ t + 1, ∀ z₁ z₂,
      pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun a =>
        pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun b =>
          |initialWindowLeft A G hT z₁ b z₂ a - initialWindowRight A G hT z₁ b z₂ a|)) ≤ δ)
    (hinterior : ∀ (i : ℕ) (hi : i + 3 ≤ t + 1) c z,
      pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun a =>
        pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun b =>
          |twoRoundWindowError A G i hi c z a b|)) ≤ δ) :
    statisticalDistance (transcriptDistribution hn A 0) (transcriptDistribution hn A 1) ≤
      ((t + 1 : ℕ) : ℝ) * (K leakage : ℝ) ^ 3 * δ := by
  let P₀ : History leakage (t + 1) → ℝ := fun h => (transcriptDistribution hn A 0 h).toReal
  let P₁ : History leakage (t + 1) → ℝ := fun h => (transcriptDistribution hn A 1 h).toReal
  let Q : ℕ → History leakage (t + 1) → ℝ := fun j =>
    if hj₀ : j = 0 then P₀
    else if hj : j ≤ t + 1 then signedHybrid A G ⟨j - 1, by omega⟩ else P₁
  have hstep : ∀ j < (t + 1) + 1,
      massL1 (Q j) (Q (j + 1)) ≤ (K leakage : ℝ) ^ 3 * δ := by
    intro j hj
    by_cases hj₀ : j = 0
    · subst j
      simpa only [Q, dite_eq_left rfl, dite_eq_right (by omega : ¬1 = 0),
        dite_eq_left (by omega : 1 ≤ t + 1), Nat.sub_self] using
        first_endpoint_l1_le hn A G (by omega) δ hδ hfirst
    · by_cases hjlast : j = t + 1
      · subst j
        simpa only [Q, dite_eq_right (by omega : ¬t + 1 = 0), dite_eq_left le_rfl,
          dite_eq_right (by omega : ¬(t + 1) + 1 = 0),
          dite_eq_right (by omega : ¬(t + 1) + 1 ≤ t + 1), Nat.add_sub_cancel] using
          last_endpoint_l1_le hn A G δ hδ hlast
      · have hjlt : j < t + 1 := by omega
        by_cases hjone : j = 1
        · subst j
          have hT : 2 ≤ t + 1 := by omega
          simpa only [Q, dite_eq_right (by omega : ¬1 = 0), dite_eq_left (by omega : 1 ≤ t + 1),
            dite_eq_right (by omega : ¬2 = 0), dite_eq_left hT, Nat.sub_self, Nat.reduceSub] using
            signedHybrid_first_neighbor_l1_le A G hT δ (hinitial hT)
        · obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
          have hi : i + 3 ≤ t + 1 := by omega
          have hb : massL1 (signedHybrid A G ⟨i + 1, by omega⟩)
              (signedHybrid A G ⟨i + 2, by omega⟩) ≤ (K leakage : ℝ) ^ 3 * δ := by
            unfold massL1
            simp_rw [signedHybrid_neighbor_difference A G i hi]
            exact canonicalBlockDifference_l1_le A i hi _ δ (hinterior i hi)
          simpa only [Q, dite_eq_right (by omega : ¬i + 2 = 0),
            dite_eq_left (by omega : i + 2 ≤ t + 1),
            dite_eq_right (by omega : ¬(i + 2) + 1 = 0), dite_eq_left hi,
            Nat.add_sub_cancel, (show i + 2 - 1 = i + 1 by omega)] using hb
  have hchain := massL1_chain_uniform Q ((t + 1) + 1) ((K leakage : ℝ) ^ 3 * δ) hstep
  have hends : massL1 (Q 0) (Q ((t + 1) + 1)) = massL1 P₀ P₁ := by
    simp only [Q, dite_eq_left rfl, dite_eq_right (by omega : ¬(t + 1) + 1 = 0),
      dite_eq_right (by omega : ¬(t + 1) + 1 ≤ t + 1)]
  rw [hends] at hchain
  have hb : 0 ≤ (K leakage : ℝ) ^ 3 * δ := by positivity
  have hcount : (((t + 1) + 1 : ℕ) : ℝ) ≤ 2 * ((t + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : (t + 1) + 1 ≤ 2 * (t + 1))
  change (1 / 2 : ℝ) * massL1 P₀ P₁ ≤ _
  calc
    _ ≤ (1 / 2 : ℝ) * ((((t + 1) + 1 : ℕ) : ℝ) * ((K leakage : ℝ) ^ 3 * δ)) :=
      mul_le_mul_of_nonneg_left hchain (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (2 * ((t + 1 : ℕ) : ℝ) * ((K leakage : ℝ) ^ 3 * δ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcount hb) (by norm_num)
    _ = _ := by ring

end RefreshingProof
