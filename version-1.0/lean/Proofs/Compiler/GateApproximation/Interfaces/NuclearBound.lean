import Proofs.Compiler.GateApproximation.Interfaces.AnswerPairing
import Proofs.Compiler.GateApproximation.Interfaces.NuclearGram



/-!
# A constant nuclear budget for the actual answer-table truncation

This proves a nuclear budget of four for the exact strict truncation of the actual conditional answer table. The bound uses the already-proved general injective-feature variance estimate `κ ≤ 3/d`; its slightly coarser constant replaces the paper's budget of two without changing the cube-root threshold or the leakage-rate exponents.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.TruncatedAnswerNorm

open Refresh MatrixRefresh TableAnalysis RefreshAnalysis SingularTruncation

noncomputable section

/-- The scalar bootstrap with the coarse, fully proved injective-feature variance and density constants. -/
-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For d, β, r, N, κ, δ ∈ ℝ, assume 0 < d; 0 < β; β ≤ 1; 1 ≤ d · β³; 0 ≤ r; 0 ≤ N; 0 ≤ κ; κ ≤ 3 / d; δ ≤ 3 / d; r · β ≤ N; 2 · N ≤ 1 + √(κ · (1 / β²) · r) + δ · (1 / β²). Then

N ≤ 4.
-/
theorem nuclear_bootstrap_four (d β r N κ δ : ℝ)
    (hd : 0 < d) (hβ : 0 < β) (hβone : β ≤ 1) (hthreshold : 1 ≤ d * β ^ 3)
    (hr : 0 ≤ r) (hN : 0 ≤ N) (hκ : 0 ≤ κ) (hκle : κ ≤ 3 / d)
    (hδ : δ ≤ 3 / d) (hrank : r * β ≤ N)
    (hbound : 2 * N ≤ 1 + Real.sqrt (κ * (1 / β ^ 2) * r) + δ * (1 / β ^ 2)) :
    N ≤ 4 := by
  have hrle : r ≤ N / β := (le_div_iff₀ hβ).mpr hrank
  have hvar : κ * (1 / β ^ 2) * r ≤ 3 * N := by
    calc
      _ ≤ (3 / d) * (1 / β ^ 2) * (N / β) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right hκle (by positivity)) hrle hr
          (by positivity)
      _ = (3 * N) / (d * β ^ 3) := by ring
      _ ≤ 3 * N := div_le_self (by positivity) hthreshold
  have hthreshold2 : 1 ≤ d * β ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hβone (show 0 ≤ d * β ^ 2 by positivity)
    nlinarith [hthreshold]
  have herr : δ * (1 / β ^ 2) ≤ 3 := by
    calc
      _ ≤ (3 / d) * (1 / β ^ 2) := mul_le_mul_of_nonneg_right hδ (by positivity)
      _ = 3 / (d * β ^ 2) := by ring
      _ ≤ 3 := div_le_self (by norm_num) hthreshold2
  have ht0 : 0 ≤ κ * (1 / β ^ 2) * r := by positivity
  have htsq := Real.sq_sqrt ht0
  by_contra h
  have hNgt : 4 < N := lt_of_not_ge h
  have hlower : 0 ≤ 2 * N - 4 := by linarith
  have ht : 2 * N - 4 ≤ Real.sqrt (κ * (1 / β ^ 2) * r) := by linarith
  have hs := pow_le_pow_left₀ hlower ht 2
  nlinarith [sq_nonneg (N - 4)]

variable {F X Z : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Z] {m : ℕ}

/-- Direct nuclear bound for the exact strictly truncated conditional answer probability table of any injective binary feature refresh. No operator, Gram, mask-pairing, or nuclear bound is assumed. -/

/-
Mathematical statement (normal notation): Let m ≥ 2, work over the binary field, and let a,b:X → 𝔽₂ᵐ ∖ {0} be injective. For every leakage partition and answer z, put A = prob_z. If 0<β ≤ 1 and |X| · β³ ≥ 1, then

‖A^(>β)‖_* ≤ 4.

The formalized numerical bound here is four; the corresponding displayed bound in the paper is two.
-/
theorem feature_answer_strict_nuclear_le_four (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (p : TableRectanglePartition X (Refresh.«GL» F m) Z) (z : Z)
    (β : ℝ) (hβ : 0 < β) (hβone : β ≤ 1)
    (hthreshold : 1 ≤ (Fintype.card X : ℝ) * β ^ 3) :
    tableNuclearNorm (strictTruncation (answerProb a b p z) β) ≤ 4 := by
  letI : Nonempty (U F m) := ⟨a (Classical.choice inferInstance)⟩
  let A := answerProb a b p z
  have hA : ∀ x y, |A x y| ≤ 1 := AnswerApproximation.answerProb_le_one a b p z
  have hpair := AnswerApproximation.feature_answer_pairing_le_graph_op hq hm a b p z
    (strictPolar A β) (1 / β ^ 2) (by positivity) (strictPolar_entry A β hβ hA)
  rw [strictPolar_pairing, abs_of_nonneg (tableNuclearNorm_nonneg _)] at hpair
  have hmean := strictPolar_graph_mean hq hm a b ha hb A β hβ hA
  have hbound := hpair.trans (add_le_add hmean le_rfl)
  have hd : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcard : (Fintype.card X : ℝ) ≤ (vectorCard F m : ℝ) - 1 := by
    rw [← card_U_real]
    exact_mod_cast Fintype.card_le_of_injective a ha
  have hQ := vectorCard_real_ge_four (F := F) hm
  have hδ : 2 / ((vectorCard F m : ℝ) - 2) ≤ 3 / (Fintype.card X : ℝ) := by
    apply (div_le_div_iff₀ (by linarith) hd).mpr
    nlinarith
  exact nuclear_bootstrap_four (Fintype.card X : ℝ) β (strictRank A β)
    (tableNuclearNorm (strictTruncation A β)) (featureVarianceCoefficient F X m)
    (2 / ((vectorCard F m : ℝ) - 2)) hd hβ hβone hthreshold (strictRank_nonneg A β)
    (tableNuclearNorm_nonneg _) (featureVarianceCoefficient_nonneg hm)
    (featureVarianceCoefficient_le hq hm a ha) hδ (strictRank_mul_cutoff A β) hbound

omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- Ordinary refreshing is the identity-feature instance of the same actual answer-table theorem, with `q = vectorCard F m - 1` nonzero shares. -/

/-
Mathematical statement (normal notation): Let m ≥ 2 and work over the binary field. For every refresh leakage partition and answer z, put A = prob_z. If 0<β ≤ 1 and (2ᵐ-1) · β³ ≥ 1, then

‖A^(>β)‖_* ≤ 4.

The formalized numerical bound here is four; the corresponding displayed bound in the paper is two.
-/
theorem refresh_answer_strict_nuclear_le_four (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (p : TableRectanglePartition (U F m) (Refresh.«GL» F m) Z) (z : Z)
    (β : ℝ) (hβ : 0 < β) (hβone : β ≤ 1)
    (hthreshold : 1 ≤ ((vectorCard F m : ℝ) - 1) * β ^ 3) :
    tableNuclearNorm (strictTruncation (answerProb id id p z) β) ≤ 4 := by
  letI : Nonempty (U F m) := ⟨unitShare ⟨0, by omega⟩⟩
  apply feature_answer_strict_nuclear_le_four hq hm id id Function.injective_id
    Function.injective_id p z β hβ hβone
  simpa only [card_U_real] using hthreshold

end

end CircuitCompiler.TruncatedAnswerNorm
