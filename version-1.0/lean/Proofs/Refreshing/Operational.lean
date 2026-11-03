import Proofs.Refreshing.ModelFacts

/-!
# Properties of the actual refreshing experiment

These lemmas concern the operational definitions in the specification. They do not assume a security estimate or use the challenge theorem.
-/

noncomputable section
open scoped BigOperators

namespace RefreshingProof
open Refreshing

/-- A distribution on a subsingleton type is unique. -/
theorem pmf_unique {α : Type*} [Subsingleton α] (p q : PMF α) : p = q := by
  apply PMF.ext
  intro a
  have mass (r : PMF α) : r a = 1 := by
    calc
      r a = ∑' b, r b := (tsum_eq_single a (fun b hb =>
        False.elim (hb (Subsingleton.elim b a)))).symm
      _ = 1 := r.tsum_coe
  rw [mass p, mass q]

/-- Every prefix of an actual refresh execution preserves the initial secret. -/
theorem runPrefix_preserves_secret {n T leakage : ℕ} (A : Strategy n T leakage)
    (x₀ : State n) (matrices : Fin T → RefreshMatrix n) (i : ℕ) (hi : i ≤ T) :
    secret (runPrefix A x₀ matrices i hi).1 = secret x₀ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [runPrefix]
    rw [refresh_preserves_secret]
    exact ih _

/-- There is no distinguishing transcript when no rounds are run. -/
theorem transcriptDistribution_zero_rounds {n : ℕ} (hn : 2 ≤ n) (leakage : ℕ)
    (A : Strategy n 0 leakage) :
    transcriptDistribution hn A 0 = transcriptDistribution hn A 1 :=
  pmf_unique _ _

/-- Zero-length leakage leaves only the unique formal history, at any horizon. -/
theorem transcriptDistribution_zero_leakage {n T : ℕ} (hn : 2 ≤ n)
    (A : Strategy n T 0) :
    transcriptDistribution hn A 0 = transcriptDistribution hn A 1 :=
  pmf_unique _ _

/-- The statistical distance from a finite distribution to itself is zero. -/
@[simp]
theorem statisticalDistance_self {α : Type*} [Fintype α] (P : PMF α) :
    statisticalDistance P P = 0 := by
  simp [statisticalDistance]

/-- Statistical distance between finite distributions is nonnegative. -/
theorem statisticalDistance_nonneg {α : Type*} [Fintype α] (P Q : PMF α) :
    0 ≤ statisticalDistance P Q := by
  unfold statisticalDistance
  positivity

/-- A finite PMF has total real mass one; no mass is lost in `ENNReal.toReal`. -/
theorem pmf_sum_toReal {α : Type*} [Fintype α] (P : PMF α) :
    ∑ a, (P a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => P.apply_ne_top a)]
  simpa only [tsum_fintype, ENNReal.toReal_one] using
    congrArg ENNReal.toReal P.tsum_coe

/-- The universal probability bound, useful when a rate bound exceeds one. -/
theorem statisticalDistance_le_one {α : Type*} [Fintype α] (P Q : PMF α) :
    statisticalDistance P Q ≤ 1 := by
  have h : ∑ a, |(P a).toReal - (Q a).toReal| ≤ 2 := by
    calc
      _ ≤ ∑ a, ((P a).toReal + (Q a).toReal) := by
        apply Finset.sum_le_sum
        intro a _
        have hp := ENNReal.toReal_nonneg (a := P a)
        have hq := ENNReal.toReal_nonneg (a := Q a)
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      _ = 2 := by rw [Finset.sum_add_distrib, pmf_sum_toReal, pmf_sum_toReal]; norm_num
  unfold statisticalDistance
  linarith

/-- The theorem's left-hand side is exactly zero at T = 0. -/
theorem security_zero_rounds {n : ℕ} (hn : 2 ≤ n) (leakage : ℕ)
    (A : Strategy n 0 leakage) :
    statisticalDistance (transcriptDistribution hn A 0)
      (transcriptDistribution hn A 1) = 0 := by
  rw [transcriptDistribution_zero_rounds hn leakage A, statisticalDistance_self]

/-- The theorem's left-hand side is exactly zero at leakage = 0. -/
theorem security_zero_leakage {n T : ℕ} (hn : 2 ≤ n) (A : Strategy n T 0) :
    statisticalDistance (transcriptDistribution hn A 0)
      (transcriptDistribution hn A 1) = 0 := by
  rw [transcriptDistribution_zero_leakage hn A, statisticalDistance_self]

end RefreshingProof
