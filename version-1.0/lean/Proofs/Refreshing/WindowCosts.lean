import Proofs.Refreshing.NeighborApproximation
import Proofs.Refreshing.EndpointApproximation
import Proofs.Refreshing.ReplacementCosts

/-!
# Actual local approximation implies the comparison window estimates
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RefreshingProof
open Refreshing

/-- The actual local signed approximation, with each party’s old and new shares grouped together. -/
def actualSignedRound {n leakage : ℕ} (f : LeakageQuery n leakage)
    (z : Answer leakage) (beta : ℝ) (x y : State n) : ℝ :=
  Local.localG f z beta (x.1, y.1) (x.2, y.2)

/-- The only local approximation error hypothesis, before the actual residual transfer theorem supplies its explicit numeric value. -/
def ActualErrorBound (n leakage : ℕ) (beta ε : ℝ) : Prop :=
  ∀ (f : LeakageQuery n leakage) (z : Answer leakage) (s : Bit),
    Real.sqrt (Local.average (fun x : Encoding n s => Local.average (fun y : Encoding n s =>
      ((conditionalAnswer f x y z).toReal - actualSignedRound f z beta x.val y.val) ^ 2))) ≤ ε

/-- The local error hypothesis bounds the RMS difference between the actual conditional answer and signed approximation under independent uniform same-secret endpoints. -/
theorem actualError_pmf_norm {n leakage : ℕ} {beta ε : ℝ}
    (herror : ActualErrorBound n leakage beta ε)
    (f : LeakageQuery n leakage) (z : Answer leakage) (s : Bit) [Nonempty (Encoding n s)] :
    Real.sqrt (pmfMean (uniformPMF (Encoding n s)) (fun x =>
      pmfMean (uniformPMF (Encoding n s)) (fun y =>
        ((conditionalAnswer f x y z).toReal - actualSignedRound f z beta x.val y.val) ^ 2))) ≤ ε := by
  simp_rw [pmfMean_uniform]
  exact herror f z s

/-- For arbitrary endpoint secrets, the actual signed approximation has RMS norm at most six under independent uniform encodings. -/
theorem actualSigned_pmf_norm {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) (beta : ℝ) (s t : Bit)
    [Nonempty (Encoding n s)] [Nonempty (Encoding n t)] :
    Real.sqrt (pmfMean (uniformPMF (Encoding n s)) (fun x =>
      pmfMean (uniformPMF (Encoding n t)) (fun y =>
        actualSignedRound f z beta x.val y.val ^ 2))) ≤ 6 := by
  simp_rw [pmfMean_uniform]
  exact Local.localG_encoding_norm_le_six hn f z beta s t

/-- Reversing the error's sign does not change its L₂ norm. -/
theorem actualError_reverse_pmf_norm {n leakage : ℕ} {beta ε : ℝ}
    (herror : ActualErrorBound n leakage beta ε)
    (f : LeakageQuery n leakage) (z : Answer leakage) (s : Bit) [Nonempty (Encoding n s)] :
    Real.sqrt (pmfMean (uniformPMF (Encoding n s)) (fun x =>
      pmfMean (uniformPMF (Encoding n s)) (fun y =>
        (actualSignedRound f z beta x.val y.val - (conditionalAnswer f x y z).toReal) ^ 2))) ≤ ε := by
  have hsq : pmfMean (uniformPMF (Encoding n s)) (fun x =>
      pmfMean (uniformPMF (Encoding n s)) (fun y =>
        (actualSignedRound f z beta x.val y.val - (conditionalAnswer f x y z).toReal) ^ 2)) =
    pmfMean (uniformPMF (Encoding n s)) (fun x =>
      pmfMean (uniformPMF (Encoding n s)) (fun y =>
        ((conditionalAnswer f x y z).toReal - actualSignedRound f z beta x.val y.val) ^ 2)) := by
    apply congrArg (pmfMean (uniformPMF (Encoding n s)))
    funext x
    apply congrArg (pmfMean (uniformPMF (Encoding n s)))
    funext y
    ring
  rw [hsq]
  exact actualError_pmf_norm herror f z s

/-- The second orientation of no-companion replacement. -/
theorem replacement_no_companion_left {A B : Type*} [Fintype A] [Fintype B]
    (μA : PMF A) (μB : PMF B) (e : A → B → ℝ) (ε : ℝ)
    (he : Real.sqrt (pmfMean μA (fun a => pmfMean μB (fun b => e a b ^ 2))) ≤ ε) :
    pmfMean μA (fun a => |pmfMean μB (fun b => e a b)|) ≤ ε := by
  apply replacement_no_companion μB μA (fun b a => e a b) ε
  rw [pmfMean_comm μB μA]
  exact he

/-- Initial endpoint: valid-round approximation error plus the one-G old-state label change costs at most ε+4D per answer, averaged over the new state. -/
theorem actual_first_error_le {n leakage : ℕ} (hn : 2 ≤ n)
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta ε : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3)
    (herror : ActualErrorBound n leakage beta ε) :
    pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun b =>
      |pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun a => (conditionalAnswer f a b z).toReal) -
        pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun a => actualSignedRound f z beta a.val b.val)|) ≤
      ε + 4 * (3 / Real.sqrt ((2 : ℝ) ^ n - 2)) := by
  have hpoint (b : Encoding n (0 : Bit)) := abs_sub_le
    (pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun a => (conditionalAnswer f a b z).toReal))
    (pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun a => actualSignedRound f z beta a.val b.val))
    (pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun a => actualSignedRound f z beta a.val b.val))
  simp_rw [← pmfMean_sub] at hpoint
  have hbound := pmfMean_mono (uniformPMF (Encoding n (0 : Bit))) _ _ hpoint
  rw [pmfMean_add] at hbound
  have hrep := replacement_no_companion
    (uniformPMF (Encoding n (0 : Bit))) (uniformPMF (Encoding n (0 : Bit)))
    (fun a b => (conditionalAnswer f a b z).toReal - actualSignedRound f z beta a.val b.val)
    ε (actualError_pmf_norm herror f z 0)
  have hdisc := Local.localG_left_endpoint_discrepancy hn 0 f z hbeta hbeta1 hthreshold
  exact hbound.trans (add_le_add hrep hdisc)

/-- Terminal endpoint: the one-G new-state label change and valid approximation error cost at most ε+4D per answer. -/
theorem actual_last_error_le {n leakage : ℕ} (hn : 2 ≤ n)
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta ε : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3)
    (herror : ActualErrorBound n leakage beta ε) :
    pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun a =>
      |pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun b => actualSignedRound f z beta a.val b.val) -
        pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun b => (conditionalAnswer f a b z).toReal)|) ≤
      ε + 4 * (3 / Real.sqrt ((2 : ℝ) ^ n - 2)) := by
  have hpoint (a : Encoding n (1 : Bit)) := abs_sub_le
    (pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun b => actualSignedRound f z beta a.val b.val))
    (pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun b => actualSignedRound f z beta a.val b.val))
    (pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun b => (conditionalAnswer f a b z).toReal))
  simp_rw [← pmfMean_sub] at hpoint
  have hbound := pmfMean_mono (uniformPMF (Encoding n (1 : Bit))) _ _ hpoint
  rw [pmfMean_add] at hbound
  have hrep := replacement_no_companion_left
    (uniformPMF (Encoding n (1 : Bit))) (uniformPMF (Encoding n (1 : Bit)))
    (fun a b => actualSignedRound f z beta a.val b.val - (conditionalAnswer f a b z).toReal)
    ε (actualError_reverse_pmf_norm herror f z 1)
  have hdisc := Local.localG_right_endpoint_discrepancy hn 1 f z hbeta hbeta1 hthreshold
  have h := hbound.trans (add_le_add hdisc hrep)
  linarith

/-- Two-round local comparison from actual finite factors and actual valid-round L₂ approximation errors. The answer functions are arbitrary fixed local queries. -/
theorem actual_two_round_error_le {n leakage : ℕ} (hn : 2 ≤ n)
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (f₁ f₂ : LeakageQuery n leakage) (z₁ z₂ : Answer leakage) {beta ε : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3)
    (herror : ActualErrorBound n leakage beta ε) :
    pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun a =>
      pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun b =>
        |pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun x =>
            actualSignedRound f₁ z₁ beta a.val x.val * (conditionalAnswer f₂ x b z₂).toReal) -
          pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun x =>
            (conditionalAnswer f₁ a x z₁).toReal * actualSignedRound f₂ z₂ beta x.val b.val)|)) ≤
      12 * ε + 8 * ((3 / Real.sqrt ((2 : ℝ) ^ n - 2)) / beta) := by
  let F₀ (a : Encoding n (1 : Bit)) (b : Encoding n (0 : Bit)) :=
    pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun x =>
      actualSignedRound f₁ z₁ beta a.val x.val * (conditionalAnswer f₂ x b z₂).toReal)
  let F₁ (a : Encoding n (1 : Bit)) (b : Encoding n (0 : Bit)) :=
    pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun x =>
      actualSignedRound f₁ z₁ beta a.val x.val * actualSignedRound f₂ z₂ beta x.val b.val)
  let F₂ (a : Encoding n (1 : Bit)) (b : Encoding n (0 : Bit)) :=
    pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun x =>
      actualSignedRound f₁ z₁ beta a.val x.val * actualSignedRound f₂ z₂ beta x.val b.val)
  let F₃ (a : Encoding n (1 : Bit)) (b : Encoding n (0 : Bit)) :=
    pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun x =>
      (conditionalAnswer f₁ a x z₁).toReal * actualSignedRound f₂ z₂ beta x.val b.val)
  apply local_three_move_bound (uniformPMF (Encoding n (1 : Bit)))
    (uniformPMF (Encoding n (0 : Bit))) F₀ F₁ F₂ F₃ ε _
  · have hid (a : Encoding n (1 : Bit)) (b : Encoding n (0 : Bit)) :
        F₀ a b - F₁ a b = pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun x =>
          ((conditionalAnswer f₂ x b z₂).toReal - actualSignedRound f₂ z₂ beta x.val b.val) *
            actualSignedRound f₁ z₁ beta a.val x.val) := by
      dsimp [F₀, F₁]
      rw [← pmfMean_sub]
      apply congrArg (pmfMean (uniformPMF (Encoding n (0 : Bit))))
      funext x
      ring
    simp_rw [hid]
    exact replacement_second_table
      (uniformPMF (Encoding n (1 : Bit))) (uniformPMF (Encoding n (0 : Bit)))
      (uniformPMF (Encoding n (0 : Bit))) _ _ ε
      (actualError_pmf_norm herror f₂ z₂ 0) (actualSigned_pmf_norm hn f₁ z₁ beta 1 0)
  · simpa only [F₁, F₂, actualSignedRound, mul_div_assoc] using
      localG_two_round_label_change hn f₁ f₂ z₁ z₂ hbeta hbeta1 hthreshold 1 0
  · have hid (a : Encoding n (1 : Bit)) (b : Encoding n (0 : Bit)) :
        F₂ a b - F₃ a b = pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun x =>
          (actualSignedRound f₁ z₁ beta a.val x.val - (conditionalAnswer f₁ a x z₁).toReal) *
            actualSignedRound f₂ z₂ beta x.val b.val) := by
      dsimp [F₂, F₃]
      rw [← pmfMean_sub]
      apply congrArg (pmfMean (uniformPMF (Encoding n (1 : Bit))))
      funext x
      ring
    simp_rw [hid]
    exact replacement_first_table
      (uniformPMF (Encoding n (1 : Bit))) (uniformPMF (Encoding n (1 : Bit)))
      (uniformPMF (Encoding n (0 : Bit))) _ _ ε
      (actualError_reverse_pmf_norm herror f₁ z₁ 1) (actualSigned_pmf_norm hn f₂ z₂ beta 1 0)

end RefreshingProof
