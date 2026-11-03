import Proofs.Refreshing.FactorEnergy
import Proofs.Refreshing.LocalApproximation

/-!
# Two neighboring actual signed approximations

Finite product factors and their actual energy bounds imply the averaged label-change estimate, using the proved two-secret discrepancy theorem.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RefreshingProof
open Refreshing

/-- The mean convention in the canonical experiment agrees with the paper's uniform averaging convention. -/
theorem pmfMean_uniform {X : Type*} [Fintype X] [Nonempty X] (F : X → ℝ) :
    pmfMean (uniformPMF X) F = Local.average F := uniformPMF_expectation F

/-- A uniform average over the secret-s encoding fiber equals the corresponding initial-table expectation. -/
theorem encodingMean_eq_initialTableMean {n : ℕ} (hn : 2 ≤ n) (s : Bit)
    [Nonempty (Encoding n s)] (F : State n → ℝ) :
    pmfMean (uniformPMF (Encoding n s)) (fun x => F x.val) = initialTableMean hn s F := by
  rw [Local.initialTableMean_encoding_average]
  exact pmfMean_uniform _

/-- The uniform PMF mean of a share function’s square is its probability-normalized squared L₂ norm. -/
theorem shareMean_sq_eq {n : ℕ} [Nonempty (Share n)] (u : Share n → ℝ) :
    pmfMean (uniformPMF (Share n)) (fun l => u l ^ 2) = shareL2Sq u := by
  rw [pmfMean_uniform]
  simp only [Local.average, shareL2Sq, card_share]

/-- The left share of a uniform secret-s encoding is uniformly distributed over nonzero shares. -/
theorem encodingMean_left_share {n : ℕ} (hn : 2 ≤ n) (s : Bit)
    [Nonempty (Encoding n s)] [Nonempty (Share n)] (F : Share n → ℝ) :
    pmfMean (uniformPMF (Encoding n s)) (fun x => F x.val.1) =
      pmfMean (uniformPMF (Share n)) F := by
  rw [encodingMean_eq_initialTableMean hn s (fun x => F x.1), Local.initialTableMean_left_share hn s,
    pmfMean_uniform]

/-- The right share of a uniform secret-s encoding is uniformly distributed over nonzero shares. -/
theorem encodingMean_right_share {n : ℕ} (hn : 2 ≤ n) (s : Bit)
    [Nonempty (Encoding n s)] [Nonempty (Share n)] (F : Share n → ℝ) :
    pmfMean (uniformPMF (Encoding n s)) (fun x => F x.val.2) =
      pmfMean (uniformPMF (Share n)) F := by
  rw [encodingMean_eq_initialTableMean hn s (fun x => F x.2), Local.initialTableMean_right_share hn s,
    pmfMean_uniform]

/-- Actual second-factor left energy, after averaging an independently sampled outer encoding, is the original grouped-coordinate mean energy. -/
theorem localLeftFactor_outer_mean_le {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3)
    (s : Bit) [Nonempty (Encoding n s)] [Nonempty (Share n)] :
    pmfMean (uniformPMF (Share n)) (fun l =>
      pmfMean (uniformPMF (Encoding n s)) (fun b =>
        ∑ j, Local.localLeftFactor f z beta j l b.val.1 ^ 2)) ≤ 4 := by
  have hb (l : Share n) := encodingMean_left_share hn s
    (fun lb => ∑ j, Local.localLeftFactor f z beta j l lb ^ 2)
  simp_rw [hb, pmfMean_uniform]
  have h := Local.localLeftFactor_mean_energy_le hn f z hbeta hbeta1 hthreshold
  rw [Local.average_product] at h
  exact h

/-- Averaging the right factor’s slice energy over a uniform endpoint is bounded by the local mean-energy estimate. -/
theorem localRightFactor_outer_mean_le {n leakage : ℕ} (hn : 2 ≤ n)
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3)
    (s : Bit) [Nonempty (Encoding n s)] [Nonempty (Share n)] :
    pmfMean (uniformPMF (Share n)) (fun r =>
      pmfMean (uniformPMF (Encoding n s)) (fun b =>
        ∑ j, Local.localRightFactor f z beta j r b.val.2 ^ 2)) ≤ 4 := by
  have hb (r : Share n) := encodingMean_right_share hn s
    (fun rb => ∑ j, Local.localRightFactor f z beta j r rb ^ 2)
  simp_rw [hb, pmfMean_uniform]
  have h := Local.localRightFactor_mean_energy_le hn f z hbeta hbeta1 hthreshold
  rw [Local.average_product] at h
  exact h

/-- Actual two-G product factorization as a table of the common state's shares. -/
theorem localG_product_factor_expansion {n leakage : ℕ} (hn : 2 ≤ n)
    (f₁ f₂ : LeakageQuery n leakage) (z₁ z₂ : Answer leakage) (beta : ℝ)
    (a x b : State n) :
    Local.localG f₁ z₁ beta (a.1, x.1) (a.2, x.2) *
        Local.localG f₂ z₂ beta (x.1, b.1) (x.2, b.2) =
      ∑ ij : Fin (Local.localFactorCount f₁ z₁ beta) × Fin (Local.localFactorCount f₂ z₂ beta),
        (Local.localLeftFactor f₁ z₁ beta ij.1 a.1 x.1 * Local.localLeftFactor f₂ z₂ beta ij.2 x.1 b.1) *
        (Local.localRightFactor f₁ z₁ beta ij.1 a.2 x.2 * Local.localRightFactor f₂ z₂ beta ij.2 x.2 b.2) := by
  rw [Local.localG_finite_factor_expansion hn f₁ z₁ beta a x,
    Local.localG_finite_factor_expansion hn f₂ z₂ beta x b, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Averaged factor cost of the product of two actual approximations. -/
theorem localG_product_factor_cost_le {n leakage : ℕ} (hn : 2 ≤ n)
    (f₁ f₂ : LeakageQuery n leakage) (z₁ z₂ : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3)
    (sA sB : Bit) [Nonempty (Encoding n sA)] [Nonempty (Encoding n sB)] :
    pmfMean (uniformPMF (Encoding n sA)) (fun a => pmfMean (uniformPMF (Encoding n sB)) (fun b =>
      ∑ ij : Fin (Local.localFactorCount f₁ z₁ beta) × Fin (Local.localFactorCount f₂ z₂ beta),
        Real.sqrt (shareL2Sq (fun l => Local.localLeftFactor f₁ z₁ beta ij.1 a.val.1 l *
          Local.localLeftFactor f₂ z₂ beta ij.2 l b.val.1)) *
        Real.sqrt (shareL2Sq (fun r => Local.localRightFactor f₁ z₁ beta ij.1 a.val.2 r *
          Local.localRightFactor f₂ z₂ beta ij.2 r b.val.2)))) ≤ 8 / beta := by
  let : Nonempty (Share n) := Local.share_nonempty_of_two_le hn
  have h := two_round_factor_cost_bound
    (uniformPMF (Encoding n sA)) (uniformPMF (Encoding n sB))
    (uniformPMF (Share n)) (uniformPMF (Share n))
    (fun i a l => Local.localLeftFactor f₁ z₁ beta i a.val.1 l)
    (fun j l b => Local.localLeftFactor f₂ z₂ beta j l b.val.1)
    (fun i a r => Local.localRightFactor f₁ z₁ beta i a.val.2 r)
    (fun j r b => Local.localRightFactor f₂ z₂ beta j r b.val.2)
    (2 / beta) 4 (by positivity) (by norm_num)
    (fun a l => Local.localLeftFactor_point_energy_le hn f₁ z₁ hbeta (a.val.1, l))
    (fun a r => Local.localRightFactor_point_energy_le hn f₁ z₁ hbeta (a.val.2, r))
    (localLeftFactor_outer_mean_le hn f₂ z₂ hbeta hbeta1 hthreshold sB)
    (localRightFactor_outer_mean_le hn f₂ z₂ hbeta hbeta1 hthreshold sB)
  simp_rw [shareMean_sq_eq] at h
  convert h using 1; ring

/-- The paper's averaged two-round label-change estimate 8D/β, derived from actual finite factors, actual uniform marginals, and actual two-secret discrepancy. -/
theorem localG_two_round_label_change {n leakage : ℕ} (hn : 2 ≤ n)
    (f₁ f₂ : LeakageQuery n leakage) (z₁ z₂ : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3)
    (sA sB : Bit) [Nonempty (Encoding n sA)] [Nonempty (Encoding n sB)]
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))] :
    pmfMean (uniformPMF (Encoding n sA)) (fun a => pmfMean (uniformPMF (Encoding n sB)) (fun b =>
      |pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun x =>
          Local.localG f₁ z₁ beta (a.val.1, x.val.1) (a.val.2, x.val.2) *
            Local.localG f₂ z₂ beta (x.val.1, b.val.1) (x.val.2, b.val.2)) -
        pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun x =>
          Local.localG f₁ z₁ beta (a.val.1, x.val.1) (a.val.2, x.val.2) *
            Local.localG f₂ z₂ beta (x.val.1, b.val.1) (x.val.2, b.val.2))|)) ≤
      8 * (3 / Real.sqrt ((2 : ℝ) ^ n - 2)) / beta := by
  let u (a : Encoding n sA) (b : Encoding n sB)
      (ij : Fin (Local.localFactorCount f₁ z₁ beta) × Fin (Local.localFactorCount f₂ z₂ beta)) (l : Share n) :=
    Local.localLeftFactor f₁ z₁ beta ij.1 a.val.1 l * Local.localLeftFactor f₂ z₂ beta ij.2 l b.val.1
  let v (a : Encoding n sA) (b : Encoding n sB)
      (ij : Fin (Local.localFactorCount f₁ z₁ beta) × Fin (Local.localFactorCount f₂ z₂ beta)) (r : Share n) :=
    Local.localRightFactor f₁ z₁ beta ij.1 a.val.2 r * Local.localRightFactor f₂ z₂ beta ij.2 r b.val.2
  have hd (a : Encoding n sA) (b : Encoding n sB) :
      |pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun x =>
          Local.localG f₁ z₁ beta (a.val.1, x.val.1) (a.val.2, x.val.2) *
            Local.localG f₂ z₂ beta (x.val.1, b.val.1) (x.val.2, b.val.2)) -
        pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun x =>
          Local.localG f₁ z₁ beta (a.val.1, x.val.1) (a.val.2, x.val.2) *
            Local.localG f₂ z₂ beta (x.val.1, b.val.1) (x.val.2, b.val.2))| ≤
      (3 / Real.sqrt ((2 : ℝ) ^ n - 2)) *
        ∑ ij, Real.sqrt (shareL2Sq (u a b ij)) * Real.sqrt (shareL2Sq (v a b ij)) := by
    simp_rw [localG_product_factor_expansion hn f₁ f₂ z₁ z₂ beta]
    rw [encodingMean_eq_initialTableMean hn 0 (fun x => ∑ ij, u a b ij x.1 * v a b ij x.2),
      encodingMean_eq_initialTableMean hn 1 (fun x => ∑ ij, u a b ij x.1 * v a b ij x.2)]
    exact two_secret_product_sum_discrepancy hn (u a b) (v a b)
  have hbound := pmfMean_mono (uniformPMF (Encoding n sA)) _ _
    (fun a => pmfMean_mono (uniformPMF (Encoding n sB)) _ _ (hd a))
  simp_rw [pmfMean_const_mul] at hbound
  have hcost := localG_product_factor_cost_le hn f₁ f₂ z₁ z₂ hbeta hbeta1 hthreshold sA sB
  have hD : 0 ≤ 3 / Real.sqrt ((2 : ℝ) ^ n - 2) := by positivity
  calc
    _ ≤ (3 / Real.sqrt ((2 : ℝ) ^ n - 2)) *
        pmfMean (uniformPMF (Encoding n sA)) (fun a => pmfMean (uniformPMF (Encoding n sB)) (fun b =>
          ∑ ij, Real.sqrt (shareL2Sq (u a b ij)) * Real.sqrt (shareL2Sq (v a b ij)))) := hbound
    _ ≤ (3 / Real.sqrt ((2 : ℝ) ^ n - 2)) * (8 / beta) :=
      mul_le_mul_of_nonneg_left hcost hD
    _ = _ := by ring

end RefreshingProof
