import Proofs.Refreshing.LocalApproximation
import Proofs.Refreshing.FiniteExpectation

/-!
# One-signed-round endpoint label changes

Actual finite factors and actual uniform share marginals give the paper's averaged endpoint cost 4D, where D is the proved two-secret discrepancy rate.
-/

noncomputable section
open scoped BigOperators Matrix

namespace RefreshingProof.Local
open Refreshing

/-- Expectation under the uniform finite PMF equals the probability-normalized finite average. -/
theorem pmfMean_uniform_eq_average {X : Type*} [Fintype X] [Nonempty X]
    (H : X → ℝ) : pmfMean (uniformPMF X) H = average H := uniformPMF_expectation H

/-- Expectation over the uniform secret-s encoding fiber equals the initial-table expectation. -/
theorem pmfMean_uniform_encoding_eq {n : ℕ} (hn : 2 ≤ n) (s : Bit)
    [Nonempty (Encoding n s)] (H : State n → ℝ) :
    pmfMean (uniformPMF (Encoding n s)) (fun x => H x.val) = initialTableMean hn s H := by
  rw [pmfMean_uniform_eq_average, initialTableMean_encoding_average]

/-- A share function’s squared L₂ norm is its uniform mean square. -/
theorem shareL2Sq_eq_average {n : ℕ} (H : Share n → ℝ) :
    shareL2Sq H = average (fun x => H x ^ 2) := by simp only [shareL2Sq, average, card_share]

/-- A share function’s squared L₂ norm is nonnegative. -/
theorem shareL2Sq_nonneg {n : ℕ} (H : Share n → ℝ) : 0 ≤ shareL2Sq H := by
  rw [shareL2Sq_eq_average]
  exact average_nonneg fun _ => sq_nonneg _

/-- Squaring the square root of a share function’s squared L₂ norm recovers that norm. -/
@[simp] theorem sqrt_shareL2Sq_sq {n : ℕ} (H : Share n → ℝ) :
    Real.sqrt (shareL2Sq H) ^ 2 = shareL2Sq H := Real.sq_sqrt (shareL2Sq_nonneg H)

/-- Factor cost for changing the old endpoint while fixing the new endpoint. -/
def endpointFactorCost {n m : ℕ} (a b : Fin m → Share n → Share n → ℝ) (x : State n) : ℝ :=
  ∑ i, Real.sqrt (shareL2Sq (fun l => a i l x.1)) * Real.sqrt (shareL2Sq (fun r => b i r x.2))

/-- The averaged left slice energy equals the full grouped factor energy, using the proved actual left marginal of μ_s. -/
theorem endpoint_left_slice_mean {n m : ℕ} (hn : 2 ≤ n) (s : Bit) [Nonempty (Encoding n s)]
    (a : Fin m → Share n → Share n → ℝ) :
    pmfMean (uniformPMF (Encoding n s)) (fun x => ∑ i, shareL2Sq (fun l => a i l x.val.1)) =
      average (fun ll : State n => ∑ i, a i ll.1 ll.2 ^ 2) := by
  rw [pmfMean_uniform_encoding_eq hn s (fun x => ∑ i, shareL2Sq (fun l => a i l x.1)),
    initialTableMean_left_share hn s (fun l' => ∑ i, shareL2Sq (fun l => a i l l'))]
  simp_rw [shareL2Sq_eq_average]
  have hs (l' : Share n) : (∑ i : Fin m, average (fun l => a i l l' ^ 2)) =
      average (fun l => ∑ i : Fin m, a i l l' ^ 2) := (average_sum Finset.univ _).symm
  simp_rw [hs]
  rw [average_comm]
  exact (average_product (fun ll : State n => ∑ i : Fin m, a i ll.1 ll.2 ^ 2)).symm

/-- Averaging right slice energies over an actual uniform endpoint encoding gives the full grouped right-factor energy. -/
theorem endpoint_right_slice_mean {n m : ℕ} (hn : 2 ≤ n) (s : Bit) [Nonempty (Encoding n s)]
    (b : Fin m → Share n → Share n → ℝ) :
    pmfMean (uniformPMF (Encoding n s)) (fun x => ∑ i, shareL2Sq (fun r => b i r x.val.2)) =
      average (fun rr : State n => ∑ i, b i rr.1 rr.2 ^ 2) := by
  rw [pmfMean_uniform_encoding_eq hn s (fun x => ∑ i, shareL2Sq (fun r => b i r x.2)),
    initialTableMean_right_share hn s (fun r' => ∑ i, shareL2Sq (fun r => b i r r'))]
  simp_rw [shareL2Sq_eq_average]
  have hs (r' : Share n) : (∑ i : Fin m, average (fun r => b i r r' ^ 2)) =
      average (fun r => ∑ i : Fin m, b i r r' ^ 2) := (average_sum Finset.univ _).symm
  simp_rw [hs]
  rw [average_comm]
  exact (average_product (fun rr : State n => ∑ i : Fin m, b i rr.1 rr.2 ^ 2)).symm

/-- Product-index weighted means are exactly PMF means of ordinary finite sums. -/
theorem weightedMean_product_index {X J : Type*} [Fintype X] [Fintype J]
    (p : PMF X) (H : X → J → ℝ) :
    weightedMean (fun xj : X × J => (p xj.1).toReal) (fun xj => H xj.1 xj.2) =
      pmfMean p (fun x => ∑ j, H x j) := by
  simp only [weightedMean, pmfMean, Fintype.sum_prod_type, Finset.mul_sum]

/-- Cauchy--Schwarz across both the actual endpoint encoding and the factor index gives endpoint factor cost at most four from two mean-energy bounds. -/
theorem endpointFactorCost_mean_le_four {n m : ℕ} (hn : 2 ≤ n) (s : Bit)
    [Nonempty (Encoding n s)] (a b : Fin m → Share n → Share n → ℝ)
    (ha : average (fun ll : State n => ∑ i, a i ll.1 ll.2 ^ 2) ≤ 4)
    (hb : average (fun rr : State n => ∑ i, b i rr.1 rr.2 ^ 2) ≤ 4) :
    pmfMean (uniformPMF (Encoding n s)) (fun x => endpointFactorCost a b x.val) ≤ 4 := by
  let p := uniformPMF (Encoding n s)
  let w : Encoding n s × Fin m → ℝ := fun xi => (p xi.1).toReal
  let A : Encoding n s × Fin m → ℝ := fun xi => Real.sqrt (shareL2Sq (fun l => a xi.2 l xi.1.val.1))
  let B : Encoding n s × Fin m → ℝ := fun xi => Real.sqrt (shareL2Sq (fun r => b xi.2 r xi.1.val.2))
  have hc := weighted_cauchy_schwarz w A B (fun _ => ENNReal.toReal_nonneg)
  have hA : weightedMean w (fun xi => A xi ^ 2) ≤ 4 := by
    dsimp [w, A]
    simp_rw [sqrt_shareL2Sq_sq]
    rw [weightedMean_product_index p (fun (x : Encoding n s) (i : Fin m) => shareL2Sq (fun l => a i l x.val.1))]
    exact (endpoint_left_slice_mean hn s a).trans_le ha
  have hB : weightedMean w (fun xi => B xi ^ 2) ≤ 4 := by
    dsimp [w, B]
    simp_rw [sqrt_shareL2Sq_sq]
    rw [weightedMean_product_index p (fun (x : Encoding n s) (i : Fin m) => shareL2Sq (fun r => b i r x.val.2))]
    exact (endpoint_right_slice_mean hn s b).trans_le hb
  have he : weightedMean w (fun xi => |A xi * B xi|) =
      pmfMean p (fun x => endpointFactorCost a b x.val) := by
    dsimp [w, A, B]
    rw [weightedMean_product_index p (fun (x : Encoding n s) (i : Fin m) => |Real.sqrt (shareL2Sq (fun l => a i l x.val.1)) * Real.sqrt (shareL2Sq (fun r => b i r x.val.2))|)]
    apply congrArg (pmfMean p)
    funext x
    apply Finset.sum_congr rfl
    intro i hi
    exact abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [he] at hc
  calc
    _ ≤ Real.sqrt (weightedMean w (fun xi => A xi ^ 2)) *
        Real.sqrt (weightedMean w (fun xi => B xi ^ 2)) := hc
    _ ≤ Real.sqrt 4 * Real.sqrt 4 :=
      mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by norm_num

/-- Kernel represented by two grouped local factor arrays. -/
def factorKernel {n m : ℕ} (a b : Fin m → Share n → Share n → ℝ) (x y : State n) : ℝ :=
  ∑ i, a i x.1 y.1 * b i x.2 y.2

/-- Actual two-secret discrepancy applied to a fixed opposite endpoint. -/
theorem factorKernel_endpoint_discrepancy {n m : ℕ} (hn : 2 ≤ n)
    (a b : Fin m → Share n → Share n → ℝ) (y : State n) :
    |initialTableMean hn 0 (fun x => factorKernel a b x y) -
      initialTableMean hn 1 (fun x => factorKernel a b x y)| ≤
      (3 / Real.sqrt ((2 : ℝ) ^ n - 2)) * endpointFactorCost a b y :=
  two_secret_product_sum_discrepancy hn (fun i l => a i l y.1) (fun i r => b i r y.2)

/-- The abstract one-G endpoint bound with actual fixed-secret sampling. -/
theorem factorKernel_averaged_endpoint_le {n m : ℕ} (hn : 2 ≤ n) (s : Bit)
    [Nonempty (Encoding n s)] (a b : Fin m → Share n → Share n → ℝ)
    (ha : average (fun ll : State n => ∑ i, a i ll.1 ll.2 ^ 2) ≤ 4)
    (hb : average (fun rr : State n => ∑ i, b i rr.1 rr.2 ^ 2) ≤ 4) :
    pmfMean (uniformPMF (Encoding n s)) (fun y =>
      |initialTableMean hn 0 (fun x => factorKernel a b x y.val) -
        initialTableMean hn 1 (fun x => factorKernel a b x y.val)|) ≤
      4 * (3 / Real.sqrt ((2 : ℝ) ^ n - 2)) := by
  have h := pmfMean_mono (uniformPMF (Encoding n s)) _ _ (fun y => factorKernel_endpoint_discrepancy hn a b y.val)
  rw [pmfMean_const_mul] at h
  have hc := endpointFactorCost_mean_le_four hn s a b ha hb
  calc
    _ ≤ (3 / Real.sqrt ((2 : ℝ) ^ n - 2)) * pmfMean (uniformPMF (Encoding n s)) (fun x => endpointFactorCost a b x.val) := h
    _ ≤ (3 / Real.sqrt ((2 : ℝ) ^ n - 2)) * 4 := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
/-- A concrete finite product representation transfers the averaged factor bound to the exact encoded-state endpoint expectations. -/
theorem averaged_endpoint_of_factors {n m : ℕ} (hn : 2 ≤ n) (s : Bit)
    [Nonempty (Encoding n 0)] [Nonempty (Encoding n 1)] [Nonempty (Encoding n s)]
    (K : State n → State n → ℝ) (a b : Fin m → Share n → Share n → ℝ)
    (hexpand : ∀ x y, K x y = factorKernel a b x y)
    (ha : average (fun ll : State n => ∑ i, a i ll.1 ll.2 ^ 2) ≤ 4)
    (hb : average (fun rr : State n => ∑ i, b i rr.1 rr.2 ^ 2) ≤ 4) :
    pmfMean (uniformPMF (Encoding n s)) (fun y =>
      |pmfMean (uniformPMF (Encoding n 0)) (fun x => K x.val y.val) -
        pmfMean (uniformPMF (Encoding n 1)) (fun x => K x.val y.val)|) ≤
      4 * (3 / Real.sqrt ((2 : ℝ) ^ n - 2)) := by
  have hm (t : Bit) [Nonempty (Encoding n t)] (y : State n) :
      pmfMean (uniformPMF (Encoding n t)) (fun x => K x.val y) =
        initialTableMean hn t (fun x => factorKernel a b x y) := by
    calc
      _ = pmfMean (uniformPMF (Encoding n t)) (fun x => factorKernel a b x.val y) := by
        apply congrArg (pmfMean _)
        funext x
        exact hexpand x.val y
      _ = _ := pmfMean_uniform_encoding_eq hn t (fun x : State n => factorKernel a b x y)
  simp_rw [hm (0 : Bit), hm (1 : Bit)]
  exact factorKernel_averaged_endpoint_le hn s a b ha hb

/-- Changing the old endpoint label of actual G has averaged cost at most4D. -/
theorem localG_left_endpoint_discrepancy {n leakage : ℕ} (hn : 2 ≤ n) (s : Bit)
    [Nonempty (Encoding n 0)] [Nonempty (Encoding n 1)] [Nonempty (Encoding n s)]
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3) :
    pmfMean (uniformPMF (Encoding n s)) (fun y =>
      |pmfMean (uniformPMF (Encoding n 0)) (fun x => localG f z beta (x.val.1, y.val.1) (x.val.2, y.val.2)) -
        pmfMean (uniformPMF (Encoding n 1)) (fun x => localG f z beta (x.val.1, y.val.1) (x.val.2, y.val.2))|) ≤
      4 * (3 / Real.sqrt ((2 : ℝ) ^ n - 2)) :=
  averaged_endpoint_of_factors hn s (fun x y => localG f z beta (x.1, y.1) (x.2, y.2)) (localLeftFactor f z beta) (localRightFactor f z beta)
    (localG_finite_factor_expansion hn f z beta)
    (localLeftFactor_mean_energy_le hn f z hbeta hbeta1 hthreshold)
    (localRightFactor_mean_energy_le hn f z hbeta hbeta1 hthreshold)

/-- Swapping the two grouped share coordinates leaves the uniform mean energy unchanged. -/
theorem transposed_factor_mean_energy {n m : ℕ} (a : Fin m → Share n → Share n → ℝ) :
    average (fun ll : State n => ∑ i, a i ll.2 ll.1 ^ 2) =
      average (fun ll : State n => ∑ i, a i ll.1 ll.2 ^ 2) := by
  rw [average_product, average_product]
  exact average_comm _

/-- Changing the new endpoint label has the same actual averaged cost4D. -/
theorem localG_right_endpoint_discrepancy {n leakage : ℕ} (hn : 2 ≤ n) (s : Bit)
    [Nonempty (Encoding n 0)] [Nonempty (Encoding n 1)] [Nonempty (Encoding n s)]
    (f : LeakageQuery n leakage) (z : Answer leakage) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hthreshold : 1 ≤ (q n : ℝ) * beta ^ 3) :
    pmfMean (uniformPMF (Encoding n s)) (fun x =>
      |pmfMean (uniformPMF (Encoding n 0)) (fun y => localG f z beta (x.val.1, y.val.1) (x.val.2, y.val.2)) -
        pmfMean (uniformPMF (Encoding n 1)) (fun y => localG f z beta (x.val.1, y.val.1) (x.val.2, y.val.2))|) ≤
      4 * (3 / Real.sqrt ((2 : ℝ) ^ n - 2)) := by
  let a : Fin (localFactorCount f z beta) → Share n → Share n → ℝ :=
    fun i l l' => localLeftFactor f z beta i l' l
  let b : Fin (localFactorCount f z beta) → Share n → Share n → ℝ :=
    fun i r r' => localRightFactor f z beta i r' r
  have ha : average (fun ll : State n => ∑ i, a i ll.1 ll.2 ^ 2) ≤ 4 := by
    change average (fun ll : State n => ∑ i, localLeftFactor f z beta i ll.2 ll.1 ^ 2) ≤ 4
    rw [transposed_factor_mean_energy]
    exact localLeftFactor_mean_energy_le hn f z hbeta hbeta1 hthreshold
  have hb : average (fun rr : State n => ∑ i, b i rr.1 rr.2 ^ 2) ≤ 4 := by
    change average (fun rr : State n => ∑ i, localRightFactor f z beta i rr.2 rr.1 ^ 2) ≤ 4
    rw [transposed_factor_mean_energy]
    exact localRightFactor_mean_energy_le hn f z hbeta hbeta1 hthreshold
  apply averaged_endpoint_of_factors hn s (fun x y => localG f z beta (y.1, x.1) (y.2, x.2)) a b _ ha hb
  intro x y
  exact localG_finite_factor_expansion hn f z beta y x

end RefreshingProof.Local
