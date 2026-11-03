import Proofs.Compiler.GateApproximation.MatrixPhase.AugmentedRefreshLabelled
import Proofs.Compiler.GateApproximation.Interfaces.Gadget.Factors



/-!
# Arbitrary labelled distributions for the augmented matrix phase

All three encodings may be independently labelled. Their joint density is at most 27 relative to independent uniform shares over a binary field. In particular, the bound on the approximation itself holds even when the three labels do not satisfy the gate equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical

namespace CircuitCompiler.GadgetApproximation

open Refresh MatrixRefresh TableAnalysis RefreshAnalysis SingularTruncation

open TruncatedAnswerNorm AveragedEnergyComparison

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n m : ℕ}

/-
Mathematical definition (normal notation): For s, t, v ∈ F, assume 2 ≤ n; 2 ≤ m. define

independentLabelledPortDistribution(s, t, v) := (gateRegroup(n, m)_*((μₛ ⊗ μₜ) ⊗ μᵥ)).
-/
def independentLabelledPortDistribution (hn : 2 ≤ n) (hm : 2 ≤ m) (s t v : F) :
    FiniteDistribution (GateSide F n m × GateSide F n m) :=
  (((mu F n hn s).prod (mu F n hn t)).prod (mu F m hm v)).map (gateRegroup n m)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For k ∈ ℕ; s ∈ F; x ∈ State(F, k), assume |F| = 2; 2 ≤ k. Then

μₛ(x) ≤ 3 · independentStateDistribution(F, k)(x).
-/
theorem mu_weight_le_three (hq : fieldCard F = 2) {k : ℕ} (hk : 2 ≤ k) (s : F)
    (x : State F k) :
    (mu F k hk s).weight x ≤ 3 * (independentStateDistribution F k hk).weight x := by
  rw [mu_weight_density]
  apply mul_le_mul_of_nonneg_right _ ((independentStateDistribution F k hk).nonneg x)
  split_ifs
  · have h := densityWeight_le_q_add_one hk s
    rw [hq] at h
    norm_num at h ⊢
    exact h
  · norm_num

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s, t, v ∈ F; xy ∈ GateSide(F, n, m) × GateSide(F, n, m), assume |F| = 2; 2 ≤ n; 2 ≤ m; U(F, n) ≠ ∅; U(F, m) ≠ ∅. Then

independentLabelledPortDistribution(s, t, v)(xy) ≤ 27 · 𝒰_(GateSide(F, n, m) × GateSide(F, n, m))(xy).
-/
theorem independentLabelledPortDistribution_weight_le (hq : fieldCard F = 2)
    (hn : 2 ≤ n) (hm : 2 ≤ m) (s t v : F)
    [Nonempty (U F n)] [Nonempty (U F m)]
    (xy : GateSide F n m × GateSide F n m) :
    (independentLabelledPortDistribution hn hm s t v).weight xy ≤
      27 * (FiniteDistribution.uniform : FiniteDistribution (GateSide F n m × GateSide F n m)).weight xy := by
  rw [independentLabelledPortDistribution, FiniteDistribution.map_equiv_weight]
  let ab := (gateRegroup n m).symm xy
  change (mu F n hn s).weight ab.1.1 * (mu F n hn t).weight ab.1.2 *
    (mu F m hm v).weight ab.2 ≤ _
  have h12 := mul_le_mul (mu_weight_le_three hq hn s ab.1.1)
    (mu_weight_le_three hq hn t ab.1.2) ((mu F n hn t).nonneg _)
    (mul_nonneg (by norm_num) ((independentStateDistribution F n hn).nonneg _))
  have h123 := mul_le_mul h12 (mu_weight_le_three hq hm v ab.2)
    ((mu F m hm v).nonneg _) (mul_nonneg
      (mul_nonneg (by norm_num) ((independentStateDistribution F n hn).nonneg _))
      (mul_nonneg (by norm_num) ((independentStateDistribution F n hn).nonneg _)))
  refine h123.trans_eq ?_
  simp only [independentStateDistribution_weight, FiniteDistribution.uniform, GateSide, Fintype.card_prod,
    Nat.cast_mul, nonzero_vector_card, mul_inv_rev, div_eq_mul_inv, shareCard, vectorCard]
  ring

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s, t, v ∈ F; f ∈ GateSide(F, n, m) → GateSide(F, n, m) → ℝ, assume |F| = 2; 2 ≤ n; 2 ≤ m; ∀ x, y, 0 ≤ f(x, y). Then

𝔼_(xy ← independentLabelledPortDistribution(s, t, v)) [f((xy)₁, (xy)₂)] ≤ 27 · 𝔼_(xy ∈ GateSide(F, n, m) × GateSide(F, n, m)) [f((xy)₁, (xy)₂)].
-/
theorem independentLabelledPortDistribution_expect_le (hq : fieldCard F = 2)
    (hn : 2 ≤ n) (hm : 2 ≤ m) (s t v : F)
    (f : GateSide F n m → GateSide F n m → ℝ) (hf : ∀ x y, 0 ≤ f x y) :
    (independentLabelledPortDistribution hn hm s t v).expect (fun xy => f xy.1 xy.2) ≤
      27 * uavg (fun xy : GateSide F n m × GateSide F n m => f xy.1 xy.2) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  letI : Nonempty (U F m) := ⟨unitShare ⟨0, by omega⟩⟩
  rw [uavg_eq_expect_uniform]
  unfold FiniteDistribution.expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro xy _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (independentLabelledPortDistribution_weight_le hq hn hm s t v xy) (hf xy.1 xy.2)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s, t, v ∈ F; G ∈ ℝ^(GateSide(F, n, m) × GateSide(F, n, m)), assume |F| = 2; 2 ≤ n; 2 ≤ m. Then

‖ ((xy ↦ G((xy)₁, (xy)₂)))‖_(2,independentLabelledPortDistribution(s, t, v)) ≤ √27 · ‖ G‖₂.
-/
theorem independentLabelledPortDistribution_rms_le (hq : fieldCard F = 2)
    (hn : 2 ≤ n) (hm : 2 ≤ m) (s t v : F)
    (G : Matrix (GateSide F n m) (GateSide F n m) ℝ) :
    rms (independentLabelledPortDistribution hn hm s t v) (fun xy => G xy.1 xy.2) ≤
      Real.sqrt 27 * tableL2Norm G := by
  have h := independentLabelledPortDistribution_expect_le hq hn hm s t v
    (fun x y => G x y ^ 2) (fun _ _ => sq_nonneg _)
  have hsq : uavg (fun xy : GateSide F n m × GateSide F n m => G xy.1 xy.2 ^ 2) =
      tableL2Norm G ^ 2 := (tableL2Norm_sq G).symm
  rw [hsq] at h
  have hr := Real.sqrt_le_sqrt h
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 27), Real.sqrt_sq (tableL2Norm_nonneg G)] at hr
  exact hr

/-- Any labels, including inconsistent labels, give an absolute `L₂` bound for the actual doubled strict approximation. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s, t, v ∈ F; A ∈ ℝ^(GateSide(F, n, m) × GateSide(F, n, m)); β ∈ ℝ, assume |F| = 2; 2 ≤ n; 2 ≤ m; ∀ x, y, |A(x, y)| ≤ 1. Then

‖ ((xy ↦ strictDoubled(A, β, (xy)₁, (xy)₂)))‖_(2,independentLabelledPortDistribution(s, t, v)) ≤ 12.
-/
theorem independentLabelledPortDistribution_doubled_rms_le_twelve (hq : fieldCard F = 2)
    (hn : 2 ≤ n) (hm : 2 ≤ m) (s t v : F)
    (A : Matrix (GateSide F n m) (GateSide F n m) ℝ)
    (β : ℝ) (hA : ∀ x y, |A x y| ≤ 1) :
    rms (independentLabelledPortDistribution hn hm s t v)
      (fun xy => strictDoubled A β xy.1 xy.2) ≤ 12 := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  letI : Nonempty (U F m) := ⟨unitShare ⟨0, by omega⟩⟩
  have h := (independentLabelledPortDistribution_rms_le hq hn hm s t v (strictDoubled A β)).trans
    (mul_le_mul_of_nonneg_left (strictDoubled_l2_le_two A β hA) (Real.sqrt_nonneg 27))
  have hroot : Real.sqrt 27 ≤ 6 := by
    apply Real.sqrt_le_iff.mpr
    norm_num
  linarith

/-- The independent three-label distribution can equally be evaluated by first sampling the two old encodings and then a uniformly sampled output fiber. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s, t, v ∈ F; f ∈ GateSide(F, n, m) → GateSide(F, n, m) → ℝ, assume 2 ≤ n; 2 ≤ m; Fiber(F, m, v) ≠ ∅. Then

𝔼_(ou ← (oldLabelDistribution(s, t) ⊗ 𝒰_(Fiber(F, m, v)))) [f((((ou)₁)₁, ou.2.val.L), (((ou)₁)₂, ou.2.val.R))] = 𝔼_(xy ← independentLabelledPortDistribution(s, t, v)) [f((xy)₁, (xy)₂)].
-/
theorem independentLabelledPortDistribution_fiber_expect
    (hn : 2 ≤ n) (hm : 2 ≤ m) (s t v : F) [Nonempty (Fiber F m v)]
    (f : GateSide F n m → GateSide F n m → ℝ) :
    ((oldLabelDistribution hn s t).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F m v))).expect
      (fun ou => f (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)) =
      (independentLabelledPortDistribution hn hm s t v).expect (fun xy => f xy.1 xy.2) := by
  rw [independentLabelledPortDistribution, expect_map, expect_prod,
    expect_prod, oldLabelDistribution, expect_map]
  simp only [mu, expect_map]
  rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): If a tuple has positive probability under independently sampled encodings of s, t, and s · t+c, then its augmented old shares and long output shares are consistent: their inner products are equal. -/
theorem independentLabelledPortDistribution_valid
    (hn : 2 ≤ n) (c s t : F) (xy : GateSide F n (n*n+1) × GateSide F n (n*n+1))
    (hxy : (independentLabelledPortDistribution hn (by nlinarith) s t (s*t+c)).weight xy ≠ 0) :
    refreshConsistent (Rectangular.augmentedShare c) (Rectangular.augmentedShare 1)
      xy.1 xy.2 := by
  rw [independentLabelledPortDistribution, FiniteDistribution.map_equiv_weight] at hxy
  change ((mu F n hn s).weight ⟨xy.1.1.1,xy.2.1.1⟩ *
    (mu F n hn t).weight ⟨xy.1.1.2,xy.2.1.2⟩) *
    (mu F (n*n+1) (by nlinarith) (s*t+c)).weight ⟨xy.1.2,xy.2.2⟩ ≠ 0 at hxy
  have hs := mu_supports n hn s ⟨xy.1.1.1,xy.2.1.1⟩
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hxy).1).1
  have ht := mu_supports n hn t ⟨xy.1.1.2,xy.2.1.2⟩
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hxy).1).2
  have hv := mu_supports (n*n+1) (by nlinarith) (s*t+c) ⟨xy.1.2,xy.2.2⟩
    (mul_ne_zero_iff.mp hxy).2
  simp only [secret, stateLeftShare, stateRightShare] at hs ht hv
  unfold refreshConsistent
  rw [Rectangular.augmentedShare_dot, hs, ht]
  exact hv

/-- On valid gate labels the consistency projection changes no evaluated entry, so the global supported residual is exactly the desired error. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): On the valid-label distribution μₛ ⊗ μₜ ⊗ μ_(s · t+c), every sampled tuple is consistent. Therefore for arbitrary real tables A,H,

‖A-2 · H‖₂ = ‖A-2 · project(H)‖₂,

where both norms in this identity use that valid-label distribution.
-/
theorem validLabelled_projection_error_rms
    (hn : 2 ≤ n) (c s t : F)
    (A H : Matrix (GateSide F n (n*n+1)) (GateSide F n (n*n+1)) ℝ) :
    rms (independentLabelledPortDistribution hn (by nlinarith) s t (s*t+c))
      (fun xy => A xy.1 xy.2 - 2 * H xy.1 xy.2) =
    rms (independentLabelledPortDistribution hn (by nlinarith) s t (s*t+c))
      (fun xy => (A - (2 : ℝ) • project
        (refreshConsistent (Rectangular.augmentedShare c) (Rectangular.augmentedShare 1)) H)
        xy.1 xy.2) := by
  unfold rms
  congr 1
  unfold FiniteDistribution.expect
  apply Finset.sum_congr rfl
  intro xy _
  by_cases hxy : (independentLabelledPortDistribution hn (by nlinarith) s t (s*t+c)).weight xy = 0
  · simp [hxy]
  · have hv := independentLabelledPortDistribution_valid hn c s t xy hxy
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, project, if_pos hv]

end

end CircuitCompiler.GadgetApproximation
