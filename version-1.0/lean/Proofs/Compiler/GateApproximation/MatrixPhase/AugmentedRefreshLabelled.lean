import Proofs.Compiler.GateApproximation.MatrixPhase.AugmentedRefreshApproximation
import Proofs.Compiler.GateApproximation.MatrixPhase.FullGateApproximation



/-!
# One augmented matrix approximation for every pair of input labels

Fixing the two old plaintexts costs only the existing `4 q²` density factor. The output fiber contains their product plus the public offset. The common approximating tables are selected before either plaintext label is fixed.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {F Z : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype Z]

variable {n m : ℕ}

/-- Reference port distribution with an arbitrary public additive offset. -/
/-
Mathematical definition (normal notation): For c ∈ F, assume 2 ≤ n; 2 ≤ m. define

offsetJointPortDistribution(c) := (gateRegroup(n, m)_*joint((independentStateDistribution(F, n) ⊗ independentStateDistribution(F, n)))(((ab ↦ μ_(secret((ab)₁) · secret((ab)₂) + c))))).
-/
def offsetJointPortDistribution (hn : 2 ≤ n) (hm : 2 ≤ m) (c : F) :
    FiniteDistribution (GateSide F n m × GateSide F n m) :=
  (((independentStateDistribution F n hn).prod (independentStateDistribution F n hn)).joint
    (fun ab => mu F m hm (secret ab.1 * secret ab.2 + c))).map (gateRegroup n m)

/-- The same experiment with its two operand plaintexts fixed. -/
/-
Mathematical definition (normal notation): For c, s, t ∈ F, assume 2 ≤ n; 2 ≤ m. define

offsetLabelledPortDistribution(c, s, t) := (gateRegroup(n, m)_*joint((μₛ ⊗ μₜ))(((ab ↦ μ_(secret((ab)₁) · secret((ab)₂) + c))))).
-/
def offsetLabelledPortDistribution (hn : 2 ≤ n) (hm : 2 ≤ m) (c s t : F) :
    FiniteDistribution (GateSide F n m × GateSide F n m) :=
  (((mu F n hn s).prod (mu F n hn t)).joint
    (fun ab => mu F m hm (secret ab.1 * secret ab.2 + c))).map (gateRegroup n m)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c ∈ F; x, y ∈ GateSide(F, n, m), assume 2 ≤ n; 2 ≤ m. Then

offsetJointPortDistribution(c)((x, y)) = (|GateSide(F, n, m)|)⁻¹ · ((|GateSide(F, n, m)|)⁻¹ · encodingDensity((portProduct(x, y) + c), (x)₂, (y)₂)).
-/
theorem offsetJointPortDistribution_weight (hn : 2 ≤ n) (hm : 2 ≤ m) (c : F)
    (x y : GateSide F n m) :
    (offsetJointPortDistribution hn hm c).weight (x,y) =
      (Fintype.card (GateSide F n m) : ℝ)⁻¹ *
        ((Fintype.card (GateSide F n m) : ℝ)⁻¹ *
          encodingDensity (portProduct x y + c) x.2 y.2) := by
  rw [offsetJointPortDistribution, FiniteDistribution.map_equiv_weight]
  change (independentStateDistribution F n hn).weight _ *
    (independentStateDistribution F n hn).weight _ * (mu F m hm _).weight _ = _
  rw [mu_weight_density]
  simp only [independentStateDistribution_weight]
  change (1 / (shareCard F n : ℝ) ^ 2) * (1 / (shareCard F n : ℝ) ^ 2) *
    (encodingDensity (portProduct x y+c) x.2 y.2 * (1 / (shareCard F m : ℝ) ^ 2)) = _
  simp only [GateSide, Fintype.card_prod, Nat.cast_mul, nonzero_vector_card]
  change _ = ((shareCard F n : ℝ) * shareCard F n * shareCard F m)⁻¹ *
    (((shareCard F n : ℝ) * shareCard F n * shareCard F m)⁻¹ * encodingDensity (portProduct x y+c) x.2 y.2)
  simp only [mul_inv_rev, div_eq_mul_inv]
  ring

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c ∈ F; f ∈ GateSide(F, n, m) → GateSide(F, n, m) → ℝ, assume 2 ≤ n; 2 ≤ m. Then

𝔼_(xy ← offsetJointPortDistribution(c)) [f((xy)₁, (xy)₂)] = 𝔼ₓ [𝔼_y [encodingDensity((portProduct(x, y) + c), (x)₂, (y)₂) · f(x, y)]].
-/
theorem offsetJointPortDistribution_expect (hn : 2 ≤ n) (hm : 2 ≤ m) (c : F)
    (f : GateSide F n m → GateSide F n m → ℝ) :
    (offsetJointPortDistribution hn hm c).expect (fun xy => f xy.1 xy.2) =
      uavg (fun x => uavg (fun y => encodingDensity (portProduct x y+c) x.2 y.2 * f x y)) := by
  simp only [FiniteDistribution.expect, Fintype.sum_prod_type, offsetJointPortDistribution_weight, uavg,
    Finset.mul_sum, mul_assoc]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c, s, t ∈ F; xy ∈ GateSide(F, n, m) × GateSide(F, n, m), assume 2 ≤ n; 2 ≤ m. Then

offsetLabelledPortDistribution(c, s, t)(xy) ≤ (4 · (|F|)²) · offsetJointPortDistribution(c)(xy).
-/
theorem offsetLabelledPortDistribution_weight_le (hn : 2 ≤ n) (hm : 2 ≤ m)
    (c s t : F) (xy : GateSide F n m × GateSide F n m) :
    (offsetLabelledPortDistribution hn hm c s t).weight xy ≤
      (4 * (fieldCard F : ℝ)^2) * (offsetJointPortDistribution hn hm c).weight xy := by
  rw [offsetLabelledPortDistribution, offsetJointPortDistribution, FiniteDistribution.map_equiv_weight, FiniteDistribution.map_equiv_weight]
  change (mu F n hn s).weight _ * (mu F n hn t).weight _ *
    (mu F m hm _).weight _ ≤ _ *
      ((independentStateDistribution F n hn).weight _ * (independentStateDistribution F n hn).weight _ *
        (mu F m hm _).weight _)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mixed_state_density_le n hn s t _ _)
    ((mu F m hm _).nonneg _)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c, s, t ∈ F; f ∈ GateSide(F, n, m) → GateSide(F, n, m) → ℝ, assume 2 ≤ n; 2 ≤ m; ∀ x, y, 0 ≤ f(x, y). Then

𝔼_(xy ← offsetLabelledPortDistribution(c, s, t)) [f((xy)₁, (xy)₂)] ≤ (4 · (|F|)²) · 𝔼ₓ [𝔼_y [encodingDensity((portProduct(x, y) + c), (x)₂, (y)₂) · f(x, y)]].
-/
theorem offsetLabelledPortDistribution_expect_le (hn : 2 ≤ n) (hm : 2 ≤ m) (c s t : F)
    (f : GateSide F n m → GateSide F n m → ℝ) (hf : ∀ x y, 0 ≤ f x y) :
    (offsetLabelledPortDistribution hn hm c s t).expect (fun xy => f xy.1 xy.2) ≤
      (4 * (fieldCard F : ℝ)^2) * uavg (fun x => uavg (fun y =>
        encodingDensity (portProduct x y+c) x.2 y.2 * f x y)) := by
  rw [← offsetJointPortDistribution_expect hn hm c]
  unfold FiniteDistribution.expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro xy _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (offsetLabelledPortDistribution_weight_le hn hm c s t xy) (hf xy.1 xy.2)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c, s, t ∈ F, assume 2 ≤ n; 2 ≤ m. Then

joint((μₛ ⊗ μₜ))(((ab ↦ μ_(secret((ab)₁) · secret((ab)₂) + c)))) = ((μₛ ⊗ μₜ) ⊗ μ_(s · t + c)).
-/
private theorem offset_old_joint_eq_prod (hn : 2 ≤ n) (hm : 2 ≤ m) (c s t : F) :
    ((mu F n hn s).prod (mu F n hn t)).joint
      (fun ab => mu F m hm (secret ab.1 * secret ab.2 + c)) =
    ((mu F n hn s).prod (mu F n hn t)).prod (mu F m hm (s*t+c)) := by
  ext abu
  change ((mu F n hn s).prod (mu F n hn t)).weight abu.1 *
      (mu F m hm (secret abu.1.1 * secret abu.1.2+c)).weight abu.2 =
    ((mu F n hn s).prod (mu F n hn t)).weight abu.1 * (mu F m hm (s*t+c)).weight abu.2
  by_cases h : ((mu F n hn s).prod (mu F n hn t)).weight abu.1 = 0
  · simp [h]
  · have h' : (mu F n hn s).weight abu.1.1 * (mu F n hn t).weight abu.1.2 ≠ 0 := h
    rw [mu_supports n hn s abu.1.1 (mul_ne_zero_iff.mp h').1,
      mu_supports n hn t abu.1.2 (mul_ne_zero_iff.mp h').2]

/-- Presampling the product-plus-offset output fiber is the labelled port distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c, s, t ∈ F; f ∈ GateSide(F, n, m) → GateSide(F, n, m) → ℝ, assume 2 ≤ n; 2 ≤ m; Fiber(F, m, (s · t + c)) ≠ ∅. Then

𝔼_(ou ← (oldLabelDistribution(s, t) ⊗ 𝒰_(Fiber(F, m, (s · t + c))))) [f((((ou)₁)₁, ou.2.val.L), (((ou)₁)₂, ou.2.val.R))] = 𝔼_(xy ← offsetLabelledPortDistribution(c, s, t)) [f((xy)₁, (xy)₂)].
-/
theorem offset_oldLabelDistribution_fiber_expect (hn : 2 ≤ n) (hm : 2 ≤ m) (c s t : F)
    [Nonempty (Fiber F m (s*t+c))]
    (f : GateSide F n m → GateSide F n m → ℝ) :
    ((oldLabelDistribution hn s t).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F m (s*t+c)))).expect
      (fun ou => f (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)) =
    (offsetLabelledPortDistribution hn hm c s t).expect (fun xy => f xy.1 xy.2) := by
  rw [offsetLabelledPortDistribution, offset_old_joint_eq_prod hn hm c s t, expect_map, expect_prod]
  rw [expect_prod, oldLabelDistribution, expect_map]
  simp only [mu, expect_map]
  rfl

/-- The masked conditional table equals the actual answer distribution on every old encoding in the support of the chosen input labels. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c, s, t ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n + 1)(F), Z); o ∈ (U(F, n) × U(F, n)) × (U(F, n) × U(F, n)); u ∈ Fiber(F, (n · n + 1), (s · t + c)); z ∈ Z, assume 2 ≤ n; oldLabelDistribution(s, t)(o) ≠ 0. Then

answerDistribution(Rectangular.augmentedShare(c), Rectangular.augmentedShare(1), p, (o)₁, (o)₂, u)(z) = answerProb(Rectangular.augmentedShare(c), Rectangular.augmentedShare(1), p, z, ((o)₁, u.val.L), ((o)₂, u.val.R)).
-/
theorem augmented_answer_prob_on_support (hn : 2 ≤ n) (c s t : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) Z)
    (o : (U F n × U F n) × (U F n × U F n))
    (ho : (oldLabelDistribution hn s t).weight o ≠ 0)
    (u : Fiber F (n*n+1) (s*t+c)) (z : Z) :
    (answerDistribution (Rectangular.augmentedShare c) (Rectangular.augmentedShare 1)
      p o.1 o.2 u.val).weight z =
    answerProb (Rectangular.augmentedShare c) (Rectangular.augmentedShare 1)
      p z (o.1,u.val.L) (o.2,u.val.R) := by
  have ho' := oldLabelDistribution_product hn s t o ho
  have hu : dot u.val.L.val u.val.R.val = s*t+c := u.property
  simp only [answerProb, Rectangular.augmentedShare_dot, ho', hu, if_pos]

/-- Passing the same table error to fixed input labels costs at most `4q²`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c, s, t ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n + 1)(F), Z); G ∈ Z → ℝ^(GateSide(F, n, (n · n + 1)) × GateSide(F, n, (n · n + 1))); η ∈ ℝ, assume 2 ≤ n; Fiber(F, (n · n + 1), (s · t + c)) ≠ ∅; (∑_z (𝔼_(xy ∈ GateSide(F, n, (n · n + 1)) × GateSide(F, n, (n · n + 1))) [refreshDensity(Rectangular.augmentedShare(c), Rectangular.augmentedShare(1), (xy)₁, (xy)₂) · |answerProb(Rectangular.augmentedShare(c), Rectangular.augmentedShare(1), p, z, (xy)₁, (xy)₂) - G(z, (xy)₁, (xy)₂)|])) ≤ η. Then

𝔼_(ou ← (oldLabelDistribution(s, t) ⊗ 𝒰_(Fiber(F, (n · n + 1), (s · t + c))))) [∑_z (|answerProb(Rectangular.augmentedShare(c), Rectangular.augmentedShare(1), p, z, (((ou)₁)₁, ou.2.val.L), (((ou)₁)₂, ou.2.val.R)) - G(z, (((ou)₁)₁, ou.2.val.L), (((ou)₁)₂, ou.2.val.R))|)] ≤ 4 · (|F|)² · η.
-/
theorem augmented_fixed_labels_table_L1 (hn : 2 ≤ n) (c s t : F)
    [Nonempty (Fiber F (n*n+1) (s*t+c))]
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) Z)
    (G : Z → Matrix (GateSide F n (n*n+1)) (GateSide F n (n*n+1)) ℝ)
    (η : ℝ)
    (herr : (∑ z, uavg (fun xy : GateSide F n (n*n+1) × GateSide F n (n*n+1) =>
      refreshDensity (Rectangular.augmentedShare c) (Rectangular.augmentedShare 1) xy.1 xy.2 *
        |answerProb (Rectangular.augmentedShare c) (Rectangular.augmentedShare 1)
          p z xy.1 xy.2 - G z xy.1 xy.2|)) ≤ η) :
    ((oldLabelDistribution hn s t).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n*n+1) (s*t+c)))).expect
      (fun ou => ∑ z, |answerProb (Rectangular.augmentedShare c)
        (Rectangular.augmentedShare 1) p z (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R) -
          G z (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)|) ≤ 4*(fieldCard F : ℝ)^2*η := by
  rw [offset_oldLabelDistribution_fiber_expect hn (by nlinarith) c s t (fun x y => ∑ z,
    |answerProb (Rectangular.augmentedShare c) (Rectangular.augmentedShare 1)
      p z x y - G z x y|)]
  apply (offsetLabelledPortDistribution_expect_le hn (by nlinarith) c s t
    (fun x y => ∑ z, |answerProb (Rectangular.augmentedShare c)
      (Rectangular.augmentedShare 1) p z x y - G z x y|)
    (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 4*(fieldCard F : ℝ)^2)
  simpa only [augmented_refreshDensity, portProduct, uavg_prod, Finset.mul_sum, uavg_sum] using herr

/-- The same estimate holds for the actual conditional matrix answer distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c, s, t ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n + 1)(F), Z); G ∈ Z → ℝ^(GateSide(F, n, (n · n + 1)) × GateSide(F, n, (n · n + 1))); η ∈ ℝ, assume 2 ≤ n; Fiber(F, (n · n + 1), (s · t + c)) ≠ ∅; (∑_z (𝔼_(xy ∈ GateSide(F, n, (n · n + 1)) × GateSide(F, n, (n · n + 1))) [refreshDensity(Rectangular.augmentedShare(c), Rectangular.augmentedShare(1), (xy)₁, (xy)₂) · |answerProb(Rectangular.augmentedShare(c), Rectangular.augmentedShare(1), p, z, (xy)₁, (xy)₂) - G(z, (xy)₁, (xy)₂)|])) ≤ η. Then

𝔼_(ou ← (oldLabelDistribution(s, t) ⊗ 𝒰_(Fiber(F, (n · n + 1), (s · t + c))))) [∑_z (|answerDistribution(Rectangular.augmentedShare(c), Rectangular.augmentedShare(1), p, ((ou)₁)₁, ((ou)₁)₂, (ou)₂)(z) - G(z, (((ou)₁)₁, ou.2.val.L), (((ou)₁)₂, ou.2.val.R))|)] ≤ 4 · (|F|)² · η.
-/
theorem augmented_fixed_labels_L1 (hn : 2 ≤ n) (c s t : F)
    [Nonempty (Fiber F (n*n+1) (s*t+c))]
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) Z)
    (G : Z → Matrix (GateSide F n (n*n+1)) (GateSide F n (n*n+1)) ℝ)
    (η : ℝ)
    (herr : (∑ z, uavg (fun xy : GateSide F n (n*n+1) × GateSide F n (n*n+1) =>
      refreshDensity (Rectangular.augmentedShare c) (Rectangular.augmentedShare 1) xy.1 xy.2 *
        |answerProb (Rectangular.augmentedShare c) (Rectangular.augmentedShare 1)
          p z xy.1 xy.2 - G z xy.1 xy.2|)) ≤ η) :
    ((oldLabelDistribution hn s t).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n*n+1) (s*t+c)))).expect
      (fun ou => ∑ z, |(answerDistribution (Rectangular.augmentedShare c)
        (Rectangular.augmentedShare 1) p ou.1.1 ou.1.2 ou.2.val).weight z -
          G z (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)|) ≤ 4*(fieldCard F : ℝ)^2*η := by
  have he : ((oldLabelDistribution hn s t).prod
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n*n+1) (s*t+c)))).expect
      (fun ou => ∑ z, |(answerDistribution (Rectangular.augmentedShare c)
        (Rectangular.augmentedShare 1) p ou.1.1 ou.1.2 ou.2.val).weight z -
          G z (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)|) =
    ((oldLabelDistribution hn s t).prod
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n*n+1) (s*t+c)))).expect
      (fun ou => ∑ z, |answerProb (Rectangular.augmentedShare c)
        (Rectangular.augmentedShare 1) p z (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R) -
          G z (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)|) := by
    unfold FiniteDistribution.expect
    apply Finset.sum_congr rfl
    intro ou _
    by_cases ho : (oldLabelDistribution hn s t).weight ou.1 = 0
    · simp [FiniteDistribution.prod, FiniteDistribution.joint, ho]
    · simp_rw [augmented_answer_prob_on_support hn c s t p ou.1 ho ou.2]
  rw [he]
  exact augmented_fixed_labels_table_L1 hn c s t p G η herr

/-- One common family works simultaneously for all pairs of input plaintexts. Only the evaluation distribution changes with the labels. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Over the binary field with n ≥ 2, every augmented matrix-phase leakage partition admits one family of real approximations (G_z)_z, shared by all input secrets, such that

‖G_z‖_* ≤ 1, ∑_z ‖G_z‖_* ≤ |Z|.

For every s,t, independently sample the two input encodings and a long output encoding of s · t+c. The total expected answer error satisfies

𝔼[∑_z |prob_z-G_z|] ≤ 3328 · |Z| · 2^(−n/4).

On this valid-label distribution, the supported answer table and the actual conditional answer probabilities coincide.
-/
theorem augmented_labelled_local_approximation (hq : fieldCard F = 2) (hn : 2 ≤ n) (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) Z) :
    ∃ G : Z → Matrix (GateSide F n (n*n+1)) (GateSide F n (n*n+1)) ℝ,
      (∀ z, tableNuclearNorm (G z) ≤ 1) ∧
      (∑ z, tableNuclearNorm (G z)) ≤ Fintype.card Z ∧
      ∀ s t : F,
        letI := encoding_fiber_nonempty (show 2 ≤ n*n+1 by nlinarith) (s*t+c)
        ((oldLabelDistribution hn s t).prod
          (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n*n+1) (s*t+c)))).expect
          (fun ou => ∑ z, |(answerDistribution (Rectangular.augmentedShare c)
            (Rectangular.augmentedShare 1) p ou.1.1 ou.1.2 ou.2.val).weight z -
              G z (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)|) ≤
            16*208*Fintype.card Z*Real.exp (-Real.log 2 * (n : ℝ) / 4) := by
  obtain ⟨G,hG,hsum,herr⟩ := augmented_local_approximation hq hn c p
  refine ⟨G,hG,hsum,?_⟩
  intro s t
  letI := encoding_fiber_nonempty (show 2 ≤ n*n+1 by nlinarith) (s*t+c)
  have h := augmented_fixed_labels_L1 hn c s t p G
    (208*Fintype.card Z*Real.exp (-Real.log 2 * (n : ℝ) / 4)) herr
  rw [hq] at h
  convert h using 1
  ring

/-- The same label-independent family in the masked-table form used by rectangular shortening's linear transport. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Over the binary field with n ≥ 2, every augmented matrix-phase leakage partition admits one family of real approximations (G_z)_z, shared by all input secrets, such that

‖G_z‖_* ≤ 1, ∑_z ‖G_z‖_* ≤ |Z|.

For every s,t, independently sample the two input encodings and a long output encoding of s · t+c. The total expected answer error satisfies

𝔼[∑_z |prob_z-G_z|] ≤ 3328 · |Z| · 2^(−n/4).

On this valid-label distribution, the supported answer table and the actual conditional answer probabilities coincide.
-/
theorem augmented_labelled_table_approximation (hq : fieldCard F = 2) (hn : 2 ≤ n) (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) Z) :
    ∃ G : Z → Matrix (GateSide F n (n*n+1)) (GateSide F n (n*n+1)) ℝ,
      (∀ z, tableNuclearNorm (G z) ≤ 1) ∧
      (∑ z, tableNuclearNorm (G z)) ≤ Fintype.card Z ∧
      ∀ s t : F,
        letI := encoding_fiber_nonempty (show 2 ≤ n*n+1 by nlinarith) (s*t+c)
        ((oldLabelDistribution hn s t).prod
          (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n*n+1) (s*t+c)))).expect
          (fun ou => ∑ z, |answerProb (Rectangular.augmentedShare c)
            (Rectangular.augmentedShare 1) p z (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R) -
              G z (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)|) ≤
            16*208*Fintype.card Z*Real.exp (-Real.log 2 * (n : ℝ) / 4) := by
  obtain ⟨G,hG,hsum,herr⟩ := augmented_local_approximation hq hn c p
  refine ⟨G,hG,hsum,?_⟩
  intro s t
  letI := encoding_fiber_nonempty (show 2 ≤ n*n+1 by nlinarith) (s*t+c)
  have h := augmented_fixed_labels_table_L1 hn c s t p G
    (208*Fintype.card Z*Real.exp (-Real.log 2 * (n : ℝ) / 4)) herr
  rw [hq] at h
  convert h using 1
  ring

end

end CircuitCompiler.RefreshAnalysis
