import Proofs.Compiler.GateApproximation.MatrixPhase.GateAnswerProbabilities
import Proofs.Compiler.Foundations.MatrixRefreshing.Analysis.Tables
import Proofs.Compiler.Foundations.MatrixRefreshing.Probability.FamilyNorms
import Proofs.Compiler.Construction.Parameters



/-!
# The joint multiplication-port reference density

The old operands and new long encoding are grouped by party. The density is defined on this single carrier for all represented values and has uniform one-sided marginals. These are the measure facts used in the joint-port approximation argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace CircuitCompiler

open Refresh MatrixRefresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The sharper density constant needed for the long encoding. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; s ∈ F, assume 2 ≤ m. Then

densityWeight(F, m, s) ≤ |F| + 1.
-/
theorem densityWeight_le_q_add_one {m : ℕ} (hm : 2 ≤ m) (s : F) :
    densityWeight F m s ≤ (fieldCard F : ℝ) + 1 := by
  have hq := fieldCard_cast_pos (F := F)
  have hN := vectorCard_real_ge_fieldCard_sq (F := F) hm
  have hNpos : 0 < (vectorCard F m : ℝ) := by
    have := vectorCard_real_ge_four (F := F) hm
    linarith
  by_cases hs : s = 0
  · subst s
    rw [densityWeight_zero hm, shareCard_cast_real]
    apply (div_le_iff₀ (zeroFiber_denominator_pos hm)).2
    nlinarith
  · rw [densityWeight_of_ne_zero hm s hs, shareCard_cast_real]
    apply (div_le_iff₀ hNpos).2
    nlinarith

/-- A normalized fiber density, before grouping with the two old operands. -/
/-
Mathematical definition (normal notation): For m ∈ ℕ; s ∈ F; l, r ∈ U(F, m), define

encodingDensity(s, l, r) := { densityWeight(F, m, s) if (l · r) = s,; 0 otherwise }.
-/
noncomputable def encodingDensity {m : ℕ} (s : F) (l r : U F m) : ℝ :=
  if dot l.val r.val = s then densityWeight F m s else 0

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; s ∈ F; l ∈ U(F, m), assume 2 ≤ m. Then

𝔼ᵤ [encodingDensity(s, l, u)] = 1.
-/
theorem encodingDensity_average_right {m : ℕ} (hm : 2 ≤ m) (s : F) (l : U F m) :
    uavg (encodingDensity s l) = 1 := by
  classical
  have hcard : Fintype.card (Fiber F m s) =
      Fintype.card (U F m) * Fintype.card {r : U F m // dot l.val r.val = s} := by
    rw [fiber_card_eq_sum]
    simp_rw [partner_card_eq]
    simp
  have hd : (Fintype.card (U F m) : ℝ) ≠ 0 := by
    rw [nonzero_vector_card]
    exact ne_of_gt (nonzeroCard_real_pos hm)
  have hf : (Fintype.card (Fiber F m s) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (fiber_card_pos hm s)
  have hcount : (∑ r : U F m, if dot l.val r.val = s then (1 : ℝ) else 0) =
      (Fintype.card {r : U F m // dot l.val r.val = s} : ℝ) := by
    simp [Fintype.card_subtype]
  unfold uavg encodingDensity
  have he (r : U F m) : (if dot l.val r.val = s then densityWeight F m s else 0) =
      (if dot l.val r.val = s then (1 : ℝ) else 0) * densityWeight F m s := by
    split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.sum_mul]
  rw [hcount]
  unfold densityWeight
  unfold shareCard vectorCard
  rw [← nonzero_vector_card]
  have hc : (Fintype.card (Fiber F m s) : ℝ) =
      (Fintype.card (U F m) : ℝ) *
        (Fintype.card {r : U F m // dot l.val r.val = s} : ℝ) := by
    exact_mod_cast hcard
  field_simp
  nlinarith

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; s ∈ F; r ∈ U(F, m), assume 2 ≤ m. Then

𝔼ₗ [encodingDensity(s, l, r)] = 1.
-/
theorem encodingDensity_average_left {m : ℕ} (hm : 2 ≤ m) (s : F) (r : U F m) :
    uavg (fun l => encodingDensity s l r) = 1 := by
  have he : (fun l => encodingDensity s l r) = encodingDensity s r := by
    funext l
    unfold encodingDensity
    rw [dot_comm]
  rw [he]
  exact encodingDensity_average_right hm s r

/-- The represented product as a function of the two grouped old sides. -/
/- Mathematical definition (normal notation): For grouped operand shares x = (L₁,L₂) and y = (R₁,R₂), the represented product secret is (L₁ · R₁)(L₂ · R₂). -/
def portProduct {n m : ℕ} (x y : GateSide F n m) : F :=
  dot x.1.1.val y.1.1.val * dot x.1.2.val y.1.2.val

/-- The manuscript's density `D`, on one plaintext-independent joint carrier. -/
/-
Mathematical definition (normal notation): For n, m ∈ ℕ; x, y ∈ GateSide(F, n, m), define

gateDensity(x, y) := encodingDensity(portProduct(x, y), (x)₂, (y)₂).
-/
noncomputable def gateDensity {n m : ℕ} (x y : GateSide F n m) : ℝ :=
  encodingDensity (portProduct x y) x.2 y.2

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; x, y ∈ GateSide(F, n, m), assume 2 ≤ m. Then

0 ≤ gateDensity(x, y).
-/
theorem gateDensity_nonneg {n m : ℕ} (hm : 2 ≤ m) (x y : GateSide F n m) :
    0 ≤ gateDensity x y := by
  unfold gateDensity encodingDensity
  split_ifs
  · exact (densityWeight_pos hm _).le
  · rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; x, y ∈ GateSide(F, n, m), assume 2 ≤ m. Then

gateDensity(x, y) ≤ |F| + 1.
-/
theorem gateDensity_le {n m : ℕ} (hm : 2 ≤ m) (x y : GateSide F n m) :
    gateDensity x y ≤ (fieldCard F : ℝ) + 1 := by
  unfold gateDensity encodingDensity
  split_ifs
  · exact densityWeight_le_q_add_one hm _
  · have := fieldCard_cast_pos (F := F); linarith

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; x ∈ GateSide(F, n, m), assume 2 ≤ m; U(F, n) ≠ ∅. Then

𝔼ᵤ [gateDensity(x, u)] = 1.
-/
theorem gateDensity_average_right {n m : ℕ} (hm : 2 ≤ m)
    [Nonempty (U F n)] (x : GateSide F n m) :
    uavg (gateDensity x) = 1 := by
  rw [uavg_prod]
  have h (old : U F n × U F n) :
      uavg (fun r : U F m => gateDensity x (old, r)) = 1 :=
    encodingDensity_average_right hm
      (dot x.1.1.val old.1.val * dot x.1.2.val old.2.val) x.2
  simp_rw [h]
  exact uavg_const 1

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; y ∈ GateSide(F, n, m), assume 2 ≤ m; U(F, n) ≠ ∅. Then

𝔼ₓ [gateDensity(x, y)] = 1.
-/
theorem gateDensity_average_left {n m : ℕ} (hm : 2 ≤ m)
    [Nonempty (U F n)] (y : GateSide F n m) :
    uavg (fun x => gateDensity x y) = 1 := by
  rw [uavg_prod]
  have h (old : U F n × U F n) :
      uavg (fun l : U F m => gateDensity (old, l) y) = 1 :=
    encodingDensity_average_left hm
      (dot old.1.val y.1.1.val * dot old.2.val y.1.2.val) y.2
  simp_rw [h]
  exact uavg_const 1

/-- Regrouping old operands and the new encoding by party is a bijection. -/
/- Mathematical definition (normal notation): Regroup two old encodings and one new encoding by party: ((L₁,R₁),(L₂,R₂),(L',R')) ↦ (((L₁,L₂),L'),((R₁,R₂),R')). This is a bijection. -/
def gateRegroup (n m : ℕ) :
    ((State F n × State F n) × State F m) ≃ (GateSide F n m × GateSide F n m) where
  toFun p := (((p.1.1.L, p.1.2.L), p.2.L), ((p.1.1.R, p.1.2.R), p.2.R))
  invFun p := ((⟨p.1.1.1, p.2.1.1⟩, ⟨p.1.1.2, p.2.1.2⟩), ⟨p.1.2, p.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The reference experiment: independent uniform old shares, followed by a uniform new encoding of their represented product. -/
/-
Mathematical definition (normal notation): For n, m ∈ ℕ, assume 2 ≤ n; 2 ≤ m. define

jointPortDistribution := (gateRegroup(n, m)_*joint((independentStateDistribution(F, n) ⊗ independentStateDistribution(F, n)))(((ab ↦ μ_(secret((ab)₁) · secret((ab)₂)))))) .
-/
noncomputable def jointPortDistribution {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    FiniteDistribution (GateSide F n m × GateSide F n m) :=
  (((independentStateDistribution F n hn).prod (independentStateDistribution F n hn)).joint
    (fun ab => mu F m hm (secret ab.1 * secret ab.2))).map (gateRegroup n m)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; x, y ∈ GateSide(F, n, m), assume 2 ≤ n; 2 ≤ m. Then

jointPortDistribution((x, y)) = (|GateSide(F, n, m)|)⁻¹ · ((|GateSide(F, n, m)|)⁻¹ · gateDensity(x, y)).
-/
theorem jointPortDistribution_weight {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (x y : GateSide F n m) :
    (jointPortDistribution hn hm).weight (x, y) =
      (Fintype.card (GateSide F n m) : ℝ)⁻¹ *
        ((Fintype.card (GateSide F n m) : ℝ)⁻¹ * gateDensity x y) := by
  rw [jointPortDistribution, FiniteDistribution.map_equiv_weight]
  change (independentStateDistribution F n hn).weight _ *
    (independentStateDistribution F n hn).weight _ * (mu F m hm _).weight _ = _
  rw [mu_weight_density]
  simp only [independentStateDistribution_weight]
  change (1 / (shareCard F n : ℝ) ^ 2) * (1 / (shareCard F n : ℝ) ^ 2) *
    (gateDensity x y * (1 / (shareCard F m : ℝ) ^ 2)) = _
  simp only [GateSide, Fintype.card_prod, Nat.cast_mul, nonzero_vector_card]
  change _ = ((shareCard F n : ℝ) * shareCard F n * shareCard F m)⁻¹ *
    (((shareCard F n : ℝ) * shareCard F n * shareCard F m)⁻¹ * gateDensity x y)
  simp only [mul_inv_rev, div_eq_mul_inv]
  ring

/-- Weighted uniform averaging is exactly expectation in the reference experiment, for every real test including all squared error tests. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; f ∈ GateSide(F, n, m) → GateSide(F, n, m) → ℝ, assume 2 ≤ n; 2 ≤ m. Then

𝔼_(p ← jointPortDistribution) [f((p)₁, (p)₂)] = 𝔼ₓ [𝔼_y [gateDensity(x, y) · f(x, y)]].
-/
theorem jointPortDistribution_expect {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (f : GateSide F n m → GateSide F n m → ℝ) :
    (jointPortDistribution hn hm).expect (fun p => f p.1 p.2) =
      uavg (fun x => uavg (fun y => gateDensity x y * f x y)) := by
  simp only [FiniteDistribution.expect, Fintype.sum_prod_type, jointPortDistribution_weight, uavg,
    Finset.mul_sum, mul_assoc]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A,B a set; P ∈ 𝒟((A × B)); a ∈ A, assume A is finite; B is finite. Then

((Prod)₁_*P)(a) = ∑_b (P((a, b))).
-/
private theorem map_fst_weight {A B : Type*} [Fintype A] [Fintype B]
    (P : FiniteDistribution (A × B)) (a : A) :
    (P.map Prod.fst).weight a = ∑ b, P.weight (a, b) := by
  classical
  simp only [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.pure, Fintype.sum_prod_type,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A,B a set; P ∈ 𝒟((A × B)); b ∈ B, assume A is finite; B is finite. Then

((Prod)₂_*P)(b) = ∑ₐ (P((a, b))).
-/
private theorem map_snd_weight {A B : Type*} [Fintype A] [Fintype B]
    (P : FiniteDistribution (A × B)) (b : B) :
    (P.map Prod.snd).weight b = ∑ a, P.weight (a, b) := by
  classical
  simp [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.pure, Fintype.sum_prod_type]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ, assume 2 ≤ n; 2 ≤ m; U(F, n) ≠ ∅; U(F, m) ≠ ∅. Then

((Prod)₁_*jointPortDistribution(F = F)) = FiniteDistribution.uniform.
-/
theorem jointPortDistribution_left_marginal {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    [Nonempty (U F n)] [Nonempty (U F m)] :
    (jointPortDistribution (F := F) hn hm).map Prod.fst = FiniteDistribution.uniform := by
  ext x
  rw [map_fst_weight]
  simp_rw [jointPortDistribution_weight]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  change _ * uavg (gateDensity x) = _
  rw [gateDensity_average_right hm]
  simp [FiniteDistribution.uniform]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ, assume 2 ≤ n; 2 ≤ m; U(F, n) ≠ ∅; U(F, m) ≠ ∅. Then

((Prod)₂_*jointPortDistribution(F = F)) = FiniteDistribution.uniform.
-/
theorem jointPortDistribution_right_marginal {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    [Nonempty (U F n)] [Nonempty (U F m)] :
    (jointPortDistribution (F := F) hn hm).map Prod.snd = FiniteDistribution.uniform := by
  ext y
  rw [map_snd_weight]
  simp_rw [jointPortDistribution_weight]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  change _ * uavg (fun x => gateDensity x y) = _
  rw [gateDensity_average_left hm]
  simp [FiniteDistribution.uniform]

/-- The reference distribution is produced by the actual uniform full-matrix refresh, with the two old operands sampled independently from uniform nonzero shares. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, assume 2 ≤ n; 2 ≤ n · n. Then

(gateRegroup(n, (n · n))_*joint((independentStateDistribution(F, n) ⊗ independentStateDistribution(F, n)))(((ab ↦ (refreshedTensor((ab)₁, (ab)₂)_*𝒰_(GL_(n · n)(F))))))) = jointPortDistribution.
-/
theorem jointPortDistribution_from_matrix {n : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ n * n) :
    (((independentStateDistribution F n hn).prod (independentStateDistribution F n hn)).joint
      (fun ab => (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n * n))).map
        (refreshedTensor ab.1 ab.2))).map (gateRegroup n (n * n)) =
      jointPortDistribution hn hm := by
  simp_rw [refreshedTensor_uniform hm]
  rfl

/-- The same joint experiment restricted to two specified input plaintexts. -/
/-
Mathematical definition (normal notation): For n, m ∈ ℕ; s, t ∈ F, assume 2 ≤ n; 2 ≤ m. define

labelledPortDistribution(s, t) := (gateRegroup(n, m)_*joint((μₛ ⊗ μₜ))(((ab ↦ μ_(secret((ab)₁) · secret((ab)₂)))))) .
-/
noncomputable def labelledPortDistribution {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (s t : F) :
    FiniteDistribution (GateSide F n m × GateSide F n m) :=
  (((mu F n hn s).prod (mu F n hn t)).joint
    (fun ab => mu F m hm (secret ab.1 * secret ab.2))).map (gateRegroup n m)

/-- Fixing the two input plaintexts costs at most `4 q²` in density, uniformly in both labels. No conditioning on leakage appears in this comparison. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; s, t ∈ F; xy ∈ GateSide(F, n, m) × GateSide(F, n, m), assume 2 ≤ n; 2 ≤ m. Then

labelledPortDistribution(s, t)(xy) ≤ (4 · (|F|)²) · jointPortDistribution(xy).
-/
theorem labelledPortDistribution_weight_le {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (s t : F) (xy : GateSide F n m × GateSide F n m) :
    (labelledPortDistribution hn hm s t).weight xy ≤
      (4 * (fieldCard F : ℝ) ^ 2) * (jointPortDistribution hn hm).weight xy := by
  rw [labelledPortDistribution, jointPortDistribution, FiniteDistribution.map_equiv_weight, FiniteDistribution.map_equiv_weight]
  change (mu F n hn s).weight _ * (mu F n hn t).weight _ *
    (mu F m hm _).weight _ ≤ _ *
      ((independentStateDistribution F n hn).weight _ * (independentStateDistribution F n hn).weight _ *
        (mu F m hm _).weight _)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mixed_state_density_le n hn s t _ _)
    ((mu F m hm _).nonneg _)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; s, t ∈ F; f ∈ GateSide(F, n, m) → GateSide(F, n, m) → ℝ, assume 2 ≤ n; 2 ≤ m; ∀ x, y, 0 ≤ f(x, y). Then

𝔼_(xy ← labelledPortDistribution(s, t)) [f((xy)₁, (xy)₂)] ≤ (4 · (|F|)²) · 𝔼ₓ [𝔼_y [gateDensity(x, y) · f(x, y)]].
-/
theorem labelledPortDistribution_expect_le {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (s t : F) (f : GateSide F n m → GateSide F n m → ℝ)
    (hf : ∀ x y, 0 ≤ f x y) :
    (labelledPortDistribution hn hm s t).expect (fun xy => f xy.1 xy.2) ≤
      (4 * (fieldCard F : ℝ) ^ 2) *
        uavg (fun x => uavg (fun y => gateDensity x y * f x y)) := by
  rw [← jointPortDistribution_expect hn hm]
  unfold FiniteDistribution.expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro xy _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (labelledPortDistribution_weight_le hn hm s t xy) (hf xy.1 xy.2)

/-- Convert a squared family error into the answer-summed mean absolute error. The answer alphabet is counted, so the loss is its square root. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Ω,Z a set; P ∈ 𝒟(Ω); f ∈ Z → Ω → ℝ; η ∈ ℝ, assume Ω is finite; Z is finite; 0 ≤ η; 𝔼_(ω ← P) [∑_z ((f(z, ω))²)] ≤ η². Then

(∑_z (𝔼_(ω ← P) [|f(z, ω)|])) ≤ √(|Z|) · η.
-/
theorem family_mean_abs_le {Ω Z : Type*} [Fintype Ω] [Fintype Z]
    (P : FiniteDistribution Ω) (f : Z → Ω → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (herr : P.expect (fun ω => ∑ z, f z ω ^ 2) ≤ η ^ 2) :
    (∑ z, P.expect (fun ω => |f z ω|)) ≤ Real.sqrt (Fintype.card Z) * η := by
  have h := abs_sum_expect_mul_le_familyRms_mul_familyRms P
    (fun _z : Z => fun _ω => (1 : ℝ)) (fun z ω => |f z ω|)
  have hnonneg : 0 ≤ ∑ z, P.expect (fun ω => |f z ω|) :=
    Finset.sum_nonneg (fun _ _ => P.expect_nonneg _ (fun _ => abs_nonneg _))
  simp only [one_mul, abs_of_nonneg hnonneg] at h
  have hone : familyRms P (fun _z : Z => fun _ω => (1 : ℝ)) =
      Real.sqrt (Fintype.card Z) := by simp [familyRms]
  have herr' : familyRms P (fun z ω => |f z ω|) ≤ η := by
    unfold familyRms
    simp only [sq_abs]
    exact (Real.sqrt_le_left hη).2 herr
  rw [hone] at h
  exact h.trans (mul_le_mul_of_nonneg_left herr' (Real.sqrt_nonneg _))

/-- A joint density-weighted L₂ approximation yields a local mean-absolute approximation simultaneously for every pair of input plaintexts. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Z a set; n, m ∈ ℕ; s, t ∈ F; err ∈ Z → GateSide(F, n, m) → GateSide(F, n, m) → ℝ; η ∈ ℝ, assume Z is finite; 2 ≤ n; 2 ≤ m; 0 ≤ η; 𝔼ₓ [𝔼_y [gateDensity(x, y) · ∑_z ((err(z, x, y))²)]] ≤ η². Then

(∑_z (𝔼_(xy ← labelledPortDistribution(s, t)) [|err(z, (xy)₁, (xy)₂)|])) ≤ √(|Z|) · (2 · |F| · η).
-/
theorem labelledPortDistribution_family_mean_abs {Z : Type*} [Fintype Z]
    {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (s t : F)
    (err : Z → GateSide F n m → GateSide F n m → ℝ)
    (η : ℝ) (hη : 0 ≤ η)
    (herr : uavg (fun x => uavg (fun y =>
      gateDensity x y * ∑ z, err z x y ^ 2)) ≤ η ^ 2) :
    (∑ z, (labelledPortDistribution hn hm s t).expect (fun xy => |err z xy.1 xy.2|)) ≤
      Real.sqrt (Fintype.card Z) * (2 * (fieldCard F : ℝ) * η) := by
  apply family_mean_abs_le _ _ _ (by have := fieldCard_cast_pos (F := F); positivity)
  have h := labelledPortDistribution_expect_le hn hm s t (fun x y => ∑ z, err z x y ^ 2)
    (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hc : 0 ≤ 4 * (fieldCard F : ℝ) ^ 2 := by positivity
  have h' := h.trans (mul_le_mul_of_nonneg_left herr hc)
  nlinarith

end CircuitCompiler
