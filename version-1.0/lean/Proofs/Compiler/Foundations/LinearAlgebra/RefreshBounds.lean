import Proofs.Compiler.Foundations.MatrixRefreshing.Analysis.Tables
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.EncodingMeasure
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Freshness
import Proofs.Compiler.Foundations.MatrixRefreshing.Probability.FamilyNorms
import Proofs.Compiler.Construction.Parameters



/-!
# Signed one-round refresh bounds

State averages are normalized; answer sums are not. The generic estimates require a nonnegative partition of the answers and apply to rectangle partitions produced by adaptive local transcript trees. Concrete transition bounds instantiate them for the actual shared GL refresh.
-/

set_option autoImplicit false

open scoped BigOperators

namespace TableAnalysis

open MatrixRefresh Refresh

noncomputable section

variable {X G Z : Type*} [Fintype X] [Fintype G] [Fintype Z]

/-- A signed density relative to uniform current-state measure. -/
/-
Mathematical definition (normal notation): For X a set, define

SignedTable := X → ℝ.
-/
abbrev SignedTable (X : Type*) := X → ℝ

/- Mathematical definition (normal notation): The normalized L₁ norm of a real function F is ‖F‖₁ := 𝔼_(x ← X) [|F(x)|]. -/
def signedL1 (F : SignedTable X) : ℝ := uavg (fun x => |F x|)

/- Mathematical definition (normal notation): The squared normalized L₂ norm is ‖F‖₂² := 𝔼_(x ← X) [F(x)²]. -/
def signedL2Sq (F : SignedTable X) : ℝ := uavg (fun x => F x ^ 2)

/- Mathematical definition (normal notation): The normalized L₂ norm is ‖F‖₂ := √(𝔼_(x ← X) [F(x)²]). -/
def signedL2 (F : SignedTable X) : ℝ := Real.sqrt (signedL2Sq F)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For F ∈ SignedTable(X), we have

0 ≤ signedL1(F).
-/
theorem signedL1_nonneg (F : SignedTable X) : 0 ≤ signedL1 F :=
  uavg_nonneg (fun _ => abs_nonneg _)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For F ∈ SignedTable(X), we have

0 ≤ ‖ F‖₂².
-/
theorem signedL2Sq_nonneg (F : SignedTable X) : 0 ≤ signedL2Sq F :=
  uavg_nonneg (fun _ => sq_nonneg _)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For F ∈ SignedTable(X), we have

0 ≤ ‖ F‖₂.
-/
theorem signedL2_nonneg (F : SignedTable X) : 0 ≤ signedL2 F :=
  Real.sqrt_nonneg _

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For F ∈ SignedTable(X), we have

(‖ F‖₂)² = ‖ F‖₂².
-/
@[simp] theorem signedL2_sq (F : SignedTable X) : signedL2 F ^ 2 = signedL2Sq F :=
  Real.sq_sqrt (signedL2Sq_nonneg F)

/-- Each sampled refresh is a permutation of the current-state carrier. -/
/- Mathematical definition (normal notation): A finite refresh action is a family of bijections e_g:X → X indexed by g ∈ G. No group distribution is required by this generic definition. -/
abbrev FiniteRefresh (X G : Type*) := G → X ≃ X

/-- Push forward a signed density, retaining the specified transcript leaf. -/
/-
Mathematical definition (normal notation): For e ∈ FiniteRefresh(X, G); p ∈ RoundPartition(X, G, Z); F ∈ SignedTable(X); z ∈ Z; x ∈ X, define

roundOp(e, p, F, z, x) := 𝔼_g [F((e(g))⁻¹(x)) · weight(p)(z, g, (e(g))⁻¹(x))].
-/
def roundOp (e : FiniteRefresh X G) (p : RoundPartition X G Z)
    (F : SignedTable X) (z : Z) (x : X) : ℝ :=
  uavg (fun g => F ((e g).symm x) * p.weight z g ((e g).symm x))

/-- The unsigned refresh average dominating all leaf densities together. -/
/-
Mathematical definition (normal notation): For e ∈ FiniteRefresh(X, G); F ∈ SignedTable(X); x ∈ X, define

unsignedRefresh(e, F, x) := 𝔼_g [|F((e(g))⁻¹(x))|].
-/
def unsignedRefresh (e : FiniteRefresh X G) (F : SignedTable X) (x : X) : ℝ :=
  uavg (fun g => |F ((e g).symm x)|)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ Z → G → ℝ, we have

𝔼_g [∑_z (f(z, g))] = ∑_z (𝔼ᵤ [f(z, u)]).
-/
theorem uavg_sum (f : Z → G → ℝ) :
    uavg (fun g => ∑ z, f z g) = ∑ z, uavg (f z) := by
  simp only [uavg, Finset.mul_sum]
  rw [Finset.sum_comm]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ G → ℝ, assume G ≠ ∅. Then

|𝔼ᵤ [f(u)]| ≤ 𝔼_g [|f(g)|].
-/
theorem abs_uavg_le [Nonempty G] (f : G → ℝ) :
    |uavg f| ≤ uavg (fun g => |f g|) := by
  simpa only [uavg_eq_expect_uniform] using
    abs_expect_le_expect_abs (FiniteDistribution.uniform : FiniteDistribution G) f

omit [Fintype X] in
/-- Pointwise domination uses only nonnegativity and completeness of leaves. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ FiniteRefresh(X, G); p ∈ RoundPartition(X, G, Z); F ∈ SignedTable(X); x ∈ X, assume G ≠ ∅. Then

∑_z (|roundOp(e, p, F, z, x)|) ≤ unsignedRefresh(e, F, x).
-/
theorem sum_abs_roundOp_le [Nonempty G] (e : FiniteRefresh X G)
    (p : RoundPartition X G Z) (F : SignedTable X) (x : X) :
    ∑ z, |roundOp e p F z x| ≤ unsignedRefresh e F x := by
  classical
  calc
    _ ≤ ∑ z, uavg (fun g =>
        |F ((e g).symm x) * p.weight z g ((e g).symm x)|) :=
      Finset.sum_le_sum (fun z _ => abs_uavg_le _)
    _ = uavg (fun g => ∑ z,
        |F ((e g).symm x) * p.weight z g ((e g).symm x)|) := (uavg_sum _).symm
    _ = unsignedRefresh e F x := by
      apply uavg_congr
      intro g
      simp only [abs_mul, abs_of_nonneg (p.nonneg _ _ _), ← Finset.mul_sum,
        p.complete, mul_one]

omit [Fintype X] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ FiniteRefresh(X, G); F ∈ SignedTable(X); x ∈ X, we have

0 ≤ unsignedRefresh(e, F, x).
-/
theorem unsignedRefresh_nonneg (e : FiniteRefresh X G) (F : SignedTable X) (x : X) :
    0 ≤ unsignedRefresh e F x :=
  uavg_nonneg (fun _ => abs_nonneg _)

/-- Refresh averaging preserves total unsigned mass. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ FiniteRefresh(X, G); F ∈ SignedTable(X), assume G ≠ ∅. Then

𝔼ᵤ [unsignedRefresh(e, F, u)] = signedL1(F).
-/
theorem unsignedRefresh_mean [Nonempty G] (e : FiniteRefresh X G) (F : SignedTable X) :
    uavg (unsignedRefresh e F) = signedL1 F := by
  unfold unsignedRefresh
  rw [uavg_comm]
  have hmean (g : G) : uavg (fun x => |F ((e g).symm x)|) = signedL1 F :=
    uavg_equiv (e g).symm (fun x => |F x|)
  simp_rw [hmean]
  exact uavg_const _

/-- Summing over the answers contracts total signed L1 mass. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ FiniteRefresh(X, G); p ∈ RoundPartition(X, G, Z); F ∈ SignedTable(X), assume G ≠ ∅. Then

∑_z (signedL1(roundOp(e, p, F, z))) ≤ signedL1(F).
-/
theorem sum_signedL1_roundOp_le [Nonempty G] (e : FiniteRefresh X G)
    (p : RoundPartition X G Z) (F : SignedTable X) :
    ∑ z, signedL1 (roundOp e p F z) ≤ signedL1 F := by
  calc
    _ = uavg (fun x => ∑ z, |roundOp e p F z x|) := (uavg_sum _).symm
    _ ≤ uavg (unsignedRefresh e F) := uavg_mono (sum_abs_roundOp_le e p F)
    _ = signedL1 F := unsignedRefresh_mean e F

/-- Explicit transition-density hypothesis: every backward transition has density at most `1/pMin` relative to uniform state measure. It is proved for the actual GL action below, rather than assumed as a norm conclusion. -/
/-
Mathematical definition (normal notation): For e ∈ FiniteRefresh(X, G); pMin ∈ ℝ, assume G ≠ ∅; X ≠ ∅. define

TransitionDensityBound(e, pMin) := ∀ x, y, (((g ↦ (e(g))⁻¹(x)))_*𝒰_G)(y) ≤ (pMin)⁻¹ · 𝒰_X(y).
-/
def TransitionDensityBound [Nonempty G] [Nonempty X]
    (e : FiniteRefresh X G) (pMin : ℝ) : Prop :=
  ∀ x y, ((FiniteDistribution.uniform : FiniteDistribution G).map (fun g => (e g).symm x)).weight y ≤
    pMin⁻¹ * (FiniteDistribution.uniform : FiniteDistribution X).weight y

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ FiniteRefresh(X, G); pMin ∈ ℝ; F ∈ SignedTable(X); x ∈ X, assume G ≠ ∅; X ≠ ∅; TransitionDensityBound(e, pMin). Then

unsignedRefresh(e, F, x) ≤ signedL1(F) / pMin.
-/
theorem unsignedRefresh_le [Nonempty G] [Nonempty X]
    (e : FiniteRefresh X G) (pMin : ℝ) (hker : TransitionDensityBound e pMin)
    (F : SignedTable X) (x : X) :
    unsignedRefresh e F x ≤ signedL1 F / pMin := by
  calc
    unsignedRefresh e F x =
        ((FiniteDistribution.uniform : FiniteDistribution G).map (fun g => (e g).symm x)).expect
          (fun y => |F y|) := by
      rw [expect_map]
      exact uavg_eq_expect_uniform _
    _ ≤ ∑ y, (pMin⁻¹ * (FiniteDistribution.uniform : FiniteDistribution X).weight y) * |F y| := by
      exact Finset.sum_le_sum (fun y _ =>
        mul_le_mul_of_nonneg_right (hker x y) (abs_nonneg _))
    _ = signedL1 F / pMin := by
      simp only [signedL1, uavg_eq_expect_uniform, FiniteDistribution.expect,
        ← Finset.mul_sum, mul_assoc, div_eq_mul_inv]
      ring

/-- A pointwise bound on each answer-specific density update. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ FiniteRefresh(X, G); p ∈ RoundPartition(X, G, Z); pMin ∈ ℝ; F ∈ SignedTable(X); z ∈ Z; x ∈ X, assume G ≠ ∅; X ≠ ∅; TransitionDensityBound(e, pMin). Then

|roundOp(e, p, F, z, x)| ≤ signedL1(F) / pMin.
-/
theorem abs_roundOp_le [Nonempty G] [Nonempty X]
    (e : FiniteRefresh X G) (p : RoundPartition X G Z)
    (pMin : ℝ) (hker : TransitionDensityBound e pMin) (F : SignedTable X) (z : Z) (x : X) :
    |roundOp e p F z x| ≤ signedL1 F / pMin := by
  classical
  exact (Finset.single_le_sum (fun a _ => abs_nonneg (roundOp e p F a x))
    (Finset.mem_univ z)).trans
      ((sum_abs_roundOp_le e p F x).trans (unsignedRefresh_le e pMin hker F x))

/-- The sum of squared output L2 norms is bounded by the input L1 norm squared divided by the transition-density parameter. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ FiniteRefresh(X, G); p ∈ RoundPartition(X, G, Z); pMin ∈ ℝ; F ∈ SignedTable(X), assume G ≠ ∅; X ≠ ∅; 0 < pMin; TransitionDensityBound(e, pMin). Then

∑_z (‖ roundOp(e, p, F, z)‖₂²) ≤ (signedL1(F))² / pMin.
-/
theorem sum_signedL2Sq_roundOp_le [Nonempty G] [Nonempty X]
    (e : FiniteRefresh X G) (p : RoundPartition X G Z)
    (pMin : ℝ) (_hpMin : 0 < pMin) (hker : TransitionDensityBound e pMin) (F : SignedTable X) :
    ∑ z, signedL2Sq (roundOp e p F z) ≤ signedL1 F ^ 2 / pMin := by
  classical
  have hpoint (x : X) : ∑ z, roundOp e p F z x ^ 2 ≤
      (signedL1 F / pMin) * unsignedRefresh e F x := by
    have hs := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := Finset.univ) (f := fun z => |roundOp e p F z x|)
      (fun _ _ => abs_nonneg _)
    simp only [sq_abs] at hs
    have ha := unsignedRefresh_nonneg e F x
    have hb := Finset.sum_nonneg (fun z (_ : z ∈ Finset.univ) =>
      abs_nonneg (roundOp e p F z x))
    have hc := sum_abs_roundOp_le e p F x
    have hd := unsignedRefresh_le e pMin hker F x
    have he := mul_le_mul_of_nonneg_right hd ha
    nlinarith
  calc
    _ = uavg (fun x => ∑ z, roundOp e p F z x ^ 2) := (uavg_sum _).symm
    _ ≤ uavg (fun x => (signedL1 F / pMin) * unsignedRefresh e F x) := uavg_mono hpoint
    _ = signedL1 F ^ 2 / pMin := by
      rw [uavg_const_mul, unsignedRefresh_mean]
      ring

/-- Taking square roots gives the joint L2 bound over the answer family. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ FiniteRefresh(X, G); p ∈ RoundPartition(X, G, Z); pMin ∈ ℝ; F ∈ SignedTable(X), assume G ≠ ∅; X ≠ ∅; 0 < pMin; TransitionDensityBound(e, pMin). Then

√(∑_z ((‖ roundOp(e, p, F, z)‖₂)²)) ≤ signedL1(F) / √pMin.
-/
theorem tuple_signedL2_roundOp_le [Nonempty G] [Nonempty X]
    (e : FiniteRefresh X G) (p : RoundPartition X G Z)
    (pMin : ℝ) (hpMin : 0 < pMin) (hker : TransitionDensityBound e pMin) (F : SignedTable X) :
    Real.sqrt (∑ z, signedL2 (roundOp e p F z) ^ 2) ≤ signedL1 F / Real.sqrt pMin := by
  simp only [signedL2_sq]
  have h := Real.sqrt_le_sqrt (sum_signedL2Sq_roundOp_le e p pMin hpMin hker F)
  simpa only [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (signedL1_nonneg F)] using h

/-- Summing individual L2 norms costs the square root of the answer alphabet cardinality. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ FiniteRefresh(X, G); p ∈ RoundPartition(X, G, Z); pMin ∈ ℝ; F ∈ SignedTable(X), assume G ≠ ∅; X ≠ ∅; 0 < pMin; TransitionDensityBound(e, pMin). Then

∑_z (‖ roundOp(e, p, F, z)‖₂) ≤ √(|Z| / pMin) · signedL1(F) .
-/
theorem sum_signedL2_roundOp_le [Nonempty G] [Nonempty X]
    (e : FiniteRefresh X G) (p : RoundPartition X G Z)
    (pMin : ℝ) (hpMin : 0 < pMin) (hker : TransitionDensityBound e pMin) (F : SignedTable X) :
    ∑ z, signedL2 (roundOp e p F z) ≤
      Real.sqrt ((Fintype.card Z : ℝ) / pMin) * signedL1 F := by
  have hcs := sum_bounded_mul_sq_le (fun _ : Z => (1 : ℝ))
    (fun z => signedL2 (roundOp e p F z)) (by intro _; norm_num)
  simp only [one_mul, signedL2_sq] at hcs
  have hb := mul_le_mul_of_nonneg_left (sum_signedL2Sq_roundOp_le e p pMin hpMin hker F)
    (Nat.cast_nonneg (Fintype.card Z) : (0 : ℝ) ≤ _)
  have h := Real.sqrt_le_sqrt (hcs.trans hb)
  have hsum : 0 ≤ ∑ z, signedL2 (roundOp e p F z) :=
    Finset.sum_nonneg (fun _ _ => signedL2_nonneg _)
  rw [Real.sqrt_sq hsum] at h
  have heq : (Fintype.card Z : ℝ) * (signedL1 F ^ 2 / pMin) =
      ((Fintype.card Z : ℝ) / pMin) * signedL1 F ^ 2 := by ring
  rw [heq, Real.sqrt_mul (div_nonneg (Nat.cast_nonneg _) hpMin.le),
    Real.sqrt_sq (signedL1_nonneg F)] at h
  exact h

section ActualGL

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- The exact minimum secret-fiber probability under independent nonzero shares. -/
/-
Mathematical definition (normal notation): For F a set; n ∈ ℕ, assume F is a field; F is finite. define

minSecretProbability(n) := (|F|ⁿ - |F|) / (|F| · (|F|ⁿ-1)).
-/
def minSecretProbability (F : Type*) [Field F] [Fintype F] (n : ℕ) : ℝ :=
  ((vectorCard F n : ℝ) - (fieldCard F : ℝ)) / ((fieldCard F : ℝ) * (shareCard F n : ℝ))

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

0 < minSecretProbability(F, n).
-/
theorem minSecretProbability_pos (hn : 2 ≤ n) : 0 < minSecretProbability F n :=
  div_pos (zeroFiber_denominator_pos hn)
    (mul_pos fieldCard_cast_pos (nonzeroCard_real_pos hn))

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F, assume 2 ≤ n. Then

densityWeight(F, n, s) ≤ (minSecretProbability(F, n))⁻¹.
-/
theorem densityWeight_le_inv_minSecretProbability (hn : 2 ≤ n) (s : F) :
    densityWeight F n s ≤ (minSecretProbability F n)⁻¹ := by
  rw [minSecretProbability, inv_div]
  by_cases hs : s = 0
  · subst s
    exact (densityWeight_zero hn).le
  · rw [densityWeight_of_ne_zero hn s hs]
    exact div_le_div_of_nonneg_left
      (mul_nonneg (fieldCard_cast_pos (F := F)).le (nonzeroCard_real_pos hn).le)
      (zeroFiber_denominator_pos hn) (sub_le_self _ (fieldCard_cast_pos (F := F)).le)

/-- The actual state update is a permutation, inverted using the same matrix inverse. -/
/- Mathematical definition (normal notation): The map (ℓ,r) ↦ (ℓ · M,M⁻¹ · r) is a bijection of encoding states. Its inverse is the refresh map with M⁻¹. -/
def glRefreshEquiv (M : Refresh.«GL» F n) : State F n ≃ State F n where
  toFun x := refresh x M
  invFun x := refresh x M⁻¹
  left_inv x := by dsimp only; rw [refresh_mul, mul_inv_cancel, refresh_one]
  right_inv x := by dsimp only; rw [refresh_mul, inv_mul_cancel, refresh_one]

/-- Nonempty states are a proved consequence of `n ≥ 2`. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

State(F, n) ≠ ∅.
-/
theorem state_nonempty (hn : 2 ≤ n) : Nonempty (State F n) := by
  obtain ⟨x⟩ := fiber_nonempty F n hn (0 : F)
  exact ⟨x.val⟩

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume State(F, n) ≠ ∅; 2 ≤ n. Then

𝒰_(State(F, n)) = independentStateDistribution(F, n).
-/
theorem uniform_state_eq_independent [Nonempty (State F n)] (hn : 2 ≤ n) :
    (FiniteDistribution.uniform : FiniteDistribution (State F n)) = independentStateDistribution F n hn := by
  ext x
  rw [independentStateDistribution_weight]
  change (Fintype.card (State F n) : ℝ)⁻¹ = 1 / (shareCard F n : ℝ) ^ 2
  have hc : Fintype.card (State F n) = shareCard F n * shareCard F n := by
    rw [Fintype.card_congr (stateEquivProd F n), Fintype.card_prod,
      nonzero_vector_card]
    rfl
  rw [hc]
  simp [Nat.cast_mul, pow_two, one_div]

/-- Inverting a uniform GL matrix preserves its distribution, so backward freshness is the same proved uniform-fiber theorem as forward freshness. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For x ∈ State(F, n), assume 2 ≤ n. Then

(((M ↦ refresh(x, (M)⁻¹)))_*𝒰_(GLₙ(F))) = μ_(secret(x)).
-/
theorem gl_backward_uniform (hn : 2 ≤ n) (x : State F n) :
    (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F n)).map (fun M => refresh x M⁻¹) =
      mu F n hn (secret x) := by
  have hinv : (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F n)).map (Equiv.inv (Refresh.«GL» F n)) =
      (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F n)) := by
    ext M
    rw [FiniteDistribution.map_equiv_weight]
    rfl
  calc
    _ = ((FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F n)).map (Equiv.inv (Refresh.«GL» F n))).map
        (refresh x) := by rw [FiniteDistribution.map_map]; rfl
    _ = (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F n)).map (refresh x) := by rw [hinv]
    _ = mu F n hn (secret x) := refresh_uniform hn (secret x) x rfl

/-- Actual GL satisfies the precise transition-density bound required above. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume State(F, n) ≠ ∅; 2 ≤ n. Then

TransitionDensityBound(glRefreshEquiv(F = F, n = n), minSecretProbability(F, n)).
-/
theorem gl_transitionDensityBound [Nonempty (State F n)] (hn : 2 ≤ n) :
    TransitionDensityBound (glRefreshEquiv (F := F) (n := n)) (minSecretProbability F n) := by
  intro x y
  change ((FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F n)).map
    (fun M => refresh x M⁻¹)).weight y ≤ _
  rw [gl_backward_uniform hn, mu_weight_density, uniform_state_eq_independent hn]
  apply mul_le_mul_of_nonneg_right _ ((independentStateDistribution F n hn).nonneg y)
  split_ifs
  · exact densityWeight_le_inv_minSecretProbability hn _
  · exact inv_nonneg.mpr (minSecretProbability_pos hn).le

/-- Literal local indicator rectangles, allowing arbitrary dependence on the entire common matrix and on the fixed preceding transcript. -/
/- Mathematical definition (normal notation): A rectangular leakage partition for matrix refreshing assigns left and right Boolean masks to each answer z and invertible matrix M. For every state (ℓ,r) and M, exactly one answer has both masks equal to true. -/
structure GLRectanglePartition (F : Type*) [Field F] (n : ℕ)
    (Z : Type*) [Fintype Z] where
  left : Z → Refresh.«GL» F n → U F n → Bool
  right : Z → Refresh.«GL» F n → U F n → Bool
  complete : ∀ M x, ∑ z,
    (if left z M (stateLeftShare x) then (1 : ℝ) else 0) *
      (if right z M (stateRightShare x) then (1 : ℝ) else 0) = 1

/- Mathematical definition (normal notation): At a fixed state (ℓ,r) and invertible matrix M, answer z receives weight 1 if its left and right leakage masks both accept, and weight 0 otherwise. This is the normalized round-answer distribution. -/
def GLRectanglePartition.toRoundPartition (p : GLRectanglePartition F n Z) :
    RoundPartition (State F n) (Refresh.«GL» F n) Z where
  weight z M x := (if p.left z M (stateLeftShare x) then 1 else 0) *
    (if p.right z M (stateRightShare x) then 1 else 0)
  nonneg z M x := by split_ifs <;> norm_num
  complete := p.complete

/-- The signed-density update for one round of the shared-matrix refresh protocol. -/
/-
Mathematical definition (normal notation): For p ∈ GLRectanglePartition(F, n, Z); A ∈ SignedTable(State(F, n)), define

glRoundOp(p, A) := roundOp(glRefreshEquiv, p.toRoundPartition, A).
-/
def glRoundOp (p : GLRectanglePartition F n Z) (A : SignedTable (State F n)) :
    Z → SignedTable (State F n) :=
  roundOp glRefreshEquiv p.toRoundPartition A

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ GLRectanglePartition(F, n, Z); A ∈ SignedTable(State(F, n)); z ∈ Z; x ∈ State(F, n), we have

glRoundOp(p, A, z, x) = 𝔼_M [A(refresh(x, (M)⁻¹)) · (({ 1 if p.left(z, M, rowRefresh(L(x), (M)⁻¹)),; 0 otherwise }) · ({ 1 if p.right(z, M, columnRefresh(R(x), (M)⁻¹)),; 0 otherwise }))].
-/
theorem glRoundOp_apply (p : GLRectanglePartition F n Z)
    (A : SignedTable (State F n)) (z : Z) (x : State F n) :
    glRoundOp p A z x = uavg (fun M => A (refresh x M⁻¹) *
      ((if p.left z M (rowRefresh (stateLeftShare x) M⁻¹) then 1 else 0) *
        (if p.right z M (columnRefresh (stateRightShare x) M⁻¹) then 1 else 0))) :=
  rfl

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ GLRectanglePartition(F, n, Z); A ∈ SignedTable(State(F, n)), we have

∑_z (signedL1(glRoundOp(p, A, z))) ≤ signedL1(A).
-/
theorem gl_sum_signedL1_roundOp_le (p : GLRectanglePartition F n Z)
    (A : SignedTable (State F n)) :
    ∑ z, signedL1 (glRoundOp p A z) ≤ signedL1 A :=
  sum_signedL1_roundOp_le _ _ _

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ GLRectanglePartition(F, n, Z); A ∈ SignedTable(State(F, n)); z ∈ Z; x ∈ State(F, n), assume 2 ≤ n. Then

|glRoundOp(p, A, z, x)| ≤ signedL1(A) / minSecretProbability(F, n).
-/
theorem gl_abs_roundOp_le (hn : 2 ≤ n) (p : GLRectanglePartition F n Z)
    (A : SignedTable (State F n)) (z : Z) (x : State F n) :
    |glRoundOp p A z x| ≤ signedL1 A / minSecretProbability F n := by
  letI := state_nonempty (F := F) hn
  exact abs_roundOp_le _ _ _ (gl_transitionDensityBound hn) _ _ _

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ GLRectanglePartition(F, n, Z); A ∈ SignedTable(State(F, n)), assume 2 ≤ n. Then

∑_z (‖ glRoundOp(p, A, z)‖₂²) ≤ (signedL1(A))² / minSecretProbability(F, n).
-/
theorem gl_sum_signedL2Sq_roundOp_le (hn : 2 ≤ n) (p : GLRectanglePartition F n Z)
    (A : SignedTable (State F n)) :
    ∑ z, signedL2Sq (glRoundOp p A z) ≤ signedL1 A ^ 2 / minSecretProbability F n := by
  letI := state_nonempty (F := F) hn
  exact sum_signedL2Sq_roundOp_le _ _ _ (minSecretProbability_pos hn) (gl_transitionDensityBound hn) _

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ GLRectanglePartition(F, n, Z); A ∈ SignedTable(State(F, n)), assume 2 ≤ n. Then

√(∑_z ((‖ glRoundOp(p, A, z)‖₂)²)) ≤ signedL1(A) / √(minSecretProbability(F, n)).
-/
theorem gl_tuple_signedL2_roundOp_le (hn : 2 ≤ n) (p : GLRectanglePartition F n Z)
    (A : SignedTable (State F n)) :
    Real.sqrt (∑ z, signedL2 (glRoundOp p A z) ^ 2) ≤
      signedL1 A / Real.sqrt (minSecretProbability F n) := by
  letI := state_nonempty (F := F) hn
  exact tuple_signedL2_roundOp_le _ _ _ (minSecretProbability_pos hn) (gl_transitionDensityBound hn) _

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ GLRectanglePartition(F, n, Z); A ∈ SignedTable(State(F, n)), assume 2 ≤ n. Then

∑_z (‖ glRoundOp(p, A, z)‖₂) ≤ √(|Z| / minSecretProbability(F, n)) · signedL1(A).
-/
theorem gl_sum_signedL2_roundOp_le (hn : 2 ≤ n) (p : GLRectanglePartition F n Z)
    (A : SignedTable (State F n)) :
    ∑ z, signedL2 (glRoundOp p A z) ≤
      Real.sqrt ((Fintype.card Z : ℝ) / minSecretProbability F n) * signedL1 A := by
  letI := state_nonempty (F := F) hn
  exact sum_signedL2_roundOp_le _ _ _ (minSecretProbability_pos hn) (gl_transitionDensityBound hn) _

end ActualGL

end

end TableAnalysis
