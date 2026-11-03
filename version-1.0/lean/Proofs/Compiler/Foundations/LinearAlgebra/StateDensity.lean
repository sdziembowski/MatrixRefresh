import Proofs.Compiler.Foundations.LinearAlgebra.RefreshBounds
import Proofs.Compiler.Construction.Parameters



/-!
# Forward current-state densities for adaptive rectangle protocols

The input density is the product-uniform distribution, with density one. The protocol chooses a local rectangle partition at each complete public history. No intermediate secret is selected or changed in this recursion.
-/

set_option autoImplicit false

open scoped BigOperators

namespace TableAnalysis

open MatrixRefresh Refresh

noncomputable section

variable {X G Z : Type*} [Fintype X] [Fintype G] [Fintype Z]

/-- The signed round operator preserves total mass after summing leaves. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ FiniteRefresh(X, G); p ∈ RoundPartition(X, G, Z); F ∈ X → ℝ, assume X ≠ ∅; G ≠ ∅. Then

(∑_z (𝔼ᵤ [roundOp(e, p, F, z, u)])) = 𝔼ᵥ [F(v)].
-/
theorem roundOp_total_mass [Nonempty X] [Nonempty G]
    (e : FiniteRefresh X G) (p : RoundPartition X G Z) (F : X → ℝ) :
    (∑ z, uavg (roundOp e p F z)) = uavg F := by
  rw [← uavg_sum]
  unfold roundOp
  simp_rw [← uavg_sum]
  rw [uavg_comm]
  have hpoint (g : G) :
      uavg (fun x => ∑ z, F ((e g).symm x) * p.weight z g ((e g).symm x)) =
        uavg F := by
    simp_rw [← Finset.mul_sum, p.complete, mul_one]
    exact uavg_equiv (e g).symm F
  simp_rw [hpoint]
  exact uavg_const _

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For μ ∈ 𝒟(X); f ∈ G → X → ℝ, we have

𝔼_(x ← μ) [𝔼_g [f(g, x)]] = 𝔼_g [𝔼_(w ← μ) [f(g, w)]].
-/
theorem expect_uavg (μ : FiniteDistribution X) (f : G → X → ℝ) :
    μ.expect (fun x => uavg (fun g => f g x)) =
      uavg (fun g => μ.expect (f g)) := by
  simp only [FiniteDistribution.expect, uavg, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Fixed-secret mass preservation follows from invariance of the encoding measure under every sampled permutation. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For μ ∈ 𝒟(X); e ∈ FiniteRefresh(X, G); p ∈ RoundPartition(X, G, Z); F ∈ X → ℝ, assume G ≠ ∅; ∀ g, 𝔼_(x ← μ) [F((e(g))⁻¹(x))] = 𝔼_(v ← μ) [F(v)]. Then

(∑_z (𝔼_(w ← μ) [roundOp(e, p, F, z, w)])) = 𝔼_(y ← μ) [F(y)].
-/
theorem roundOp_expect_total_mass [Nonempty G] (μ : FiniteDistribution X)
    (e : FiniteRefresh X G) (p : RoundPartition X G Z) (F : X → ℝ)
    (hinv : ∀ g, μ.expect (fun x => F ((e g).symm x)) = μ.expect F) :
    (∑ z, μ.expect (roundOp e p F z)) = μ.expect F := by
  rw [← expect_sum]
  unfold roundOp
  simp_rw [← uavg_sum, ← Finset.mul_sum, p.complete, mul_one]
  rw [expect_uavg]
  simp_rw [hinv]
  exact uavg_const _

/- Mathematical definition (normal notation): Appending one answer gives the bijection (h,z) ↦ h‖z between a length-i history with a new answer and a length-(i+1) history. -/
def publicHistoryExtension (i : ℕ) :
    PublicHistory Z i × Z ≃ PublicHistory Z (i + 1) where
  toFun hz := Fin.snoc hz.1 hz.2
  invFun h := (Fin.init h, h (Fin.last i))
  left_inv hz := by simp
  right_inv h := Fin.snoc_init_self h

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For i ∈ ℕ; f ∈ PublicHistory(Z, (i + 1)) → ℝ, we have

(∑ₕ (f(h))) = ∑_(h ∈ PublicHistory(Z, i)) (∑_z (f(Fin.snoc(h, z)))).
-/
theorem sum_publicHistory_snoc (i : ℕ) (f : PublicHistory Z (i + 1) → ℝ) :
    (∑ h, f h) = ∑ h : PublicHistory Z i, ∑ z, f (Fin.snoc h z) := by
  rw [← (publicHistoryExtension (Z := Z) i).sum_comp f, Fintype.sum_prod_type]
  rfl

section Adaptive

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- A rectangle description of every round at every complete public prefix. The indicators may read the entire common matrix and all earlier answers. -/
/-
Mathematical definition (normal notation): For F a set; n ∈ ℕ; Z a set, assume F is a field; Z is finite. define

RectangleProtocol(n) := ∏_(i ∈ ℕ) PublicHistory(Z, i) → GLRectanglePartition(F, n, Z).
-/
abbrev RectangleProtocol (F : Type*) [Field F] (n : ℕ) (Z : Type*) [Fintype Z] :=
  (i : ℕ) → PublicHistory Z i → GLRectanglePartition F n Z

/- Mathematical definition (normal notation): Define the initial density by P_(0,∅) := 1. Recursively define P_(i+1,h‖z) := 𝒯_(i,h,z)(P_(i,h)), where 𝒯 is the answer-restricted round operator. -/
def currentDensity (p : RectangleProtocol F n Z) :
    (i : ℕ) → PublicHistory Z i → State F n → ℝ
  | 0, _, _ => 1
  | i + 1, h, x => glRoundOp (p i (Fin.init h))
      (currentDensity p i (Fin.init h)) (h (Fin.last i)) x

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); h ∈ PublicHistory(Z, 0); x ∈ State(F, n), we have

currentDensity(p, 0, h, x) = 1.
-/
@[simp] theorem currentDensity_zero (p : RectangleProtocol F n Z)
    (h : PublicHistory Z 0) (x : State F n) : currentDensity p 0 h x = 1 :=
  rfl

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); i ∈ ℕ; h ∈ PublicHistory(Z, i); z ∈ Z; x ∈ State(F, n), we have

currentDensity(p, (i + 1), Fin.snoc(h, z), x) = glRoundOp(p(i, h), currentDensity(p, i, h), z, x).
-/
@[simp] theorem currentDensity_snoc (p : RectangleProtocol F n Z) (i : ℕ)
    (h : PublicHistory Z i) (z : Z) (x : State F n) :
    currentDensity p (i + 1) (Fin.snoc h z) x =
      glRoundOp (p i h) (currentDensity p i h) z x := by
  simp [currentDensity, Fin.init_snoc, Fin.snoc_last]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); i ∈ ℕ; h ∈ PublicHistory(Z, i); x ∈ State(F, n), we have

0 ≤ currentDensity(p, i, h, x).
-/
theorem currentDensity_nonneg (p : RectangleProtocol F n Z) (i : ℕ)
    (h : PublicHistory Z i) (x : State F n) : 0 ≤ currentDensity p i h x := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
      change 0 ≤ uavg (fun M => _)
      apply uavg_nonneg
      intro M
      exact mul_nonneg (ih _ _)
        ((p i (Fin.init h)).toRoundPartition.nonneg _ _ _)

/-- At every time, the real joint state/history density has mass exactly one under the product-uniform reference distribution. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); i ∈ ℕ, assume 2 ≤ n. Then

(∑ₕ (𝔼ᵤ [currentDensity(p, i, h, u)])) = 1.
-/
theorem currentDensity_mass (hn : 2 ≤ n) (p : RectangleProtocol F n Z) (i : ℕ) :
    (∑ h, uavg (currentDensity p i h)) = 1 := by
  letI := state_nonempty (F := F) hn
  induction i with
  | zero => simp [currentDensity]
  | succ i ih =>
      rw [sum_publicHistory_snoc]
      simp_rw [show ∀ h z, currentDensity p (i + 1) (Fin.snoc h z) =
          glRoundOp (p i h) (currentDensity p i h) z from by
        intro h z; funext x; exact currentDensity_snoc p i h z x]
      simp_rw [glRoundOp, roundOp_total_mass]
      exact ih

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); i ∈ ℕ, assume 2 ≤ n. Then

(∑ₕ (signedL1(currentDensity(p, i, h)))) = 1.
-/
theorem currentDensity_L1_mass (hn : 2 ≤ n) (p : RectangleProtocol F n Z) (i : ℕ) :
    (∑ h, signedL1 (currentDensity p i h)) = 1 := by
  simp only [signedL1]
  simp_rw [abs_of_nonneg (currentDensity_nonneg p i _ _)]
  exact currentDensity_mass hn p i

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F; M ∈ GLₙ(F); x ∈ State(F, n), assume 2 ≤ n. Then

μₛ(refresh(x, M)) = μₛ(x).
-/
theorem mu_weight_refresh (hn : 2 ≤ n) (s : F) (M : Refresh.«GL» F n)
    (x : State F n) :
    (mu F n hn s).weight (refresh x M) = (mu F n hn s).weight x := by
  simp only [mu_weight, refresh_secret]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F; M ∈ GLₙ(F); f ∈ State(F, n) → ℝ, assume 2 ≤ n. Then

𝔼_(x ← μₛ) [f((glRefreshEquiv(M))⁻¹(x))] = 𝔼_(v ← μₛ) [f(v)].
-/
theorem mu_expect_inverse_refresh (hn : 2 ≤ n) (s : F) (M : Refresh.«GL» F n)
    (f : State F n → ℝ) :
    (mu F n hn s).expect (fun x => f ((glRefreshEquiv M).symm x)) =
      (mu F n hn s).expect f := by
  unfold FiniteDistribution.expect
  calc
    _ = ∑ x, (mu F n hn s).weight ((glRefreshEquiv M).symm x) *
        f ((glRefreshEquiv M).symm x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [show (glRefreshEquiv M).symm x = refresh x M⁻¹ from rfl,
        mu_weight_refresh hn s M⁻¹ x]
      rfl
    _ = _ := Equiv.sum_comp (glRefreshEquiv M).symm
      (fun x => (mu F n hn s).weight x * f x)

/-- The same forward density gives a normalized transcript distribution for every secret. This is proved from fixed-matrix fiber invariance, including zero. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); s ∈ F; i ∈ ℕ, assume 2 ≤ n. Then

(∑ₕ (𝔼_(u ← μₛ) [currentDensity(p, i, h, u)])) = 1.
-/
theorem currentDensity_secret_mass (hn : 2 ≤ n) (p : RectangleProtocol F n Z)
    (s : F) (i : ℕ) : (∑ h, (mu F n hn s).expect (currentDensity p i h)) = 1 := by
  induction i with
  | zero => simp [currentDensity]
  | succ i ih =>
      rw [sum_publicHistory_snoc]
      simp_rw [show ∀ h z, currentDensity p (i + 1) (Fin.snoc h z) =
          glRoundOp (p i h) (currentDensity p i h) z from by
        intro h z; funext x; exact currentDensity_snoc p i h z x]
      have hone (h : PublicHistory Z i) :
          (∑ z, (mu F n hn s).expect (glRoundOp (p i h) (currentDensity p i h) z)) =
            (mu F n hn s).expect (currentDensity p i h) :=
        roundOp_expect_total_mass _ _ _ _
          (fun M => mu_expect_inverse_refresh hn s M _)
      simp_rw [hone]
      exact ih

/- Mathematical definition (normal notation): The transcript distribution under secret s assigns probability 𝔼_((L,R) ← μₛ) [P_(i,h)(L,R)] to each length-i history h. -/
def stateTranscriptDistribution (hn : 2 ≤ n) (p : RectangleProtocol F n Z) (s : F) (i : ℕ) :
    FiniteDistribution (PublicHistory Z i) where
  weight h := (mu F n hn s).expect (currentDensity p i h)
  nonneg h := (mu F n hn s).expect_nonneg _ (currentDensity_nonneg p i h)
  total := currentDensity_secret_mass hn p s i

end Adaptive

end

end TableAnalysis
