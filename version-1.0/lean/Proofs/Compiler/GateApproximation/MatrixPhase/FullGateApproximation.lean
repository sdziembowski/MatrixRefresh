import Proofs.Compiler.GateApproximation.MatrixPhase.GateDimensions
import Proofs.Compiler.GateApproximation.MatrixPhase.GateLabelError
import Proofs.Compiler.GateApproximation.MatrixPhase.JointApproximation
import Proofs.Compiler.GateApproximation.Shortening.ShorteningAnswerProbabilities



/-!
# Common tables for the complete concrete gate

The canonical answer table is the same conditional answer probability function used by the real-gate coupling. The approximation tables are transported from the common all-port matrix tables, and hence do not depend on the input plaintext labels.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical

namespace CircuitCompiler

open Refresh MatrixRefresh TableAnalysis Shortening

noncomputable section

variable {F A B : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype A] [Fintype B] [DecidableEq B]

/-
Mathematical definition (normal notation): For F,A,B a set; n, t ∈ ℕ, assume F is a field; F is finite; B is finite. define

GateRectangles(n, t) := A → V(F, t) → Pivot(F, n) → RectanglePartition(B, ((U(F, n) × U(F, n)) × U(F, n)), (((U(F, n) × U(F, n)) × U(F, n)) × V(F, t))).
-/
abbrev GateRectangles (F A B : Type*) [Field F] [Fintype F] [DecidableEq F]
    [Fintype B] (n t : ℕ) :=
  A → V F t → Pivot F n → RectanglePartition B
    ((U F n × U F n) × U F n) (((U F n × U F n) × U F n) × V F t)

/-- The actual complete canonical gate answer table on the common three-port carrier, zero off its algebraically consistent output fiber. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); r ∈ GateRectangles(F, A, B, n, t); β₀ ∈ B; αβ ∈ A × B; x, y ∈ GateSide(F, n, n), assume 2 ≤ n; n · n = n + t; ε ≠ 0. define

fullGateAnswerProb(c, ε, p, r, β₀, αβ, x, y) := { ambientGateAnswerDistribution(c, ε, p, (((x)₁)₁, ((y)₁)₁), (((x)₁)₂, ((y)₁)₂), rectangleLeak(c, ε, portProduct(x, y), r, β₀, ((x)₁, (y)₁)), ((x)₂, (y)₂))(αβ) if ((x)₂ · (y)₂) = c + ε · portProduct(x, y),; 0 otherwise }.
-/
def fullGateAnswerProb {n t : ℕ} (hn : 2 ≤ n) (hdim : n * n = n + t)
    (c ε : F) (hε : ε ≠ 0)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (r : GateRectangles F A B n t) (β₀ : B) (αβ : A × B)
    (x y : GateSide F n n) : ℝ :=
  if h : dot x.2.val y.2.val = c + ε * portProduct x y then
    (ambientGateAnswerDistribution hn hdim c ε hε p ⟨x.1.1, y.1.1⟩ ⟨x.1.2, y.1.2⟩
      (rectangleLeak c ε (portProduct x y) r β₀ (x.1, y.1)) ⟨x.2, y.2⟩).weight αβ
  else 0

/-- The normalized ambient answer distribution, including irrelevant off-fiber values. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); r ∈ GateRectangles(F, A, B, n, t); β₀ ∈ B; αβ ∈ A × B; x, y ∈ GateSide(F, n, n), assume 2 ≤ n; n · n = n + t; ε ≠ 0. define

fullGateAmbientWeight(c, ε, p, r, β₀, αβ, x, y) := ambientGateAnswerDistribution(c, ε, p, (((x)₁)₁, ((y)₁)₁), (((x)₁)₂, ((y)₁)₂), rectangleLeak(c, ε, portProduct(x, y), r, β₀, ((x)₁, (y)₁)), ((x)₂, (y)₂))(αβ).
-/
def fullGateAmbientWeight {n t : ℕ} (hn : 2 ≤ n) (hdim : n * n = n + t)
    (c ε : F) (hε : ε ≠ 0)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (r : GateRectangles F A B n t) (β₀ : B) (αβ : A × B)
    (x y : GateSide F n n) : ℝ :=
  (ambientGateAnswerDistribution hn hdim c ε hε p ⟨x.1.1, y.1.1⟩ ⟨x.1.2, y.1.2⟩
    (rectangleLeak c ε (portProduct x y) r β₀ (x.1, y.1)) ⟨x.2, y.2⟩).weight αβ

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); r ∈ GateRectangles(F, A, B, n, t); β₀ ∈ B; αβ ∈ A × B; x, y ∈ GateSide(F, n, n), assume 2 ≤ n; n · n = n + t; ε ≠ 0; ((x)₂ · (y)₂) = c + ε · portProduct(x, y). Then

fullGateAnswerProb(c, ε, p, r, β₀, αβ, x, y) = fullGateAmbientWeight(c, ε, p, r, β₀, αβ, x, y).
-/
theorem fullGateAnswerProb_eq_ambientWeight {n t : ℕ} (hn : 2 ≤ n) (hdim : n * n = n + t)
    (c ε : F) (hε : ε ≠ 0)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (r : GateRectangles F A B n t) (β₀ : B) (αβ : A × B) (x y : GateSide F n n)
    (h : dot x.2.val y.2.val = c + ε * portProduct x y) :
    fullGateAnswerProb hn hdim c ε hε p r β₀ αβ x y =
      fullGateAmbientWeight hn hdim c ε hε p r β₀ αβ x y := by
  simp only [fullGateAnswerProb, h, dite_true, fullGateAmbientWeight]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); r ∈ GateRectangles(F, A, B, n, t); β₀ ∈ B; αβ ∈ A × B; x, y ∈ GateSide(F, n, n), assume 2 ≤ n; n · n = n + t; ε ≠ 0. Then

0 ≤ fullGateAnswerProb(c, ε, p, r, β₀, αβ, x, y).
-/
theorem fullGateAnswerProb_nonneg {n t : ℕ} (hn : 2 ≤ n) (hdim : n * n = n + t)
    (c ε : F) (hε : ε ≠ 0)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (r : GateRectangles F A B n t) (β₀ : B) (αβ : A × B) (x y : GateSide F n n) :
    0 ≤ fullGateAnswerProb hn hdim c ε hε p r β₀ αβ x y := by
  unfold fullGateAnswerProb
  split_ifs
  · exact FiniteDistribution.nonneg _ _
  · rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); r ∈ GateRectangles(F, A, B, n, t); β₀ ∈ B; x, y ∈ GateSide(F, n, n), assume 2 ≤ n; n · n = n + t; ε ≠ 0. Then

(∑_αβ (fullGateAnswerProb(c, ε, p, r, β₀, αβ, x, y))) ≤ 1.
-/
theorem fullGateAnswerProb_sum_le {n t : ℕ} (hn : 2 ≤ n) (hdim : n * n = n + t)
    (c ε : F) (hε : ε ≠ 0)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (r : GateRectangles F A B n t) (β₀ : B) (x y : GateSide F n n) :
    (∑ αβ, fullGateAnswerProb hn hdim c ε hε p r β₀ αβ x y) ≤ 1 := by
  unfold fullGateAnswerProb
  split_ifs
  · exact (FiniteDistribution.total _).le
  · simp

/-- On a correct output, the common probability table is the circuit runner's normalized conditional answer distribution, entry for entry. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); r ∈ GateRectangles(F, A, B, n, t); β₀ ∈ B; a, b, u ∈ State(F, n); αβ ∈ A × B, assume 2 ≤ n; n · n = n + t; ε ≠ 0; secret(u) = c + ε · (secret(a) · secret(b)). Then

fullGateAnswerProb(c, ε, p, r, β₀, αβ, ((a.L, b.L), u.L), ((a.R, b.R), u.R)) = ambientGateAnswerDistribution(c, ε, p, a, b, rectangleLeak(c, ε, (secret(a) · secret(b)), r, β₀, ((a.L, b.L), (a.R, b.R))), u)(αβ).
-/
theorem fullGateAnswerProb_eq_ambient {n t : ℕ} (hn : 2 ≤ n) (hdim : n * n = n + t)
    (c ε : F) (hε : ε ≠ 0)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (r : GateRectangles F A B n t) (β₀ : B) (a b u : State F n)
    (hu : secret u = c + ε * (secret a * secret b)) (αβ : A × B) :
    fullGateAnswerProb hn hdim c ε hε p r β₀ αβ ((a.L, b.L), u.L) ((a.R, b.R), u.R) =
      (ambientGateAnswerDistribution hn hdim c ε hε p a b
        (rectangleLeak c ε (secret a * secret b) r β₀ ((a.L, b.L), (a.R, b.R))) u).weight αβ := by
  unfold fullGateAnswerProb
  dsimp only [portProduct]
  have h : dot u.L.val u.R.val = c + ε * (dot a.L.val a.R.val * dot b.L.val b.R.val) := hu
  simp only [h, dite_true]
  rfl

/-- Exact weighted answer table identity for the canonical transition. Off-fiber normalization choices disappear because the fresh output distribution has zero mass. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); r ∈ GateRectangles(F, A, B, n, t); β₀ ∈ B; a, b, u ∈ State(F, n); αβ ∈ A × B, assume 2 ≤ n; n · n = n + t; ε ≠ 0. Then

(((v ↦ ((v)₁, (v)₂)))_*fullGateCanonical(c, ε, p, a, b, rectangleLeak(c, ε, (secret(a) · secret(b)), r, β₀, ((a.L, b.L), (a.R, b.R)))))((u, αβ)) = μ_(c + ε · (secret(a) · secret(b)))(u) · fullGateAnswerProb(c, ε, p, r, β₀, αβ, ((a.L, b.L), u.L), ((a.R, b.R), u.R)).
-/
theorem fullGateCanonical_rectangle_weight {n t : ℕ} (hn : 2 ≤ n) (hdim : n * n = n + t)
    (c ε : F) (hε : ε ≠ 0)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (r : GateRectangles F A B n t) (β₀ : B) (a b u : State F n) (αβ : A × B) :
    ((fullGateCanonical hn hdim c ε hε p a b
      (rectangleLeak c ε (secret a * secret b) r β₀ ((a.L, b.L), (a.R, b.R)))).map
        (fun v => (v.1.val, v.2))).weight (u, αβ) =
      (mu F n hn (c + ε * (secret a * secret b))).weight u *
        fullGateAnswerProb hn hdim c ε hε p r β₀ αβ ((a.L, b.L), u.L) ((a.R, b.R), u.R) := by
  rw [fullGateCanonical_ambient]
  change (mu F n hn _).weight u * _ = _
  by_cases hu : secret u = c + ε * (secret a * secret b)
  · rw [fullGateAnswerProb_eq_ambient hn hdim c ε hε p r β₀ a b u hu]
  · rw [mu_weight]
    simp only [hu, if_false, zero_mul]

/-- On every valid old/output triple, the common answer table is exactly the shortening answer table for the genuine conditional shared-matrix answer. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); r ∈ GateRectangles(F, A, B, n, t); β₀ ∈ B; z ∈ F; o ∈ (U(F, n) × U(F, n)) × (U(F, n) × U(F, n)); u ∈ Fiber(F, n, (c + ε · z)); αβ ∈ A × B, assume 2 ≤ n; n · n = n + t; ε ≠ 0; Accepted(F, n, t, c, ε, z) ≠ ∅; (((o)₁)₁ · ((o)₂)₁) · (((o)₁)₂ · ((o)₂)₂) = z. Then

fullGateAnswerProb(c, ε, p, r, β₀, αβ, ((o)₁, u.val.L), ((o)₂, u.val.R)) = shortenedAnswerDistribution(c, ε, z, auxiliaryPortAnswerDistribution(p, z), r, β₀, o, u)(αβ).
-/
theorem fullGateAnswerProb_eq_shortened {n t : ℕ} (hn : 2 ≤ n) (hdim : n * n = n + t)
    (c ε : F) (hε : ε ≠ 0)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (r : GateRectangles F A B n t) (β₀ : B) (z : F)
    [Nonempty (Accepted F n t c ε z)]
    (o : (U F n × U F n) × (U F n × U F n))
    (ho : dot o.1.1.val o.2.1.val * dot o.1.2.val o.2.2.val = z)
    (u : Fiber F n (c + ε * z)) (αβ : A × B) :
    fullGateAnswerProb hn hdim c ε hε p r β₀ αβ (o.1, u.val.L) (o.2, u.val.R) =
      (shortenedAnswerDistribution c ε z (auxiliaryPortAnswerDistribution hdim p z) r β₀ o u).weight αβ := by
  subst z
  have hu : dot u.val.L.val u.val.R.val = c + ε *
      (dot o.1.1.val o.2.1.val * dot o.1.2.val o.2.2.val) := u.property
  unfold fullGateAnswerProb
  dsimp only [portProduct]
  simp only [hu, dite_true]
  change (ambientGateAnswerDistribution hn hdim c ε hε p ⟨o.1.1, o.2.1⟩ ⟨o.1.2, o.2.2⟩
    (rectangleLeak c ε _ r β₀ o) u.val).weight αβ = _
  letI := encoding_fiber_nonempty hn
    (c + ε * (secret (⟨o.1.1, o.2.1⟩ : State F n) * secret (⟨o.1.2, o.2.2⟩ : State F n)))
  letI := accepted_nonempty (n := n) (t := t) c ε
    (secret (⟨o.1.1, o.2.1⟩ : State F n) * secret (⟨o.1.2, o.2.2⟩ : State F n)) hε
  rw [ambientGateAnswerDistribution_fiber]
  unfold shortenedAnswerDistribution fullGateAnswer
  congr 3
  funext v
  exact congrArg (fun K : FiniteDistribution A => K.joint (rectangleLeak c ε _ r β₀ o v))
    (auxiliaryPortAnswerDistribution_eq hdim p ⟨o.1.1, o.2.1⟩ ⟨o.1.2, o.2.2⟩ v).symm

/-- The reference three-port distribution for a prescribed affine multiplication gate. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; c, ε, s₁, s₂ ∈ F, assume 2 ≤ n. define

shortGateLabelDistribution(c, ε, s₁, s₂) := (gateRegroup(n, n)_*((μ_(s₁) ⊗ μ_(s₂)) ⊗ μ_(c + ε · (s₁ · s₂)))).
-/
def shortGateLabelDistribution {n : ℕ} (hn : 2 ≤ n) (c ε s₁ s₂ : F) :
    FiniteDistribution (GateSide F n n × GateSide F n n) :=
  (((mu F n hn s₁).prod (mu F n hn s₂)).prod
    (mu F n hn (c + ε * (s₁ * s₂)))).map (gateRegroup n n)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; c, ε, s₁, s₂ ∈ F; f ∈ GateSide(F, n, n) → GateSide(F, n, n) → ℝ, assume 2 ≤ n; Fiber(F, n, (c + ε · (s₁ · s₂))) ≠ ∅. Then

𝔼_(ou ← (oldLabelDistribution(s₁, s₂) ⊗ 𝒰_(Fiber(F, n, (c + ε · (s₁ · s₂)))))) [f((((ou)₁)₁, ou.2.val.L), (((ou)₁)₂, ou.2.val.R))] = 𝔼_(xy ← shortGateLabelDistribution(c, ε, s₁, s₂)) [f((xy)₁, (xy)₂)].
-/
theorem shortGateLabelDistribution_fiber_expect {n : ℕ} (hn : 2 ≤ n) (c ε s₁ s₂ : F)
    [Nonempty (Fiber F n (c + ε * (s₁ * s₂)))]
    (f : GateSide F n n → GateSide F n n → ℝ) :
    ((oldLabelDistribution hn s₁ s₂).prod
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (c + ε * (s₁ * s₂))))).expect
      (fun ou => f (ou.1.1, ou.2.val.L) (ou.1.2, ou.2.val.R)) =
      (shortGateLabelDistribution hn c ε s₁ s₂).expect (fun xy => f xy.1 xy.2) := by
  rw [shortGateLabelDistribution, expect_map, expect_prod, expect_prod, oldLabelDistribution, expect_map]
  simp only [mu, expect_map]
  rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); r ∈ GateRectangles(F, A, B, n, t); β₀ ∈ B; s₁, s₂ ∈ F; αβ ∈ A × B; f ∈ GateSide(F, n, n) → GateSide(F, n, n) → ℝ → ℝ, assume 2 ≤ n; n · n = n + t; ε ≠ 0. Then

𝔼_(xy ← shortGateLabelDistribution(c, ε, s₁, s₂)) [f((xy)₁, (xy)₂, fullGateAnswerProb(c, ε, p, r, β₀, αβ, (xy)₁, (xy)₂))] = 𝔼_(xy ← shortGateLabelDistribution(c, ε, s₁, s₂)) [f((xy)₁, (xy)₂, fullGateAmbientWeight(c, ε, p, r, β₀, αβ, (xy)₁, (xy)₂))].
-/
theorem shortGateLabelDistribution_kernel_expect {n t : ℕ} (hn : 2 ≤ n) (hdim : n * n = n + t)
    (c ε : F) (hε : ε ≠ 0)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (r : GateRectangles F A B n t) (β₀ : B) (s₁ s₂ : F) (αβ : A × B)
    (f : GateSide F n n → GateSide F n n → ℝ → ℝ) :
    (shortGateLabelDistribution hn c ε s₁ s₂).expect (fun xy =>
      f xy.1 xy.2 (fullGateAnswerProb hn hdim c ε hε p r β₀ αβ xy.1 xy.2)) =
    (shortGateLabelDistribution hn c ε s₁ s₂).expect (fun xy =>
      f xy.1 xy.2 (fullGateAmbientWeight hn hdim c ε hε p r β₀ αβ xy.1 xy.2)) := by
  rw [shortGateLabelDistribution, expect_map, expect_map]
  conv_lhs => rw [expect_prod]
  conv_rhs => rw [expect_prod]
  apply Finset.sum_congr rfl
  intro ab _
  by_cases hab : ((mu F n hn s₁).prod (mu F n hn s₂)).weight ab = 0
  · simp only [hab, zero_mul]
  · have hab' : (mu F n hn s₁).weight ab.1 * (mu F n hn s₂).weight ab.2 ≠ 0 := hab
    have hs₁ := mu_supports n hn s₁ ab.1 (mul_ne_zero_iff.mp hab').1
    have hs₂ := mu_supports n hn s₂ ab.2 (mul_ne_zero_iff.mp hab').2
    congr 1
    simp only [mu, expect_map]
    apply congrArg (FiniteDistribution.expect _)
    funext u
    congr 1
    apply fullGateAnswerProb_eq_ambientWeight
    change secret u.val = c + ε * (secret ab.1 * secret ab.2)
    rw [hs₁, hs₂]
    exact u.property

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s₁, s₂ ∈ F; o ∈ (U(F, n) × U(F, n)) × (U(F, n) × U(F, n)), assume 2 ≤ n; oldLabelDistribution(s₁, s₂)(o) ≠ 0. Then

(((o)₁)₁ · ((o)₂)₁) · (((o)₁)₂ · ((o)₂)₂) = s₁ · s₂.
-/
theorem oldLabelDistribution_product {n : ℕ} (hn : 2 ≤ n) (s₁ s₂ : F)
    (o : (U F n × U F n) × (U F n × U F n))
    (ho : (oldLabelDistribution hn s₁ s₂).weight o ≠ 0) :
    dot o.1.1.val o.2.1.val * dot o.1.2.val o.2.2.val = s₁ * s₂ := by
  rw [oldLabelDistribution, FiniteDistribution.map_equiv_weight] at ho
  change (mu F n hn s₁).weight ⟨o.1.1, o.2.1⟩ *
    (mu F n hn s₂).weight ⟨o.1.2, o.2.2⟩ ≠ 0 at ho
  rw [← show secret (⟨o.1.1, o.2.1⟩ : State F n) = _ from
    mu_supports n hn s₁ _ (mul_ne_zero_iff.mp ho).1,
    ← show secret (⟨o.1.2, o.2.2⟩ : State F n) = _ from
    mu_supports n hn s₂ _ (mul_ne_zero_iff.mp ho).2]
  rfl

/-- Complete gate squared-error transport for the same common matrix tables and every pair of plaintext labels. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); r ∈ GateRectangles(F, A, B, n, t); β₀ ∈ B; G ∈ A → ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))); η ∈ ℝ; s₁, s₂ ∈ F, assume 2 ≤ n; n · n = n + t; ε ≠ 0; 𝔼ₓ [𝔼_y [gateDensity(x, y) · ∑_α ((groupedMatrixAnswerProb(p, α, x, y) - G(α, x, y))²)]] ≤ η². Then

𝔼_(xy ← shortGateLabelDistribution(c, ε, s₁, s₂)) [∑_α (∑ᵦ ((fullGateAnswerProb(c, ε, p, r, β₀, (α, β), (xy)₁, (xy)₂) - transportMatrix(c, ε, r(α), reindexGateTable(G(α)), β, (xy)₁, (xy)₂))²))] ≤ (acceptanceMass(n = n, t = t, c, ε, (s₁ · s₂)))⁻¹ · ((2 · |F| · η)² + 1 / (|F|)^(n + t − 1)).
-/
theorem fullGateAnswerProb_error_L2 {n t : ℕ} (hn : 2 ≤ n) (hdim : n * n = n + t)
    (c ε : F) (hε : ε ≠ 0)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (r : GateRectangles F A B n t) (β₀ : B)
    (G : A → Matrix (GateSide F n (n * n)) (GateSide F n (n * n)) ℝ)
    (η : ℝ)
    (herr : uavg (fun x => uavg (fun y => gateDensity x y *
      ∑ α, (groupedMatrixAnswerProb p α x y - G α x y) ^ 2)) ≤ η ^ 2)
    (s₁ s₂ : F) :
    (shortGateLabelDistribution hn c ε s₁ s₂).expect (fun xy => ∑ α, ∑ β,
      (fullGateAnswerProb hn hdim c ε hε p r β₀ (α, β) xy.1 xy.2 -
        transportMatrix c ε (r α) (reindexGateTable hdim (G α)) β xy.1 xy.2) ^ 2) ≤
      (acceptanceMass (n := n) (t := t) c ε (s₁ * s₂))⁻¹ *
        ((2 * (fieldCard F : ℝ) * η) ^ 2 + 1 / (fieldCard F : ℝ) ^ (n + t - 1)) := by
  have hm : 2 ≤ n * n := by nlinarith
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  letI := encoding_fiber_nonempty hn (c + ε * (s₁ * s₂))
  letI := encoding_fiber_nonempty hm (s₁ * s₂)
  letI := encoding_fiber_nonempty (by omega : 2 ≤ n + t) (s₁ * s₂)
  letI := accepted_nonempty (n := n) (t := t) c ε (s₁ * s₂) hε
  letI := auxiliary_nonempty (m := n + t) (s₁ * s₂)
  have he := matrixAnswerDistribution_fixed_labels_L2 hn hm s₁ s₂ p G η herr
  rw [← auxiliaryPortAnswerDistribution_reindex_error hdim p (s₁ * s₂) (oldLabelDistribution hn s₁ s₂) G] at he
  have hshort := shortenedAnswerDistribution_error_L2 (by omega : 2 ≤ n + t) c ε (s₁ * s₂) hε
    (oldLabelDistribution hn s₁ s₂) (auxiliaryPortAnswerDistribution hdim p (s₁ * s₂)) r
    (fun α => reindexGateTable hdim (G α)) β₀ (2 * (fieldCard F : ℝ) * η) he
  rw [← shortGateLabelDistribution_fiber_expect hn c ε s₁ s₂ (fun x y => ∑ α, ∑ β,
    (fullGateAnswerProb hn hdim c ε hε p r β₀ (α, β) x y -
      transportMatrix c ε (r α) (reindexGateTable hdim (G α)) β x y) ^ 2)]
  convert hshort using 1
  rw [expect_prod, expect_prod]
  apply Finset.sum_congr rfl
  intro o _
  by_cases ho : (oldLabelDistribution hn s₁ s₂).weight o = 0
  · simp [ho]
  · congr 1
    apply congrArg (FiniteDistribution.expect (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (c + ε * (s₁ * s₂)))))
    funext u
    simp only [fullGateAnswerProb_eq_shortened hn hdim c ε hε p r β₀ (s₁ * s₂)
      o (oldLabelDistribution_product hn s₁ s₂ o ho) u]

/-- A uniform numerical lower bound for the ordinary shortening acceptance. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F, assume 2 ≤ n. Then

(acceptanceMass(n = n, t = t, c, ε, z))⁻¹ ≤ 4.
-/
theorem acceptanceMass_inv_le_four {n t : ℕ} (hn : 2 ≤ n) (c ε z : F) :
    (acceptanceMass (n := n) (t := t) c ε z)⁻¹ ≤ 4 := by
  have hq := fieldCard_cast_ge_two (F := F)
  have hpow : (fieldCard F : ℝ) ^ 2 ≤ (fieldCard F : ℝ) ^ n :=
    pow_le_pow_right₀ (by linarith) hn
  have hden : 0 < (fieldCard F : ℝ) ^ n := pow_pos (fieldCard_cast_pos (F := F)) _
  have hratio : ((fieldCard F : ℝ) + 1) / (fieldCard F : ℝ) ^ n ≤ 3 / 4 := by
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg ((fieldCard F : ℝ) - 2)]
  have hmass := (failureMass_le (t := t) hn c ε z).trans hratio
  have hpos : 0 < acceptanceMass (n := n) (t := t) c ε z := by linarith
  have h : 1 / acceptanceMass (n := n) (t := t) c ε z ≤ 4 :=
    (div_le_iff₀ hpos).2 (by linarith)
  simpa only [one_div] using h

/-- The virtual-zero error is smaller than the squared matrix approximation rate for every valid tensor dimension. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ, assume 2 ≤ n; n · n = n + t. Then

1 / (|F|)^(n + t − 1) ≤ ((|F|ⁿ)^(−((1 / 10))))².
-/
theorem gate_virtual_error_le_rate_sq {n t : ℕ} (hn : 2 ≤ n) (hdim : n * n = n + t) :
    1 / (fieldCard F : ℝ) ^ (n + t - 1) ≤ ((vectorCard F n : ℝ) ^ (-(1 / 10) : ℝ)) ^ 2 := by
  have hq := fieldCard_cast_ge_two (F := F)
  have hN : 1 ≤ (vectorCard F n : ℝ) := by
    have h := vectorCard_real_ge_four (F := F) hn
    linarith
  have hN0 : 0 ≤ (vectorCard F n : ℝ) := le_trans (by norm_num) hN
  have hexp : n ≤ n + t - 1 := by
    have : n + 1 ≤ n * n := by nlinarith
    omega
  have hpow : (vectorCard F n : ℝ) ≤ (fieldCard F : ℝ) ^ (n + t - 1) := by
    simpa only [vectorCard, Nat.cast_pow] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ fieldCard F) hexp
  calc
    _ ≤ 1 / (vectorCard F n : ℝ) := one_div_le_one_div_of_le (by positivity) hpow
    _ = (vectorCard F n : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
    _ ≤ (vectorCard F n : ℝ) ^ ((-(1 / 10) : ℝ) * 2) :=
      Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
    _ = _ := by rw [Real.rpow_mul hN0, Real.rpow_two]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X,Z a set; D ∈ ℝ^(X × X); E ∈ Z → ℝ^(X × X), assume X is finite; Z is finite. Then

densityTablePair(D, E, E) = 𝔼ₓ [𝔼_y [D(x, y) · ∑_z ((E(z, x, y))²)]].
-/
theorem densityTablePair_self_average {X Z : Type*} [Fintype X] [Fintype Z]
    (D : Matrix X X ℝ) (E : Z → Matrix X X ℝ) :
    densityTablePair D E E =
      uavg (fun x => uavg (fun y => D x y * ∑ z, E z x y ^ 2)) := by
  simp only [densityTablePair, uavg_prod, Finset.mul_sum, uavg_sum, pow_two, mul_assoc]

/-
Mathematical definition (normal notation): For F a set, assume F is a field; F is finite. define

fullGateErrorConstant := 4 · |F| · jointApproximationConstant(F) + 2.
-/
def fullGateErrorConstant (F : Type*) [Field F] [Fintype F] [DecidableEq F] : ℝ :=
  4 * (fieldCard F : ℝ) * jointApproximationConstant F + 2

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

0 < fullGateErrorConstant(F).
-/
theorem fullGateErrorConstant_pos : 0 < fullGateErrorConstant F := by
  have := jointApproximationConstant_pos (F := F)
  unfold fullGateErrorConstant
  positivity

/-- Common three-port tables for the actual complete gate. The tables are chosen once, before either input plaintext is specified. The nuclear budget counts the two leakage alphabets multiplicatively; the error holds for every pair of input labels under their genuine independent encoding distributions. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); r ∈ GateRectangles(F, A, B, n, t); β₀ ∈ B, assume A ≠ ∅; 2 ≤ n; n · n = n + t; ε ≠ 0. Then

∃ T ∈ A × B → ℝ^(GateSide(F, n, n) × GateSide(F, n, n)), (∑_αβ (‖ T(αβ)‖_*)) ≤ ((|F| / (|F| - 1)) · √(n · (|F| - 1) · |B|)) · √(|A|) ∧ ∀ s₁, s₂ ∈ F, (∑_αβ (𝔼_(xy ← shortGateLabelDistribution(c, ε, s₁, s₂)) [|fullGateAnswerProb(c, ε, p, r, β₀, αβ, (xy)₁, (xy)₂) - T(αβ, (xy)₁, (xy)₂)|])) ≤ fullGateErrorConstant(F) · |A| · √(|(A × B)|) · (|F|ⁿ)^(−((1 / 10))).
-/
theorem exists_fullGate_approximation [Nonempty A] {n t : ℕ}
    (hn : 2 ≤ n) (hdim : n * n = n + t) (c ε : F) (hε : ε ≠ 0)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (r : GateRectangles F A B n t) (β₀ : B) :
    ∃ T : A × B → Matrix (GateSide F n n) (GateSide F n n) ℝ,
      (∑ αβ, tableNuclearNorm (T αβ)) ≤
        (((fieldCard F : ℝ) / ((fieldCard F : ℝ) - 1)) *
          Real.sqrt ((n * (fieldCard F - 1) : ℕ) * Fintype.card B)) * Real.sqrt (Fintype.card A : ℝ) ∧
      ∀ s₁ s₂ : F,
        (∑ αβ, (shortGateLabelDistribution hn c ε s₁ s₂).expect (fun xy =>
          |fullGateAnswerProb hn hdim c ε hε p r β₀ αβ xy.1 xy.2 - T αβ xy.1 xy.2|)) ≤
        fullGateErrorConstant F * Fintype.card A * Real.sqrt (Fintype.card (A × B) : ℝ) *
          (vectorCard F n : ℝ) ^ (-(1 / 10) : ℝ) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  letI : Nonempty (U F (n + t)) := ⟨unitShare ⟨0, by omega⟩⟩
  obtain ⟨G, hGnuclear, hGerror⟩ := exists_jointPort_approximation hn p
  let T := fun αβ : A × B => transportMatrix c ε (r αβ.1) (reindexGateTable hdim (G αβ.1)) αβ.2
  refine ⟨T, ?_, ?_⟩
  · dsimp only [T]
    rw [Fintype.sum_prod_type]
    have h := transportMatrix_family_nuclear (by omega : 1 ≤ n) c ε hε r
      (fun α => reindexGateTable hdim (G α))
    simp only [reindexGateTable_nuclear] at h
    exact h.trans (mul_le_mul_of_nonneg_left hGnuclear
      (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by
        have := fieldCard_cast_ge_two (F := F); linarith)) (Real.sqrt_nonneg _)))
  · intro s₁ s₂
    let rate : ℝ := (vectorCard F n : ℝ) ^ (-(1 / 10) : ℝ)
    let η : ℝ := jointApproximationConstant F * Fintype.card A * rate
    have hrate : 0 ≤ rate := Real.rpow_nonneg (by positivity) _
    have hC : 0 ≤ jointApproximationConstant F := (jointApproximationConstant_pos (F := F)).le
    have hη : 0 ≤ η := by dsimp [η]; positivity
    have hA : 1 ≤ (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
    have henergy : uavg (fun x => uavg (fun y => gateDensity x y *
        ∑ α, (groupedMatrixAnswerProb p α x y - G α x y) ^ 2)) ≤ η ^ 2 := by
      have h := (Real.sqrt_le_left hη).mp hGerror
      simpa only [densityTablePair_self_average] using h
    have hshort := fullGateAnswerProb_error_L2 hn hdim c ε hε p r β₀ G η henergy s₁ s₂
    have hvirt := gate_virtual_error_le_rate_sq (F := F) hn hdim
    have haccept := acceptanceMass_inv_le_four (t := t) hn c ε (s₁ * s₂)
    have hu : 0 ≤ 2 * (fieldCard F : ℝ) * η := by positivity
    have hshort' : (shortGateLabelDistribution hn c ε s₁ s₂).expect (fun xy => ∑ α, ∑ β,
        (fullGateAnswerProb hn hdim c ε hε p r β₀ (α, β) xy.1 xy.2 - T (α, β) xy.1 xy.2) ^ 2) ≤
        (2 * (2 * (fieldCard F : ℝ) * η + rate)) ^ 2 := by
      refine hshort.trans ?_
      calc
        _ ≤ 4 * ((2 * (fieldCard F : ℝ) * η) ^ 2 + 1 / (fieldCard F : ℝ) ^ (n + t - 1)) :=
          mul_le_mul_of_nonneg_right haccept (by positivity)
        _ ≤ 4 * ((2 * (fieldCard F : ℝ) * η) ^ 2 + rate ^ 2) := by gcongr
        _ ≤ _ := by nlinarith [mul_nonneg hu hrate]
    have hscale : 2 * (2 * (fieldCard F : ℝ) * η + rate) ≤
        fullGateErrorConstant F * Fintype.card A * rate := by
      have hArate := mul_le_mul_of_nonneg_right hA hrate
      dsimp only [η, fullGateErrorConstant]
      nlinarith
    have hscaled := hshort'.trans
      (pow_le_pow_left₀ (by positivity) hscale 2)
    have habs := family_mean_abs_le (shortGateLabelDistribution hn c ε s₁ s₂)
      (fun αβ xy => fullGateAnswerProb hn hdim c ε hε p r β₀ αβ xy.1 xy.2 - T αβ xy.1 xy.2)
      (fullGateErrorConstant F * Fintype.card A * rate)
      (by have := fullGateErrorConstant_pos (F := F); positivity)
      (by simpa only [Fintype.sum_prod_type] using hscaled)
    exact habs.trans_eq (by ring)

/-
Mathematical definition (normal notation): For F a set, assume F is a field; F is finite. define

fullGateApproximationConstant := 1 + (|F| / (|F| - 1)) · √(|F| - 1) + fullGateErrorConstant(F) .
-/
def fullGateApproximationConstant (F : Type*) [Field F] [Fintype F] [DecidableEq F] : ℝ :=
  1 + ((fieldCard F : ℝ) / ((fieldCard F : ℝ) - 1)) * Real.sqrt ((fieldCard F - 1 : ℕ) : ℝ) +
    fullGateErrorConstant F

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

1 ≤ fullGateApproximationConstant(F).
-/
theorem fullGateApproximationConstant_ge_one : 1 ≤ fullGateApproximationConstant F := by
  have hρ : 0 ≤ (fieldCard F : ℝ) / ((fieldCard F : ℝ) - 1) :=
    div_nonneg (Nat.cast_nonneg _) (by have := fieldCard_cast_ge_two (F := F); linarith)
  have hE := (fullGateErrorConstant_pos (F := F)).le
  have hs := mul_nonneg hρ (Real.sqrt_nonneg ((fieldCard F - 1 : ℕ) : ℝ))
  unfold fullGateApproximationConstant
  linarith

/-- The complete local approximation in the form used by circuit composition. One explicit field-only constant controls both bounds. `K` is the cardinality of the complete answer pair, including both matrix and shortening leakage. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); r ∈ GateRectangles(F, A, B, n, t); β₀ ∈ B, assume A ≠ ∅; 2 ≤ n; n · n = n + t; ε ≠ 0. Then

∃ T ∈ A × B → ℝ^(GateSide(F, n, n) × GateSide(F, n, n)), (∑_αβ (‖ T(αβ)‖_*)) ≤ fullGateApproximationConstant(F) · √(n · |(A × B)|) ∧ ∀ s₁, s₂ ∈ F, (∑_αβ (𝔼_(xy ← shortGateLabelDistribution(c, ε, s₁, s₂)) [|fullGateAnswerProb(c, ε, p, r, β₀, αβ, (xy)₁, (xy)₂) - T(αβ, (xy)₁, (xy)₂)|])) ≤ fullGateApproximationConstant(F) · (|(A × B)|)² · (|F|ⁿ)^(−((1 / 10))).
-/
theorem fullGate_approximation [Nonempty A] {n t : ℕ}
    (hn : 2 ≤ n) (hdim : n * n = n + t) (c ε : F) (hε : ε ≠ 0)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (r : GateRectangles F A B n t) (β₀ : B) :
    ∃ T : A × B → Matrix (GateSide F n n) (GateSide F n n) ℝ,
      (∑ αβ, tableNuclearNorm (T αβ)) ≤ fullGateApproximationConstant F *
        Real.sqrt ((n : ℝ) * Fintype.card (A × B)) ∧
      ∀ s₁ s₂ : F,
        (∑ αβ, (shortGateLabelDistribution hn c ε s₁ s₂).expect (fun xy =>
          |fullGateAnswerProb hn hdim c ε hε p r β₀ αβ xy.1 xy.2 - T αβ xy.1 xy.2|)) ≤
        fullGateApproximationConstant F * (Fintype.card (A × B) : ℝ) ^ 2 *
          (vectorCard F n : ℝ) ^ (-(1 / 10) : ℝ) := by
  obtain ⟨T, hT, herr⟩ := exists_fullGate_approximation hn hdim c ε hε p r β₀
  letI : Nonempty B := ⟨β₀⟩
  have hρ : 0 ≤ (fieldCard F : ℝ) / ((fieldCard F : ℝ) - 1) :=
    div_nonneg (Nat.cast_nonneg _) (by have := fieldCard_cast_ge_two (F := F); linarith)
  have hE := (fullGateErrorConstant_pos (F := F)).le
  have hcoef : ((fieldCard F : ℝ) / ((fieldCard F : ℝ) - 1)) * Real.sqrt ((fieldCard F - 1 : ℕ) : ℝ) ≤
      fullGateApproximationConstant F := by unfold fullGateApproximationConstant; linarith
  have hEbound : fullGateErrorConstant F ≤ fullGateApproximationConstant F := by
    have hs := mul_nonneg hρ (Real.sqrt_nonneg ((fieldCard F - 1 : ℕ) : ℝ))
    unfold fullGateApproximationConstant
    linarith
  refine ⟨T, hT.trans ?_, fun s₁ s₂ => (herr s₁ s₂).trans ?_⟩
  · have heq : (((fieldCard F : ℝ) / ((fieldCard F : ℝ) - 1)) *
        Real.sqrt ((n * (fieldCard F - 1) : ℕ) * Fintype.card B)) * Real.sqrt (Fintype.card A : ℝ) =
        (((fieldCard F : ℝ) / ((fieldCard F : ℝ) - 1)) * Real.sqrt ((fieldCard F - 1 : ℕ) : ℝ)) *
          Real.sqrt ((n : ℝ) * Fintype.card (A × B)) := by
      have hroot : Real.sqrt ((n * (fieldCard F - 1) : ℕ) * Fintype.card B) *
          Real.sqrt (Fintype.card A : ℝ) = Real.sqrt ((fieldCard F - 1 : ℕ) : ℝ) *
            Real.sqrt ((n : ℝ) * Fintype.card (A × B)) := by
        rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (Nat.cast_nonneg (fieldCard F - 1))]
        congr 1
        simp only [Fintype.card_prod, Nat.cast_mul]
        ring
      calc
        _ = ((fieldCard F : ℝ) / ((fieldCard F : ℝ) - 1)) *
          (Real.sqrt ((n * (fieldCard F - 1) : ℕ) * Fintype.card B) * Real.sqrt (Fintype.card A : ℝ)) := by ring
        _ = _ := by rw [hroot]; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)
  · have hA : 1 ≤ (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
    have hB : 1 ≤ (Fintype.card B : ℝ) := by exact_mod_cast Fintype.card_pos
    have hK : 1 ≤ (Fintype.card (A × B) : ℝ) := by exact_mod_cast Fintype.card_pos
    have hAK : (Fintype.card A : ℝ) ≤ Fintype.card (A × B) := by
      rw [Fintype.card_prod, Nat.cast_mul]
      nlinarith
    have hsqrt : Real.sqrt (Fintype.card (A × B) : ℝ) ≤ Fintype.card (A × B) :=
      (Real.sqrt_le_left (by positivity)).2 (by nlinarith)
    have hcards : (Fintype.card A : ℝ) * Real.sqrt (Fintype.card (A × B) : ℝ) ≤
        (Fintype.card (A × B) : ℝ) ^ 2 := by
      simpa only [pow_two] using mul_le_mul hAK hsqrt (Real.sqrt_nonneg _) (by positivity)
    calc
      _ = fullGateErrorConstant F *
        ((Fintype.card A : ℝ) * Real.sqrt (Fintype.card (A × B) : ℝ)) *
          (vectorCard F n : ℝ) ^ (-(1 / 10) : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul hEbound hcards (by positivity) (le_trans hE hEbound)) (by positivity)

/-- The same complete gate approximation for the normalized ambient answer answer table used by the executable topological circuit runner. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); r ∈ GateRectangles(F, A, B, n, t); β₀ ∈ B, assume A ≠ ∅; 2 ≤ n; n · n = n + t; ε ≠ 0. Then

∃ T ∈ A × B → ℝ^(GateSide(F, n, n) × GateSide(F, n, n)), (∑_αβ (‖ T(αβ)‖_*)) ≤ fullGateApproximationConstant(F) · √(n · |(A × B)|) ∧ ∀ s₁, s₂ ∈ F, (∑_αβ (𝔼_(xy ← shortGateLabelDistribution(c, ε, s₁, s₂)) [|fullGateAmbientWeight(c, ε, p, r, β₀, αβ, (xy)₁, (xy)₂) - T(αβ, (xy)₁, (xy)₂)|])) ≤ fullGateApproximationConstant(F) · (|(A × B)|)² · (|F|ⁿ)^(−((1 / 10))).
-/
theorem fullGate_ambient_approximation [Nonempty A] {n t : ℕ}
    (hn : 2 ≤ n) (hdim : n * n = n + t) (c ε : F) (hε : ε ≠ 0)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (r : GateRectangles F A B n t) (β₀ : B) :
    ∃ T : A × B → Matrix (GateSide F n n) (GateSide F n n) ℝ,
      (∑ αβ, tableNuclearNorm (T αβ)) ≤ fullGateApproximationConstant F *
        Real.sqrt ((n : ℝ) * Fintype.card (A × B)) ∧
      ∀ s₁ s₂ : F,
        (∑ αβ, (shortGateLabelDistribution hn c ε s₁ s₂).expect (fun xy =>
          |fullGateAmbientWeight hn hdim c ε hε p r β₀ αβ xy.1 xy.2 - T αβ xy.1 xy.2|)) ≤
        fullGateApproximationConstant F * (Fintype.card (A × B) : ℝ) ^ 2 *
          (vectorCard F n : ℝ) ^ (-(1 / 10) : ℝ) := by
  obtain ⟨T, hT, herr⟩ := fullGate_approximation hn hdim c ε hε p r β₀
  refine ⟨T, hT, fun s₁ s₂ => ?_⟩
  have he (αβ : A × B) := shortGateLabelDistribution_kernel_expect hn hdim c ε hε p r β₀ s₁ s₂ αβ
    (fun x y v => |v - T αβ x y|)
  simp_rw [← he]
  exact herr s₁ s₂

end

end CircuitCompiler
