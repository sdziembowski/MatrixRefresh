import Proofs.Compiler.GateApproximation.MatrixPhase.Binary
import Proofs.Compiler.Construction.Parameters



/-!
# Conditional leakage for maps from old data to long shares

The maps from old data to long shares may have any long dimension. This gives the actual shared matrix experiment and its exact density pairing before any analytic estimate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1200000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {F X Z : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype X] [Nonempty X] [Fintype Z] {m : ℕ}

/-
Mathematical definition (normal notation): For ω = ((x,u),(y,v)), define

prob_z(ω) := { Pr[Z = z | a(x) · M = u, M⁻¹ · b(y) = v], u · v = a(x) · b(y),; 0, otherwise }

Thus impossible endpoint tuples are filled with zero.
-/
def answerProb (a b : X → U F m)
    (p : TableRectanglePartition X (Refresh.«GL» F m) Z)
    (z : Z) (x y : X × U F m) : ℝ :=
  if dot x.2.val y.2.val = dot (a x.1).val (b y.1).val then
    (answerDistribution a b p x.1 y.1 ⟨x.2,y.2⟩).weight z else 0

/-
Mathematical definition (normal notation): At ((x,u),(y,v)), the density is the density of a fresh encoding of a(x) · b(y), evaluated at (u,v), relative to independent uniform nonzero shares:

φ((x,u),(y,v)) := (μ_(a(x) · b(y))(u,v))/(ν(u,v)).
-/
def refreshDensity (a b : X → U F m) (x y : X × U F m) : ℝ :=
  encodingDensity (dot (a x.1).val (b y.1).val) x.2 y.2

/- Mathematical definition (normal notation): Define the scalar consistency mask to be 1 when u · v = a(x) · b(y), and 0 otherwise. It records exactly which old/new tuples preserve the encoded value. -/
def consistencyIndicator (a b : X → U F m) (x y : X × U F m) : ℝ :=
  if dot x.2.val y.2.val = dot (a x.1).val (b y.1).val then 1 else 0

omit [Fintype X] [Nonempty X] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); x, y ∈ X, assume 2 ≤ m. Then

(refreshedEncoding(a, b, x, y)_*𝒰_(GLₘ(F))) = μ_(a(x) · b(y)).
-/
theorem refreshedEncoding_uniform (hm : 2 ≤ m) (a b : X → U F m) (x y : X) :
    (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F m)).map (refreshedEncoding a b x y) =
      mu F m hm (dot (a x).val (b y).val) :=
  refresh_uniform hm _ ⟨a x,b y⟩ rfl

omit [Fintype X] [Nonempty X] in
/-- The output encoding can be sampled before the conditional answer, with no independence assumption on the two parties' common matrix. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); p ∈ TableRectanglePartition(X, GLₘ(F), Z); x, y ∈ X, assume 2 ≤ m. Then

(((pair ↦ (refreshedEncoding(a, b, x, y, (pair)₁), (pair)₂)))_*joint(𝒰_(GLₘ(F)))(fixedMatrixAnswerDistribution(p, x, y))) = joint(μ_(a(x) · b(y)))(answerDistribution(a, b, p, x, y)).
-/
theorem feature_execution_eq_canonical (hm : 2 ≤ m) (a b : X → U F m)
    (p : TableRectanglePartition X (Refresh.«GL» F m) Z) (x y : X) :
    ((FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F m)).joint (fixedMatrixAnswerDistribution p x y)).map
      (fun pair => (refreshedEncoding a b x y pair.1, pair.2)) =
    (mu F m hm (dot (a x).val (b y).val)).joint (answerDistribution a b p x y) := by
  have h := answer_joint_conditional
    (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F m))
    (refreshedEncoding a b x y) (fixedMatrixAnswerDistribution p x y)
  rw [refreshedEncoding_uniform hm] at h
  exact h.symm

omit [Fintype X] [Nonempty X] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); p ∈ TableRectanglePartition(X, GLₘ(F), Z); z ∈ Z; x, y ∈ X × U(F, m), we have

0 ≤ answerProb(a, b, p, z, x, y).
-/
theorem answerProb_nonneg (a b : X → U F m)
    (p : TableRectanglePartition X (Refresh.«GL» F m) Z) (z : Z) (x y : X × U F m) :
    0 ≤ answerProb a b p z x y := by
  unfold answerProb
  split_ifs
  · exact (answerDistribution a b p x.1 y.1 ⟨x.2,y.2⟩).nonneg z
  · rfl

omit [Fintype X] [Nonempty X] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); p ∈ TableRectanglePartition(X, GLₘ(F), Z); x, y ∈ X × U(F, m), we have

∑_z (answerProb(a, b, p, z, x, y)) = consistencyIndicator(a, b, x, y).
-/
theorem answerProb_sum (a b : X → U F m)
    (p : TableRectanglePartition X (Refresh.«GL» F m) Z) (x y : X × U F m) :
    ∑ z, answerProb a b p z x y = consistencyIndicator a b x y := by
  unfold answerProb consistencyIndicator
  split_ifs
  · exact (answerDistribution a b p x.1 y.1 ⟨x.2,y.2⟩).total
  · simp

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A,B a set; P ∈ 𝒟(A); Q ∈ A → 𝒟(B); f ∈ A × B → ℝ, assume A is finite; B is finite. Then

𝔼_(u ← P.joint(Q)) [f(u)] = 𝔼_(a ← P) [𝔼_(b ← Q(a)) [f((a, b))]].
-/
private theorem feature_expect_joint {A B : Type*} [Fintype A] [Fintype B]
    (P : FiniteDistribution A) (Q : A → FiniteDistribution B) (f : A × B → ℝ) :
    (P.joint Q).expect f = P.expect (fun a => (Q a).expect (fun b => f (a,b))) := by
  simp only [FiniteDistribution.expect, FiniteDistribution.joint, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

omit [Fintype X] [Nonempty X] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); p ∈ TableRectanglePartition(X, GLₘ(F), Z); x, y ∈ X; z ∈ Z; W ∈ State(F, m) → ℝ, assume 2 ≤ m. Then

𝔼_(u ← μ_(a(x) · b(y))) [answerProb(a, b, p, z, (x, u.L), (y, u.R)) · W(u)] = 𝔼_M [fixedMatrixAnswerDistribution(p, x, y, M)(z) · W(refreshedEncoding(a, b, x, y, M))].
-/
theorem answerDistribution_pairing (hm : 2 ≤ m) (a b : X → U F m)
    (p : TableRectanglePartition X (Refresh.«GL» F m) Z) (x y : X) (z : Z)
    (W : State F m → ℝ) :
    (mu F m hm (dot (a x).val (b y).val)).expect
      (fun u => answerProb a b p z (x,u.L) (y,u.R) * W u) =
    uavg (fun M => (fixedMatrixAnswerDistribution p x y M).weight z * W (refreshedEncoding a b x y M)) := by
  have he := congrArg (fun P => P.expect (fun uz : State F m × Z =>
    if uz.2 = z then W uz.1 else 0)) (feature_execution_eq_canonical hm a b p x y)
  rw [expect_map, feature_expect_joint, feature_expect_joint] at he
  simp only [FiniteDistribution.expect, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at he
  have hmask (u : State F m) :
      (mu F m hm (dot (a x).val (b y).val)).weight u *
          (answerProb a b p z (x,u.L) (y,u.R) * W u) =
      (mu F m hm (dot (a x).val (b y).val)).weight u *
          ((answerDistribution a b p x y u).weight z * W u) := by
    unfold answerProb
    split_ifs with h
    · rfl
    · rw [mu_weight]
      simp only [secret, stateLeftShare, stateRightShare] at h ⊢
      simp [h]
  simp only [FiniteDistribution.expect, hmask]
  exact he.symm.trans (by simp [FiniteDistribution.uniform, uavg, Finset.mul_sum])

/-- Uniform independent nonzero shares, weighted by their fiber density, are precisely the uniform encoding of the specified field element. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F; f ∈ State(F, m) → ℝ, assume 2 ≤ m. Then

𝔼_(v ← μₛ) [f(v)] = 𝔼ₗ [𝔼ᵣ [encodingDensity(s, l, r) · f((l, r))]].
-/
theorem mu_expect_encodingDensity (hm : 2 ≤ m) (s : F) (f : State F m → ℝ) :
    (mu F m hm s).expect f =
      uavg (fun l => uavg (fun r => encodingDensity s l r * f ⟨l,r⟩)) := by
  have he : (mu F m hm s).expect f =
      (independentStateDistribution F m hm).expect (fun u => encodingDensity s u.L u.R * f u) := by
    simp only [FiniteDistribution.expect, mu_weight_density, encodingDensity, secret, stateLeftShare, stateRightShare, mul_assoc]
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [he, independentStateDistribution, expect_map, expect_prod]
  simp only [uniformShare, ← uavg_eq_expect_uniform]
  rfl

/-- Exact dual identity on the grouped carrier for arbitrary input features. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); p ∈ TableRectanglePartition(X, GLₘ(F), Z); z ∈ Z; W ∈ ℝ^((X × U(F, m)) × (X × U(F, m))), assume 2 ≤ m. Then

𝔼ₓ [𝔼_y [refreshDensity(a, b, x, y) · answerProb(a, b, p, z, x, y) · W(x, y)]] = 𝔼_M [𝔼ₓ [𝔼_y [p.leftIndicator(z, M, x) · p.rightIndicator(z, M, y) · W((x, rowRefresh(a(x), M)), (y, columnRefresh(b(y), M)))]]].
-/
theorem answerDistribution_density_pairing (hm : 2 ≤ m) (a b : X → U F m)
    (p : TableRectanglePartition X (Refresh.«GL» F m) Z) (z : Z)
    (W : Matrix (X × U F m) (X × U F m) ℝ) :
    uavg (fun x => uavg (fun y => refreshDensity a b x y *
      answerProb a b p z x y * W x y)) =
    uavg (fun M => uavg (fun x => uavg (fun y =>
      p.leftIndicator z M x * p.rightIndicator z M y *
        W (x,rowRefresh (a x) M) (y,columnRefresh (b y) M)))) := by
  simp_rw [uavg_prod]
  conv_lhs => arg 1; ext x; rw [uavg_comm]
  have hfixed (x y : X) :
      uavg (fun l => uavg (fun r => refreshDensity a b (x,l) (y,r) *
        answerProb a b p z (x,l) (y,r) * W (x,l) (y,r))) =
      uavg (fun M => p.leftIndicator z M x * p.rightIndicator z M y *
        W (x,rowRefresh (a x) M) (y,columnRefresh (b y) M)) := by
    have h := answerDistribution_pairing hm a b p x y z (fun u => W (x,u.L) (y,u.R))
    rw [mu_expect_encodingDensity hm] at h
    simpa only [refreshDensity, refreshedEncoding, refresh, fixedMatrixAnswerDistribution,
      stateLeftShare, stateRightShare, TableRectanglePartition.toRoundPartition, mul_assoc] using h
  simp_rw [hfixed]
  conv_lhs => arg 1; ext x; rw [uavg_comm]
  rw [uavg_comm]

omit [Fintype X] [Nonempty X] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); x, y ∈ X × U(F, m), assume 2 ≤ m. Then

0 ≤ refreshDensity(a, b, x, y).
-/
theorem refreshDensity_nonneg (hm : 2 ≤ m) (a b : X → U F m) (x y : X × U F m) :
    0 ≤ refreshDensity a b x y := by
  unfold refreshDensity encodingDensity
  split_ifs
  · exact (densityWeight_pos hm _).le
  · rfl

omit [Fintype X] [Nonempty X] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); x, y ∈ X × U(F, m), assume |F| = 2; 2 ≤ m. Then

|refreshDensity(a, b, x, y) - 2 · consistencyIndicator(a, b, x, y)| ≤ 2 / (|F|ᵐ - 2).
-/
theorem feature_density_close (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (x y : X × U F m) :
    |refreshDensity a b x y - 2 * consistencyIndicator a b x y| ≤
      2 / ((vectorCard F m : ℝ) - 2) := by
  unfold refreshDensity encodingDensity consistencyIndicator
  split_ifs
  · simpa only [mul_one] using binary_densityWeight_close hq hm (dot (a x.1).val (b y.1).val)
  · simp only [mul_zero, sub_self, abs_zero]
    have := vectorCard_real_ge_four (F := F) hm
    exact div_nonneg (by norm_num) (by linarith)

end

end CircuitCompiler.RefreshAnalysis
