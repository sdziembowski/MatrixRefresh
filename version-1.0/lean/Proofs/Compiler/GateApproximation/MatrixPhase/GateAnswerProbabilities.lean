import Proofs.Compiler.GateApproximation.MatrixPhase.Disintegration
import Proofs.Compiler.GateApproximation.MatrixPhase.GateAlgebra
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.EncodingMeasure
import Proofs.Compiler.Foundations.LinearAlgebra.RectangularRefresh



/-!
# The actual full-matrix leakage probability table

Both parties' rectangles may depend on the same matrix and on both retained old operand shares. Conditioning on the fresh long encoding exactly recovers the joint execution distribution. The answer table takes encodings as arguments, so the same function is used for every plaintext labeling.
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler

open Refresh TableAnalysis

variable {F Z : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype Z]

/-- A complete rectangle partition is a normalized answer distribution for every fixed shared matrix and pair of old operand encodings. -/
/- Mathematical definition (normal notation): For fixed operand encodings and shared matrix M, the leakage rectangle partition defines a probability distribution on answers: each answer has the weight of its rectangle at those local operands and M. Completeness of the partition gives total mass one. -/
noncomputable def matrixAnswer {n : ℕ}
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) Z)
    (a b : State F n) (M : Refresh.«GL» F (n * n)) : FiniteDistribution Z where
  weight z := p.toRoundPartition.weight z M ((a.L, b.L), (a.R, b.R))
  nonneg z := p.toRoundPartition.nonneg z M _
  total := p.toRoundPartition.complete M _

/-- Conditional leakage after fixing the new long encoding. All common-matrix dependence is retained by conditioning the original matrix distribution. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z); a, b ∈ State(F, n); u ∈ State(F, (n · n)), define

matrixAnswerDistribution(p, a, b, u) := bind(conditional(𝒰_(GL_(n · n)(F)), refreshedTensor(a, b), u), matrixAnswer(p, a, b)).
-/
noncomputable def matrixAnswerDistribution {n : ℕ}
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) Z)
    (a b : State F n) (u : State F (n * n)) : FiniteDistribution Z :=
  (conditional (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n * n)))
    (refreshedTensor a b) u).bind (matrixAnswer p a b)

/-- The real full-matrix gate phase, including the new encoding and answer. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z); a, b ∈ State(F, n), define

matrixExecution(p, a, b) := (((pair ↦ (refreshedTensor(a, b, (pair)₁), (pair)₂)))_*joint(𝒰_(GL_(n · n)(F)))(matrixAnswer(p, a, b))).
-/
noncomputable def matrixExecution {n : ℕ}
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) Z)
    (a b : State F n) : FiniteDistribution (State F (n * n) × Z) :=
  ((FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n * n))).joint (matrixAnswer p a b)).map
    (fun pair => (refreshedTensor a b pair.1, pair.2))

/-- Exact canonical disintegration for the real phase. This proves that its new encoding can be sampled first from the product-value fiber, followed by the conditional answer; it does not assume independence after leakage. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z); a, b ∈ State(F, n), assume 2 ≤ n · n. Then

matrixExecution(p, a, b) = joint(μ_(secret(a) · secret(b)))(matrixAnswerDistribution(p, a, b)).
-/
theorem matrixExecution_eq_canonical {n : ℕ} (hn : 2 ≤ n * n)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) Z)
    (a b : State F n) :
    matrixExecution p a b =
      (mu F (n * n) hn (secret a * secret b)).joint (matrixAnswerDistribution p a b) := by
  have h := answer_joint_conditional
    (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n * n)))
    (refreshedTensor a b) (matrixAnswer p a b)
  rw [refreshedTensor_uniform hn] at h
  exact h.symm

/-- The answer table's zero extension on inconsistent triples. This is globally a subprobability table and remains the same function across all labelings. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z); a, b ∈ State(F, n); u ∈ State(F, (n · n)); z ∈ Z, define

matrixAnswerProb(p, a, b, u, z) := { matrixAnswerDistribution(p, a, b, u)(z) if secret(u) = secret(a) · secret(b),; 0 otherwise }.
-/
noncomputable def matrixAnswerProb {n : ℕ}
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) Z)
    (a b : State F n) (u : State F (n * n)) (z : Z) : ℝ :=
  if secret u = secret a * secret b then (matrixAnswerDistribution p a b u).weight z else 0

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z); a, b ∈ State(F, n); u ∈ State(F, (n · n)); z ∈ Z, we have

0 ≤ matrixAnswerProb(p, a, b, u, z).
-/
theorem matrixAnswerProb_nonneg {n : ℕ}
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) Z)
    (a b : State F n) (u : State F (n * n)) (z : Z) :
    0 ≤ matrixAnswerProb p a b u z := by
  unfold matrixAnswerProb
  split_ifs
  · exact (matrixAnswerDistribution p a b u).nonneg z
  · rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z); a, b ∈ State(F, n); u ∈ State(F, (n · n)), we have

∑_z (matrixAnswerProb(p, a, b, u, z)) = { 1 if secret(u) = secret(a) · secret(b),; 0 otherwise }.
-/
theorem matrixAnswerProb_sum {n : ℕ}
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) Z)
    (a b : State F n) (u : State F (n * n)) :
    ∑ z, matrixAnswerProb p a b u z =
      if secret u = secret a * secret b then 1 else 0 := by
  classical
  unfold matrixAnswerProb
  split_ifs with h
  · exact (matrixAnswerDistribution p a b u).total
  · simp

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z); a, b ∈ State(F, n); u ∈ State(F, (n · n)), we have

∑_z (matrixAnswerProb(p, a, b, u, z)) ≤ 1.
-/
theorem matrixAnswerProb_sum_le {n : ℕ}
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) Z)
    (a b : State F n) (u : State F (n * n)) :
    ∑ z, matrixAnswerProb p a b u z ≤ 1 := by
  rw [matrixAnswerProb_sum]
  split_ifs <;> norm_num

/-- Zero extension does not change the real execution: every unsupported output encoding already has zero mass under its exact fiber distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): For fixed operands, the joint probability of refreshed tensor output u and answer z factors as Pr[U = u,Z = z] = μ_(s₁s₂)(u) · prob_z(u), where the encoding dimension is n² ≥ 2. The answer factor is the conditional matrix-answer probability for those same fixed operands. -/
theorem matrixExecution_weight {n : ℕ} (hn : 2 ≤ n * n)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) Z)
    (a b : State F n) (u : State F (n * n)) (z : Z) :
    (matrixExecution p a b).weight (u, z) =
      (mu F (n * n) hn (secret a * secret b)).weight u *
        matrixAnswerProb p a b u z := by
  rw [matrixExecution_eq_canonical hn]
  change _ * (matrixAnswerDistribution p a b u).weight z = _
  unfold matrixAnswerProb
  split_ifs with h
  · rfl
  · rw [mu_weight]
    simp [h]

end CircuitCompiler
