import Proofs.Compiler.GateApproximation.MatrixPhase.FullGate
import Proofs.Compiler.GateApproximation.MatrixPhase.GateDual
import Proofs.Compiler.Foundations.LinearAlgebra.FiniteCarrier
import Proofs.Compiler.Construction.Parameters



/-!
# Coherent dimension changes for the tensor gate
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler

open Refresh MatrixRefresh TableAnalysis Shortening

noncomputable section

variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype A]

/-
Mathematical definition (normal notation): For m, k ∈ ℕ, assume m = k. define

stateDimensionEquiv := Equiv.cast(congrArg(State(F))) .
-/
def stateDimensionEquiv {m k : ℕ} (h : m = k) : State F m ≃ State F k :=
  Equiv.cast (congrArg (State F) h)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m, k ∈ ℕ; x ∈ State(F, m), assume m = k. Then

L(stateDimensionEquiv(x)) = shareDimensionEquiv(x.L).
-/
@[simp] theorem stateDimensionEquiv_left {m k : ℕ} (h : m = k) (x : State F m) :
    (stateDimensionEquiv h x).L = shareDimensionEquiv h x.L := by
  subst k; rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m, k ∈ ℕ; x ∈ State(F, m), assume m = k. Then

R(stateDimensionEquiv(x)) = shareDimensionEquiv(x.R).
-/
@[simp] theorem stateDimensionEquiv_right {m k : ℕ} (h : m = k) (x : State F m) :
    (stateDimensionEquiv h x).R = shareDimensionEquiv h x.R := by
  subst k; rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m, k ∈ ℕ; z ∈ F; u ∈ Fiber(F, m, z), assume m = k. Then

fiberDimensionEquiv(z, u) = stateDimensionEquiv(u).
-/
@[simp] theorem fiberDimensionEquiv_val {m k : ℕ} (h : m = k) (z : F) (u : Fiber F m z) :
    (fiberDimensionEquiv h z u).val = stateDimensionEquiv h u.val := by
  subst k; rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m, k ∈ ℕ; z ∈ F; u ∈ Fiber(F, k, z), assume m = k. Then

(fiberDimensionEquiv(z))⁻¹(u) = (stateDimensionEquiv)⁻¹(u).
-/
@[simp] theorem fiberDimensionEquiv_symm_val {m k : ℕ} (h : m = k) (z : F) (u : Fiber F k z) :
    ((fiberDimensionEquiv h z).symm u).val = (stateDimensionEquiv h).symm u.val := by
  subst k; rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m, k ∈ ℕ; x ∈ State(F, k), assume m = k. Then

L((stateDimensionEquiv)⁻¹(x)) = (shareDimensionEquiv)⁻¹(x.L).
-/
@[simp] theorem stateDimensionEquiv_symm_left {m k : ℕ} (h : m = k) (x : State F k) :
    ((stateDimensionEquiv h).symm x).L = (shareDimensionEquiv h).symm x.L := by
  subst k; rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m, k ∈ ℕ; x ∈ State(F, k), assume m = k. Then

R((stateDimensionEquiv)⁻¹(x)) = (shareDimensionEquiv)⁻¹(x.R).
-/
@[simp] theorem stateDimensionEquiv_symm_right {m k : ℕ} (h : m = k) (x : State F k) :
    ((stateDimensionEquiv h).symm x).R = (shareDimensionEquiv h).symm x.R := by
  subst k; rfl

/-
Mathematical definition (normal notation): For n ∈ ℕ; m, k ∈ ℕ, assume m = k. define

sideDimensionEquiv(n) := prodCongr(Equiv.refl((U(F, n) × U(F, n))))(shareDimensionEquiv).
-/
def sideDimensionEquiv (n : ℕ) {m k : ℕ} (h : m = k) : GateSide F n m ≃ GateSide F n k :=
  (Equiv.refl (U F n × U F n)).prodCongr (shareDimensionEquiv h)

/-
Mathematical definition (normal notation): For n, m, k ∈ ℕ; G ∈ ℝ^(GateSide(F, n, m) × GateSide(F, n, m)), assume m = k. define

reindexGateTable(G) := reindexTable(G, sideDimensionEquiv(n), sideDimensionEquiv(n)).
-/
def reindexGateTable {n m k : ℕ} (h : m = k)
    (G : Matrix (GateSide F n m) (GateSide F n m) ℝ) :
    Matrix (GateSide F n k) (GateSide F n k) ℝ :=
  reindexTable G (sideDimensionEquiv n h) (sideDimensionEquiv n h)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m, k ∈ ℕ; G ∈ ℝ^(GateSide(F, n, m) × GateSide(F, n, m)), assume m = k. Then

‖ reindexGateTable(G)‖_* = ‖ G‖_*.
-/
theorem reindexGateTable_nuclear {n m k : ℕ} (h : m = k)
    (G : Matrix (GateSide F n m) (GateSide F n m) ℝ) :
    tableNuclearNorm (reindexGateTable h G) = tableNuclearNorm G :=
  reindexTable_tableNuclearNorm G _ _

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For O a set; m, k ∈ ℕ; z ∈ F; P ∈ 𝒟(O); f ∈ O × Fiber(F, k, z) → ℝ, assume O is finite; m = k; Fiber(F, m, z) ≠ ∅; Fiber(F, k, z) ≠ ∅. Then

𝔼_(u ← (P ⊗ 𝒰_(Fiber(F, k, z)))) [f(u)] = 𝔼_(op ← (P ⊗ 𝒰_(Fiber(F, m, z)))) [f(((op)₁, fiberDimensionEquiv(z, (op)₂)))].
-/
theorem fiberDimension_expect {O : Type*} [Fintype O] {m k : ℕ} (h : m = k) (z : F)
    [Nonempty (Fiber F m z)] [Nonempty (Fiber F k z)]
    (P : FiniteDistribution O) (f : O × Fiber F k z → ℝ) :
    (P.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F k z))).expect f =
      (P.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F m z))).expect
        (fun op => f (op.1, fiberDimensionEquiv h z op.2)) := by
  subst k
  rfl

/-- Matrix answer on the auxiliary carrier, with the represented value kept as a type parameter only for its inner-product equation. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); z ∈ F; o ∈ (U(F, n) × U(F, n)) × (U(F, n) × U(F, n)); u ∈ Auxiliary(F, (n + t), z), assume n · n = n + t. define

auxiliaryPortAnswerDistribution(p, z, o, u) := { matrixAnswerDistribution(p, (((o)₁)₁, ((o)₂)₁), (((o)₁)₂, ((o)₂)₂), (stateDimensionEquiv)⁻¹(((u)₁, ((u)₂, h)))) if (u)₂ ≠ 0,; matrixAnswer(p, (((o)₁)₁, ((o)₂)₁), (((o)₁)₂, ((o)₂)₂), 1) otherwise }.
-/
def auxiliaryPortAnswerDistribution {n t : ℕ} (hdim : n * n = n + t)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (z : F) (o : (U F n × U F n) × (U F n × U F n))
    (u : Auxiliary F (n + t) z) : FiniteDistribution A :=
  if h : u.2.val ≠ 0 then
    matrixAnswerDistribution p ⟨o.1.1, o.2.1⟩ ⟨o.1.2, o.2.2⟩
      ((stateDimensionEquiv hdim).symm ⟨u.1, ⟨u.2.val, h⟩⟩)
  else matrixAnswer p ⟨o.1.1, o.2.1⟩ ⟨o.1.2, o.2.2⟩ 1

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); z ∈ F; o ∈ (U(F, n) × U(F, n)) × (U(F, n) × U(F, n)); u ∈ Fiber(F, (n + t), z), assume n · n = n + t. Then

auxiliaryPortAnswerDistribution(p, z, o, actualEmbedding(z, u)) = matrixAnswerDistribution(p, (((o)₁)₁, ((o)₂)₁), (((o)₁)₂, ((o)₂)₂), (stateDimensionEquiv)⁻¹(u)).
-/
@[simp] theorem auxiliaryPortAnswerDistribution_actual {n t : ℕ} (hdim : n * n = n + t)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (z : F) (o : (U F n × U F n) × (U F n × U F n)) (u : Fiber F (n + t) z) :
    auxiliaryPortAnswerDistribution hdim p z o (actualEmbedding z u) =
      matrixAnswerDistribution p ⟨o.1.1, o.2.1⟩ ⟨o.1.2, o.2.2⟩ ((stateDimensionEquiv hdim).symm u.val) := by
  simp! [auxiliaryPortAnswerDistribution, actualEmbedding, Function.Embedding.coeFn_mk,
    u.val.R.property]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); a, b ∈ State(F, n); u ∈ Auxiliary(F, (n + t), (secret(a) · secret(b))), assume n · n = n + t. Then

auxiliaryPortAnswerDistribution(p, (secret(a) · secret(b)), ((a.L, b.L), (a.R, b.R)), u) = auxiliaryMatrixAnswerDistribution(p, a, b, u).
-/
theorem auxiliaryPortAnswerDistribution_eq {n t : ℕ} (hdim : n * n = n + t)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (a b : State F n) (u : Auxiliary F (n + t) (secret a * secret b)) :
    auxiliaryPortAnswerDistribution hdim p (secret a * secret b) ((a.L, b.L), (a.R, b.R)) u =
      auxiliaryMatrixAnswerDistribution hdim p a b u := by
  unfold auxiliaryPortAnswerDistribution auxiliaryMatrixAnswerDistribution
  split_ifs with h
  · rw [typedMatrixAnswerDistribution_eq_matrixAnswerDistribution, fiberDimensionEquiv_symm_val]
  · rfl

/-- Exact preservation of the actual matrix-approximation energy when its long coordinate is reindexed to the head-plus-tail shortening dimension. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); z ∈ F; P ∈ 𝒟(((U(F, n) × U(F, n)) × (U(F, n) × U(F, n)))); G ∈ A → ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))), assume n · n = n + t; Fiber(F, (n · n), z) ≠ ∅; Fiber(F, (n + t), z) ≠ ∅. Then

𝔼_(op ← (P ⊗ 𝒰_(Fiber(F, (n + t), z)))) [∑_α ((auxiliaryPortAnswerDistribution(p, z, (op)₁, actualEmbedding(z, (op)₂))(α) - reindexGateTable(G(α), (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R)))²)] = 𝔼_(op ← (P ⊗ 𝒰_(Fiber(F, (n · n), z)))) [∑_α ((matrixAnswerDistribution(p, ((((op)₁)₁)₁, (((op)₁)₂)₁), ((((op)₁)₁)₂, (((op)₁)₂)₂), (op)₂)(α) - G(α, (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R)))²)].
-/
theorem auxiliaryPortAnswerDistribution_reindex_error {n t : ℕ} (hdim : n * n = n + t)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (z : F) [Nonempty (Fiber F (n * n) z)] [Nonempty (Fiber F (n + t) z)]
    (P : FiniteDistribution ((U F n × U F n) × (U F n × U F n)))
    (G : A → Matrix (GateSide F n (n * n)) (GateSide F n (n * n)) ℝ) :
    (P.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n + t) z))).expect
      (fun op => ∑ α, ((auxiliaryPortAnswerDistribution hdim p z op.1 (actualEmbedding z op.2)).weight α -
        reindexGateTable hdim (G α) (op.1.1, op.2.val.L) (op.1.2, op.2.val.R)) ^ 2) =
    (P.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n * n) z))).expect
      (fun op => ∑ α, ((matrixAnswerDistribution p ⟨op.1.1.1, op.1.2.1⟩ ⟨op.1.1.2, op.1.2.2⟩ op.2.val).weight α -
        G α (op.1.1, op.2.val.L) (op.1.2, op.2.val.R)) ^ 2) := by
  rw [fiberDimension_expect hdim z]
  apply congrArg (FiniteDistribution.expect _)
  funext op
  simp only [auxiliaryPortAnswerDistribution_actual, fiberDimensionEquiv_val, Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro α _
  congr 2
  simp [reindexGateTable, reindexTable, sideDimensionEquiv, stateDimensionEquiv_left,
    stateDimensionEquiv_right]

end

end CircuitCompiler
