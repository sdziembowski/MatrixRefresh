import Proofs.Compiler.GateApproximation.Shortening.ShorteningFullTransport
import Proofs.Compiler.Foundations.LinearAlgebra.NuclearIdentification



/-!
# The actual linear shortening operator

For arbitrary tables, the operator evaluates the exact inverse change of variables, selects the deterministic rectangle leaf, and averages the two independent tails. It is linear. Its rank-one specialization is precisely the operator already bounded in `ShorteningFullTransport`.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.Shortening

open Refresh MatrixRefresh TableAnalysis

variable {F O Z : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [DecidableEq O] [Nonempty O] [Fintype Z]

/-- One integrand of the actual shortening transport, before tail averaging. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; c, ε ∈ F; r ∈ V(F, t) → Pivot(F, n) → RectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × V(F, t))); G ∈ ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))); β ∈ Z; x, y ∈ O × U(F, n); B, D ∈ V(F, t), define

transportValue(c, ε, r, G, β, x, y, B, D) := { zeroExtend(((V ↦ G(((x)₁, leftEmbedding(((x)₂, B))), ((y)₁, V)))), Fin.append(inverseHead(c, ε, (x)₂, B, (y)₂, D), D)) if left(r(B, pivotMessage((x)₂)))(β, x) ∧ right(r(B, pivotMessage((x)₂)))(β, (y, D)),; 0 otherwise }.
-/
def transportValue {n t : ℕ} (c ε : F)
    (r : V F t → Pivot F n → RectanglePartition Z (O × U F n) ((O × U F n) × V F t))
    (G : Matrix (O × U F (n + t)) (O × U F (n + t)) ℝ)
    (β : Z) (x y : O × U F n) (B D : V F t) : ℝ :=
  if (r B (pivotMessage x.2)).left β x && (r B (pivotMessage x.2)).right β (y, D) then
    zeroExtend (fun V => G (x.1, leftEmbedding (x.2, B)) (y.1, V))
      (Fin.append (inverseHead c ε x.2 B y.2.val D) D)
  else 0

/-- Averaging the actual integrand over the two independent uniform tails. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; c, ε ∈ F; r ∈ V(F, t) → Pivot(F, n) → RectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × V(F, t))); G ∈ ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))); β ∈ Z, define

transportMatrix(c, ε, r, G, β) := (x, y ↦ 𝔼_(B ← 𝒰_(V(F, t))) [𝔼_(D ← 𝒰_(V(F, t))) [transportValue(c, ε, r, G, β, x, y, B, D)]]).
-/
noncomputable def transportMatrix {n t : ℕ} (c ε : F)
    (r : V F t → Pivot F n → RectanglePartition Z (O × U F n) ((O × U F n) × V F t))
    (G : Matrix (O × U F (n + t)) (O × U F (n + t)) ℝ)
    (β : Z) : Matrix (O × U F n) (O × U F n) ℝ :=
  fun x y => (FiniteDistribution.uniform : FiniteDistribution (V F t)).expect (fun B =>
    (FiniteDistribution.uniform : FiniteDistribution (V F t)).expect (fun D => transportValue c ε r G β x y B D))

/-- Pointwise linearity under table addition. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; r ∈ V(F, t) → Pivot(F, n) → RectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × V(F, t))); G, H ∈ ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))); β ∈ Z; x, y ∈ O × U(F, n); B, D ∈ V(F, t), we have

transportValue(c, ε, r, (G + H), β, x, y, B, D) = transportValue(c, ε, r, G, β, x, y, B, D) + transportValue(c, ε, r, H, β, x, y, B, D).
-/
theorem transportValue_add {n t : ℕ} (c ε : F)
    (r : V F t → Pivot F n → RectanglePartition Z (O × U F n) ((O × U F n) × V F t))
    (G H : Matrix (O × U F (n + t)) (O × U F (n + t)) ℝ)
    (β : Z) (x y : O × U F n) (B D : V F t) :
    transportValue c ε r (G + H) β x y B D =
      transportValue c ε r G β x y B D + transportValue c ε r H β x y B D := by
  unfold transportValue zeroExtend
  split_ifs <;> simp

/-- Pointwise linearity under scalar multiplication. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; r ∈ V(F, t) → Pivot(F, n) → RectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × V(F, t))); G ∈ ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))); a ∈ ℝ; β ∈ Z; x, y ∈ O × U(F, n); B, D ∈ V(F, t), we have

transportValue(c, ε, r, (a · G), β, x, y, B, D) = a · transportValue(c, ε, r, G, β, x, y, B, D) .
-/
theorem transportValue_smul {n t : ℕ} (c ε : F)
    (r : V F t → Pivot F n → RectanglePartition Z (O × U F n) ((O × U F n) × V F t))
    (G : Matrix (O × U F (n + t)) (O × U F (n + t)) ℝ) (a : ℝ)
    (β : Z) (x y : O × U F n) (B D : V F t) :
    transportValue c ε r (a • G) β x y B D = a * transportValue c ε r G β x y B D := by
  unfold transportValue zeroExtend
  split_ifs <;> simp

/-- Linear-map packaging of the concrete field-vector shortening operator. -/
/- Mathematical definition (normal notation): Package the shortening transport as a real-linear map from a long table to a family of short tables indexed by shortening answers. The masks and coordinate substitutions are fixed while the input table varies. -/
noncomputable def transportLinear {n t : ℕ} (c ε : F)
    (r : V F t → Pivot F n → RectanglePartition Z (O × U F n) ((O × U F n) × V F t)) :
    Matrix (O × U F (n + t)) (O × U F (n + t)) ℝ →ₗ[ℝ]
      (Z → Matrix (O × U F n) (O × U F n) ℝ) where
  toFun G := transportMatrix c ε r G
  map_add' G H := by
    ext β x y
    simp only [transportMatrix, transportValue_add, expect_add, Pi.add_apply, Matrix.add_apply]
  map_smul' a G := by
    ext β x y
    simp only [transportMatrix, transportValue_smul, expect_smul, Pi.smul_apply, Matrix.smul_apply, RingHom.id_apply, smul_eq_mul]

/-- Specializing the actual inverse-map operator to a rank-one input gives exactly the pivot-grouped expression bounded by the nuclear transport proof. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; r ∈ V(F, t) → Pivot(F, n) → RectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × V(F, t))); a, b ∈ O × U(F, (n + t)) → ℝ; β ∈ Z, assume ε ≠ 0; U(F, n) ≠ ∅. Then

transportMatrix(c, ε, r, ((x, y ↦ a(x) · b(y))), β) = rankOneTransport(c, ε, r, a, b, β).
-/
theorem transportMatrix_rankOne {n t : ℕ} (c ε : F) (hε : ε ≠ 0)
    [Nonempty (U F n)]
    (r : V F t → Pivot F n → RectanglePartition Z (O × U F n) ((O × U F n) × V F t))
    (a b : O × U F (n + t) → ℝ) (β : Z) :
    transportMatrix c ε r (fun x y => a x * b y) β = rankOneTransport c ε hε r a b β := by
  ext x y
  apply congrArg (FiniteDistribution.expect (FiniteDistribution.uniform : FiniteDistribution (V F t)))
  funext B
  rw [Finset.sum_eq_single (pivotMessage x.2)]
  · simp only [leftFactor, ite_true]
    by_cases hL : (r B (pivotMessage x.2)).left β x = true
    · simp only [hL, ite_true]
      rw [← expect_smul]
      apply congrArg (FiniteDistribution.expect (FiniteDistribution.uniform : FiniteDistribution (V F t)))
      funext D
      simp only [transportValue, hL, Bool.true_and, rightFactor, rightEmbedding]
      rw [inverseHead_message c ε x.2 B y.2.val D]
      simp only [Function.Embedding.coeFn_mk]
      unfold zeroExtend
      split_ifs <;> simp
    · simp [transportValue, hL]
  · intro p _ hp
    simp [leftFactor, Ne.symm hp]
  · simp

end CircuitCompiler.Shortening
