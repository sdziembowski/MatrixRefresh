import Proofs.Compiler.GateApproximation.MatrixPhase.NuclearTransportLift
import Proofs.Compiler.GateApproximation.Shortening.ShorteningLinear



/-!
# Shortening transport: the full nuclear-norm theorem

This is the manuscript's nuclear transport lemma for arbitrary real tables, with the explicit constant `q/(q-1)` and the exact pivot count `n(q-1)`. It follows from the concrete field-vector operator, its proved rank-one bound, and a genuine singular-value decomposition of each input table.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.Shortening

open Refresh MatrixRefresh TableAnalysis

variable {F O Z : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [DecidableEq O] [Nonempty O] [Fintype Z]

/-- Nuclear-norm transport for every real table, including arbitrary retained old operands as the side coordinate `O`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; r ∈ V(F, t) → Pivot(F, n) → RectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × V(F, t))); G ∈ ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))), assume 1 ≤ n; U(F, n) ≠ ∅; U(F, (n + t)) ≠ ∅; ε ≠ 0. Then

(∑ᵦ (‖ transportMatrix(c, ε, r, G, β)‖_*)) ≤ ((|F| / (|F| - 1)) · √(n · (|F| - 1) · |Z|)) · ‖ G‖_*.
-/
theorem transportMatrix_nuclear {n t : ℕ} (hn : 1 ≤ n)
    [Nonempty (U F n)] [Nonempty (U F (n + t))]
    (c ε : F) (hε : ε ≠ 0)
    (r : V F t → Pivot F n → RectanglePartition Z (O × U F n) ((O × U F n) × V F t))
    (G : Matrix (O × U F (n + t)) (O × U F (n + t)) ℝ) :
    (∑ β, tableNuclearNorm (transportMatrix c ε r G β)) ≤
      (((fieldCard F : ℝ) / ((fieldCard F : ℝ) - 1)) *
        Real.sqrt ((n * (fieldCard F - 1) : ℕ) * Fintype.card Z)) * tableNuclearNorm G := by
  apply linear_transport_nuclear_bound (transportLinear c ε r)
  intro a b
  change (∑ β, tableNuclearNorm (transportMatrix c ε r (fun x y => a x * b y) β)) ≤ _
  simp_rw [transportMatrix_rankOne c ε hε]
  exact rankOneTransport_nuclear hn c ε hε r a b

/-- Summing over all preceding matrix-phase answers preserves the same shortening loss; there is no extra factor for the first-phase leaf count. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A a set; n, t ∈ ℕ; c, ε ∈ F; r ∈ A → V(F, t) → Pivot(F, n) → RectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × V(F, t))); G ∈ A → ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))), assume A is finite; 1 ≤ n; U(F, n) ≠ ∅; U(F, (n + t)) ≠ ∅; ε ≠ 0. Then

(∑_α (∑ᵦ (‖ transportMatrix(c, ε, r(α), G(α), β)‖_*))) ≤ ((|F| / (|F| - 1)) · √(n · (|F| - 1) · |Z|)) · (∑_α (‖ G(α)‖_*)).
-/
theorem transportMatrix_family_nuclear {A : Type*} [Fintype A]
    {n t : ℕ} (hn : 1 ≤ n)
    [Nonempty (U F n)] [Nonempty (U F (n + t))]
    (c ε : F) (hε : ε ≠ 0)
    (r : A → V F t → Pivot F n → RectanglePartition Z (O × U F n) ((O × U F n) × V F t))
    (G : A → Matrix (O × U F (n + t)) (O × U F (n + t)) ℝ) :
    (∑ α, ∑ β, tableNuclearNorm (transportMatrix c ε (r α) (G α) β)) ≤
      (((fieldCard F : ℝ) / ((fieldCard F : ℝ) - 1)) *
        Real.sqrt ((n * (fieldCard F - 1) : ℕ) * Fintype.card Z)) * (∑ α, tableNuclearNorm (G α)) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun α _ => transportMatrix_nuclear hn c ε hε (r α) (G α))

end CircuitCompiler.Shortening
