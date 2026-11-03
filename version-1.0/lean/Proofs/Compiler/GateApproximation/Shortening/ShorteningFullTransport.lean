import Proofs.Compiler.GateApproximation.Shortening.ShorteningFactorEnergies
import Proofs.Compiler.GateApproximation.Shortening.ShorteningNuclear



/-!
# The complete rank-one shortening transport estimate

All old operands are retained. Private tails and pivot messages are averaged explicitly. The leaf cost, pivot cost, and both finite-field density costs are combined into the manuscript's `C_q sqrt(n K_S)` nuclear bound.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.Shortening

open Refresh MatrixRefresh TableAnalysis

variable {F O Z : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [DecidableEq O] [Nonempty O] [Fintype Z]

/-- The exact finite average of rank-one shortening rectangle pieces. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; c, ε ∈ F; r ∈ V(F, t) → Pivot(F, n) → RectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × V(F, t))); a, b ∈ O × U(F, (n + t)) → ℝ; β ∈ Z, assume ε ≠ 0; U(F, n) ≠ ∅. define

rankOneTransport(c, ε, r, a, b, β) := (x, y ↦ 𝔼_(B ← 𝒰_(V(F, t))) [∑_(p ∈ Pivot(F, n)) (({ leftFactor(a, B, p, x) if left(r(B, p))(β, x),; 0 otherwise }) · 𝔼_(D ← 𝒰_(V(F, t))) [{ rightFactor(c, ε, b, B, p, (y, D)) if right(r(B, p))(β, (y, D)),; 0 otherwise }])]).
-/
noncomputable def rankOneTransport {n t : ℕ} (c ε : F) (hε : ε ≠ 0)
    [Nonempty (U F n)]
    (r : V F t → Pivot F n → RectanglePartition Z (O × U F n) ((O × U F n) × V F t))
    (a b : O × U F (n + t) → ℝ) (β : Z) : Matrix (O × U F n) (O × U F n) ℝ :=
  fun x y => (FiniteDistribution.uniform : FiniteDistribution (V F t)).expect (fun B =>
    ∑ p : Pivot F n,
      (if (r B p).left β x then leftFactor a B p x else 0) *
      (FiniteDistribution.uniform : FiniteDistribution (V F t)).expect (fun D =>
        if (r B p).right β (y, D) then rightFactor c ε hε b B p (y, D) else 0))

/-- Concrete nuclear bound for a complete rank-one transported table. No pullback norm or factorization certificate is assumed: the two field-space energy bounds and the rectangle partition prove the estimate. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; r ∈ V(F, t) → Pivot(F, n) → RectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × V(F, t))); a, b ∈ O × U(F, (n + t)) → ℝ, assume 1 ≤ n; U(F, n) ≠ ∅; U(F, (n + t)) ≠ ∅; ε ≠ 0. Then

(∑ᵦ (‖ rankOneTransport(c, ε, r, a, b, β)‖_*)) ≤ (|F| / (|F| - 1)) · √(n · (|F| - 1) · |Z|) · ‖ a‖_(2,𝒰_(O × U(F, (n + t)))) · ‖ b‖_(2,𝒰_(O × U(F, (n + t)))).
-/
theorem rankOneTransport_nuclear {n t : ℕ} (hn : 1 ≤ n)
    [Nonempty (U F n)] [Nonempty (U F (n + t))]
    (c ε : F) (hε : ε ≠ 0)
    (r : V F t → Pivot F n → RectanglePartition Z (O × U F n) ((O × U F n) × V F t))
    (a b : O × U F (n + t) → ℝ) :
    (∑ β, tableNuclearNorm (rankOneTransport c ε hε r a b β)) ≤
      ((fieldCard F : ℝ) / ((fieldCard F : ℝ) - 1)) *
        Real.sqrt ((n * (fieldCard F - 1) : ℕ) * Fintype.card Z) *
        rms (FiniteDistribution.uniform : FiniteDistribution (O × U F (n + t))) a *
        rms (FiniteDistribution.uniform : FiniteDistribution (O × U F (n + t))) b := by
  let ρ : ℝ := (fieldCard F : ℝ) / ((fieldCard F : ℝ) - 1)
  let L : FiniteDistribution (O × U F n) := FiniteDistribution.uniform
  let Q : FiniteDistribution (V F t) := FiniteDistribution.uniform
  let S : FiniteDistribution (O × U F (n + t)) := FiniteDistribution.uniform
  let u := fun B p => rms L (leftFactor a B p)
  let v := fun B p => Real.sqrt (Fintype.card Z) * rms (L.prod Q) (rightFactor c ε hε b B p)
  let T := fun B p β => (fun x y : O × U F n =>
    (if (r B p).left β x then leftFactor a B p x else 0) *
      Q.expect (fun D => if (r B p).right β (y, D) then rightFactor c ε hε b B p (y, D) else 0))
  have hq : (1 : ℝ) < fieldCard F := by
    exact_mod_cast (show 1 < fieldCard F by have := fieldCard_ge_two (F := F); omega)
  have hρ : 0 ≤ ρ := div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hleft : Q.expect (fun B => ∑ p, u B p ^ 2) ≤ ρ * rms S a ^ 2 := by
    have h := leftFactor_energy hn (FiniteDistribution.uniform : FiniteDistribution O) a
    rw [← uniform_prod, ← uniform_prod] at h
    exact h
  have hright (B : V F t) (p : Pivot F n) :
      v B p ≤ Real.sqrt (Fintype.card Z) * Real.sqrt ρ * rms S b := by
    have h := rightFactor_energy hn (FiniteDistribution.uniform : FiniteDistribution O) c ε hε b B p
    have h' : rms (L.prod Q) (rightFactor c ε hε b B p) ^ 2 ≤ ρ * rms S b ^ 2 := by
      simpa only [L, Q, S, ρ, uniform_prod] using h
    have hh : rms (L.prod Q) (rightFactor c ε hε b B p) ≤ Real.sqrt ρ * rms S b := by
      apply (sq_le_sq₀ (rms_nonneg _ _) (mul_nonneg (Real.sqrt_nonneg _) (rms_nonneg _ _))).1
      simpa only [mul_pow, Real.sq_sqrt hρ] using h'
    exact (mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg _)).trans_eq (by ring)
  have hlocal (B : V F t) (p : Pivot F n) :
      (∑ β, tableNuclearNorm (T B p β)) ≤ u B p * v B p := by
    have h := rectangle_nuclear_budget (r B p) Q (leftFactor a B p) (rightFactor c ε hε b B p)
    exact h.trans_eq (by dsimp [u, v, L]; ring)
  have h := averaged_nuclear_budget Q T u v ρ (rms S a)
    (Real.sqrt (Fintype.card Z) * Real.sqrt ρ * rms S b)
    hρ (rms_nonneg _ _)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (rms_nonneg _ _))
    (fun _ _ => rms_nonneg _ _)
    (fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (rms_nonneg _ _)) hleft hright hlocal
  change (∑ β, tableNuclearNorm (rankOneTransport c ε hε r a b β)) ≤ _ at h
  refine h.trans_eq ?_
  rw [pivot_card]
  change Real.sqrt (n * (fieldCard F - 1) : ℕ) * Real.sqrt ρ * rms S a *
    (Real.sqrt (Fintype.card Z) * Real.sqrt ρ * rms S b) = _
  have hroot : Real.sqrt (((n * (fieldCard F - 1) : ℕ) : ℝ) * (Fintype.card Z : ℝ)) =
      Real.sqrt (n * (fieldCard F - 1) : ℕ) * Real.sqrt (Fintype.card Z) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _)]
  rw [hroot]
  change _ = ρ * (Real.sqrt (n * (fieldCard F - 1) : ℕ) * Real.sqrt (Fintype.card Z)) * rms S a * rms S b
  calc
    _ = (Real.sqrt ρ * Real.sqrt ρ) *
        (Real.sqrt (n * (fieldCard F - 1) : ℕ) * Real.sqrt (Fintype.card Z)) * rms S a * rms S b := by ring
    _ = _ := by rw [Real.mul_self_sqrt hρ]

end CircuitCompiler.Shortening
