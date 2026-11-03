import Proofs.Compiler.GateApproximation.Shortening.ShorteningPivots



/-!
# Concrete source-energy bounds for shortening factors

The old operands remain an arbitrary finite side coordinate. Both density bounds are therefore valid with the old operands retained in the leakage view.
-/
set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace CircuitCompiler.Shortening

open Refresh MatrixRefresh

variable {F O : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype O]

/-- The left rank-one factor after fixing the private tail and pivot message. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; a ∈ O × U(F, (n + t)) → ℝ; B ∈ V(F, t); p ∈ Pivot(F, n); x ∈ O × U(F, n), define

leftFactor(a, B, p, x) := { a(((x)₁, leftEmbedding(((x)₂, B)))) if pivotMessage((x)₂) = p,; 0 otherwise } .
-/
def leftFactor {n t : ℕ} (a : O × U F (n + t) → ℝ)
    (B : V F t) (p : Pivot F n) (x : O × U F n) : ℝ :=
  if pivotMessage x.2 = p then a (x.1, leftEmbedding (x.2, B)) else 0

/-- The right rank-one factor pulled back using only the fixed private message. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; c, ε ∈ F; b ∈ O × U(F, (n + t)) → ℝ; B ∈ V(F, t); p ∈ Pivot(F, n); yD ∈ (O × U(F, n)) × V(F, t), assume ε ≠ 0. define

rightFactor(c, ε, b, B, p, yD) := zeroExtend(((V ↦ b((((yD)₁)₁, V)))), rightEmbedding(c, ε, pivotRepresentative(p), B, (((yD)₁)₂, (yD)₂))).
-/
def rightFactor {n t : ℕ} (c ε : F) (hε : ε ≠ 0)
    (b : O × U F (n + t) → ℝ) (B : V F t) (p : Pivot F n)
    (yD : (O × U F n) × V F t) : ℝ :=
  zeroExtend (fun V => b (yD.1.1, V))
    (rightEmbedding c ε hε (pivotRepresentative p) B (yD.1.2, yD.2))

/-- All pivots and tails together cost only the field-dependent density ratio in the left factor's averaged squared energy. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; P ∈ 𝒟(O); a ∈ O × U(F, (n + t)) → ℝ, assume 1 ≤ n; U(F, n) ≠ ∅; U(F, (n + t)) ≠ ∅. Then

𝔼_(B ← 𝒰_(V(F, t))) [∑_(p ∈ Pivot(F, n)) ((‖ leftFactor(a, B, p)‖_(2,(P ⊗ 𝒰_(U(F, n)))))²)] ≤ (|F| / (|F| - 1)) · (‖ a‖_(2,(P ⊗ 𝒰_(U(F, (n + t))))))².
-/
theorem leftFactor_energy {n t : ℕ} (hn : 1 ≤ n)
    [Nonempty (U F n)] [Nonempty (U F (n + t))]
    (P : FiniteDistribution O) (a : O × U F (n + t) → ℝ) :
    (FiniteDistribution.uniform : FiniteDistribution (V F t)).expect (fun B =>
      ∑ p : Pivot F n, rms (P.prod (FiniteDistribution.uniform : FiniteDistribution (U F n)))
        (leftFactor a B p) ^ 2) ≤
      ((fieldCard F : ℝ) / ((fieldCard F : ℝ) - 1)) *
        rms (P.prod (FiniteDistribution.uniform : FiniteDistribution (U F (n + t)))) a ^ 2 := by
  let QA : FiniteDistribution (U F n) := FiniteDistribution.uniform
  let QB : FiniteDistribution (V F t) := FiniteDistribution.uniform
  have hpoint (B : V F t) :
      (∑ p : Pivot F n, rms (P.prod QA) (leftFactor a B p) ^ 2) =
        (P.prod QA).expect (fun x => a (x.1, leftEmbedding (x.2, B)) ^ 2) := by
    simp only [rms_sq]
    rw [← expect_sum]
    apply congrArg (P.prod QA).expect
    funext x
    exact pivot_mask_energy x.2 _
  simp only [rms_sq]
  change QB.expect _ ≤ _
  calc
    _ = QB.expect (fun B => (P.prod QA).expect
        (fun x => a (x.1, leftEmbedding (x.2, B)) ^ 2)) := by
      apply congrArg QB.expect
      funext B
      simpa only [rms_sq] using hpoint B
    _ = P.expect (fun o => QB.expect (fun B => QA.expect
        (fun A => a (o, leftEmbedding (A, B)) ^ 2))) := by
      simp only [expect_prod]
      exact expect_comm QB P _
    _ = P.expect (fun o => (FiniteDistribution.uniform : FiniteDistribution (U F n × V F t)).expect
        (fun AB => a (o, leftEmbedding AB) ^ 2)) := by
      apply congrArg P.expect
      funext o
      rw [uniform_prod, expect_prod]
      exact expect_comm QB QA _
    _ ≤ P.expect (fun o => ((fieldCard F : ℝ) / ((fieldCard F : ℝ) - 1)) *
        (FiniteDistribution.uniform : FiniteDistribution (U F (n + t))).expect (fun U => a (o, U) ^ 2)) := by
      apply P.expect_mono
      intro o
      refine (left_pullback_energy (fun U => a (o, U))).trans ?_
      exact mul_le_mul_of_nonneg_right (left_density_le hn)
        (FiniteDistribution.expect_nonneg _ _ (fun _ => sq_nonneg _))
    _ = _ := by rw [expect_smul, expect_prod]

/-- At every fixed private message, the right factor has the same field-only squared-energy cost. The old right operands are averaged without removal. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; P ∈ 𝒟(O); c, ε ∈ F; b ∈ O × U(F, (n + t)) → ℝ; B ∈ V(F, t); p ∈ Pivot(F, n), assume 1 ≤ n; U(F, n) ≠ ∅; U(F, (n + t)) ≠ ∅; ε ≠ 0. Then

(‖ rightFactor(c, ε, b, B, p)‖_(2,((P ⊗ 𝒰_(U(F, n))) ⊗ 𝒰_(V(F, t)))))² ≤ (|F| / (|F| - 1)) · (‖ b‖_(2,(P ⊗ 𝒰_(U(F, (n + t))))))².
-/
theorem rightFactor_energy {n t : ℕ} (hn : 1 ≤ n)
    [Nonempty (U F n)] [Nonempty (U F (n + t))]
    (P : FiniteDistribution O) (c ε : F) (hε : ε ≠ 0)
    (b : O × U F (n + t) → ℝ) (B : V F t) (p : Pivot F n) :
    rms ((P.prod (FiniteDistribution.uniform : FiniteDistribution (U F n))).prod
      (FiniteDistribution.uniform : FiniteDistribution (V F t))) (rightFactor c ε hε b B p) ^ 2 ≤
      ((fieldCard F : ℝ) / ((fieldCard F : ℝ) - 1)) *
        rms (P.prod (FiniteDistribution.uniform : FiniteDistribution (U F (n + t)))) b ^ 2 := by
  rw [rms_sq, rms_sq, expect_prod, expect_prod, expect_prod, ← expect_smul]
  apply P.expect_mono
  intro o
  have h := right_pullback_energy c ε hε (pivotRepresentative p) B (fun U => b (o, U))
  rw [uniform_prod, expect_prod] at h
  change (FiniteDistribution.uniform : FiniteDistribution (U F n)).expect (fun R =>
    (FiniteDistribution.uniform : FiniteDistribution (V F t)).expect (fun D =>
      zeroExtend (fun V => b (o, V))
        (rightEmbedding c ε hε (pivotRepresentative p) B (R, D)) ^ 2)) ≤ _
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_right (right_density_le hn)
    (FiniteDistribution.expect_nonneg _ _ (fun _ => sq_nonneg _))

end CircuitCompiler.Shortening
