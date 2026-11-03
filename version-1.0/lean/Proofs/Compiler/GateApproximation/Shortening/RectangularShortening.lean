import Proofs.Compiler.GateApproximation.MatrixPhase.GateAlgebra
import Proofs.Compiler.GateApproximation.MatrixPhase.UniformSampling
import Proofs.Compiler.Construction.Parameters
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Freshness



/-!
# Rectangular shortening: matrices, attempts, and correctness

A full-row-rank matrix is represented by a matrix with a right inverse. An attempt samples a nonzero row `A` and a full-row-rank `H` with `A*H=u`, then computes `H*v`. Rejection occurs exactly when this last vector is zero. There is no reconstruction or fallback branch in this protocol.
-/
set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace CircuitCompiler.Rectangular

open Refresh

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Surjectivity follows directly from the right inverse. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; H ∈ F^({0,…,n−1} × {0,…,m−1}), assume FullRowRank(H). Then

Matrix.mulVec(H) is surjective.
-/
theorem fullRowRank_surjective {n m : ℕ} {H : Matrix (Fin n) (Fin m) F}
    (hH : FullRowRank H) : Function.Surjective (Matrix.mulVec H) := by
  obtain ⟨J,hJ⟩ := hH
  intro r
  refine ⟨J.mulVec r, ?_⟩
  rw [Matrix.mulVec_mulVec, hJ, Matrix.one_mulVec]

/-- This is the usual full-row-rank condition, equivalently surjectivity. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; H ∈ F^({0,…,n−1} × {0,…,m−1}), we have

FullRowRank(H) ⇔ Matrix.mulVec(H) is surjective.
-/
theorem fullRowRank_iff_surjective {n m : ℕ} (H : Matrix (Fin n) (Fin m) F) :
    FullRowRank H ↔ Function.Surjective (Matrix.mulVec H) :=
  Matrix.mulVec_surjective_iff_exists_right_inverse.symm

/-- Correctness holds for each individual attempt, without any randomness. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): Every attempt satisfies the exact deterministic identity A · (H · v) = (A · H) · v = u · v, including attempts later rejected because H · v = 0. -/
theorem attempt_correct {n m : ℕ} {u : U F m} (v : U F m)
    (p : Attempt (n := n) u) : dot p.val.1.val (rightOutput v p) = dot u.val v.val := by
  change dotProduct p.val.1.val (Matrix.mulVec p.val.2.val v.val) = dotProduct u.val v.val
  rw [Matrix.dotProduct_mulVec, p.property]

instance successFintype {n m : ℕ} (u v : U F m) : Fintype (Success (n := n) u v) :=
  Fintype.ofFinite _

/-- The accepted output, retaining its exact plaintext equation. -/
/- Mathematical definition (normal notation): The output of a successful attempt (A,H) is the short encoding (A,H · v). Both shares are nonzero and A · (H · v) = u · v, so it lies in the encoding fiber of the same secret as the fixed long input pair. -/
def output {n m : ℕ} {u v : U F m} (p : Success (n := n) u v) :
    Fiber F n (dot u.val v.val) :=
  ⟨⟨p.val.val.1, ⟨rightOutput v p.val, p.property⟩⟩, attempt_correct v p.val⟩

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; u ∈ U(F, m); p ∈ Attempt(n = n, u), we have

attemptAction(1, p) = p.
-/
@[simp] theorem attemptAction_one {n m : ℕ} {u : U F m} (p : Attempt (n := n) u) :
    attemptAction 1 p = p := by
  apply Subtype.ext
  apply Prod.ext
  · simp [attemptAction]
  · apply Subtype.ext
    simp [attemptAction]

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; u ∈ U(F, m); B, C ∈ GLₙ(F); p ∈ Attempt(n = n, u), we have

attemptAction(C, attemptAction(B, p)) = attemptAction((B · C), p).
-/
theorem attemptAction_mul {n m : ℕ} {u : U F m} (B C : Refresh.«GL» F n)
    (p : Attempt (n := n) u) : attemptAction C (attemptAction B p) = attemptAction (B*C) p := by
  apply Subtype.ext
  apply Prod.ext
  · exact rowRefresh_mul p.val.1 B C
  · apply Subtype.ext
    simp [attemptAction, mul_inv_rev, Matrix.mul_assoc]

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; u ∈ U(F, m); v ∈ U(F, m); B ∈ GLₙ(F); p ∈ Attempt(n = n, u), we have

rightOutput(v, attemptAction(B, p)) = Matrix.mulVec((B)⁻¹, rightOutput(v, p)).
-/
@[simp] theorem rightOutput_action {n m : ℕ} {u : U F m} (v : U F m)
    (B : Refresh.«GL» F n) (p : Attempt (n := n) u) :
    rightOutput v (attemptAction B p) = Matrix.mulVec (B⁻¹).val (rightOutput v p) := by
  simp [rightOutput, attemptAction, Matrix.mulVec_mulVec]

/-- The same change of basis is a bijection on accepted attempts. -/
/-
Mathematical definition (normal notation): For n, m ∈ ℕ; u, v ∈ U(F, m); B ∈ GLₙ(F); p ∈ Success(n = n, u, v), define

successAction(B, p) := attemptAction(B, p).
-/
def successAction {n m : ℕ} {u v : U F m} (B : Refresh.«GL» F n)
    (p : Success (n := n) u v) : Success (n := n) u v :=
  ⟨attemptAction B p.val, by
    rw [rightOutput_action]
    intro h
    apply p.property
    have := congrArg (Matrix.mulVec B.val) h
    simpa [Matrix.mulVec_mulVec] using this⟩

/- Mathematical definition (normal notation): For an invertible short matrix B, the action (a,H) ↦ (a · B,B⁻¹ · H) permutes successful shortening attempts for a fixed long pair. Its inverse uses B⁻¹. -/
def successEquiv {n m : ℕ} {u v : U F m} (B : Refresh.«GL» F n) :
    Success (n := n) u v ≃ Success (n := n) u v where
  toFun := successAction B
  invFun := successAction B⁻¹
  left_inv p := by
    apply Subtype.ext
    change attemptAction B⁻¹ (attemptAction B p.val) = p.val
    rw [attemptAction_mul, mul_inv_cancel, attemptAction_one]
  right_inv p := by
    apply Subtype.ext
    change attemptAction B (attemptAction B⁻¹ p.val) = p.val
    rw [attemptAction_mul, inv_mul_cancel, attemptAction_one]

/-- Output transforms exactly as an ordinary square refresh. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; u, v ∈ U(F, m); B ∈ GLₙ(F); p ∈ Success(n = n, u, v), we have

output(successAction(B, p)) = refreshInFiber(output(p), B).
-/
theorem output_action {n m : ℕ} {u v : U F m} (B : Refresh.«GL» F n)
    (p : Success (n := n) u v) :
    output (successAction B p) = refreshInFiber (output p) B := by
  apply Subtype.ext
  apply State.ext
  · rfl
  · apply Subtype.ext
    exact rightOutput_action v B p.val

/-- Accepted attempts yielding two short states in the same fiber are in bijection, even when the fixed encoded value is zero. -/
/- Mathematical definition (normal notation): The action (a,H) ↦ (a · B,B⁻¹ · H) bijects successful attempts producing a given short encoding y with successful attempts producing its refresh (y_L · B,B⁻¹ · y_R). -/
def outputFiberEquiv {n m : ℕ} {u v : U F m} (B : Refresh.«GL» F n)
    (y : Fiber F n (dot u.val v.val)) :
    {p : Success (n := n) u v // output p = y} ≃
      {p : Success (n := n) u v // output p = refreshInFiber y B} where
  toFun p := ⟨successAction B p.val, by rw [output_action, p.property]⟩
  invFun p := ⟨successAction B⁻¹ p.val, by
    rw [output_action, p.property]
    apply Subtype.ext
    simp [refreshInFiber, refresh_mul]⟩
  left_inv p := Subtype.ext ((successEquiv B).left_inv p.val)
  right_inv p := Subtype.ext ((successEquiv B).right_inv p.val)

/-- Uniform accepted attempts have exactly the uniform short encoding distribution. No averaging over the fixed inputs `u,v` is used. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; u, v ∈ U(F, m), assume Success(n = n, u, v) ≠ ∅; Fiber(F, n, (u · v)) ≠ ∅. Then

(output_*𝒰_(Success(n = n, u, v))) = 𝒰_(Fiber(F, n, (u · v))).
-/
theorem accepted_output_uniform {n m : ℕ} (u v : U F m)
    [Nonempty (Success (n := n) u v)] [Nonempty (Fiber F n (dot u.val v.val))] :
    (FiniteDistribution.uniform : FiniteDistribution (Success (n := n) u v)).map output =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (dot u.val v.val))) := by
  classical
  let y₀ : Fiber F n (dot u.val v.val) := Classical.choice inferInstance
  apply FiniteDistribution.uniform_map_of_fiber_card output
    (Fintype.card {p : Success (n := n) u v // output p = y₀})
  intro y
  obtain ⟨B,hB⟩ := refresh_transitive y₀.val y.val (y₀.property.trans y.property.symm)
  have h : refreshInFiber y₀ B = y := Subtype.ext hB
  rw [← h]
  exact (Fintype.card_congr (outputFiberEquiv B y₀)).symm

/-- Exact freshness for every input, with all existence conditions discharged. -/

/- Mathematical statement (normal notation): For every fixed nonzero long input pair (u,v), with n ≥ 2, a uniform successful shortening attempt produces a uniform short encoding: ℒ(A,H · v) = μ_(u · v). The assertion holds for each fixed input pair, not merely on average over inputs. -/
theorem output_uniform {n t : ℕ} (hn : 2 ≤ n) (u v : U F (n+t)) :
    letI := success_nonempty hn u v
    letI := fiber_nonempty F n hn (dot u.val v.val)
    (FiniteDistribution.uniform : FiniteDistribution (Success (n := n) u v)).map output =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (dot u.val v.val))) := by
  letI := success_nonempty hn u v
  letI := fiber_nonempty F n hn (dot u.val v.val)
  exact accepted_output_uniform u v

/-- Rejection conditioning is precisely the uniform successful-attempt distribution. Together with `output_uniform`, this identifies the returned encoding. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): For a fixed long pair (u,v) with n ≥ 2, condition the actual shortening-attempt distribution on H · v ≠ 0. The result is exactly uniform over the successful attempts satisfying a · H = u. -/
theorem accepted_attemptDistribution {n t : ℕ} (hn : 2 ≤ n) (u v : U F (n+t)) :
    letI := success_nonempty hn u v
    Sampling.accepted (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0))
      (attempt_acceptance_pos hn u v) =
      (FiniteDistribution.uniform : FiniteDistribution (Success (n := n) u v)).map Subtype.val := by
  classical
  letI := success_nonempty hn u v
  letI : Nonempty (Attempt (n := n) u) := ⟨(Classical.choice (success_nonempty hn u v)).val⟩
  let e : Success (n := n) u v ≃
      {p : Attempt (n := n) u // decide (rightOutput v p ≠ 0) = true} :=
    Equiv.subtypeEquivRight (fun _ => by simp)
  letI : Nonempty {p : Attempt (n := n) u // decide (rightOutput v p ≠ 0) = true} :=
    ⟨e (Classical.choice (success_nonempty hn u v))⟩
  have hp := attempt_acceptance_pos hn u v
  simp only [attemptDistribution_uniform] at hp ⊢
  rw [Sampling.accepted_uniform, ← uniform_equiv e, FiniteDistribution.map_map]
  rfl

/-- A nonzero plaintext rules out retries pointwise. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; u, v ∈ U(F, m); p ∈ Attempt(n = n, u), assume (u · v) ≠ 0. Then

rightOutput(v, p) ≠ 0.
-/
theorem no_rejection_of_dot_ne_zero {n m : ℕ} {u v : U F m}
    (hs : dot u.val v.val ≠ 0) (p : Attempt (n := n) u) : rightOutput v p ≠ 0 := by
  intro h
  have hc := attempt_correct v p
  rw [h] at hc
  exact hs (by simpa [dot] using hc.symm)

end

end CircuitCompiler.Rectangular
