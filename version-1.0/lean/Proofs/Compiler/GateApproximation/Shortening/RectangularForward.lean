import Proofs.Compiler.GateApproximation.Shortening.RectangularJoint
import Proofs.Compiler.Construction.Parameters



/-!
# Forward and reverse successful records
-/
set_option autoImplicit false

set_option maxHeartbeats 1500000

open scoped BigOperators

namespace CircuitCompiler.Rectangular

open Refresh MatrixRefresh

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Changing the fixed long row bijects its completion sets. -/
/- Mathematical definition (normal notation): If u · M = w with M invertible, right multiplication H ↦ H · M bijects completions of a · H = u with completions of a · H = w. -/
def completionChangeRow {n m : ℕ} (u w : U F m) (a : U F n)
    (M : Refresh.«GL» F m) (hM : rowRefresh u M = w) : Completion u a ≃ Completion w a where
  toFun H := ⟨⟨H.val.val*M.val,fullRowRank_right H.val M⟩, by
    rw [← Matrix.vecMul_vecMul,H.property]
    exact congrArg Subtype.val hM⟩
  invFun H := ⟨⟨H.val.val*(M⁻¹).val,fullRowRank_right H.val M⁻¹⟩, by
    rw [← Matrix.vecMul_vecMul,H.property]
    have h := congrArg (fun x => (rowRefresh x M⁻¹).val) hM
    simpa [rowRefresh,Matrix.vecMul_vecMul] using h.symm⟩
  left_inv H := by apply Subtype.ext; apply Subtype.ext; simp [Matrix.mul_assoc]
  right_inv H := by apply Subtype.ext; apply Subtype.ext; simp [Matrix.mul_assoc]

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; u, w ∈ U(F, m); a, b ∈ U(F, n), we have

|Completion(u, a)| = |Completion(w, b)|.
-/
theorem completion_card_independent_inputs {n m : ℕ} (u w : U F m) (a b : U F n) :
    Fintype.card (Completion u a) = Fintype.card (Completion w b) := by
  obtain ⟨M,hM⟩ := exists_rowRefresh_eq u w
  exact (Fintype.card_congr (completionChangeRow u w a M hM)).trans
    (completion_card_eq w a b)

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; u, w ∈ U(F, m), we have

|Attempt(n = n, u)| = |Attempt(n = n, w)|.
-/
theorem attempt_card_independent_input {n m : ℕ} (u w : U F m) :
    Fintype.card (Attempt (n := n) u) = Fintype.card (Attempt (n := n) w) := by
  rw [Fintype.card_congr (attemptSigmaEquiv (n := n) u),
    Fintype.card_congr (attemptSigmaEquiv (n := n) w),Fintype.card_sigma,Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun a _ => completion_card_independent_inputs u w a a)

instance forwardRecordFintype (n m : ℕ) (s : F) : Fintype (ForwardRecord F n m s) :=
  Fintype.ofFinite _

/-- Consequently uniform successful forward records have the reverse distribution. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; s ∈ F, assume ForwardRecord(F, n, m, s) ≠ ∅; Backward(F, n, m, s) ≠ ∅. Then

(forwardBackwardEquiv(s)_*𝒰_(ForwardRecord(F, n, m, s))) = 𝒰_(Backward(F, n, m, s)).
-/
theorem forward_records_reverse_uniform {n m : ℕ} (s : F)
    [Nonempty (ForwardRecord F n m s)] [Nonempty (Backward F n m s)] :
    (FiniteDistribution.uniform : FiniteDistribution (ForwardRecord F n m s)).map (forwardBackwardEquiv s) =
      (FiniteDistribution.uniform : FiniteDistribution (Backward F n m s)) :=
  uniform_equiv _

/-- Before acceptance, sampling a uniform long pair and then the actual attempt sampler is uniform on all admissible forward choices. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): For n ≥ 2, sample a long encoding uniformly from the fiber of secret s, then sample a shortening attempt according to its actual attempt distribution. The resulting pair is uniform on the set of all long encodings of s together with one allowed attempt for that encoding. -/
theorem joint_forward_attempts_uniform {n t : ℕ} (hn : 2 ≤ n) (s : F) :
    letI := fiber_nonempty F (n+t) (by omega) s
    letI : ∀ x : Fiber F (n+t) s, Nonempty (Attempt (n := n) x.val.L) :=
      fun x => ⟨(Classical.choice (success_nonempty hn x.val.L x.val.R)).val⟩
    letI : Nonempty ((x : Fiber F (n+t) s) × Attempt (n := n) x.val.L) :=
      ⟨⟨Classical.choice inferInstance,Classical.choice inferInstance⟩⟩
    (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) s)).bind (fun x =>
      (attemptDistribution hn x.val.L).map (fun p =>
        (⟨x,p⟩ : (x : Fiber F (n+t) s) × Attempt (n := n) x.val.L))) =
      (FiniteDistribution.uniform : FiniteDistribution ((x : Fiber F (n+t) s) × Attempt (n := n) x.val.L)) := by
  classical
  letI := fiber_nonempty F (n+t) (by omega) s
  letI : ∀ x : Fiber F (n+t) s, Nonempty (Attempt (n := n) x.val.L) :=
    fun x => ⟨(Classical.choice (success_nonempty hn x.val.L x.val.R)).val⟩
  letI : Nonempty ((x : Fiber F (n+t) s) × Attempt (n := n) x.val.L) :=
    ⟨⟨Classical.choice inferInstance,Classical.choice inferInstance⟩⟩
  simp_rw [attemptDistribution_uniform]
  exact uniform_sigma_bind (Classical.choice inferInstance)
    (fun x => attempt_card_independent_input x.val.L _)

/-- The accepted subset of the forward sampler is exactly the record space. -/
/- Mathematical definition (normal notation): Regrouping a long encoding and one shortening attempt, restricted to nonzero right output, gives a bijection with successful forward records. The correspondence preserves the long shares, sampled short row, and full-row-rank matrix. -/
def successfulForwardEquiv {n m : ℕ} (s : F) :
    {p : (x : Fiber F m s) × Attempt (n := n) x.val.L //
      rightOutput p.1.val.R p.2 ≠ 0} ≃ ForwardRecord F n m s where
  toFun p := ⟨(p.val.1.val,p.val.2.val.1,p.val.2.val.2),
    p.val.1.property,p.val.2.property,p.property⟩
  invFun p := ⟨⟨⟨p.val.1,p.property.1⟩,⟨(p.val.2.1,p.val.2.2),p.property.2.1⟩⟩,
    p.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Conditioning the uniform forward choice space and rearranging its accepted records gives exactly the reverse experiment. -/

/- Mathematical statement (normal notation): Assuming the finite record spaces are nonempty, the bijection from successful forward records to reverse records carries the uniform distribution to the uniform distribution. Thus uniformly choosing a valid long encoding and a successful attempt is equivalent to uniformly choosing the corresponding reverse record; the encoding secret s is the same on both sides. -/
theorem successful_forward_reverse_uniform {n m : ℕ} (s : F)
    [Nonempty {p : (x : Fiber F m s) × Attempt (n := n) x.val.L //
      rightOutput p.1.val.R p.2 ≠ 0}] [Nonempty (Backward F n m s)] :
    (FiniteDistribution.uniform : FiniteDistribution {p : (x : Fiber F m s) × Attempt (n := n) x.val.L //
      rightOutput p.1.val.R p.2 ≠ 0}).map
        ((successfulForwardEquiv s).trans (forwardBackwardEquiv s)) =
      (FiniteDistribution.uniform : FiniteDistribution (Backward F n m s)) :=
  uniform_equiv _

end

end CircuitCompiler.Rectangular
