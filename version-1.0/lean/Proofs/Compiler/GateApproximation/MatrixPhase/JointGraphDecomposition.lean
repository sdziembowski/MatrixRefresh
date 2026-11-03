import Proofs.Compiler.GateApproximation.MatrixPhase.JointGraphCycle



/-!
# Character cancellation on the actual graph

All four share pairings are preserved by the same matrix and its inverse. Every graph character is therefore one. Untwisting retained blocks disappears on the actual graph, after which the operator triangle inequality applies.
-/
set_option autoImplicit false

open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical

namespace CircuitCompiler

open Refresh MatrixRefresh

noncomputable section

variable {F X : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype X] [DecidableEq X]

/-
Mathematical definition (normal notation): For m ∈ ℕ; ψ ∈ AddChar(F, ℂ); a, b ∈ X → U(F, m); c ∈ F, define

graphPhase(ψ, a, b, c) := (x, y ↦ ψ((c · graphConstraint(a, b, x, y)))).
-/
def graphPhase {m : ℕ} (ψ : AddChar F ℂ) (a b : X → U F m) (c : F) :
    Matrix (X × U F m) (X × U F m) ℂ :=
  fun x y => ψ (c * graphConstraint a b x y)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; a, b ∈ X → U(F, m); M ∈ GLₘ(F); x, y ∈ X, we have

graphConstraint(a, b, (x, rowRefresh(a(x), M)), (y, columnRefresh(b(y), M))) = 0.
-/
@[simp] theorem graphConstraint_on_graph {m : ℕ} (a b : X → U F m)
    (M : Refresh.«GL» F m) (x y : X) :
    graphConstraint a b (x, rowRefresh (a x) M) (y, columnRefresh (b y) M) = 0 := by
  unfold graphConstraint
  rw [rowRefresh_val, columnRefresh_val, shared_pairing, sub_self]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; ψ ∈ AddChar(F, ℂ); a, b ∈ X → U(F, m); c ∈ F; M ∈ GLₘ(F); x, y ∈ X, we have

graphPhase(ψ, a, b, c, (x, rowRefresh(a(x), M)), (y, columnRefresh(b(y), M))) = 1.
-/
@[simp] theorem graphPhase_on_graph {m : ℕ} (ψ : AddChar F ℂ) (a b : X → U F m)
    (c : F) (M : Refresh.«GL» F m) (x y : X) :
    graphPhase ψ a b c (x, rowRefresh (a x) M) (y, columnRefresh (b y) M) = 1 := by
  simp [graphPhase]

/-- Every inverse character disappears pointwise on the actual graph. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; ψ ∈ AddChar(F, ℂ); a, b ∈ X → U(F, m); c ∈ F; Q ∈ ℂ^((X × U(F, m)) × (X × U(F, m))); M ∈ GLₘ(F), we have

graphRestriction(a, b, (inversePhase(graphPhase(ψ, a, b, c)) ⊙ Q), M) = graphRestriction(a, b, Q, M).
-/
theorem graphRestriction_inversePhase {m : ℕ} (ψ : AddChar F ℂ) (a b : X → U F m)
    (c : F) (Q : Matrix (X × U F m) (X × U F m) ℂ) (M : Refresh.«GL» F m) :
    graphRestriction a b (inversePhase (graphPhase ψ a b c) ⊙ Q) M = graphRestriction a b Q M := by
  ext x y
  simp [graphRestriction, inversePhase, Matrix.hadamard_apply]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; a, b ∈ X → U(F, m); A, B ∈ ℂ^((X × U(F, m)) × (X × U(F, m))); M ∈ GLₘ(F), we have

graphRestriction(a, b, (A + B), M) = graphRestriction(a, b, A, M) + graphRestriction(a, b, B, M).
-/
@[simp] theorem graphRestriction_add {m : ℕ} (a b : X → U F m)
    (A B : Matrix (X × U F m) (X × U F m) ℂ) (M : Refresh.«GL» F m) :
    graphRestriction a b (A + B) M = graphRestriction a b A M + graphRestriction a b B M :=
  rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For C a set; m ∈ ℕ; a, b ∈ X → U(F, m); Q ∈ C → ℂ^((X × U(F, m)) × (X × U(F, m))); M ∈ GLₘ(F), assume C is finite. Then

graphRestriction(a, b, (∑_c (Q(c))), M) = ∑_c (graphRestriction(a, b, Q(c), M)).
-/
theorem graphRestriction_sum {C : Type*} [Fintype C] {m : ℕ} (a b : X → U F m)
    (Q : C → Matrix (X × U F m) (X × U F m) ℂ) (M : Refresh.«GL» F m) :
    graphRestriction a b (∑ c, Q c) M = ∑ c, graphRestriction a b (Q c) M := by
  ext x y
  simp only [graphRestriction, Matrix.sum_apply]

/-- The grouped twisted decomposition becomes an ordinary block sum after restricting to the actual matrix graph. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; ψ ∈ AddChar(F, ℂ); a, b ∈ X → U(F, m); A, E ∈ ℂ^((X × U(F, m)) × (X × U(F, m))); Q ∈ F → ℂ^((X × U(F, m)) × (X × U(F, m))); M ∈ GLₘ(F), assume A = (∑_c (inversePhase(graphPhase(ψ, a, b, c)) ⊙ Q(c))) + E. Then

graphRestriction(a, b, A, M) = (∑_c (graphRestriction(a, b, Q(c), M))) + graphRestriction(a, b, E, M).
-/
theorem graphRestriction_decomposition {m : ℕ} (ψ : AddChar F ℂ) (a b : X → U F m)
    (A E : Matrix (X × U F m) (X × U F m) ℂ)
    (Q : F → Matrix (X × U F m) (X × U F m) ℂ)
    (hA : A = (∑ c, inversePhase (graphPhase ψ a b c) ⊙ Q c) + E)
    (M : Refresh.«GL» F m) :
    graphRestriction a b A M = (∑ c, graphRestriction a b (Q c) M) + graphRestriction a b E M := by
  rw [hA, graphRestriction_add, graphRestriction_sum]
  simp_rw [graphRestriction_inversePhase]

/-- Triangle inequality for the normalized actual graph operator, retaining one term per character block and the genuine graph residual. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; ψ ∈ AddChar(F, ℂ); a, b ∈ X → U(F, m); A, E ∈ ℂ^((X × U(F, m)) × (X × U(F, m))); Q ∈ F → ℂ^((X × U(F, m)) × (X × U(F, m))); M ∈ GLₘ(F), assume A = (∑_c (inversePhase(graphPhase(ψ, a, b, c)) ⊙ Q(c))) + E. Then

‖ graphRestriction(a, b, A, M)‖ / |X| ≤ (∑_c (‖ graphRestriction(a, b, Q(c), M)‖ / |X|)) + ‖ graphRestriction(a, b, E, M)‖ / |X|.
-/
theorem graphRestriction_decomposition_norm {m : ℕ} (ψ : AddChar F ℂ) (a b : X → U F m)
    (A E : Matrix (X × U F m) (X × U F m) ℂ)
    (Q : F → Matrix (X × U F m) (X × U F m) ℂ)
    (hA : A = (∑ c, inversePhase (graphPhase ψ a b c) ⊙ Q c) + E)
    (M : Refresh.«GL» F m) :
    ‖graphRestriction a b A M‖ / Fintype.card X ≤
      (∑ c, ‖graphRestriction a b (Q c) M‖ / Fintype.card X) +
        ‖graphRestriction a b E M‖ / Fintype.card X := by
  rw [graphRestriction_decomposition ψ a b A E Q hA M]
  have h : ‖(∑ c, graphRestriction a b (Q c) M) + graphRestriction a b E M‖ ≤
      (∑ c, ‖graphRestriction a b (Q c) M‖) + ‖graphRestriction a b E M‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (le_refl _))
  have hd := div_le_div_of_nonneg_right h (Nat.cast_nonneg (Fintype.card X) : (0 : ℝ) ≤ _)
  simpa only [add_div, Finset.sum_div] using hd

/-- Averaging preserves the block decomposition bound. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; ψ ∈ AddChar(F, ℂ); a, b ∈ X → U(F, m); A, E ∈ ℂ^((X × U(F, m)) × (X × U(F, m))); Q ∈ F → ℂ^((X × U(F, m)) × (X × U(F, m))), assume A = (∑_c (inversePhase(graphPhase(ψ, a, b, c)) ⊙ Q(c))) + E. Then

𝔼_(M ∈ GLₘ(F)) [‖ graphRestriction(a, b, A, M)‖ / |X|] ≤ (∑_c (𝔼_(M ∈ GLₘ(F)) [‖ graphRestriction(a, b, Q(c), M)‖ / |X|])) + 𝔼_(M ∈ GLₘ(F)) [‖ graphRestriction(a, b, E, M)‖ / |X|].
-/
theorem graphRestriction_decomposition_mean {m : ℕ} (ψ : AddChar F ℂ) (a b : X → U F m)
    (A E : Matrix (X × U F m) (X × U F m) ℂ)
    (Q : F → Matrix (X × U F m) (X × U F m) ℂ)
    (hA : A = (∑ c, inversePhase (graphPhase ψ a b c) ⊙ Q c) + E) :
    uavg (fun M : Refresh.«GL» F m => ‖graphRestriction a b A M‖ / Fintype.card X) ≤
      (∑ c, uavg (fun M : Refresh.«GL» F m => ‖graphRestriction a b (Q c) M‖ / Fintype.card X)) +
        uavg (fun M : Refresh.«GL» F m => ‖graphRestriction a b E M‖ / Fintype.card X) := by
  have h := uavg_mono (graphRestriction_decomposition_norm ψ a b A E Q hA)
  rw [uavg_add] at h
  convert h using 1
  simp only [uavg, ← Finset.mul_sum]
  rw [Finset.sum_comm]

end

end CircuitCompiler
