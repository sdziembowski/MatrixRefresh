import Proofs.Compiler.GateApproximation.Shortening.ShorteningEmbeddings



/-!
# The finite pivot messages in shortening

A communicated pivot consists of its coordinate and nonzero field value. Grouping by this message is exactly the `n(q-1)`-way split in the nuclear proof.
-/
set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace CircuitCompiler.Shortening

open Refresh MatrixRefresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The finite private pivot-message alphabet. -/
/-
Mathematical definition (normal notation): For F a set; n ∈ ℕ, assume Zero(F). define

Pivot(n) := {0,…,n-1} × {x ∈ F | x ≠ 0}.
-/
abbrev Pivot (F : Type*) [Zero F] (n : ℕ) := Fin n × {x : F // x ≠ 0}

/-- The actual index and value sent by the left party. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; A ∈ U(F, n), define

pivotMessage(A) := (pivot(A), A(pivot(A))).
-/
def pivotMessage {n : ℕ} (A : U F n) : Pivot F n :=
  (pivot A, ⟨A.val (pivot A), pivot_nonzero A⟩)

/-- Exactly `n(q-1)` possible pivot messages. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, we have

|Pivot(F, n)| = n · (|F| - 1).
-/
theorem pivot_card (n : ℕ) : Fintype.card (Pivot F n) = n * (fieldCard F - 1) := by
  rw [Fintype.card_prod, Fintype.card_fin]
  congr 1
  simpa only [fieldCard, Fintype.card_subtype_eq] using
    Fintype.card_subtype_compl (α := F) (p := fun x => x = 0)

/-- A canonical nonzero head carrying any prescribed pivot message. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; p ∈ Pivot(F, n), define

pivotRepresentative(p) := Pi.single((p)₁, (p)₂).
-/
def pivotRepresentative {n : ℕ} (p : Pivot F n) : U F n :=
  ⟨Pi.single p.1 p.2.val, by
    intro h
    have hi := congrFun h p.1
    exact p.2.property (by simpa using hi)⟩

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ Pivot(F, n), we have

pivot(pivotRepresentative(p)) = (p)₁.
-/
@[simp] theorem pivot_representative {n : ℕ} (p : Pivot F n) :
    pivot (pivotRepresentative p) = p.1 := by
  by_contra h
  have hp := pivot_nonzero (pivotRepresentative p)
  change (Pi.single p.1 p.2.val : V F n) (pivot (pivotRepresentative p)) ≠ 0 at hp
  simp [Pi.single_apply, h, Ne.symm h] at hp

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ Pivot(F, n), we have

pivotMessage(pivotRepresentative(p)) = p.
-/
@[simp] theorem pivotMessage_representative {n : ℕ} (p : Pivot F n) :
    pivotMessage (pivotRepresentative p) = p := by
  apply Prod.ext
  · exact pivot_representative p
  · apply Subtype.ext
    change (pivotRepresentative p).val (pivot (pivotRepresentative p)) = p.2.val
    rw [pivot_representative]
    simp [pivotRepresentative]

/-- The inverse right head depends on the left head only through the private pivot message; this is the separation needed for the rectangle factors. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; A ∈ U(F, n); B ∈ V(F, t); R ∈ V(F, n); D ∈ V(F, t), we have

inverseHead(c, ε, A, B, R, D) = inverseHead(c, ε, pivotRepresentative(pivotMessage(A)), B, R, D).
-/
theorem inverseHead_message {n t : ℕ} (c ε : F) (A : U F n)
    (B : V F t) (R : V F n) (D : V F t) :
    inverseHead c ε A B R D =
      inverseHead c ε (pivotRepresentative (pivotMessage A)) B R D := by
  funext i
  simp only [inverseHead, pivot_representative]
  simp [pivotMessage, pivotRepresentative]

/-- Splitting any squared left factor according to the actual pivot is an exact disjoint partition; no loss occurs before Cauchy--Schwarz over pivots. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; A ∈ U(F, n); a ∈ ℝ, we have

(∑_(p ∈ Pivot(F, n)) (({ a if pivotMessage(A) = p,; 0 otherwise })²)) = a².
-/
theorem pivot_mask_energy {n : ℕ} (A : U F n) (a : ℝ) :
    (∑ p : Pivot F n, (if pivotMessage A = p then a else 0) ^ 2) = a ^ 2 := by
  simp only [ite_pow, zero_pow (by omega : 2 ≠ 0), Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- Every pivot class uses the same fixed-message inverse injection. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; A ∈ U(F, n); B ∈ V(F, t); R ∈ V(F, n); D ∈ V(F, t); p ∈ Pivot(F, n), assume pivotMessage(A) = p. Then

inverseHead(c, ε, A, B, R, D) = inverseHead(c, ε, pivotRepresentative(p), B, R, D).
-/
theorem inverseHead_of_message {n t : ℕ} (c ε : F) (A : U F n)
    (B : V F t) (R : V F n) (D : V F t) (p : Pivot F n)
    (hp : pivotMessage A = p) :
    inverseHead c ε A B R D = inverseHead c ε (pivotRepresentative p) B R D := by
  simpa only [hp] using inverseHead_message c ε A B R D

end CircuitCompiler.Shortening
