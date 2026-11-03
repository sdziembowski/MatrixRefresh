import Proofs.Compiler.GateApproximation.MatrixPhase.GateAlgebra



/-!
# Exact algebra and counting for affine shortening

The ordinary branch takes a long encoding `(A,B),(C,D)` with `A ≠ 0`. It outputs `(A,R)` representing `c + ε*z`. For multiplication use `c = 0` and `ε = 1`; for a complemented product use `ε = -1`.

The inverse formulas below establish a genuine bijection, including zero plaintexts, rather than postulating freshness. The auxiliary long right share may be zero, exactly as in the manuscript's auxiliary experiment.
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler.Shortening

open Refresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
/-- Every nonzero share has a nonzero coordinate. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; A ∈ U(F, n), we have

∃ j, A(j) ≠ 0.
-/
theorem exists_nonzero_coordinate {n : ℕ} (A : U F n) : ∃ j, A.val j ≠ 0 := by
  by_contra h
  apply A.property
  funext i
  simpa using not_exists.mp h i

/-- The message includes the first nonzero coordinate, as specified in the protocol. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; A ∈ U(F, n), define

pivot(A) := Fin.find(((j ↦ A(j) ≠ 0))).
-/
def pivot {n : ℕ} (A : U F n) : Fin n :=
  Fin.find (fun j => A.val j ≠ 0) (exists_nonzero_coordinate A)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; A ∈ U(F, n), we have

A(pivot(A)) ≠ 0.
-/
@[simp] theorem pivot_nonzero {n : ℕ} (A : U F n) : A.val (pivot A) ≠ 0 :=
  Fin.find_spec (exists_nonzero_coordinate A)

/-- All coordinates preceding the transmitted index are zero. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; A ∈ U(F, n); i ∈ {0,…,n-1}, assume i < pivot(A). Then

A(i) = 0.
-/
theorem before_pivot_zero {n : ℕ} (A : U F n) (i : Fin n) (hi : i < pivot A) :
    A.val i = 0 := by
  simpa using Fin.find_min (exists_nonzero_coordinate A) hi

/-- The actual right output coordinate, with no symbolic indicator notation. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; c, ε ∈ F; A ∈ U(F, n); B ∈ V(F, t); C ∈ V(F, n); D ∈ V(F, t), define

right(c, ε, A, B, C, D) := (i ↦ ε · C(i) + { (c + ε · (B · D)) / A(pivot(A)) if i = pivot(A),; 0 otherwise }).
-/
def right {n t : ℕ} (c ε : F) (A : U F n) (B : V F t)
    (C : V F n) (D : V F t) : V F n :=
  fun i => ε * C i + if i = pivot A then
    (c + ε * dot B D) / A.val (pivot A) else 0

/-- The inverse head of the long right share, for any nonzero `ε`. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; c, ε ∈ F; A ∈ U(F, n); B ∈ V(F, t); R ∈ V(F, n); D ∈ V(F, t), define

inverseHead(c, ε, A, B, R, D) := (i ↦ (ε)⁻¹ · R(i) - { ((ε)⁻¹ · c + (B · D)) / A(pivot(A)) if i = pivot(A),; 0 otherwise }).
-/
def inverseHead {n t : ℕ} (c ε : F) (A : U F n) (B : V F t)
    (R : V F n) (D : V F t) : V F n :=
  fun i => ε⁻¹ * R i - if i = pivot A then
    (ε⁻¹ * c + dot B D) / A.val (pivot A) else 0

/-- Shortening has the advertised affine effect on the inner product. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; A ∈ U(F, n); B ∈ V(F, t); C ∈ V(F, n); D ∈ V(F, t), we have

(A · right(c, ε, A, B, C, D)) = c + ε · ((A · C) + (B · D)).
-/
theorem right_dot {n t : ℕ} (c ε : F) (A : U F n)
    (B : V F t) (C : V F n) (D : V F t) :
    dot A.val (right c ε A B C D) = c + ε * (dot A.val C + dot B D) := by
  unfold right dot dotProduct
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  have hsum : (∑ i, A.val i * (ε * C i)) = ε * ∑ i, A.val i * C i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  field_simp
  ring

/-- Substitution into the inverse recovers the long right head exactly. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; A ∈ U(F, n); B ∈ V(F, t); C ∈ V(F, n); D ∈ V(F, t), assume ε ≠ 0. Then

inverseHead(c, ε, A, B, right(c, ε, A, B, C, D), D) = C.
-/
@[simp] theorem inverseHead_right {n t : ℕ} (c ε : F) (hε : ε ≠ 0)
    (A : U F n) (B : V F t) (C : V F n) (D : V F t) :
    inverseHead c ε A B (right c ε A B C D) D = C := by
  funext i
  by_cases hi : i = pivot A
  · simp only [inverseHead, right, hi, ite_true]
    field_simp
    ring
  · simp [inverseHead, right, hi, hε]

/-- Substitution of the inverse head realizes every proposed short output. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; A ∈ U(F, n); B ∈ V(F, t); R ∈ V(F, n); D ∈ V(F, t), assume ε ≠ 0. Then

right(c, ε, A, B, inverseHead(c, ε, A, B, R, D), D) = R.
-/
@[simp] theorem right_inverseHead {n t : ℕ} (c ε : F) (hε : ε ≠ 0)
    (A : U F n) (B : V F t) (R : V F n) (D : V F t) :
    right c ε A B (inverseHead c ε A B R D) D = R := by
  funext i
  by_cases hi : i = pivot A
  · simp only [inverseHead, right, hi, ite_true]
    field_simp
    ring
  · simp [inverseHead, right, hi, hε]

/-- An output representing the affine target reconstructs a long encoding of `z`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; A ∈ U(F, n); B ∈ V(F, t); R ∈ V(F, n); D ∈ V(F, t), assume ε ≠ 0; (A · R) = c + ε · z. Then

(A · inverseHead(c, ε, A, B, R, D)) + (B · D) = z.
-/
theorem inverseHead_dot {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    (A : U F n) (B : V F t) (R : V F n) (D : V F t)
    (hR : dot A.val R = c + ε * z) :
    dot A.val (inverseHead c ε A B R D) + dot B D = z := by
  have h := right_dot c ε A B (inverseHead c ε A B R D) D
  rw [right_inverseHead c ε hε, hR] at h
  exact (mul_left_cancel₀ hε (add_left_cancel h)).symm

/-- The long encoding, split into its head and tail, after excluding `A = 0`. No condition excluding a zero long right share is imposed here. -/
/- Mathematical definition (normal notation): Split the long left and right shares into (A,B) and (C,D), where A ∈ Fⁿ is nonzero, B,D ∈ Fᵗ, and C ∈ Fⁿ. This auxiliary carrier does not require the long right share to be nonzero. -/
@[ext] structure Data (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n t : ℕ) where
  A : U F n
  B : V F t
  C : V F n
  D : V F t
  deriving Fintype

/-- Pairing of the concatenated long vectors. -/
/- Mathematical definition (normal notation): For long shares split into blocks (A,B) and (C,D), their encoded secret is A · C+B · D, the inner product of the concatenated vectors. -/
def longSecret {n t : ℕ} (p : Data F n t) : F := dot p.A.val p.C + dot p.B p.D

/-- The right output computed from a split long encoding. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ Data(F, n, t), define

outputRight(c, ε, p) := right(c, ε, p.A, p.B, p.C, p.D).
-/
def outputRight {n t : ℕ} (c ε : F) (p : Data F n t) : V F n :=
  right c ε p.A p.B p.C p.D

/-- Exactly the ordinary-branch auxiliary long encodings of `z`. -/
/-
Mathematical definition (normal notation): For F a set; n, t ∈ ℕ; c, ε, z ∈ F, assume F is a field; F is finite. define

Accepted(n, t, c, ε, z) := {p ∈ Data(F, n, t) | longSecret(p) = z ∧ outputRight(c, ε, p) ≠ 0}.
-/
abbrev Accepted (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n t : ℕ) (c ε z : F) :=
  {p : Data F n t // longSecret p = z ∧ outputRight c ε p ≠ 0}

/-- The short output, including its nonzero shares and encoded-value proof. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; p ∈ Accepted(F, n, t, c, ε, z), define

output(c, ε, z, p) := (p.val.A, (outputRight(c, ε, p), (p.property)₂)).
-/
def output {n t : ℕ} (c ε z : F) (p : Accepted F n t c ε z) :
    Fiber F n (c + ε * z) :=
  ⟨⟨p.val.A, ⟨outputRight c ε p.val, p.property.2⟩⟩, by
    change dot p.val.A.val (right c ε p.val.A p.val.B p.val.C p.val.D) = _
    rw [right_dot]
    exact congrArg (fun v => c + ε * v) p.property.1⟩

/-- Reconstruct a long encoding from its short output and two freely chosen tails. -/
/- Mathematical definition (normal notation): Given a short encoding of c+ε z and arbitrary tails B,D, retain its left head and use the inverse affine right-head transformation to recover the unique accepted long record encoding z with those tails. -/
def reconstruct {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    (p : Fiber F n (c + ε * z)) (B D : V F t) : Accepted F n t c ε z :=
  ⟨⟨p.val.L, B, inverseHead c ε p.val.L B p.val.R.val D, D⟩, by
    constructor
    · exact inverseHead_dot c ε z hε p.val.L B p.val.R.val D p.property
    · simpa only [outputRight, right_inverseHead c ε hε] using p.val.R.property⟩

/-- Reconstruction followed by shortening returns the exact proposed encoding. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; p ∈ Fiber(F, n, (c + ε · z)); B, D ∈ V(F, t), assume ε ≠ 0. Then

output(c, ε, z, reconstruct(c, ε, z, p, B, D)) = p.
-/
@[simp] theorem output_reconstruct {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    (p : Fiber F n (c + ε * z)) (B D : V F t) :
    output c ε z (reconstruct c ε z hε p B D) = p := by
  apply Subtype.ext
  apply State.ext
  · rfl
  · apply Subtype.ext
    exact right_inverseHead c ε hε p.val.L B p.val.R.val D

/-- Shortening retains all long data once its two tails are retained. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; p ∈ Accepted(F, n, t, c, ε, z), assume ε ≠ 0. Then

reconstruct(c, ε, z, output(c, ε, z, p), p.val.B, p.val.D) = p.
-/
@[simp] theorem reconstruct_output {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    (p : Accepted F n t c ε z) :
    reconstruct c ε z hε (output c ε z p) p.val.B p.val.D = p := by
  apply Subtype.ext
  apply Data.ext
  · rfl
  · rfl
  · exact inverseHead_right c ε hε p.val.A p.val.B p.val.C p.val.D
  · rfl

/-- The exact canonical change of variables. Every accepted short output has one preimage for each ordered pair of tails, independently of its plaintext. -/
/- Mathematical definition (normal notation): Accepted shortening records encoding z are in bijection with triples consisting of a short encoding of c+ε z and two arbitrary tails B,D ∈ Fᵗ. The forward map returns output and tails; the inverse reconstructs the long record. -/
def acceptedEquiv {n t : ℕ} (c ε z : F) (hε : ε ≠ 0) :
    Accepted F n t c ε z ≃ Fiber F n (c + ε * z) × (V F t × V F t) where
  toFun p := (output c ε z p, p.val.B, p.val.D)
  invFun p := reconstruct c ε z hε p.1 p.2.1 p.2.2
  left_inv p := reconstruct_output c ε z hε p
  right_inv p := by
    rcases p with ⟨p, B, D⟩
    change (output c ε z (reconstruct c ε z hε p B D), B, D) = (p, B, D)
    rw [output_reconstruct]

/-- A fixed output's preimages are exactly all ordered pairs of tails. -/
/- Mathematical definition (normal notation): For a fixed short output, its accepted long preimages are in bijection with all ordered tail pairs (B,D) ∈ Fᵗ × Fᵗ, through reconstruction. -/
def outputFiberEquiv {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    (p : Fiber F n (c + ε * z)) :
    {a : Accepted F n t c ε z // output c ε z a = p} ≃ (V F t × V F t) where
  toFun a := (a.val.val.B, a.val.val.D)
  invFun tails := ⟨reconstruct c ε z hε p tails.1 tails.2,
    output_reconstruct c ε z hε p tails.1 tails.2⟩
  left_inv a := by
    apply Subtype.ext
    change reconstruct c ε z hε p a.val.val.B a.val.val.D = a.val
    simpa only [a.property] using reconstruct_output c ε z hε a.val
  right_inv _ := rfl

/-- The manuscript's exact `q^(2t)` preimage count. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F; p ∈ Fiber(F, n, (c + ε · z)), assume ε ≠ 0. Then

|{a ∈ Accepted(F, n, t, c, ε, z) | output(c, ε, z, a) = p}| = (|F|)^(2 · t).
-/
theorem output_fiber_card {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    (p : Fiber F n (c + ε * z)) :
    Fintype.card {a : Accepted F n t c ε z // output c ε z a = p} = fieldCard F ^ (2 * t) := by
  classical
  rw [Fintype.card_congr (outputFiberEquiv c ε z hε p), Fintype.card_prod]
  simp only [vector_card, ← pow_add, two_mul]

/-- Exact accepted-domain cardinality, with no asymptotic constant. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F, assume ε ≠ 0. Then

|Accepted(F, n, t, c, ε, z)| = |Fiber(F, n, (c + ε · z))| · (|F|)^(2 · t).
-/
theorem accepted_card {n t : ℕ} (c ε z : F) (hε : ε ≠ 0) :
    Fintype.card (Accepted F n t c ε z) =
      Fintype.card (Fiber F n (c + ε * z)) * fieldCard F ^ (2 * t) := by
  classical
  rw [Fintype.card_congr (acceptedEquiv c ε z hε), Fintype.card_prod,
    Fintype.card_prod]
  simp only [vector_card, ← pow_add, two_mul]

/-- Whenever the target encoding fiber exists, the accepted ordinary branch exists. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F, assume ε ≠ 0; Fiber(F, n, (c + ε · z)) ≠ ∅. Then

Accepted(F, n, t, c, ε, z) ≠ ∅.
-/
theorem accepted_nonempty {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    [Nonempty (Fiber F n (c + ε * z))] : Nonempty (Accepted F n t c ε z) := by
  classical
  exact ⟨reconstruct c ε z hε (Classical.choice inferInstance) 0 0⟩

/-- Uniform sampling among accepted auxiliary long encodings produces an exact uniform short encoding. The preceding cardinality theorem proves the premise of the finite uniform-map theorem. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F, assume ε ≠ 0; Accepted(F, n, t, c, ε, z) ≠ ∅; Fiber(F, n, (c + ε · z)) ≠ ∅. Then

(output(c, ε, z)_*𝒰_(Accepted(F, n, t, c, ε, z))) = 𝒰_(Fiber(F, n, (c + ε · z))).
-/
theorem accepted_output_uniform {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    [Nonempty (Accepted F n t c ε z)] [Nonempty (Fiber F n (c + ε * z))] :
    (FiniteDistribution.uniform : FiniteDistribution (Accepted F n t c ε z)).map (output c ε z) =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (c + ε * z))) := by
  classical
  exact FiniteDistribution.uniform_map_of_fiber_card _ (fieldCard F ^ (2 * t))
    (output_fiber_card c ε z hε)

/-- The two excluded zero-right coordinates would produce a zero output for multiplication. Thus every accepted product preimage already has nonzero long right share; the auxiliary extension changes no accepted multiplication input. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; z ∈ F; p ∈ Accepted(F, n, t, 0, 1, z), we have

¬ ((p.val.C = 0 ∧ p.val.D = 0)).
-/
theorem accepted_product_right_nonzero {n t : ℕ} (z : F)
    (p : Accepted F n t (0 : F) 1 z) : ¬ (p.val.C = 0 ∧ p.val.D = 0) := by
  rintro ⟨hC, hD⟩
  apply p.property.2
  funext i
  simp [outputRight, right, hC, hD]

omit [Fintype F] [DecidableEq F] in
/-- Concatenation realizes the split-coordinate pairing as the actual long inner product on `n+t` coordinates. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; A, C ∈ V(F, n); B, D ∈ V(F, t), we have

(Fin.append(A, B) · Fin.append(C, D)) = (A · C) + (B · D).
-/
theorem append_dot {n t : ℕ} (A C : V F n) (B D : V F t) :
    dot (Fin.append A B) (Fin.append C D) = dot A C + dot B D := by
  unfold dot dotProduct
  rw [Fin.sum_univ_add]
  simp

/-- Uniform finite distributions are transported exactly by an explicit bijection. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α,β a set; e ∈ α ≃ β, assume α is finite; β is finite; α ≠ ∅; β ≠ ∅. Then

(e_*𝒰_α) = 𝒰ᵦ.
-/
private theorem uniform_equiv {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (e : α ≃ β) :
    (FiniteDistribution.uniform : FiniteDistribution α).map e = (FiniteDistribution.uniform : FiniteDistribution β) := by
  classical
  apply FiniteDistribution.uniform_map_of_fiber_card _ 1
  intro b
  letI : Unique {a : α // e a = b} :=
    ⟨⟨e.symm b, e.apply_symm_apply b⟩, by
      intro a
      apply Subtype.ext
      exact e.injective (a.property.trans (e.apply_symm_apply b).symm)⟩
  exact Fintype.card_unique

/-- The accepted output and the two tails are jointly independent uniform objects. This proves the conditional tail distribution used in transport. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F, assume ε ≠ 0; Accepted(F, n, t, c, ε, z) ≠ ∅; Fiber(F, n, (c + ε · z)) ≠ ∅. Then

(acceptedEquiv(c, ε, z)_*𝒰_(Accepted(F, n, t, c, ε, z))) = (𝒰_(Fiber(F, n, (c + ε · z))) ⊗ (𝒰_(V(F, t)) ⊗ 𝒰_(V(F, t)))).
-/
theorem accepted_joint_uniform {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    [Nonempty (Accepted F n t c ε z)] [Nonempty (Fiber F n (c + ε * z))] :
    (FiniteDistribution.uniform : FiniteDistribution (Accepted F n t c ε z)).map (acceptedEquiv c ε z hε) =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (c + ε * z))).prod
        ((FiniteDistribution.uniform : FiniteDistribution (V F t)).prod (FiniteDistribution.uniform : FiniteDistribution (V F t))) := by
  rw [uniform_equiv]
  ext p
  simp [FiniteDistribution.prod, FiniteDistribution.joint, FiniteDistribution.uniform, Fintype.card_prod, mul_assoc]
  ring

/-- Accepted long states that also meet the actual protocol's nonzero-right requirement. The auxiliary experiment omits this additional restriction. -/
/-
Mathematical definition (normal notation): For F a set; n, t ∈ ℕ; c, ε, z ∈ F, assume F is a field; F is finite. define

ActualAccepted(n, t, c, ε, z) := {a ∈ Accepted(F, n, t, c, ε, z) | ¬ ((a.val.C = 0 ∧ a.val.D = 0))}.
-/
abbrev ActualAccepted (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n t : ℕ) (c ε z : F) :=
  {a : Accepted F n t c ε z // ¬(a.val.C = 0 ∧ a.val.D = 0)}

/-- For multiplication, all auxiliary accepted inputs are actual inputs. -/
/- Mathematical definition (normal notation): For multiplication, c = 0 and ε = 1, every accepted auxiliary record already has a nonzero long right share. Forgetting that redundant condition bijects actual accepted records with all auxiliary accepted records. -/
def productActualAcceptedEquiv {n t : ℕ} (z : F) :
    ActualAccepted F n t 0 1 z ≃ Accepted F n t 0 1 z where
  toFun a := a.val
  invFun a := ⟨a, accepted_product_right_nonzero z a⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Restricting multiplication to actual long encodings leaves each output's `q^(2t)` preimages unchanged. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; z ∈ F; p ∈ Fiber(F, n, (0 + 1 · z)), we have

|{a ∈ ActualAccepted(F, n, t, 0, 1, z) | output(0, 1, z, a) = p}| = (|F|)^(2 · t).
-/
theorem actual_product_output_fiber_card {n t : ℕ} (z : F)
    (p : Fiber F n ((0 : F) + 1 * z)) :
    Fintype.card {a : ActualAccepted F n t 0 1 z // output 0 1 z a.val = p} =
      fieldCard F ^ (2 * t) := by
  classical
  let e : {a : ActualAccepted F n t 0 1 z // output 0 1 z a.val = p} ≃
      {a : Accepted F n t 0 1 z // output 0 1 z a = p} :=
    Equiv.subtypeEquiv (productActualAcceptedEquiv (n := n) (t := t) z)
      (fun _ => Iff.rfl)
  rw [Fintype.card_congr e]
  exact output_fiber_card 0 1 z one_ne_zero p

/-- Exact output freshness for accepted actual multiplication, including a zero product. No approximation by the auxiliary experiment is needed. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; z ∈ F, assume ActualAccepted(F, n, t, 0, 1, z) ≠ ∅; Fiber(F, n, (0 + 1 · z)) ≠ ∅. Then

(((a ↦ output(0, 1, z, a)))_*𝒰_(ActualAccepted(F, n, t, 0, 1, z))) = 𝒰_(Fiber(F, n, (0 + 1 · z))).
-/
theorem actual_product_output_uniform {n t : ℕ} (z : F)
    [Nonempty (ActualAccepted F n t 0 1 z)] [Nonempty (Fiber F n ((0 : F) + 1 * z))] :
    (FiniteDistribution.uniform : FiniteDistribution (ActualAccepted F n t 0 1 z)).map
      (fun a => output 0 1 z a.val) =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F n ((0 : F) + 1 * z))) := by
  classical
  exact FiniteDistribution.uniform_map_of_fiber_card _ (fieldCard F ^ (2 * t))
    (actual_product_output_fiber_card z)

end CircuitCompiler.Shortening
