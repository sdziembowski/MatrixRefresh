import Mathlib.Tactic
import Proofs.Compiler.GateApproximation.MatrixPhase.GateAlgebra



/-!
# Algebra and exact collision counting for the retained input ports

The matrix approximation uses the tensor of two *distinct* input shares. Proportional tensor pairs are exactly those obtained by independently scaling both factors by nonzero field elements. This supplies the exact exceptional pair count in the Gram variance and four-cycle arguments.
-/

set_option autoImplicit false

namespace CircuitCompiler

open Refresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Proportionality with a nonzero multiplier, including its orientation. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; a, b ∈ V(F, n), define

NonzeroProportional(a, b) := ∃ c ∈ F, c ≠ 0 ∧ a = c · b.
-/
def NonzeroProportional {n : ℕ} (a b : V F n) : Prop :=
  ∃ c : F, c ≠ 0 ∧ a = c • b

omit [Fintype F] in
/-- A nonzero coordinate can be selected in every nonzero share. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; a ∈ U(F, n), we have

∃ i, a(i) ≠ 0.
-/
lemma exists_nonzero_coordinate {n : ℕ} (a : U F n) :
    ∃ i, a.val i ≠ 0 := by
  by_contra h
  apply a.property
  funext i
  simpa using not_exists.mp h i

/-- Tensor proportionality forces proportionality of each factor. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; a, b, a', b' ∈ U(F, n), we have

NonzeroProportional(tensorVector(a', b'), tensorVector(a, b)) ⇔ NonzeroProportional(a', a) ∧ NonzeroProportional(b', b).
-/
theorem tensorVector_proportional_iff {n : ℕ} (a b a' b' : U F n) :
    NonzeroProportional (tensorVector a'.val b'.val) (tensorVector a.val b.val) ↔
      NonzeroProportional a'.val a.val ∧ NonzeroProportional b'.val b.val := by
  constructor
  · rintro ⟨c, hc, h⟩
    obtain ⟨i, hi⟩ := exists_nonzero_coordinate a
    obtain ⟨j, hj⟩ := exists_nonzero_coordinate b
    have hp (k l : Fin n) : a'.val k * b'.val l = c * (a.val k * b.val l) := by
      have hk := congrFun h (finProdFinEquiv (k, l))
      simpa only [tensorVector_pair, Pi.smul_apply, smul_eq_mul] using hk
    have hij := hp i j
    have hi' : a'.val i ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hij
      exact mul_ne_zero hc (mul_ne_zero hi hj) hij.symm
    have hj' : b'.val j ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hij
      exact mul_ne_zero hc (mul_ne_zero hi hj) hij.symm
    constructor
    · refine ⟨a'.val i / a.val i, div_ne_zero hi' hi, ?_⟩
      funext k
      change a'.val k = (a'.val i / a.val i) * a.val k
      field_simp
      apply (mul_right_cancel₀ hj')
      linear_combination a.val i * hp k j - a.val k * hij
    · refine ⟨b'.val j / b.val j, div_ne_zero hj' hj, ?_⟩
      funext l
      change b'.val l = (b'.val j / b.val j) * b.val l
      field_simp
      apply (mul_left_cancel₀ hi')
      linear_combination b.val j * hp i l - b.val l * hij
  · rintro ⟨⟨c, hc, ha⟩, ⟨d, hd, hb⟩⟩
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    funext k
    simp only [tensorVector, ha, hb, Pi.smul_apply, smul_eq_mul]
    ring

/-- Scaling a nonzero share by a field unit preserves nonzeroness. -/
/- Mathematical definition (normal notation): Multiply every coordinate of a nonzero share by a nonzero field scalar. The result remains a nonzero share. -/
def scaleShare {n : ℕ} (a : U F n) (c : Fˣ) : U F n :=
  ⟨(c : F) • a.val, by
    intro h
    obtain ⟨i, hi⟩ := exists_nonzero_coordinate a
    have he := congrFun h i
    exact mul_ne_zero c.ne_zero hi (by simpa using he)⟩

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; a ∈ U(F, n); c ∈ Fˣ, we have

scaleShare(a, c) = c · a.
-/
@[simp] theorem scaleShare_val {n : ℕ} (a : U F n) (c : Fˣ) :
    (scaleShare a c).val = (c : F) • a.val :=
  rfl

/-- Distinct field units give distinct multiples of a fixed nonzero share. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; a ∈ U(F, n), we have

scaleShare(a) is injective.
-/
theorem scaleShare_injective {n : ℕ} (a : U F n) :
    Function.Injective (scaleShare a) := by
  intro c d h
  obtain ⟨i, hi⟩ := exists_nonzero_coordinate a
  have he := congrFun (congrArg Subtype.val h) i
  apply Units.ext
  exact mul_right_cancel₀ hi (by simpa only [scaleShare_val, Pi.smul_apply,
    smul_eq_mul] using he)

/-- The complete exceptional set for a fixed tensor of nonzero shares. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; a, b ∈ U(F, n), define

TensorProportionalFiber(a, b) := {p ∈ U(F, n) × U(F, n) | NonzeroProportional(tensorVector((p)₁, (p)₂), tensorVector(a, b))}.
-/
abbrev TensorProportionalFiber {n : ℕ} (a b : U F n) :=
  {p : U F n × U F n //
    NonzeroProportional (tensorVector p.1.val p.2.val) (tensorVector a.val b.val)}

/-- Two independent nonzero scaling factors enumerate every proportional input tensor exactly once. -/
/- Mathematical definition (normal notation): Given nonzero scalar factors c,d, send the fixed operand shares (a,b) to (ca,db). Their tensor is proportional to the original tensor; the map records this pair in the corresponding proportional-tensor fiber. -/
def tensorProportionalMap {n : ℕ} (a b : U F n) (p : Fˣ × Fˣ) :
    TensorProportionalFiber a b :=
  ⟨(scaleShare a p.1, scaleShare b p.2),
    (tensorVector_proportional_iff a b _ _).2
      ⟨⟨p.1, p.1.ne_zero, rfl⟩, ⟨p.2, p.2.ne_zero, rfl⟩⟩⟩

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; a, b ∈ U(F, n), we have

tensorProportionalMap(a, b) is bijective.
-/
theorem tensorProportionalMap_bijective {n : ℕ} (a b : U F n) :
    Function.Bijective (tensorProportionalMap a b) := by
  constructor
  · intro p p' h
    have he := congrArg Subtype.val h
    apply Prod.ext
    · exact scaleShare_injective a (congrArg Prod.fst he)
    · exact scaleShare_injective b (congrArg Prod.snd he)
  · rintro ⟨⟨a', b'⟩, hp⟩
    obtain ⟨⟨c, hc, ha⟩, ⟨d, hd, hb⟩⟩ := (tensorVector_proportional_iff a b a' b').1 hp
    refine ⟨(Units.mk0 c hc, Units.mk0 d hd), ?_⟩
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · exact ha.symm
    · exact hb.symm

/-- The exact exceptional-fiber cardinality used in both joint-port moments. In the manuscript notation this is `(q - 1)^2`, out of `(N - 1)^2` possible pairs of input shares. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; a, b ∈ U(F, n), we have

|TensorProportionalFiber(a, b)| = (|F| - 1)².
-/
theorem card_tensorProportionalFiber {n : ℕ} (a b : U F n) :
    Nat.card (TensorProportionalFiber a b) = (fieldCard F - 1) ^ 2 := by
  have hc := Nat.card_congr (Equiv.ofBijective _ (tensorProportionalMap_bijective a b))
  rw [← hc, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_units]
  simp [fieldCard, pow_two]

end CircuitCompiler
