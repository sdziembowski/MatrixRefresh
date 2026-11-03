import Proofs.Compiler.GateApproximation.Shortening.ShorteningTransport



/-!
# Injective changes of variables used by shortening transport

These are the two finite injections behind the nuclear-norm calculation. The right injection holds at every fixed communicated head pivot and tail.
-/
set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace CircuitCompiler.Shortening

open Refresh MatrixRefresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The accepted left coordinates embed in the complete nonzero long space. -/
/- Mathematical definition (normal notation): The map (A,B) ↦ (A,B) concatenates a nonzero short left share and an arbitrary tail into a nonzero long left share. It is injective. -/
def leftEmbedding {n t : ℕ} : (U F n × V F t) ↪ U F (n + t) where
  toFun p := ⟨Fin.append p.1.val p.2, append_nonzero p.1 p.2⟩
  inj' := by
    intro a b h
    have hv := congrArg Subtype.val h
    apply Prod.ext
    · apply Subtype.ext
      funext i
      simpa using congrFun hv (Fin.castAdd t i)
    · funext i
      simpa using congrFun hv (Fin.natAdd n i)

/-- For each fixed private message the inverse affine right transformation is injective, including the possible zero long right vector. -/
/- Mathematical definition (normal notation): For fixed left data, map a nonzero short right share and arbitrary tail to the long vector obtained by the inverse affine head transformation and that same tail. This map is injective, although the long vector may be zero. -/
def rightEmbedding {n t : ℕ} (c ε : F) (hε : ε ≠ 0)
    (A : U F n) (B : V F t) : (U F n × V F t) ↪ V F (n + t) where
  toFun p := Fin.append (inverseHead c ε A B p.1.val p.2) p.2
  inj' := by
    intro a b h
    have hD : a.2 = b.2 := by
      funext i
      simpa using congrFun h (Fin.natAdd n i)
    have hC : inverseHead c ε A B a.1.val a.2 = inverseHead c ε A B b.1.val b.2 := by
      funext i
      simpa using congrFun h (Fin.castAdd t i)
    apply Prod.ext
    · apply Subtype.ext
      rw [hD] at hC
      have hh := congrArg (fun C => right c ε A B C b.2) hC
      simpa only [right_inverseHead c ε hε] using hh
    · exact hD

/-- Extend a function on nonzero vectors by zero at the zero vector. -/
/-
Mathematical definition (normal notation): For m ∈ ℕ; b ∈ U(F, m) → ℝ; V ∈ V(F, m), define

zeroExtend(b, V) := { b((V, h)) if V ≠ 0,; 0 otherwise }.
-/
def zeroExtend {m : ℕ} (b : U F m → ℝ) (V : V F m) : ℝ :=
  if h : V ≠ 0 then b ⟨V, h⟩ else 0

/-- Zero extension does not change an unnormalized sum. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; b ∈ U(F, m) → ℝ, we have

(∑_(V ∈ V(F, m)) (zeroExtend(b, V))) = ∑_(U ∈ U(F, m)) (b(U)).
-/
theorem sum_zeroExtend {m : ℕ} (b : U F m → ℝ) :
    (∑ V : V F m, zeroExtend b V) = ∑ U : U F m, b U := by
  classical
  calc
    _ = ∑ v ∈ Finset.univ.filter (fun v : V F m => v ≠ 0), zeroExtend b v := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v ≠ 0 <;> simp [zeroExtend, hv]
    _ = ∑ u : U F m, zeroExtend b u.val :=
      Finset.sum_subtype _ (by intro v; simp) (zeroExtend b)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      simp only [zeroExtend, dif_pos u.property]

/-- Squaring commutes with the zero extension. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; b ∈ U(F, m) → ℝ; v ∈ V(F, m), we have

(zeroExtend(b, v))² = zeroExtend(((u ↦ (b(u))²)), v).
-/
theorem zeroExtend_sq {m : ℕ} (b : U F m → ℝ) (v : V F m) :
    zeroExtend b v ^ 2 = zeroExtend (fun u => b u ^ 2) v := by
  unfold zeroExtend
  split_ifs <;> simp

/-- The uniform mean of a nonnegative zero extension is no larger than its uniform mean over nonzero vectors. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; b ∈ U(F, m) → ℝ, assume U(F, m) ≠ ∅; ∀ u, 0 ≤ b(u). Then

𝔼_(w ← 𝒰_(V(F, m))) [zeroExtend(b, w)] ≤ 𝔼_(x ← 𝒰_(U(F, m))) [b(x)].
-/
theorem zeroExtend_expect_le {m : ℕ} [Nonempty (U F m)]
    (b : U F m → ℝ) (hb : ∀ u, 0 ≤ b u) :
    (FiniteDistribution.uniform : FiniteDistribution (V F m)).expect (zeroExtend b) ≤
      (FiniteDistribution.uniform : FiniteDistribution (U F m)).expect b := by
  have hu : (0 : ℝ) < Fintype.card (U F m) := by exact_mod_cast Fintype.card_pos
  have hv : (Fintype.card (U F m) : ℝ) ≤ Fintype.card (V F m) := by
    exact_mod_cast Fintype.card_subtype_le (fun v : V F m => v ≠ 0)
  simp only [FiniteDistribution.expect, FiniteDistribution.uniform, ← Finset.mul_sum, sum_zeroExtend]
  apply mul_le_mul_of_nonneg_right
  · exact inv_anti₀ hu hv
  · exact Finset.sum_nonneg (fun u _ => hb u)

/-- Squared energy under the fixed-message right pullback is controlled by a concrete finite-cardinality ratio, without any statement about plaintexts. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; A ∈ U(F, n); B ∈ V(F, t); b ∈ U(F, (n + t)) → ℝ, assume U(F, n) ≠ ∅; U(F, (n + t)) ≠ ∅; ε ≠ 0. Then

𝔼_(p ← 𝒰_(U(F, n) × V(F, t))) [(zeroExtend(b, rightEmbedding(c, ε, A, B, p)))²] ≤ (|V(F, (n + t))| / |(U(F, n) × V(F, t))|) · 𝔼_(v ← 𝒰_(U(F, (n + t)))) [(b(v))²].
-/
theorem right_pullback_energy {n t : ℕ} [Nonempty (U F n)] [Nonempty (U F (n + t))]
    (c ε : F) (hε : ε ≠ 0) (A : U F n) (B : V F t) (b : U F (n + t) → ℝ) :
    (FiniteDistribution.uniform : FiniteDistribution (U F n × V F t)).expect
      (fun p => zeroExtend b (rightEmbedding c ε hε A B p) ^ 2) ≤
      ((Fintype.card (V F (n + t)) : ℝ) / Fintype.card (U F n × V F t)) *
        (FiniteDistribution.uniform : FiniteDistribution (U F (n + t))).expect (fun v => b v ^ 2) := by
  have h := uniform_embedding_expect_le (rightEmbedding c ε hε A B)
    (fun v => zeroExtend b v ^ 2) (fun _ => sq_nonneg _)
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_left
  · simp only [zeroExtend_sq]
    exact zeroExtend_expect_le _ (fun _ => sq_nonneg _)
  · positivity

/-- The analogous left pullback has the exact nonzero-space ratio. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; a ∈ U(F, (n + t)) → ℝ, assume U(F, n) ≠ ∅; U(F, (n + t)) ≠ ∅. Then

𝔼_(p ← 𝒰_(U(F, n) × V(F, t))) [(a(leftEmbedding(p)))²] ≤ (|U(F, (n + t))| / |(U(F, n) × V(F, t))|) · 𝔼_(v ← 𝒰_(U(F, (n + t)))) [(a(v))²].
-/
theorem left_pullback_energy {n t : ℕ} [Nonempty (U F n)] [Nonempty (U F (n + t))]
    (a : U F (n + t) → ℝ) :
    (FiniteDistribution.uniform : FiniteDistribution (U F n × V F t)).expect
      (fun p => a (leftEmbedding p) ^ 2) ≤
      ((Fintype.card (U F (n + t)) : ℝ) / Fintype.card (U F n × V F t)) *
        (FiniteDistribution.uniform : FiniteDistribution (U F (n + t))).expect (fun v => a v ^ 2) :=
  uniform_embedding_expect_le leftEmbedding (fun v => a v ^ 2) (fun _ => sq_nonneg _)

/-- The right injection's density cost is independent of the tail length. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ, assume 1 ≤ n. Then

(|V(F, (n + t))| / |(U(F, n) × V(F, t))|) = (|F|)ⁿ / ((|F|)ⁿ - 1).
-/
theorem right_density_eq {n t : ℕ} (hn : 1 ≤ n) :
    ((Fintype.card (V F (n + t)) : ℝ) / Fintype.card (U F n × V F t)) =
      (fieldCard F : ℝ) ^ n / ((fieldCard F : ℝ) ^ n - 1) := by
  have hn1 : 1 ≤ fieldCard F ^ n := Nat.one_le_pow _ _ (by have := fieldCard_ge_two (F := F); omega)
  have hH : (0 : ℝ) < (fieldCard F : ℝ) ^ t := by
    apply pow_pos
    exact_mod_cast fieldCard_pos (F := F)
  simp only [vector_card, Fintype.card_prod, nonzero_vector_card,
    Nat.cast_mul, Nat.cast_sub hn1, Nat.cast_pow, Nat.cast_one, pow_add]
  field_simp

/-- Both pullback density losses are bounded by the field-only constant `q/(q-1)`, uniformly in both share lengths. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ, assume 1 ≤ n. Then

(|V(F, (n + t))| / |(U(F, n) × V(F, t))|) ≤ |F| / (|F| - 1).
-/
theorem right_density_le {n t : ℕ} (hn : 1 ≤ n) :
    ((Fintype.card (V F (n + t)) : ℝ) / Fintype.card (U F n × V F t)) ≤
      (fieldCard F : ℝ) / ((fieldCard F : ℝ) - 1) := by
  rw [right_density_eq hn]
  have hq : (1 : ℝ) < fieldCard F := by exact_mod_cast (show 1 < fieldCard F by
    have := fieldCard_ge_two (F := F); omega)
  have hN : (fieldCard F : ℝ) ≤ (fieldCard F : ℝ) ^ n := by
    exact_mod_cast (show fieldCard F ≤ fieldCard F ^ n by
      calc
        fieldCard F = fieldCard F ^ 1 := by simp
        _ ≤ fieldCard F ^ n := Nat.pow_le_pow_right (by have := fieldCard_ge_two (F := F); omega) hn)
  apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < (fieldCard F : ℝ) ^ n - 1)
    (by linarith : (0 : ℝ) < (fieldCard F : ℝ) - 1)).2
  nlinarith

/-- The left injection has no larger density cost than the right one. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ, assume 1 ≤ n. Then

(|U(F, (n + t))| / |(U(F, n) × V(F, t))|) ≤ |F| / (|F| - 1).
-/
theorem left_density_le {n t : ℕ} (hn : 1 ≤ n) :
    ((Fintype.card (U F (n + t)) : ℝ) / Fintype.card (U F n × V F t)) ≤
      (fieldCard F : ℝ) / ((fieldCard F : ℝ) - 1) := by
  refine le_trans ?_ (right_density_le (F := F) (t := t) hn)
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Fintype.card_subtype_le (fun v : V F (n + t) => v ≠ 0)
  · positivity

end CircuitCompiler.Shortening
