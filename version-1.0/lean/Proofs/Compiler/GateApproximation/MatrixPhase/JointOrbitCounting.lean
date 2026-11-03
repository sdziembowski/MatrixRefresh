import Proofs.Compiler.Foundations.MatrixRefreshing.Counting.LinearExtensions
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Discrepancy
import Proofs.Compiler.Foundations.LinearAlgebra.PairOrbits



/-!
# Independent compatible column pairs

Two independent row forms have affine fibers of size `q^(m-2)`. Removing zero from the first fiber and its scalar line from the second gives a uniform lower bound on the number of independent compatible column pairs. The bound avoids a case split on the rank of the prescribed pairing matrix.
-/

set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators Classical

namespace CircuitCompiler

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A fiber of two prescribed row pairings. -/
/-
Mathematical definition (normal notation): For m ∈ ℕ; l ∈ {0,…,2-1} → V(F, m); γ ∈ {0,…,2-1} → F, define

PairingFiber(l, γ) := {v ∈ V(F, m) | dotMap(l, v) = γ}.
-/
abbrev PairingFiber {m : ℕ} (l : Fin 2 → V F m) (γ : Fin 2 → F) :=
  {v : V F m // dotMap l v = γ}

/-- At most one point of an affine pairing fiber is zero. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; l ∈ {0,…,2-1} → V(F, m); γ ∈ {0,…,2-1} → F, we have

|{v ∈ PairingFiber(l, γ) | v = 0}| ≤ 1.
-/
theorem pairingFiber_zero_card_le {m : ℕ} (l : Fin 2 → V F m) (γ : Fin 2 → F) :
    Fintype.card {v : PairingFiber l γ // v.val = 0} ≤ 1 := by
  have h := Fintype.card_le_of_injective
    (fun _ : {v : PairingFiber l γ // v.val = 0} => ()) (by
      intro a b _
      apply Subtype.ext
      apply Subtype.ext
      exact a.property.trans b.property.symm)
  simpa using h

/-- At least `q^(m-2)-1` members of any pairing fiber are nonzero. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; l ∈ {0,…,2-1} → V(F, m); γ ∈ {0,…,2-1} → F, assume 2 ≤ m; LinearIndependent(F, l). Then

(|F|)^(m − 2) - 1 ≤ |{v ∈ PairingFiber(l, γ) | v ≠ 0}|.
-/
theorem pairingFiber_nonzero_card_ge {m : ℕ} (hm : 2 ≤ m)
    (l : Fin 2 → V F m) (hl : LinearIndependent F l) (γ : Fin 2 → F) :
    fieldCard F ^ (m - 2) - 1 ≤ Fintype.card {v : PairingFiber l γ // v.val ≠ 0} := by
  rw [Fintype.card_subtype_compl, card_dotMap_fiber hm l hl]
  exact Nat.sub_le_sub_left (pairingFiber_zero_card_le l γ) _

/-- Intersecting any affine fiber with a scalar line retains at most `q` points. The statement also permits the zero line. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; l ∈ {0,…,2-1} → V(F, m); γ ∈ {0,…,2-1} → F; a ∈ V(F, m), we have

|{v ∈ PairingFiber(l, γ) | ∃ c ∈ F, c · a = v}| ≤ |F|.
-/
theorem pairingFiber_line_card_le {m : ℕ} (l : Fin 2 → V F m)
    (γ : Fin 2 → F) (a : V F m) :
    Fintype.card {v : PairingFiber l γ // ∃ c : F, c • a = v.val} ≤ fieldCard F := by
  let f : {v : PairingFiber l γ // ∃ c : F, c • a = v.val} → F :=
    fun v => v.property.choose
  apply Fintype.card_le_of_injective f
  intro v w h
  apply Subtype.ext
  apply Subtype.ext
  exact v.property.choose_spec.symm.trans ((congrArg (fun c : F => c • a) h).trans
    w.property.choose_spec)

/-- Excluding a scalar line from a pairing fiber leaves at least `q^(m-2)-q` possible second columns. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; l ∈ {0,…,2-1} → V(F, m); γ ∈ {0,…,2-1} → F; a ∈ V(F, m), assume 2 ≤ m; LinearIndependent(F, l). Then

(|F|)^(m − 2) - |F| ≤ |{v ∈ PairingFiber(l, γ) | ¬ (∃ c ∈ F, c · a = v)}|.
-/
theorem pairingFiber_off_line_card_ge {m : ℕ} (hm : 2 ≤ m)
    (l : Fin 2 → V F m) (hl : LinearIndependent F l) (γ : Fin 2 → F) (a : V F m) :
    fieldCard F ^ (m - 2) - fieldCard F ≤
      Fintype.card {v : PairingFiber l γ // ¬∃ c : F, c • a = v.val} := by
  rw [Fintype.card_subtype_compl, card_dotMap_fiber hm l hl]
  exact Nat.sub_le_sub_left (pairingFiber_line_card_le l γ a) _

/-- Nonzero first columns followed by second columns outside their line. -/
/- Mathematical definition (normal notation): Choose a nonzero first column with the prescribed row pairings, then choose a second column with its prescribed pairings outside the first column's scalar span. -/
abbrev IndependentPairingChoices {m : ℕ} (l : Fin 2 → V F m)
    (γ₀ γ₁ : Fin 2 → F) :=
  Σ a : {v : PairingFiber l γ₀ // v.val ≠ 0},
    {v : PairingFiber l γ₁ // ¬∃ c : F, c • a.val.val = v.val}

/-- Independent column pairs with a prescribed two-by-two pairing matrix. -/
/-
Mathematical definition (normal notation): For m ∈ ℕ; l ∈ {0,…,2-1} → V(F, m); γ₀, γ₁ ∈ {0,…,2-1} → F, define

IndependentPairingPairs(l, γ₀, γ₁) := {p ∈ V(F, m) × V(F, m) | dotMap(l, (p)₁) = γ₀ ∧ dotMap(l, (p)₂) = γ₁ ∧ LinearIndependent(F, ((p)₁, (p)₂))}.
-/
abbrev IndependentPairingPairs {m : ℕ} (l : Fin 2 → V F m)
    (γ₀ γ₁ : Fin 2 → F) :=
  {p : V F m × V F m // dotMap l p.1 = γ₀ ∧ dotMap l p.2 = γ₁ ∧
    LinearIndependent F ![p.1, p.2]}

/-- The sequential exclusion procedure enumerates precisely the compatible independent column pairs. -/
/- Mathematical definition (normal notation): The sequential choice of a nonzero first column and a second outside its span is in bijection with independent ordered column pairs satisfying the two prescribed pairing vectors. -/
def independentPairingEquiv {m : ℕ} (l : Fin 2 → V F m) (γ₀ γ₁ : Fin 2 → F) :
    IndependentPairingChoices l γ₀ γ₁ ≃ IndependentPairingPairs l γ₀ γ₁ where
  toFun p := ⟨(p.1.val.val, p.2.val.val), p.1.val.property, p.2.val.property,
    (LinearIndependent.pair_iff' p.1.property).2 (by
      intro c hc
      exact p.2.property ⟨c, hc⟩)⟩
  invFun p := ⟨⟨⟨p.val.1, p.property.1⟩, p.property.2.2.ne_zero 0⟩,
    ⟨⟨p.val.2, p.property.2.1⟩, by
      rintro ⟨c, hc⟩
      exact (LinearIndependent.pair_iff' (p.property.2.2.ne_zero 0)).1 p.property.2.2 c hc⟩⟩
  left_inv p := by cases p; rfl
  right_inv p := rfl

/-- The uniform lower orbit-count bound, valid for every prescribed pairing matrix, including rank zero and rank one. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; l ∈ {0,…,2-1} → V(F, m); γ₀, γ₁ ∈ {0,…,2-1} → F, assume 2 ≤ m; LinearIndependent(F, l). Then

((|F|)^(m − 2) - 1) · ((|F|)^(m − 2) - |F|) ≤ |IndependentPairingPairs(l, γ₀, γ₁)|.
-/
theorem independentPairingPairs_card_ge {m : ℕ} (hm : 2 ≤ m)
    (l : Fin 2 → V F m) (hl : LinearIndependent F l) (γ₀ γ₁ : Fin 2 → F) :
    (fieldCard F ^ (m - 2) - 1) * (fieldCard F ^ (m - 2) - fieldCard F) ≤
      Fintype.card (IndependentPairingPairs l γ₀ γ₁) := by
  rw [← Fintype.card_congr (independentPairingEquiv l γ₀ γ₁), Fintype.card_sigma]
  calc
    _ ≤ Fintype.card {v : PairingFiber l γ₀ // v.val ≠ 0} *
        (fieldCard F ^ (m - 2) - fieldCard F) :=
      Nat.mul_le_mul_right _ (pairingFiber_nonzero_card_ge hm l hl γ₀)
    _ = ∑ _ : {v : PairingFiber l γ₀ // v.val ≠ 0}, (fieldCard F ^ (m - 2) - fieldCard F) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun a _ => pairingFiber_off_line_card_ge hm l hl γ₁ a.val.val)

/-- Forgetting independence embeds the orbit into two full affine fibers. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; l ∈ {0,…,2-1} → V(F, m); γ₀, γ₁ ∈ {0,…,2-1} → F, assume 2 ≤ m; LinearIndependent(F, l). Then

|IndependentPairingPairs(l, γ₀, γ₁)| ≤ ((|F|)^(m − 2))².
-/
theorem independentPairingPairs_card_le {m : ℕ} (hm : 2 ≤ m)
    (l : Fin 2 → V F m) (hl : LinearIndependent F l) (γ₀ γ₁ : Fin 2 → F) :
    Fintype.card (IndependentPairingPairs l γ₀ γ₁) ≤ (fieldCard F ^ (m - 2)) ^ 2 := by
  let e : IndependentPairingPairs l γ₀ γ₁ → PairingFiber l γ₀ × PairingFiber l γ₁ :=
    fun p => (⟨p.val.1, p.property.1⟩, ⟨p.val.2, p.property.2.1⟩)
  have h := Fintype.card_le_of_injective e (by
    intro p q h
    apply Subtype.ext
    exact Prod.ext (congrArg (fun x => x.1.val) h) (congrArg (fun x => x.2.val) h))
  simpa only [Fintype.card_prod, card_dotMap_fiber hm l hl, pow_two] using h

/-- Exactly `Q-q` nonzero vectors are independent from a fixed nonzero vector: its projective class contains exactly `q-1` members. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; a ∈ U(F, m), we have

|{b ∈ U(F, m) | LinearIndependent(F, (a, b))}| = (|F|)ᵐ - |F|.
-/
theorem independent_partner_card {m : ℕ} (a : U F m) :
    Fintype.card {b : U F m // LinearIndependent F ![a.val, b.val]} = fieldCard F ^ m - fieldCard F := by
  have he : {b : U F m // LinearIndependent F ![a.val, b.val]} ≃
      {b : U F m // ¬ projectiveRel a b} :=
    Equiv.subtypeEquivRight (fun b => by
      rw [LinearIndependent.pair_iff' a.property]
      simp only [projectiveRel, not_exists, ne_eq, eq_comm])
  rw [Fintype.card_congr he, Fintype.card_subtype_compl, nonzero_vector_card,
    projectiveRel_card]
  have := fieldCard_ge_two (F := F)
  omega

/-- There are exactly `(Q-1)(Q-q)` ordered independent nonzero row pairs. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ, we have

|IndependentRowPair(F, m)| = ((|F|)ᵐ - 1) · ((|F|)ᵐ - |F|).
-/
theorem independentRowPair_card (m : ℕ) :
    Fintype.card (IndependentRowPair F m) = (fieldCard F ^ m - 1) * (fieldCard F ^ m - fieldCard F) := by
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun (a b : U F m) => LinearIndependent F ![a.val, b.val])), Fintype.card_sigma]
  simp only [independent_partner_card, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, nonzero_vector_card]

/-- The target set of the simultaneous two-row/two-column GL action with prescribed pairing matrix `S`. The row pair and column pair are ordered. -/
/- Mathematical definition (normal notation): A compatible quadruple with matrix S ∈ F^(2 × 2) consists of an ordered independent pair of nonzero rows and an ordered independent pair of columns, such that the inner product of row i with column j is Sᵢⱼ. -/
abbrev CompatibleQuadruples {m : ℕ} (S : Matrix (Fin 2) (Fin 2) F) :=
  Σ p : IndependentRowPair F m,
    IndependentPairingPairs ![p.val.1.val, p.val.2.val]
      (fun i => S i 0) (fun i => S i 1)

/-- Uniform lower bound for the complete compatible orbit carrier. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; S ∈ F^({0,…,2−1} × {0,…,2−1}), assume 2 ≤ m. Then

(((|F|)ᵐ - 1) · ((|F|)ᵐ - |F|)) · (((|F|)^(m − 2) - 1) · ((|F|)^(m − 2) - |F|)) ≤ |CompatibleQuadruples(m = m, S)|.
-/
theorem compatibleQuadruples_card_ge {m : ℕ} (hm : 2 ≤ m)
    (S : Matrix (Fin 2) (Fin 2) F) :
    ((fieldCard F ^ m - 1) * (fieldCard F ^ m - fieldCard F)) *
      ((fieldCard F ^ (m - 2) - 1) * (fieldCard F ^ (m - 2) - fieldCard F)) ≤
      Fintype.card (CompatibleQuadruples (m := m) S) := by
  rw [Fintype.card_sigma, ← independentRowPair_card]
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using
    (Finset.sum_le_sum (s := Finset.univ)
      (fun (p : IndependentRowPair F m) _ => independentPairingPairs_card_ge hm _ p.property
        (fun i => S i 0) (fun i => S i 1)))

/-- Uniform upper bound for the complete compatible orbit carrier. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; S ∈ F^({0,…,2−1} × {0,…,2−1}), assume 2 ≤ m. Then

|CompatibleQuadruples(m = m, S)| ≤ (((|F|)ᵐ - 1) · ((|F|)ᵐ - |F|)) · ((|F|)^(m − 2))².
-/
theorem compatibleQuadruples_card_le {m : ℕ} (hm : 2 ≤ m)
    (S : Matrix (Fin 2) (Fin 2) F) :
    Fintype.card (CompatibleQuadruples (m := m) S) ≤
      ((fieldCard F ^ m - 1) * (fieldCard F ^ m - fieldCard F)) * (fieldCard F ^ (m - 2)) ^ 2 := by
  rw [Fintype.card_sigma, ← independentRowPair_card]
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using
    (Finset.sum_le_sum (s := Finset.univ)
      (fun (p : IndependentRowPair F m) _ => independentPairingPairs_card_le hm _ p.property
        (fun i => S i 0) (fun i => S i 1)))

end

end CircuitCompiler
