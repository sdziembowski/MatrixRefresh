import Proofs.Compiler.LocalComparisons.Framework.Composition
import Proofs.Compiler.GateApproximation.MatrixPhase.Factorization



/-!
# Adaptive one-wire comparison

This is the one-wire step of the signed composition proof. Local queries have bounded factorizations on the changed wire; every other query is independent of that wire once its incoming history and the other encodings are fixed. The proof carries the product of the local factors down the query tree.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace CircuitCompiler.Composition

open Refresh

namespace ErrorProcess

variable {A X Y : Type*} [Fintype A] [Fintype X] [Fintype Y]

/-- At local positions each answer has a bounded factorization. At all other positions the answer table is independent of the changed wire and its absolute answer sum is bounded. The final factor is one. -/
/- Mathematical definition (normal notation): At every position incident to the changed wire, each answer table has a chosen bounded product factorization with the specified budget. At other positions the table is independent of that wire and its absolute answer sum is bounded by the budget. Every terminal factor is one, and the conditions hold after every history. -/
def FactorControlled : {n : ℕ} → ErrorProcess A (X × Y) n →
    (Fin n → ℝ) → (Fin n → Bool) → Prop
  | 0, .stop leaf, _, _ => ∀ xy, leaf xy = 1
  | _ + 1, .query answerTable next, budget, localQuery =>
      (localQuery 0 = true → ∀ a,
        Nonempty (BoundedFactorization (fun x y => answerTable (x, y) a) (budget 0))) ∧
      (localQuery 0 = false → ∃ fixed : A → ℝ,
        (∀ xy a, answerTable xy a = fixed a) ∧ (∑ a, |fixed a|) ≤ budget 0) ∧
      ∀ a, FactorControlled (next a) (Fin.tail budget) (Fin.tail localQuery)

/-- One-wire comparison with an already accumulated factorization. This strong form is the induction invariant needed for adaptive local queries. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; P, Q ∈ 𝒟((X × Y)); L ∈ 𝒟(X); R ∈ 𝒟(Y); δ ∈ ℝ; process ∈ ErrorProcess(A, (X × Y), n); budget ∈ {0,…,n-1} → ℝ; localQuery ∈ {0,…,n-1} → Bool; f ∈ X → Y → ℝ; B ∈ ℝ; factor ∈ BoundedFactorization(f, B), assume 0 ≤ δ; ∀ a ∈ X → ℝ, ∀ b ∈ Y → ℝ, |𝔼_(xy ← P) [a((xy)₁) · b((xy)₂)] - 𝔼_(xy ← Q) [a((xy)₁) · b((xy)₂)]| ≤ δ · √(𝔼_(x ← L) [(a(x))²]) · √(𝔼_(y ← R) [(b(y))²]); ∀ i, 0 ≤ budget(i); process.FactorControlled(budget, localQuery); 0 ≤ B. Then

(∑ₕ (|𝔼_(xy ← P) [f((xy)₁, (xy)₂) · weight(process)(h, xy)] - 𝔼_(xy ← Q) [f((xy)₁, (xy)₂) · weight(process)(h, xy)]|)) ≤ δ · B · (|A|)^(localCount(localQuery)) · (∏ᵢ (budget(i))).
-/
theorem one_wire_bound_accumulated {n : ℕ}
    (P Q : FiniteDistribution (X × Y)) (L : FiniteDistribution X) (R : FiniteDistribution Y)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hscalar : ∀ a : X → ℝ, ∀ b : Y → ℝ,
      |P.expect (fun xy => a xy.1 * b xy.2) - Q.expect (fun xy => a xy.1 * b xy.2)| ≤
        δ * Real.sqrt (L.expect (fun x => a x ^ 2)) * Real.sqrt (R.expect (fun y => b y ^ 2)))
    (process : ErrorProcess A (X × Y) n)
    (budget : Fin n → ℝ) (localQuery : Fin n → Bool)
    (hbudget : ∀ i, 0 ≤ budget i)
    (hprocess : process.FactorControlled budget localQuery)
    (f : X → Y → ℝ) (B : ℝ) (hB : 0 ≤ B) (factor : BoundedFactorization f B) :
    (∑ h, |P.expect (fun xy => f xy.1 xy.2 * process.weight h xy) -
      Q.expect (fun xy => f xy.1 xy.2 * process.weight h xy)|) ≤
      δ * B * (Fintype.card A : ℝ) ^ localCount localQuery * (∏ i, budget i) := by
  classical
  induction process generalizing f B with
  | stop leaf =>
      simp only [FactorControlled] at hprocess
      simpa [Answers, weight, localCount, hprocess] using
        factor.discrepancy hB P Q L R hδ hscalar
  | @query n answerTable next ih =>
      simp only [FactorControlled] at hprocess
      simp only [Answers, Fintype.sum_prod_type, weight]
      cases hlocal : localQuery 0 with
      | true =>
          have hchild (a : A) :
              (∑ h, |P.expect (fun xy => f xy.1 xy.2 *
                    (answerTable xy a * (next a).weight h xy)) -
                Q.expect (fun xy => f xy.1 xy.2 *
                    (answerTable xy a * (next a).weight h xy))|) ≤
              δ * (B * budget 0) * (Fintype.card A : ℝ) ^ localCount (Fin.tail localQuery) *
                (∏ i, Fin.tail budget i) := by
            let childFactor := Classical.choice (hprocess.1 hlocal a)
            simpa only [mul_assoc] using ih a (Fin.tail budget) (Fin.tail localQuery)
              (fun i => hbudget i.succ) (hprocess.2.2 a)
              (fun x y => f x y * answerTable (x, y) a) (B * budget 0)
              (mul_nonneg hB (hbudget 0)) (factor.mul childFactor hB)
          calc
            _ ≤ ∑ _a : A, δ * (B * budget 0) *
                (Fintype.card A : ℝ) ^ localCount (Fin.tail localQuery) *
                  (∏ i, Fin.tail budget i) := Finset.sum_le_sum (fun a _ => hchild a)
            _ = _ := by
              rw [localCount_succ, hlocal, Fin.prod_univ_succ]
              simp only [↓reduceIte, pow_add, pow_one, Fin.tail_def,
                Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              ring
      | false =>
          obtain ⟨fixed, hfixed, hfixedBudget⟩ := hprocess.2.1 hlocal
          let tailBound := δ * B * (Fintype.card A : ℝ) ^ localCount (Fin.tail localQuery) *
            (∏ i, Fin.tail budget i)
          have htailNonneg : 0 ≤ tailBound := by
            dsimp [tailBound]
            exact mul_nonneg (mul_nonneg (mul_nonneg hδ hB)
              (pow_nonneg (Nat.cast_nonneg _) _))
              (Finset.prod_nonneg (fun i _ => hbudget i.succ))
          have hchild (a : A) :
              (∑ h, |P.expect (fun xy => f xy.1 xy.2 * (next a).weight h xy) -
                Q.expect (fun xy => f xy.1 xy.2 * (next a).weight h xy)|) ≤ tailBound :=
            ih a (Fin.tail budget) (Fin.tail localQuery) (fun i => hbudget i.succ)
              (hprocess.2.2 a) f B hB factor
          have hexpect (S : FiniteDistribution (X × Y)) (a : A) (h : Answers A n) :
              S.expect (fun xy => f xy.1 xy.2 * (answerTable xy a * (next a).weight h xy)) =
                fixed a * S.expect (fun xy => f xy.1 xy.2 * (next a).weight h xy) := by
            simp only [hfixed, FiniteDistribution.expect, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro xy _
            ring
          calc
            _ = ∑ a, |fixed a| *
                ∑ h, |P.expect (fun xy => f xy.1 xy.2 * (next a).weight h xy) -
                  Q.expect (fun xy => f xy.1 xy.2 * (next a).weight h xy)| := by
              simp only [hexpect, ← mul_sub, abs_mul, Finset.mul_sum]
            _ ≤ ∑ a, |fixed a| * tailBound :=
              Finset.sum_le_sum (fun a _ =>
                mul_le_mul_of_nonneg_left (hchild a) (abs_nonneg _))
            _ = (∑ a, |fixed a|) * tailBound := (Finset.sum_mul _ _ _).symm
            _ ≤ budget 0 * tailBound :=
              mul_le_mul_of_nonneg_right hfixedBudget htailNonneg
            _ = _ := by
              rw [localCount_succ, hlocal, Fin.prod_univ_succ]
              simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
              dsimp [tailBound]
              simp only [Fin.tail_def]
              ring

/-- The full signed transcript changes by at most the scalar wire discrepancy, one alphabet-size factor per incident gate, and all gate norm budgets. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; P, Q ∈ 𝒟((X × Y)); L ∈ 𝒟(X); R ∈ 𝒟(Y); δ ∈ ℝ; process ∈ ErrorProcess(A, (X × Y), n); budget ∈ {0,…,n-1} → ℝ; localQuery ∈ {0,…,n-1} → Bool, assume 0 ≤ δ; ∀ a ∈ X → ℝ, ∀ b ∈ Y → ℝ, |𝔼_(xy ← P) [a((xy)₁) · b((xy)₂)] - 𝔼_(xy ← Q) [a((xy)₁) · b((xy)₂)]| ≤ δ · √(𝔼_(x ← L) [(a(x))²]) · √(𝔼_(y ← R) [(b(y))²]); ∀ i, 0 ≤ budget(i); process.FactorControlled(budget, localQuery). Then

variationNorm(((h ↦ 𝔼_(ξ ← P) [weight(process)(h, ξ)] - 𝔼_(ω ← Q) [weight(process)(h, ω)]))) ≤ δ · (|A|)^(localCount(localQuery)) · (∏ᵢ (budget(i))).
-/
theorem one_wire_bound {n : ℕ}
    (P Q : FiniteDistribution (X × Y)) (L : FiniteDistribution X) (R : FiniteDistribution Y)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hscalar : ∀ a : X → ℝ, ∀ b : Y → ℝ,
      |P.expect (fun xy => a xy.1 * b xy.2) - Q.expect (fun xy => a xy.1 * b xy.2)| ≤
        δ * Real.sqrt (L.expect (fun x => a x ^ 2)) * Real.sqrt (R.expect (fun y => b y ^ 2)))
    (process : ErrorProcess A (X × Y) n)
    (budget : Fin n → ℝ) (localQuery : Fin n → Bool)
    (hbudget : ∀ i, 0 ≤ budget i)
    (hprocess : process.FactorControlled budget localQuery) :
    variationNorm (fun h => P.expect (process.weight h) - Q.expect (process.weight h)) ≤
      δ * (Fintype.card A : ℝ) ^ localCount localQuery * (∏ i, budget i) := by
  simpa only [one_mul, mul_one, variationNorm] using
    one_wire_bound_accumulated P Q L R δ hδ hscalar process budget localQuery
      hbudget hprocess (fun _ _ => 1) 1 (by norm_num) BoundedFactorization.one

/-- The displayed `K^d B^a δ` estimate when signed positions have budget `B` and all remaining positions have unit budget. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; P, Q ∈ 𝒟((X × Y)); L ∈ 𝒟(X); R ∈ 𝒟(Y); δ, B ∈ ℝ; process ∈ ErrorProcess(A, (X × Y), n); signed, localPositions ∈ Finset({0,…,n-1}), assume 0 ≤ δ; 0 ≤ B; ∀ a ∈ X → ℝ, ∀ b ∈ Y → ℝ, |𝔼_(xy ← P) [a((xy)₁) · b((xy)₂)] - 𝔼_(xy ← Q) [a((xy)₁) · b((xy)₂)]| ≤ δ · √(𝔼_(x ← L) [(a(x))²]) · √(𝔼_(y ← R) [(b(y))²]); process.FactorControlled(((i ↦ { B if i ∈ signed,; 1 otherwise })), ((i ↦ decide((i ∈ localPositions))))). Then

variationNorm(((h ↦ 𝔼_(ξ ← P) [weight(process)(h, ξ)] - 𝔼_(ω ← Q) [weight(process)(h, ω)]))) ≤ δ · (|A|)^(|localPositions|) · B^(|signed|).
-/
theorem one_wire_bound_pow {n : ℕ}
    (P Q : FiniteDistribution (X × Y)) (L : FiniteDistribution X) (R : FiniteDistribution Y)
    (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hscalar : ∀ a : X → ℝ, ∀ b : Y → ℝ,
      |P.expect (fun xy => a xy.1 * b xy.2) - Q.expect (fun xy => a xy.1 * b xy.2)| ≤
        δ * Real.sqrt (L.expect (fun x => a x ^ 2)) * Real.sqrt (R.expect (fun y => b y ^ 2)))
    (process : ErrorProcess A (X × Y) n) (signed localPositions : Finset (Fin n))
    (hprocess : process.FactorControlled
      (fun i => if i ∈ signed then B else 1)
      (fun i => decide (i ∈ localPositions))) :
    variationNorm (fun h => P.expect (process.weight h) - Q.expect (process.weight h)) ≤
      δ * (Fintype.card A : ℝ) ^ localPositions.card * B ^ signed.card := by
  classical
  have h := one_wire_bound P Q L R δ hδ hscalar process
    (fun i => if i ∈ signed then B else 1) (fun i => decide (i ∈ localPositions))
    (fun i => by (try dsimp); split_ifs <;> positivity) hprocess
  simpa only [localCount_mem, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const] using h

/-- A view may include arbitrary fixed other encodings, but its observation map must not disclose the wire whose label is being changed. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; V a set; P, Q ∈ 𝒟((X × Y)); L ∈ 𝒟(X); R ∈ 𝒟(Y); δ ∈ ℝ; process ∈ ErrorProcess(A, (X × Y), n); budget ∈ {0,…,n-1} → ℝ; localQuery ∈ {0,…,n-1} → Bool; observe ∈ Answers(A, n) → V, assume V is finite; 0 ≤ δ; ∀ a ∈ X → ℝ, ∀ b ∈ Y → ℝ, |𝔼_(xy ← P) [a((xy)₁) · b((xy)₂)] - 𝔼_(xy ← Q) [a((xy)₁) · b((xy)₂)]| ≤ δ · √(𝔼_(x ← L) [(a(x))²]) · √(𝔼_(y ← R) [(b(y))²]); ∀ i, 0 ≤ budget(i); process.FactorControlled(budget, localQuery). Then

variationNorm(((v ↦ ∑ₕ ((𝔼_(ω ← P) [weight(process)(h, ω)] - 𝔼_(ξ_(avg,6) ← Q) [weight(process)(h, ξ_(avg,6))]) · FiniteDistribution.pure(observe(h))(v))))) ≤ δ · (|A|)^(localCount(localQuery)) · (∏ᵢ (budget(i))).
-/
theorem one_wire_observed_bound {n : ℕ} {V : Type*} [Fintype V]
    (P Q : FiniteDistribution (X × Y)) (L : FiniteDistribution X) (R : FiniteDistribution Y)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hscalar : ∀ a : X → ℝ, ∀ b : Y → ℝ,
      |P.expect (fun xy => a xy.1 * b xy.2) - Q.expect (fun xy => a xy.1 * b xy.2)| ≤
        δ * Real.sqrt (L.expect (fun x => a x ^ 2)) * Real.sqrt (R.expect (fun y => b y ^ 2)))
    (process : ErrorProcess A (X × Y) n)
    (budget : Fin n → ℝ) (localQuery : Fin n → Bool)
    (hbudget : ∀ i, 0 ≤ budget i)
    (hprocess : process.FactorControlled budget localQuery)
    (observe : Answers A n → V) :
    variationNorm (fun v => ∑ h,
      (P.expect (process.weight h) - Q.expect (process.weight h)) *
        (FiniteDistribution.pure (observe h)).weight v) ≤
      δ * (Fintype.card A : ℝ) ^ localCount localQuery * (∏ i, budget i) :=
  (variationNorm_stochastic_le _ (fun h => FiniteDistribution.pure (observe h))).trans
    (one_wire_bound P Q L R δ hδ hscalar process budget localQuery hbudget hprocess)

end ErrorProcess

end CircuitCompiler.Composition
