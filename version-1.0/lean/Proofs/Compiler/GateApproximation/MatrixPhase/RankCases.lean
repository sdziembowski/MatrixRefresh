import Proofs.Compiler.GateApproximation.MatrixPhase.Counting



/-!
# The four exact binary rank cases

The four-corner moment uses two nonzero rows and two nonzero columns. Distinct binary vectors are independent; coincident vectors must have coincident prescribed outputs. These lemmas give the exact factors 16, 4, 4, and 2, including the zero probability of contradictory duplicate prescriptions.
-/
set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped Classical

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ ℕ; a, u ∈ V(F, m); v, c ∈ {0,…,s-1} → V(F, m), we have

|MatrixCompletion((a, a), v, (u, u), c)| = |MatrixCompletion((a), v, (u), c)|.
-/
theorem duplicate_row_completion_card {s : ℕ}
    (a u : V F m) (v c : Fin s → V F m) :
    Fintype.card (MatrixCompletion ![a,a] v ![u,u] c) =
      Fintype.card (MatrixCompletion ![a] v ![u] c) := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro A
  simp [Fin.forall_fin_two]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ℕ; a, u ∈ {0,…,r-1} → V(F, m); v, c ∈ V(F, m), we have

|MatrixCompletion(a, (v, v), u, (c, c))| = |MatrixCompletion(a, (v), u, (c))|.
-/
theorem duplicate_column_completion_card {r : ℕ}
    (a u : Fin r → V F m) (v c : V F m) :
    Fintype.card (MatrixCompletion a ![v,v] u ![c,c]) =
      Fintype.card (MatrixCompletion a ![v] u ![c]) := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro A
  simp [Fin.forall_fin_two]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ ℕ; a, u₀, u₁ ∈ V(F, m); v, c ∈ {0,…,s-1} → V(F, m), assume u₀ ≠ u₁. Then

|MatrixCompletion((a, a), v, (u₀, u₁), c)| = 0.
-/
theorem contradictory_row_completion_card {s : ℕ}
    (a u₀ u₁ : V F m) (v c : Fin s → V F m) (hu : u₀ ≠ u₁) :
    Fintype.card (MatrixCompletion ![a,a] v ![u₀,u₁] c) = 0 := by
  letI : IsEmpty (MatrixCompletion ![a,a] v ![u₀,u₁] c) := ⟨by
    intro A
    exact hu ((A.property.1 0).symm.trans (A.property.1 1))⟩
  exact Fintype.card_eq_zero

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ℕ; a, u ∈ {0,…,r-1} → V(F, m); v, c₀, c₁ ∈ V(F, m), assume c₀ ≠ c₁. Then

|MatrixCompletion(a, (v, v), u, (c₀, c₁))| = 0.
-/
theorem contradictory_column_completion_card {r : ℕ}
    (a u : Fin r → V F m) (v c₀ c₁ : V F m) (hc : c₀ ≠ c₁) :
    Fintype.card (MatrixCompletion a ![v,v] u ![c₀,c₁]) = 0 := by
  letI : IsEmpty (MatrixCompletion a ![v,v] u ![c₀,c₁]) := ⟨by
    intro A
    exact hc ((A.property.2 0).symm.trans (A.property.2 1))⟩
  exact Fintype.card_eq_zero

/-- Rank `(2,2)`: four independent prescriptions give coefficient `16/Q⁴`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a₀, a₁, v₀, v₁ ∈ U(F, m); u₀, u₁, c₀, c₁ ∈ V(F, m), assume |F| = 2; 2 ≤ m; a₀ ≠ a₁; v₀ ≠ v₁. Then

|MatrixCompletion((a₀, a₁), (v₀, v₁), (u₀, u₁), (c₀, c₁))| / |F^({0,…,m−1} × {0,…,m−1})| = { 16 / (|F|ᵐ)⁴ if ExtensionCompatible((a₀, a₁), (v₀, v₁), (u₀, u₁), (c₀, c₁)),; 0 otherwise }.
-/
theorem rank_two_two_probability (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a₀ a₁ v₀ v₁ : U F m) (ha : a₀ ≠ a₁) (hv : v₀ ≠ v₁)
    (u₀ u₁ c₀ c₁ : V F m) :
    (Fintype.card (MatrixCompletion ![a₀.val,a₁.val] ![v₀.val,v₁.val]
      ![u₀,u₁] ![c₀,c₁]) : ℝ) / Fintype.card (Matrix (Fin m) (Fin m) F) =
      if ExtensionCompatible ![a₀.val,a₁.val] ![v₀.val,v₁.val] ![u₀,u₁] ![c₀,c₁]
      then 16 / (vectorCard F m : ℝ) ^ 4 else 0 := by
  simpa [show (2 : ℝ)^4 = 16 by norm_num] using binary_completion_probability hq hm hm
    ![a₀.val,a₁.val] ![v₀.val,v₁.val] ![u₀,u₁] ![c₀,c₁]
    (binary_pair_independent hq a₀ a₁ ha) (binary_pair_independent hq v₀ v₁ hv)

/-- Rank `(1,2)`: the duplicate row imposes only one row prescription. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, v₀, v₁ ∈ U(F, m); u, c₀, c₁ ∈ V(F, m), assume |F| = 2; 2 ≤ m; v₀ ≠ v₁. Then

|MatrixCompletion((a, a), (v₀, v₁), (u, u), (c₀, c₁))| / |F^({0,…,m−1} × {0,…,m−1})| = { 4 / (|F|ᵐ)³ if ExtensionCompatible((a, a), (v₀, v₁), (u, u), (c₀, c₁)),; 0 otherwise }.
-/
theorem rank_one_two_probability (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a v₀ v₁ : U F m) (hv : v₀ ≠ v₁) (u c₀ c₁ : V F m) :
    (Fintype.card (MatrixCompletion ![a.val,a.val] ![v₀.val,v₁.val]
      ![u,u] ![c₀,c₁]) : ℝ) / Fintype.card (Matrix (Fin m) (Fin m) F) =
      if ExtensionCompatible ![a.val,a.val] ![v₀.val,v₁.val] ![u,u] ![c₀,c₁]
      then 4 / (vectorCard F m : ℝ) ^ 3 else 0 := by
  rw [duplicate_row_completion_card]
  have h := binary_completion_probability hq (show 1 ≤ m by omega) hm
    ![a.val] ![v₀.val,v₁.val] ![u] ![c₀,c₁]
    (linearIndependent_unique_iff.mpr a.property) (binary_pair_independent hq v₀ v₁ hv)
  simpa [ExtensionCompatible, Fin.forall_fin_two, Fin.forall_fin_one,
    show (2 : ℝ)^2 = 4 by norm_num] using h

/-- Rank `(2,1)`: the duplicate column imposes only one column prescription. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a₀, a₁, v ∈ U(F, m); u₀, u₁, c ∈ V(F, m), assume |F| = 2; 2 ≤ m; a₀ ≠ a₁. Then

|MatrixCompletion((a₀, a₁), (v, v), (u₀, u₁), (c, c))| / |F^({0,…,m−1} × {0,…,m−1})| = { 4 / (|F|ᵐ)³ if ExtensionCompatible((a₀, a₁), (v, v), (u₀, u₁), (c, c)),; 0 otherwise }.
-/
theorem rank_two_one_probability (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a₀ a₁ v : U F m) (ha : a₀ ≠ a₁) (u₀ u₁ c : V F m) :
    (Fintype.card (MatrixCompletion ![a₀.val,a₁.val] ![v.val,v.val]
      ![u₀,u₁] ![c,c]) : ℝ) / Fintype.card (Matrix (Fin m) (Fin m) F) =
      if ExtensionCompatible ![a₀.val,a₁.val] ![v.val,v.val] ![u₀,u₁] ![c,c]
      then 4 / (vectorCard F m : ℝ) ^ 3 else 0 := by
  rw [duplicate_column_completion_card]
  have h := binary_completion_probability hq hm (show 1 ≤ m by omega)
    ![a₀.val,a₁.val] ![v.val] ![u₀,u₁] ![c]
    (binary_pair_independent hq a₀ a₁ ha) (linearIndependent_unique_iff.mpr v.property)
  simpa [ExtensionCompatible, Fin.forall_fin_two, Fin.forall_fin_one,
    show (2 : ℝ)^2 = 4 by norm_num] using h

/-- Rank `(1,1)`: one row and one column prescription give coefficient `2/Q²`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, v ∈ U(F, m); u, c ∈ V(F, m), assume |F| = 2; 1 ≤ m. Then

|MatrixCompletion((a, a), (v, v), (u, u), (c, c))| / |F^({0,…,m−1} × {0,…,m−1})| = { 2 / (|F|ᵐ)² if (a · c) = (u · v),; 0 otherwise }.
-/
theorem rank_one_one_probability (hq : fieldCard F = 2) (hm : 1 ≤ m)
    (a v : U F m) (u c : V F m) :
    (Fintype.card (MatrixCompletion ![a.val,a.val] ![v.val,v.val]
      ![u,u] ![c,c]) : ℝ) / Fintype.card (Matrix (Fin m) (Fin m) F) =
      if dot a.val c = dot u v.val then 2 / (vectorCard F m : ℝ) ^ 2 else 0 := by
  rw [duplicate_row_completion_card, duplicate_column_completion_card]
  have h := binary_completion_probability hq hm hm ![a.val] ![v.val] ![u] ![c]
    (linearIndependent_unique_iff.mpr a.property) (linearIndependent_unique_iff.mpr v.property)
  simpa [ExtensionCompatible, Fin.forall_fin_one] using h

/-- All four rank cases assembled before averaging. The factor `Q⁴` is the normalization from the enlarged table and inserted uniform row images. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a₀, a₁, v₀, v₁ ∈ U(F, m); u₀, u₁, c₀, c₁ ∈ V(F, m), assume |F| = 2; 2 ≤ m; ExtensionCompatible((a₀, a₁), (v₀, v₁), (u₀, u₁), (c₀, c₁)). Then

(|F|ᵐ)⁴ · (|MatrixCompletion((a₀, a₁), (v₀, v₁), (u₀, u₁), (c₀, c₁))| / |F^({0,…,m−1} × {0,…,m−1})|) = { { { { 2 · (|F|ᵐ)² if c₀ = c₁,; 0 otherwise } if v₀ = v₁,; 4 · |F|ᵐ otherwise } if u₀ = u₁,; 0 otherwise } if a₀ = a₁,; { { 4 · |F|ᵐ if c₀ = c₁,; 0 otherwise } if v₀ = v₁,; 16 otherwise } otherwise }.
-/
theorem scaled_completion_probability (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a₀ a₁ v₀ v₁ : U F m) (u₀ u₁ c₀ c₁ : V F m)
    (hcompat : ExtensionCompatible ![a₀.val,a₁.val] ![v₀.val,v₁.val]
      ![u₀,u₁] ![c₀,c₁]) :
    (vectorCard F m : ℝ)^4 * ((Fintype.card (MatrixCompletion ![a₀.val,a₁.val] ![v₀.val,v₁.val]
      ![u₀,u₁] ![c₀,c₁]) : ℝ) / Fintype.card (Matrix (Fin m) (Fin m) F)) =
    if a₀ = a₁ then
      if u₀ = u₁ then
        if v₀ = v₁ then
          if c₀ = c₁ then 2 * (vectorCard F m : ℝ)^2 else 0
        else 4 * (vectorCard F m : ℝ)
      else 0
    else if v₀ = v₁ then
      if c₀ = c₁ then 4 * (vectorCard F m : ℝ) else 0
    else 16 := by
  have hQ : (vectorCard F m : ℝ) ≠ 0 := by
    have h : 0 < vectorCard F m := by unfold vectorCard fieldCard; positivity
    exact_mod_cast h.ne'
  by_cases ha : a₀ = a₁
  · subst a₁
    simp only [ite_true]
    by_cases hu : u₀ = u₁
    · subst u₁
      simp only [ite_true]
      by_cases hv : v₀ = v₁
      · subst v₁
        simp only [ite_true]
        by_cases hc : c₀ = c₁
        · subst c₁
          rw [if_pos rfl, rank_one_one_probability hq (by omega)]
          have hdot : dot a₀.val c₀ = dot u₀ v₀.val := hcompat 0 0
          rw [if_pos hdot]
          field_simp
        · rw [if_neg hc, contradictory_column_completion_card _ _ _ _ _ hc]
          norm_num
      · rw [if_neg hv, rank_one_two_probability hq hm a₀ v₀ v₁ hv, if_pos hcompat]
        field_simp
    · rw [if_neg hu, contradictory_row_completion_card _ _ _ _ _ hu]
      norm_num
  · rw [if_neg ha]
    by_cases hv : v₀ = v₁
    · subst v₁
      simp only [ite_true]
      by_cases hc : c₀ = c₁
      · subst c₁
        rw [if_pos rfl, rank_two_one_probability hq hm a₀ a₁ v₀ ha, if_pos hcompat]
        field_simp
      · rw [if_neg hc, contradictory_column_completion_card _ _ _ _ _ hc]
        norm_num
    · rw [if_neg hv, rank_two_two_probability hq hm a₀ a₁ v₀ v₁ ha hv, if_pos hcompat]
      field_simp

/-- A signed pointwise comparison of the four rank coefficients. Only the collision terms use absolute values; the unrestricted main term keeps its sign. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Q, e ∈ ℝ; A, U, V, C ∈ Prop, assume 0 ≤ Q. Then

({ ({ ({ ({ 2 · Q² if C,; 0 otherwise }) if V,; 4 · Q otherwise }) if U,; 0 otherwise }) if A,; ({ ({ 4 · Q if C,; 0 otherwise }) if V,; 16 otherwise }) otherwise }) · e ≤ 16 · e + 16 · ({ |e| if A ∨ V,; 0 otherwise }) + 4 · Q · ({ |e| if A ∧ U,; 0 otherwise }) + 4 · Q · ({ |e| if V ∧ C,; 0 otherwise }) + 2 · Q² · ({ |e| if A ∧ U ∧ V ∧ C,; 0 otherwise }).
-/
theorem rank_coefficient_error (Q e : ℝ) (hQ : 0 ≤ Q) (A U V C : Prop) :
    (if A then (if U then (if V then (if C then 2*Q^2 else 0) else 4*Q) else 0)
      else (if V then (if C then 4*Q else 0) else 16)) * e ≤
      16*e + 16*(if A ∨ V then |e| else 0) +
        4*Q*(if A ∧ U then |e| else 0) +
        4*Q*(if V ∧ C then |e| else 0) +
        2*Q^2*(if A ∧ U ∧ V ∧ C then |e| else 0) := by
  have h₁ := mul_le_mul_of_nonneg_left (le_abs_self e) (show 0 ≤ 4*Q by positivity)
  have h₂ := mul_le_mul_of_nonneg_left (le_abs_self e) (show 0 ≤ 2*Q^2 by positivity)
  have h₃ := mul_nonneg hQ (abs_nonneg e)
  have h₄ := mul_nonneg (sq_nonneg Q) (abs_nonneg e)
  have h₅ := neg_abs_le e
  by_cases hA : A <;> by_cases hU : U <;> by_cases hV : V <;> by_cases hC : C <;>
    simp only [hA, hU, hV, hC, ite_true, ite_false, and_self, true_and, false_and,
      and_true, and_false, or_true, or_false, true_or, false_or, mul_zero, zero_mul] <;>
    nlinarith [abs_nonneg e]

end

end CircuitCompiler.RefreshAnalysis
