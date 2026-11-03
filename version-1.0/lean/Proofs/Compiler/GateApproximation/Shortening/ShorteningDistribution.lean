import Proofs.Compiler.GateApproximation.Shortening.Shortening
import Proofs.Compiler.Foundations.MatrixRefreshing.Probability.StatisticalDistance



/-!
# The auxiliary distribution and ordinary-branch mass

The auxiliary encoding distribution is uniform on pairs with a nonzero left share and prescribed inner product, allowing a zero right share. Concrete embeddings relate actual encodings and accepted shortening inputs to this carrier. Their cardinalities give explicit statistical and failure-probability bounds.
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler.Shortening

open Refresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The manuscript's auxiliary long-encoding carrier. -/
/- Mathematical definition (normal notation): The auxiliary long-encoding carrier for secret z consists of pairs (U,V) with U ≠ 0 and U · V = z; the right share V is allowed to be zero. -/
abbrev Auxiliary (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (m : ℕ) (z : F) := Σ U : Refresh.U F m, {V : Refresh.V F m // dot U.val V = z}

/-- Every nonzero left share has exactly `q^(m-1)` auxiliary right partners. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; z ∈ F, we have

|Auxiliary(F, m, z)| = ((|F|)ᵐ - 1) · (|F|)^(m − 1).
-/
theorem auxiliary_card (m : ℕ) (z : F) :
    Fintype.card (Auxiliary F m z) = (fieldCard F ^ m - 1) * fieldCard F ^ (m - 1) := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [full_dot_fiber_card]
  simp [fieldCard]

/-- An actual nonzero-share encoding is also an auxiliary encoding. -/
/- Mathematical definition (normal notation): Include an actual encoding of z in the auxiliary carrier by forgetting only the certificate that its right share is nonzero. The inclusion is injective. -/
def actualEmbedding {m : ℕ} (z : F) : Fiber F m z ↪ Auxiliary F m z where
  toFun p := ⟨p.val.L, ⟨p.val.R.val, p.property⟩⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    apply State.ext
    · exact congrArg (fun p : Auxiliary F m z => p.1) h
    · apply Subtype.ext
      exact congrArg (fun p : Auxiliary F m z => p.2.val) h

/-- There are auxiliary encodings whenever there are actual encodings. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; z ∈ F, assume Fiber(F, m, z) ≠ ∅. Then

Auxiliary(F, m, z) ≠ ∅.
-/
theorem auxiliary_nonempty {m : ℕ} (z : F) [Nonempty (Fiber F m z)] :
    Nonempty (Auxiliary F m z) := by
  classical
  exact ⟨actualEmbedding z (Classical.choice inferInstance)⟩

omit [Fintype F] [DecidableEq F] in
/-- Appending a tail cannot erase a nonzero head. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; A ∈ U(F, n); B ∈ V(F, t), we have

Fin.append(A, B) ≠ 0.
-/
theorem append_nonzero {n t : ℕ} (A : U F n) (B : V F t) :
    Fin.append A.val B ≠ 0 := by
  intro h
  apply A.property
  funext i
  have hi := congrFun h (Fin.castAdd t i)
  simpa using hi

/-- Place an ordinary-branch long encoding on the full auxiliary carrier. -/
/- Mathematical definition (normal notation): Concatenate the left and right blocks of an accepted shortening record to obtain an auxiliary long pair encoding z. The nonzero left head ensures the left share is nonzero, and the concatenation map is injective. -/
def acceptedEmbedding {n t : ℕ} (c ε z : F) :
    Accepted F n t c ε z ↪ Auxiliary F (n + t) z where
  toFun p := ⟨⟨Fin.append p.val.A.val p.val.B, append_nonzero p.val.A p.val.B⟩,
    ⟨Fin.append p.val.C p.val.D, by rw [append_dot]; exact p.property.1⟩⟩
  inj' := by
    intro a b h
    have hL := congrArg (fun p : Auxiliary F (n + t) z => p.1.val) h
    have hR := congrArg (fun p : Auxiliary F (n + t) z => p.2.val) h
    apply Subtype.ext
    apply Data.ext
    · apply Subtype.ext
      funext i
      simpa using congrFun hL (Fin.castAdd t i)
    · funext i
      simpa using congrFun hL (Fin.natAdd n i)
    · funext i
      simpa using congrFun hR (Fin.castAdd t i)
    · funext i
      simpa using congrFun hR (Fin.natAdd n i)

/-- The auxiliary distribution differs from the actual uniform encoding by at most the fraction of zero-right auxiliary encodings. This exact rational count is valid without introducing an unspecified asymptotic constant. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; z ∈ F, assume Fiber(F, m, z) ≠ ∅; Auxiliary(F, m, z) ≠ ∅. Then

δ(𝒰_(Auxiliary(F, m, z)), (actualEmbedding(z)_*𝒰_(Fiber(F, m, z)))) ≤ 1 - |Fiber(F, m, z)| / (|F|)ᵐ - 1 · (|F|)^(m − 1).
-/
theorem auxiliary_actual_distance_card {m : ℕ} (z : F)
    [Nonempty (Fiber F m z)] [Nonempty (Auxiliary F m z)] :
    statisticalDistance (FiniteDistribution.uniform : FiniteDistribution (Auxiliary F m z))
      ((FiniteDistribution.uniform : FiniteDistribution (Fiber F m z)).map (actualEmbedding z)) ≤
      1 - (Fintype.card (Fiber F m z) : ℝ) /
        ((fieldCard F ^ m - 1 : ℕ) * fieldCard F ^ (m - 1) : ℕ) := by
  simpa only [auxiliary_card] using
    MatrixRefresh.uniform_embedding_statisticalDistance (actualEmbedding (F := F) (m := m) z)

/-- The exact accepted mass on the auxiliary long-encoding carrier, expressed as a ratio of proven finite counts. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F, define

acceptanceMass(c, ε, z) := |Fiber(F, n, (c + ε · z))| · (|F|)^(2 · t) / (|F|)^(n + t) - 1 · (|F|)^(n + t − 1).
-/
noncomputable def acceptanceMass {n t : ℕ} (c ε z : F) : ℝ :=
  (Fintype.card (Fiber F n (c + ε * z)) : ℝ) * (fieldCard F : ℝ) ^ (2 * t) /
    (((fieldCard F ^ (n + t) - 1 : ℕ) * fieldCard F ^ (n + t - 1) : ℕ) : ℝ)

/-- Replacing the auxiliary encoding by the exact accepted canonical experiment costs at most its failure probability `1 - acceptanceMass`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F, assume ε ≠ 0; Accepted(F, n, t, c, ε, z) ≠ ∅; Auxiliary(F, (n + t), z) ≠ ∅. Then

δ(𝒰_(Auxiliary(F, (n + t), z)), (acceptedEmbedding(c, ε, z)_*𝒰_(Accepted(F, n, t, c, ε, z)))) ≤ 1 - acceptanceMass(n = n, t = t, c, ε, z).
-/
theorem auxiliary_accepted_distance {n t : ℕ} (c ε z : F) (hε : ε ≠ 0)
    [Nonempty (Accepted F n t c ε z)] [Nonempty (Auxiliary F (n + t) z)] :
    statisticalDistance (FiniteDistribution.uniform : FiniteDistribution (Auxiliary F (n + t) z))
      ((FiniteDistribution.uniform : FiniteDistribution (Accepted F n t c ε z)).map (acceptedEmbedding c ε z)) ≤
      1 - acceptanceMass (n := n) (t := t) c ε z := by
  have h := MatrixRefresh.uniform_embedding_statisticalDistance
    (acceptedEmbedding (n := n) (t := t) c ε z)
  simpa only [acceptanceMass, auxiliary_card, accepted_card c ε z hε,
    Nat.cast_mul, Nat.cast_pow] using h

/-- The auxiliary discrepancy is at most `q^(1-m)`, written without negative natural exponents. In the nonzero-secret case the exact discrepancy is zero. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; z ∈ F, assume 2 ≤ m; Fiber(F, m, z) ≠ ∅; Auxiliary(F, m, z) ≠ ∅. Then

δ(𝒰_(Auxiliary(F, m, z)), (actualEmbedding(z)_*𝒰_(Fiber(F, m, z)))) ≤ 1 / (|F|)^(m − 1).
-/
theorem auxiliary_actual_distance {m : ℕ} (hm : 2 ≤ m) (z : F)
    [Nonempty (Fiber F m z)] [Nonempty (Auxiliary F m z)] :
    statisticalDistance (FiniteDistribution.uniform : FiniteDistribution (Auxiliary F m z))
      ((FiniteDistribution.uniform : FiniteDistribution (Fiber F m z)).map (actualEmbedding z)) ≤
      (1 : ℝ) / (fieldCard F : ℝ) ^ (m - 1) := by
  have hN : 0 < fieldCard F ^ m - 1 := by have := four_le_pow (F := F) hm; omega
  have hP : 0 < fieldCard F ^ (m - 1) := Nat.pow_pos (fieldCard_pos (F := F))
  have hNr : (0 : ℝ) < (fieldCard F ^ m - 1 : ℕ) := by exact_mod_cast hN
  have hPr : (0 : ℝ) < fieldCard F ^ (m - 1) := by exact_mod_cast hP
  refine (auxiliary_actual_distance_card z).trans ?_
  by_cases hz : z = 0
  · subst z
    rw [fiber_card_zero, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega :
      1 ≤ fieldCard F ^ (m - 1))]
    push_cast
    have hNr' : ((fieldCard F ^ m - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hNr
    have hPr' : (fieldCard F : ℝ) ^ (m - 1) ≠ 0 := ne_of_gt hPr
    field_simp
    nlinarith
  · rw [fiber_card_of_ne_zero m z hz]
    have hden : (((fieldCard F ^ m - 1) * fieldCard F ^ (m - 1) : ℕ) : ℝ) ≠ 0 := by
      positivity
    rw [div_self hden, sub_self]
    positivity

/-- For a nonzero represented value, allowing zero right shares adds no mass. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; z ∈ F, assume z ≠ 0; Fiber(F, m, z) ≠ ∅; Auxiliary(F, m, z) ≠ ∅. Then

δ(𝒰_(Auxiliary(F, m, z)), (actualEmbedding(z)_*𝒰_(Fiber(F, m, z)))) = 0.
-/
theorem auxiliary_actual_distance_zero {m : ℕ} (z : F) (hz : z ≠ 0)
    [Nonempty (Fiber F m z)] [Nonempty (Auxiliary F m z)] :
    statisticalDistance (FiniteDistribution.uniform : FiniteDistribution (Auxiliary F m z))
      ((FiniteDistribution.uniform : FiniteDistribution (Fiber F m z)).map (actualEmbedding z)) = 0 := by
  apply le_antisymm _ (statisticalDistance_nonneg _ _)
  have h := auxiliary_actual_distance_card (m := m) z
  rw [fiber_card_of_ne_zero m z hz] at h
  have hcard : (0 : ℝ) < Fintype.card (Fiber F m z) := by
    exact_mod_cast Fintype.card_pos
  rw [fiber_card_of_ne_zero m z hz] at hcard
  simpa only [div_self (ne_of_gt hcard), sub_self] using h

/-- A real-arithmetic estimate for the exact finite counting ratio. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For N, P, H ∈ ℝ, assume 1 < N; 1 ≤ P; 1 ≤ H. Then

1 - (1 / N + 1 / P) ≤ ((N - 1) · (P - 1) · H²) / ((N · H - 1) · (P · H)).
-/
private theorem ratio_lower (N P H : ℝ) (hN : 1 < N) (hP : 1 ≤ P) (hH : 1 ≤ H) :
    1 - (1 / N + 1 / P) ≤
      ((N - 1) * (P - 1) * H ^ 2) / ((N * H - 1) * (P * H)) := by
  have hN0 : 0 < N := lt_trans zero_lt_one hN
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hNH : 0 < N * H - 1 := by nlinarith
  calc
    1 - (1 / N + 1 / P) ≤ ((N - 1) * (P - 1)) / (N * P) := by
      apply (le_div_iff₀ (mul_pos hN0 hP0)).2
      field_simp
      nlinarith
    _ = ((N - 1) * (P - 1) * H ^ 2) / ((N * H) * (P * H)) := by
      field_simp
    _ ≤ ((N - 1) * (P - 1) * H ^ 2) / ((N * H - 1) * (P * H)) := by
      apply div_le_div_of_nonneg_left
      · exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hN.le)
          (sub_nonneg.mpr hP)) (sq_nonneg H)
      · exact mul_pos hNH (mul_pos hP0 hH0)
      · nlinarith

/-- The exact acceptance mass with all integer subtraction converted to real arithmetic, using `H = q^t` for the two free tails. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F, assume 2 ≤ n. Then

acceptanceMass(n = n, t = t, c, ε, z) = (((|F|)ⁿ - 1) · ({ (|F|)^(n − 1) - 1 if c + ε · z = 0,; (|F|)^(n − 1) otherwise }) · ((|F|)ᵗ)²) / (((|F|)ⁿ · (|F|)ᵗ - 1) · ((|F|)^(n − 1) · (|F|)ᵗ)).
-/
theorem acceptanceMass_eq {n t : ℕ} (hn : 2 ≤ n) (c ε z : F) :
    acceptanceMass (n := n) (t := t) c ε z =
      (((fieldCard F : ℝ) ^ n - 1) *
        (if c + ε * z = 0 then (fieldCard F : ℝ) ^ (n - 1) - 1
          else (fieldCard F : ℝ) ^ (n - 1)) * ((fieldCard F : ℝ) ^ t) ^ 2) /
      (((fieldCard F : ℝ) ^ n * (fieldCard F : ℝ) ^ t - 1) *
        ((fieldCard F : ℝ) ^ (n - 1) * (fieldCard F : ℝ) ^ t)) := by
  have hn1 : 1 ≤ fieldCard F ^ n := by have := four_le_pow (F := F) hn; omega
  have hnt1 : 1 ≤ fieldCard F ^ (n + t) := Nat.one_le_pow _ _ (by have := fieldCard_ge_two (F := F); omega)
  have hpred1 : 1 ≤ fieldCard F ^ (n - 1) := by have := two_le_pow_pred (F := F) hn; omega
  have hindex : n + t - 1 = (n - 1) + t := by omega
  unfold acceptanceMass
  rw [fiber_card]
  by_cases hz : c + ε * z = 0
  · simp only [hz, ite_true, Nat.cast_mul, Nat.cast_sub hn1, Nat.cast_sub hnt1,
      Nat.cast_sub hpred1, Nat.cast_pow, Nat.cast_one]
    simp only [hindex, pow_add, two_mul, pow_two]
  · simp only [hz, ite_false, Nat.cast_mul, Nat.cast_sub hn1, Nat.cast_sub hnt1,
      Nat.cast_pow, Nat.cast_one]
    simp only [hindex, pow_add, two_mul, pow_two]

/-- Uniform in the gate's represented values and affine parameters, ordinary branch failure is at most `(q+1)/q^n = (1+1/q) q^(1-n)`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε, z ∈ F, assume 2 ≤ n. Then

1 - acceptanceMass(n = n, t = t, c, ε, z) ≤ (|F| + 1) / (|F|)ⁿ.
-/
theorem failureMass_le {n t : ℕ} (hn : 2 ≤ n) (c ε z : F) :
    1 - acceptanceMass (n := n) (t := t) c ε z ≤
      ((fieldCard F : ℝ) + 1) / (fieldCard F : ℝ) ^ n := by
  have hN : 1 < (fieldCard F : ℝ) ^ n := by
    have h := four_le_pow (F := F) hn
    exact_mod_cast (show 1 < fieldCard F ^ n by omega)
  have hP : 1 ≤ (fieldCard F : ℝ) ^ (n - 1) := by
    exact_mod_cast (show 1 ≤ fieldCard F ^ (n - 1) by
      have := two_le_pow_pred (F := F) hn; omega)
  have hH : 1 ≤ (fieldCard F : ℝ) ^ t := by
    apply one_le_pow₀
    exact_mod_cast (show 1 ≤ fieldCard F by have := fieldCard_ge_two (F := F); omega)
  have hbase := ratio_lower ((fieldCard F : ℝ) ^ n) ((fieldCard F : ℝ) ^ (n - 1))
    ((fieldCard F : ℝ) ^ t) hN hP hH
  have hmass : 1 - (1 / (fieldCard F : ℝ) ^ n + 1 / (fieldCard F : ℝ) ^ (n - 1)) ≤
      acceptanceMass (n := n) (t := t) c ε z := by
    rw [acceptanceMass_eq hn]
    refine hbase.trans ?_
    apply div_le_div_of_nonneg_right
    · apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left
        · split_ifs <;> linarith
        · linarith
      · positivity
    · have : 0 ≤ (fieldCard F : ℝ) ^ n * (fieldCard F : ℝ) ^ t - 1 := by nlinarith
      positivity
  have hq : (0 : ℝ) < fieldCard F := by exact_mod_cast fieldCard_pos (F := F)
  have hp : (0 : ℝ) < (fieldCard F : ℝ) ^ (n - 1) := pow_pos hq _
  have hpow : (fieldCard F : ℝ) ^ n = (fieldCard F : ℝ) ^ (n - 1) * fieldCard F := by
    rw [← pow_succ]
    congr 1
    omega
  have hid : 1 / (fieldCard F : ℝ) ^ n + 1 / (fieldCard F : ℝ) ^ (n - 1) =
      ((fieldCard F : ℝ) + 1) / (fieldCard F : ℝ) ^ n := by
    rw [hpow]
    field_simp
    ring
  linarith

end CircuitCompiler.Shortening
