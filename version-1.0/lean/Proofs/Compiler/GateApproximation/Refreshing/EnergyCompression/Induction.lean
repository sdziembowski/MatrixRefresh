import Proofs.Compiler.Foundations.LinearAlgebra.Induction



/-!
# Numeric induction for energy compression

The analytic and operational layers supply the recurrence premises used by the security theorem. The one-round error is linear in the input nuclear norm, with θ=κ^(1/12).
-/

set_option autoImplicit false

namespace TableAnalysis.EnergyCompression

noncomputable section

open TableAnalysis

/-
Mathematical definition (normal notation): For K, pMin, θ, c, Γ, m ∈ ℝ, define

compressionError(K, pMin, θ, c, Γ, m) := θ · (2 · c / √pMin + 2 · m / pMin + 2 · √K · Γ).
-/
def compressionError (K pMin θ c Γ m : ℝ) : ℝ :=
  θ * (2 * c / Real.sqrt pMin + 2 * m / pMin + 2 * Real.sqrt K * Γ)

/-
Mathematical definition (normal notation): For K, pMin, θ, c, b, m ∈ ℝ, define

compressionIncrement(K, pMin, θ, c, b, m) := θ · √K · (2 · c / √pMin + 2 · m / pMin + 2 · √K · b).
-/
def compressionIncrement (K pMin θ c b m : ℝ) : ℝ :=
  θ * Real.sqrt K * (2 * c / Real.sqrt pMin + 2 * m / pMin + 2 * Real.sqrt K * b)

/-
Mathematical definition (normal notation): For K, pMin, θ ∈ ℝ, define

roundError(K, pMin, θ) := 16 · K² · θ / pMin.
-/
def roundError (K pMin θ : ℝ) : ℝ := 16 * K ^ 2 * θ / pMin

/-
Mathematical definition (normal notation): For K, pMin, θ, q, N ∈ ℝ; T ∈ ℕ, define

securityBound(K, pMin, θ, q, N, T) := 8 · T · K² · θ / pMin² + 2 · q · K / √(pMin · N).
-/
def securityBound (K pMin θ q N : ℝ) (T : ℕ) : ℝ :=
  8 * (T : ℝ) * K ^ 2 * θ / pMin ^ 2 + 2 * q * K / Real.sqrt (pMin * N)

-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K, pMin, θ ∈ ℝ, assume 0 ≤ K; 0 ≤ pMin; 0 ≤ θ. Then

0 ≤ roundError(K, pMin, θ).
-/
lemma roundError_nonneg (K pMin θ : ℝ) (_hK : 0 ≤ K) (hpMin : 0 ≤ pMin)
    (hθ : 0 ≤ θ) : 0 ≤ roundError K pMin θ := by
  unfold roundError
  positivity

-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K, pMin, θ, c, b, m, C, B ∈ ℝ, assume 0 < pMin; 0 ≤ θ; 0 ≤ b; 0 ≤ C; c ≤ C; b ≤ B; m ≤ 2. Then

compressionIncrement(K, pMin, θ, c, b, m) ≤ compressionIncrement(K, pMin, θ, C, B, 2).
-/
lemma compressionIncrement_mono (K pMin θ c b m C B : ℝ)
    (hpMin : 0 < pMin) (hθ : 0 ≤ θ) (_hb : 0 ≤ b) (_hC : 0 ≤ C)
    (hcC : c ≤ C) (hbB : b ≤ B) (hm : m ≤ 2) :
    compressionIncrement K pMin θ c b m ≤ compressionIncrement K pMin θ C B 2 := by
  unfold compressionIncrement
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hθ (Real.sqrt_nonneg K))
  gcongr

-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K, pMin, θ ∈ ℝ, assume 1 ≤ K; 0 < pMin; pMin ≤ 1; 0 ≤ θ. Then

compressionIncrement(K, pMin, θ, l2Envelope(K, pMin), nuclearEnvelope(K, pMin), 2) ≤ 12 · K² · θ / pMin.
-/
lemma compressionIncrement_envelopes (K pMin θ : ℝ)
    (hK : 1 ≤ K) (hpMin : 0 < pMin) (hpMin1 : pMin ≤ 1) (hθ : 0 ≤ θ) :
    compressionIncrement K pMin θ (l2Envelope K pMin) (nuclearEnvelope K pMin) 2 ≤
      12 * K ^ 2 * θ / pMin := by
  have hK0 : 0 ≤ K := by linarith
  have hp : 0 < Real.sqrt pMin := Real.sqrt_pos.2 hpMin
  have hs : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hs1 : 1 ≤ Real.sqrt K := by
    exact (Real.le_sqrt (by norm_num) hK0).2 (by simpa using hK)
  have hsK : Real.sqrt K ≤ K := by nlinarith [Real.sq_sqrt hK0]
  have hKK : K ≤ K ^ 2 := by nlinarith
  have hpMinSqrt : pMin ≤ Real.sqrt pMin := by
    nlinarith [Real.sq_sqrt hpMin.le, Real.sqrt_le_one.2 hpMin1]
  have hfirst : θ * Real.sqrt K * (2 * l2Envelope K pMin / Real.sqrt pMin) ≤
      4 * K ^ 2 * θ / pMin := by
    calc
      _ = 4 * K * θ / pMin := by
        rw [l2Envelope_eq K pMin hK0]
        field_simp
        rw [Real.sq_sqrt hK0, Real.sq_sqrt hpMin.le]
        ring
      _ ≤ _ := by gcongr
  have hsecond : θ * Real.sqrt K * (2 * (2 : ℝ) / pMin) ≤
      4 * K ^ 2 * θ / pMin := by
    have hn : Real.sqrt K ≤ K ^ 2 := hsK.trans hKK
    convert (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ 4 * θ)) hpMin.le) using 1 <;> ring
  have hthird : θ * Real.sqrt K * (2 * Real.sqrt K * nuclearEnvelope K pMin) ≤
      4 * K ^ 2 * θ / pMin := by
    calc
      _ = 4 * K ^ 2 * θ / Real.sqrt pMin := by
        unfold nuclearEnvelope
        field_simp
        nlinarith [Real.sq_sqrt hK0]
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hpMin hpMinSqrt
  unfold compressionIncrement
  linear_combination hfirst + hsecond + hthird

-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K, pMin, θ ∈ ℝ, assume 1 ≤ K; 0 < pMin; pMin ≤ 1; 0 ≤ θ. Then

compressionIncrement(K, pMin, θ, l2Envelope(K, pMin), nuclearEnvelope(K, pMin), 2) ≤ roundError(K, pMin, θ).
-/
lemma compressionIncrement_le_roundError (K pMin θ : ℝ)
    (hK : 1 ≤ K) (hpMin : 0 < pMin) (hpMin1 : pMin ≤ 1) (hθ : 0 ≤ θ) :
    compressionIncrement K pMin θ (l2Envelope K pMin) (nuclearEnvelope K pMin) 2 ≤
      roundError K pMin θ := by
  apply (compressionIncrement_envelopes K pMin θ hK hpMin hpMin1 hθ).trans
  unfold roundError
  have h : 0 ≤ K ^ 2 * θ / pMin := by positivity
  have hm := mul_le_mul_of_nonneg_right (by norm_num : (12 : ℝ) ≤ 16) h
  convert hm using 1 <;> ring

/-- Conditional numeric compression induction.  The four recurrence hypotheses are precisely the mass, L2, nuclear, and compression-error estimates that the analytic/protocol layer must supply. -/
-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K, pMin, θ ∈ ℝ; T ∈ ℕ; E, C, B, M ∈ ℕ → ℝ, assume 1 ≤ K; 0 < pMin; pMin ≤ 1; 0 ≤ θ; ∀ i, 0 ≤ B(i); E(0) ≤ 0; C(0) ≤ l2Envelope(K, pMin); B(0) ≤ nuclearEnvelope(K, pMin); ∀ i, M(i) ≤ 1 + E(i); ∀ i, C((i + 1)) ≤ √(K / pMin) · M(i); ∀ i, B((i + 1)) ≤ √K · C(i); ∀ i, E((i + 1)) ≤ E(i) + compressionIncrement(K, pMin, θ, C(i), B(i), M(i)); T · roundError(K, pMin, θ) ≤ 1. Then

∀ i, ≤, T, E(i) ≤ i · roundError(K, pMin, θ) ∧ C(i) ≤ l2Envelope(K, pMin) ∧ B(i) ≤ nuclearEnvelope(K, pMin).
-/
theorem forward_numeric_induction (K pMin θ : ℝ) (T : ℕ)
    (E C B M : ℕ → ℝ)
    (hK : 1 ≤ K) (hpMin : 0 < pMin) (hpMin1 : pMin ≤ 1) (hθ : 0 ≤ θ)
    (hBnonneg : ∀ i, 0 ≤ B i)
    (hE0 : E 0 ≤ 0)
    (hC0 : C 0 ≤ l2Envelope K pMin)
    (hB0 : B 0 ≤ nuclearEnvelope K pMin)
    (hmass : ∀ i, M i ≤ 1 + E i)
    (hL2 : ∀ i, C (i + 1) ≤ Real.sqrt (K / pMin) * M i)
    (hNuclear : ∀ i, B (i + 1) ≤ Real.sqrt K * C i)
    (hError : ∀ i, E (i + 1) ≤ E i + compressionIncrement K pMin θ (C i) (B i) (M i))
    (hT : (T : ℝ) * roundError K pMin θ ≤ 1) :
    ∀ i ≤ T, E i ≤ (i : ℝ) * roundError K pMin θ ∧
      C i ≤ l2Envelope K pMin ∧ B i ≤ nuclearEnvelope K pMin := by
  have hK0 : 0 ≤ K := by linarith
  have hδ : 0 ≤ roundError K pMin θ := roundError_nonneg K pMin θ hK0 hpMin.le hθ
  have hCbudget : 0 ≤ l2Envelope K pMin := by unfold l2Envelope; positivity
  intro i
  induction i with
  | zero =>
      intro _
      exact ⟨by simpa using hE0, hC0, hB0⟩
  | succ i ih =>
      intro hi
      obtain ⟨hEi, hCi, hBi⟩ := ih (by omega)
      have hiT : (i : ℝ) ≤ T := by exact_mod_cast (show i ≤ T by omega)
      have hEone : E i ≤ 1 :=
        hEi.trans ((mul_le_mul_of_nonneg_right hiT hδ).trans hT)
      have hMi : M i ≤ 2 := by linarith [hmass i]
      have hinc : compressionIncrement K pMin θ (C i) (B i) (M i) ≤
          roundError K pMin θ :=
        (compressionIncrement_mono K pMin θ (C i) (B i) (M i)
          (l2Envelope K pMin) (nuclearEnvelope K pMin) hpMin hθ
          (hBnonneg i) hCbudget hCi hBi hMi).trans
          (compressionIncrement_le_roundError K pMin θ hK hpMin hpMin1 hθ)
      refine ⟨?_, ?_, ?_⟩
      · have := hError i
        rw [Nat.cast_succ]
        linarith
      · calc
          C (i + 1) ≤ Real.sqrt (K / pMin) * M i := hL2 i
          _ ≤ Real.sqrt (K / pMin) * 2 := by gcongr
          _ = l2Envelope K pMin := by unfold l2Envelope; ring
      · calc
          B (i + 1) ≤ Real.sqrt K * C i := hNuclear i
          _ ≤ Real.sqrt K * l2Envelope K pMin := by gcongr
          _ = nuclearEnvelope K pMin := (nuclearEnvelope_eq K pMin hK0 hpMin).symm

-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K, pMin, θ, q, N ∈ ℝ; T ∈ ℕ, assume 0 < pMin; 0 < N. Then

T · roundError(K, pMin, θ) / (2 · pMin) + q · nuclearEnvelope(K, pMin) / √N = securityBound(K, pMin, θ, q, N, T).
-/
lemma extraction_arithmetic (K pMin θ q N : ℝ) (T : ℕ)
    (hpMin : 0 < pMin) (hN : 0 < N) :
    (T : ℝ) * roundError K pMin θ / (2 * pMin) +
        q * nuclearEnvelope K pMin / Real.sqrt N =
      securityBound K pMin θ q N T := by
  unfold roundError nuclearEnvelope securityBound
  rw [Real.sqrt_mul hpMin.le]
  field_simp
  ring

/-- The large-error branch of the security bound is automatic from `TV ≤ 1`. No norm recurrence or extraction estimate is used in this branch. -/
-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K, pMin, θ, q, N ∈ ℝ; T ∈ ℕ, assume 0 ≤ K; 0 < pMin; pMin ≤ 1 / 2; 0 ≤ q; 0 < N; 1 < T · roundError(K, pMin, θ). Then

1 ≤ securityBound(K, pMin, θ, q, N, T).
-/
lemma securityBound_ge_one_of_large_error (K pMin θ q N : ℝ) (T : ℕ)
    (hK : 0 ≤ K) (hpMin : 0 < pMin) (hpMinHalf : pMin ≤ 1 / 2)
    (hq : 0 ≤ q) (hN : 0 < N)
    (hlarge : 1 < (T : ℝ) * roundError K pMin θ) :
    1 ≤ securityBound K pMin θ q N T := by
  rw [← extraction_arithmetic K pMin θ q N T hpMin hN]
  have hden : 2 * pMin ≤ 1 := by linarith
  have hfirst : 1 ≤ (T : ℝ) * roundError K pMin θ / (2 * pMin) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * pMin)).2
    linarith
  have hsecond : 0 ≤ q * nuclearEnvelope K pMin / Real.sqrt N := by
    unfold nuclearEnvelope
    positivity
  linarith

/-- Conditional final extraction, including both the nontrivial and trivial `T δ` cases.  The hypothesis `hextract` is the numeric consequence of the encoding discrepancy and disjoint-secret-fiber argument, not a theorem about transcripts proved in this file. -/
-- Auxiliary lemma (refreshing proof); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K, pMin, θ, q, N, distance ∈ ℝ; T ∈ ℕ; E, C, B, M ∈ ℕ → ℝ, assume 1 ≤ K; 0 < pMin; pMin ≤ 1 / 2; 0 ≤ θ; 0 ≤ q; 0 < N; ∀ i, 0 ≤ B(i); E(0) ≤ 0; C(0) ≤ l2Envelope(K, pMin); B(0) ≤ nuclearEnvelope(K, pMin); ∀ i, M(i) ≤ 1 + E(i); ∀ i, C((i + 1)) ≤ √(K / pMin) · M(i); ∀ i, B((i + 1)) ≤ √K · C(i); ∀ i, E((i + 1)) ≤ E(i) + compressionIncrement(K, pMin, θ, C(i), B(i), M(i)); distance ≤ 1; distance ≤ E(T) / (2 · pMin) + q · B(T) / √N. Then

distance ≤ min{securityBound(K, pMin, θ, q, N, T), 1}.
-/
theorem final_numeric_security (K pMin θ q N distance : ℝ) (T : ℕ)
    (E C B M : ℕ → ℝ)
    (hK : 1 ≤ K) (hpMin : 0 < pMin) (hpMinHalf : pMin ≤ 1 / 2)
    (hθ : 0 ≤ θ) (hq : 0 ≤ q) (hN : 0 < N)
    (hBnonneg : ∀ i, 0 ≤ B i)
    (hE0 : E 0 ≤ 0)
    (hC0 : C 0 ≤ l2Envelope K pMin)
    (hB0 : B 0 ≤ nuclearEnvelope K pMin)
    (hmass : ∀ i, M i ≤ 1 + E i)
    (hL2 : ∀ i, C (i + 1) ≤ Real.sqrt (K / pMin) * M i)
    (hNuclear : ∀ i, B (i + 1) ≤ Real.sqrt K * C i)
    (hError : ∀ i, E (i + 1) ≤ E i + compressionIncrement K pMin θ (C i) (B i) (M i))
    (hdistance : distance ≤ 1)
    (hextract : distance ≤ E T / (2 * pMin) + q * B T / Real.sqrt N) :
    distance ≤ min (securityBound K pMin θ q N T) 1 := by
  have hK0 : 0 ≤ K := by linarith
  refine le_min ?_ hdistance
  by_cases hT : (T : ℝ) * roundError K pMin θ ≤ 1
  · obtain ⟨hET, _, hBT⟩ := forward_numeric_induction K pMin θ T E C B M
      hK hpMin (by linarith) hθ hBnonneg hE0 hC0 hB0
      hmass hL2 hNuclear hError hT T le_rfl
    calc
      distance ≤ E T / (2 * pMin) + q * B T / Real.sqrt N := hextract
      _ ≤ (T : ℝ) * roundError K pMin θ / (2 * pMin) +
          q * nuclearEnvelope K pMin / Real.sqrt N := by gcongr
      _ = securityBound K pMin θ q N T := extraction_arithmetic K pMin θ q N T hpMin hN
  · exact hdistance.trans (securityBound_ge_one_of_large_error K pMin θ q N T
      hK0 hpMin hpMinHalf hq hN (lt_of_not_ge hT))

end

end TableAnalysis.EnergyCompression
