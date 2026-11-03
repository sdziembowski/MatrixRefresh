import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic



/-!
# Numeric induction for spectral compression

The real-number bookkeeping takes norm, refresh, compression, and encoding discrepancy estimates as explicit hypotheses. These scalar results are instantiated with operational estimates when proving protocol security.

The envelopes are `C = 2 sqrt(K / pMin)`, `B = 2 K / sqrt pMin`, and `δ = 16 K^(3/2) θ / pMin`. The compression increment is bounded with coefficient 14 and then enlarged to 16 to obtain the common round-error envelope.
-/

set_option autoImplicit false

namespace TableAnalysis

noncomputable section

/-
Mathematical definition (normal notation): For K, pMin ∈ ℝ, define

l2Envelope(K, pMin) := 2 · √(K / pMin).
-/
def l2Envelope (K pMin : ℝ) : ℝ := 2 * Real.sqrt (K / pMin)

/-
Mathematical definition (normal notation): For K, pMin ∈ ℝ, define

nuclearEnvelope(K, pMin) := 2 · K / √pMin.
-/
def nuclearEnvelope (K pMin : ℝ) : ℝ := 2 * K / Real.sqrt pMin

/-
Mathematical definition (normal notation): For K, pMin, θ ∈ ℝ, define

roundError(K, pMin, θ) := 16 · K^(3 / 2) · θ / pMin.
-/
def roundError (K pMin θ : ℝ) : ℝ := 16 * K ^ ((3 : ℝ) / 2) * θ / pMin

/-
Mathematical definition (normal notation): For K, pMin, θ, c, b, m ∈ ℝ, define

compressionIncrement(K, pMin, θ, c, b, m) := θ · √K · ((2 · c + √(c · b)) / √pMin + 2 · m / pMin + 2 · √K · c).
-/
def compressionIncrement (K pMin θ c b m : ℝ) : ℝ :=
  θ * Real.sqrt K *
    ((2 * c + Real.sqrt (c * b)) / Real.sqrt pMin +
      2 * m / pMin + 2 * Real.sqrt K * c)

/-
Mathematical definition (normal notation): For K, pMin, θ, q, N ∈ ℝ; T ∈ ℕ, define

securityBound(K, pMin, θ, q, N, T) := 8 · T · K^(3 / 2) · θ / pMin² + 2 · q · K / √(pMin · N).
-/
def securityBound (K pMin θ q N : ℝ) (T : ℕ) : ℝ :=
  8 * (T : ℝ) * K ^ ((3 : ℝ) / 2) * θ / pMin ^ 2 +
    2 * q * K / Real.sqrt (pMin * N)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K ∈ ℝ, assume 0 ≤ K. Then

K^(3 / 2) = K · √K.
-/
lemma three_halves_eq (K : ℝ) (hK : 0 ≤ K) :
    K ^ ((3 : ℝ) / 2) = K * Real.sqrt K := by
  rw [Real.rpow_div_two_eq_sqrt _ hK]
  norm_num
  calc
    Real.sqrt K ^ 3 = Real.sqrt K ^ 2 * Real.sqrt K := by ring
    _ = K * Real.sqrt K := by rw [Real.sq_sqrt hK]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K, pMin ∈ ℝ, assume 0 ≤ K. Then

l2Envelope(K, pMin) = 2 · √K / √pMin.
-/
lemma l2Envelope_eq (K pMin : ℝ) (hK : 0 ≤ K) :
    l2Envelope K pMin = 2 * Real.sqrt K / Real.sqrt pMin := by
  rw [l2Envelope, Real.sqrt_div hK]
  ring

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K, pMin ∈ ℝ, assume 0 ≤ K; 0 < pMin. Then

nuclearEnvelope(K, pMin) = √K · l2Envelope(K, pMin).
-/
lemma nuclearEnvelope_eq (K pMin : ℝ) (hK : 0 ≤ K) (hpMin : 0 < pMin) :
    nuclearEnvelope K pMin = Real.sqrt K * l2Envelope K pMin := by
  rw [l2Envelope_eq K pMin hK, nuclearEnvelope]
  field_simp
  nlinarith [Real.sq_sqrt hK]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K, pMin, θ ∈ ℝ, assume 0 ≤ K; 0 ≤ pMin; 0 ≤ θ. Then

0 ≤ roundError(K, pMin, θ).
-/
lemma roundError_nonneg (K pMin θ : ℝ) (hK : 0 ≤ K) (hpMin : 0 ≤ pMin)
    (hθ : 0 ≤ θ) : 0 ≤ roundError K pMin θ := by
  unfold roundError
  positivity

/-- The initial table `1` has L2 and nuclear norm one, so both envelope bounds required by the numeric induction hold at time zero. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K, pMin ∈ ℝ, assume 1 ≤ K; 0 < pMin; pMin ≤ 1. Then

1 ≤ l2Envelope(K, pMin) ∧ 1 ≤ nuclearEnvelope(K, pMin).
-/
lemma initial_envelopes (K pMin : ℝ) (hK : 1 ≤ K) (hpMin : 0 < pMin)
    (hpMin1 : pMin ≤ 1) :
    1 ≤ l2Envelope K pMin ∧ 1 ≤ nuclearEnvelope K pMin := by
  have hratio : 1 ≤ K / pMin := by
    apply (le_div_iff₀ hpMin).2
    linarith
  have hs : 1 ≤ Real.sqrt (K / pMin) := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).2 (by simpa using hratio)
  have hp : 0 < Real.sqrt pMin := Real.sqrt_pos.2 hpMin
  have hp1 : Real.sqrt pMin ≤ 1 := Real.sqrt_le_one.2 hpMin1
  refine ⟨?_, ?_⟩
  · unfold l2Envelope
    linarith
  · unfold nuclearEnvelope
    apply (le_div_iff₀ hp).2
    linarith

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K, pMin, θ, c, b, m, C, B ∈ ℝ, assume 0 < pMin; 0 ≤ θ; 0 ≤ b; 0 ≤ C; c ≤ C; b ≤ B; m ≤ 2. Then

compressionIncrement(K, pMin, θ, c, b, m) ≤ compressionIncrement(K, pMin, θ, C, B, 2).
-/
lemma compressionIncrement_mono (K pMin θ c b m C B : ℝ)
    (hpMin : 0 < pMin) (hθ : 0 ≤ θ) (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hcC : c ≤ C) (hbB : b ≤ B) (hm : m ≤ 2) :
    compressionIncrement K pMin θ c b m ≤
      compressionIncrement K pMin θ C B 2 := by
  unfold compressionIncrement
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hθ (Real.sqrt_nonneg K))
  gcongr

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K, pMin, θ ∈ ℝ, assume 1 ≤ K; 0 < pMin; pMin ≤ 1; 0 ≤ θ. Then

compressionIncrement(K, pMin, θ, l2Envelope(K, pMin), nuclearEnvelope(K, pMin), 2) ≤ 14 · K^(3 / 2) · θ / pMin.
-/
lemma compressionIncrement_envelopes (K pMin θ : ℝ)
    (hK : 1 ≤ K) (hpMin : 0 < pMin) (hpMin1 : pMin ≤ 1) (hθ : 0 ≤ θ) :
    compressionIncrement K pMin θ (l2Envelope K pMin)
        (nuclearEnvelope K pMin) 2 ≤
      14 * K ^ ((3 : ℝ) / 2) * θ / pMin := by
  have hK0 : 0 ≤ K := by linarith
  have hs : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hs1 : 1 ≤ Real.sqrt K := by
    exact (Real.le_sqrt (by norm_num) hK0).2 (by simpa using hK)
  have hp : 0 < Real.sqrt pMin := Real.sqrt_pos.2 hpMin
  have hp1 : Real.sqrt pMin ≤ 1 := Real.sqrt_le_one.2 hpMin1
  have hpMinSqrt : pMin ≤ Real.sqrt pMin := by
    nlinarith [Real.sq_sqrt hpMin.le]
  have hsK : Real.sqrt K ≤ K := by
    nlinarith [Real.sq_sqrt hK0]
  have hC0 : 0 ≤ l2Envelope K pMin := by
    unfold l2Envelope
    positivity
  have hB0 : 0 ≤ nuclearEnvelope K pMin := by
    unfold nuclearEnvelope
    positivity
  have hCB : l2Envelope K pMin ≤ nuclearEnvelope K pMin := by
    rw [l2Envelope_eq K pMin hK0, nuclearEnvelope]
    gcongr
  have hsqrt : Real.sqrt (l2Envelope K pMin * nuclearEnvelope K pMin) ≤
      nuclearEnvelope K pMin := by
    apply (Real.sqrt_le_iff).2
    refine ⟨hB0, ?_⟩
    nlinarith [mul_le_mul_of_nonneg_right hCB hB0]
  have hfirst :
      θ * Real.sqrt K *
          ((2 * l2Envelope K pMin +
              Real.sqrt (l2Envelope K pMin * nuclearEnvelope K pMin)) /
            Real.sqrt pMin) ≤
        6 * K * Real.sqrt K * θ / pMin := by
    calc
      _ ≤ θ * Real.sqrt K * ((3 * nuclearEnvelope K pMin) / Real.sqrt pMin) := by
        gcongr
        linarith
      _ = 6 * K * Real.sqrt K * θ / pMin := by
        unfold nuclearEnvelope
        field_simp
        nlinarith [Real.sq_sqrt hpMin.le]
  have hsecond : θ * Real.sqrt K * (2 * (2 : ℝ) / pMin) ≤
      4 * K * Real.sqrt K * θ / pMin := by
    have hnum : 4 * Real.sqrt K * θ ≤ 4 * K * Real.sqrt K * θ := by
      nlinarith [mul_nonneg hs hθ]
    convert (div_le_div_of_nonneg_right hnum hpMin.le) using 1
    ring
  have hthird : θ * Real.sqrt K * (2 * Real.sqrt K * l2Envelope K pMin) ≤
      4 * K * Real.sqrt K * θ / pMin := by
    calc
      _ = (4 * K * Real.sqrt K * θ) / Real.sqrt pMin := by
        rw [l2Envelope_eq K pMin hK0]
        field_simp
        nlinarith [Real.sq_sqrt hK0]
      _ ≤ (4 * K * Real.sqrt K * θ) / pMin := by
        exact div_le_div_of_nonneg_left (by positivity) hpMin hpMinSqrt
  rw [compressionIncrement, three_halves_eq K hK0]
  linear_combination hfirst + hsecond + hthird

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For K, pMin, θ ∈ ℝ, assume 1 ≤ K; 0 < pMin; pMin ≤ 1; 0 ≤ θ. Then

compressionIncrement(K, pMin, θ, l2Envelope(K, pMin), nuclearEnvelope(K, pMin), 2) ≤ roundError(K, pMin, θ).
-/
lemma compressionIncrement_le_roundError (K pMin θ : ℝ)
    (hK : 1 ≤ K) (hpMin : 0 < pMin) (hpMin1 : pMin ≤ 1) (hθ : 0 ≤ θ) :
    compressionIncrement K pMin θ (l2Envelope K pMin)
        (nuclearEnvelope K pMin) 2 ≤ roundError K pMin θ := by
  have h := compressionIncrement_envelopes K pMin θ hK hpMin hpMin1 hθ
  unfold roundError
  have hbase : 0 ≤ K ^ ((3 : ℝ) / 2) * θ / pMin := by positivity
  linear_combination h + 2 * hbase

/-- Conditional numeric compression induction.  The four recurrence hypotheses are precisely the mass, L2, nuclear, and compression-error estimates that the analytic/protocol layer must supply. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
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

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
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
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
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
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
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

end TableAnalysis
