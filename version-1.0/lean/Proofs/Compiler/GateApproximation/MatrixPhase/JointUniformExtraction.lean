import Proofs.Compiler.GateApproximation.MatrixPhase.GateTruncation
import Proofs.Compiler.GateApproximation.MatrixPhase.JointExtraction



/-!
# Extraction in the uniform operator normalization

These are the actual finite greedy extraction certificates with the counting normalization removed. They match the row trimming and entry capping bounds.
-/

set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler

open Refresh MatrixRefresh GateTruncation

noncomputable section

variable {I C : Type*} [Fintype I] [DecidableEq I] [DecidableEq C]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I), we have

energy(A) = complexMatrixL2Sq(A) / (|I|)².
-/
lemma uniform_complex_energy (A : Matrix I I ℂ) :
    energy A = complexMatrixL2Sq A / (Fintype.card I : ℝ) ^ 2 := by
  unfold energy rowEnergy uavg complexMatrixL2Sq
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [div_eq_mul_inv, inv_pow]
  ring

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); i ∈ I, we have

rowEnergy(A, i) = complexRowL2Sq(A, i) / |I|.
-/
lemma uniform_complex_rowEnergy (A : Matrix I I ℂ) (i : I) :
    rowEnergy A i = complexRowL2Sq A i / Fintype.card I := by
  unfold rowEnergy uavg complexRowL2Sq
  ring

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℂ^(I × I); j ∈ I, we have

columnEnergy(A, j) = complexColumnL2Sq(A, j) / |I|.
-/
lemma uniform_complex_columnEnergy (A : Matrix I I ℂ) (j : I) :
    columnEnergy A j = complexColumnL2Sq A j / Fintype.card I := by
  unfold columnEnergy uavg complexColumnL2Sq
  ring

/-- All budgets are normalized by uniform measure; feature entries are unchanged. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For χ ∈ C → ℂ^(I × I); β ∈ ℝ; A ∈ ℂ^(I × I), assume I ≠ ∅; ∀ c, i, j, ‖ χ(c, i, j)‖ = 1; 0 < β. Then

∃ ts ∈ TwistedTerm(I, C)*, E ∈ ℂ^(I × I), (∀ t ∈ ts, 0 ≤ t.magnitude ∧ ‖ t.left‖ = 1 ∧ ‖ t.right‖ = 1) ∧ A = sum((TwistedTerm.value(χ)_*ts)) + E ∧ (∀ c, opNorm((χ(c) ⊙ E)) ≤ β) ∧ energy(E) ≤ energy(A) ∧ sum((TwistedTerm.magnitude_*ts)) / |I| ≤ energy(A) / β ∧ (∀ i, sum((((t ↦ (‖ t.leftFeature(i)‖)²))_*ts)) ≤ rowEnergy(A, i) / β) ∧ (∀ j, sum((((t ↦ (‖ t.rightFeature(j)‖)²))_*ts)) ≤ columnEnergy(A, j) / β).
-/
theorem exists_uniform_twisted_extraction [Nonempty I] (χ : C → Matrix I I ℂ)
    (hχ : ∀ c i j, ‖χ c i j‖ = 1) (β : ℝ) (hβ : 0 < β) (A : Matrix I I ℂ) :
    ∃ (ts : List (TwistedTerm I C)) (E : Matrix I I ℂ),
      (∀ t ∈ ts, 0 ≤ t.magnitude ∧ ‖t.left‖ = 1 ∧ ‖t.right‖ = 1) ∧
      A = (ts.map (TwistedTerm.value χ)).sum + E ∧
      (∀ c, opNorm (χ c ⊙ E) ≤ β) ∧
      energy E ≤ energy A ∧
      (ts.map TwistedTerm.magnitude).sum / Fintype.card I ≤ energy A / β ∧
      (∀ i, (ts.map (fun t => ‖t.leftFeature i‖ ^ 2)).sum ≤ rowEnergy A i / β) ∧
      (∀ j, (ts.map (fun t => ‖t.rightFeature j‖ ^ 2)).sum ≤ columnEnergy A j / β) := by
  have hd : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  obtain ⟨ts, E, ht, hdec, hres, _, henergy, hmass, hrow, hcol⟩ :=
    exists_twisted_extraction_features χ hχ (Fintype.card I * β) (mul_pos hd hβ) A
  refine ⟨ts, E, ?_, hdec, ?_, ?_, ?_, ?_, ?_⟩
  · intro t hm
    exact ⟨(mul_pos hd hβ).le.trans (ht t hm).1.le, (ht t hm).2⟩
  · intro c
    exact (div_le_iff₀ hd).2 (by simpa only [mul_comm] using hres c)
  · rw [uniform_complex_energy, uniform_complex_energy]
    exact div_le_div_of_nonneg_right henergy (sq_nonneg _)
  · have h := div_le_div_of_nonneg_right hmass hd.le
    rw [uniform_complex_energy]
    convert h using 1 <;> field_simp <;> ring
  · intro i
    rw [uniform_complex_rowEnergy]
    convert hrow i using 1 <;> ring
  · intro j
    rw [uniform_complex_columnEnergy]
    convert hcol j using 1 <;> ring

/-- The total feature trace of each block has the same normalized singular-mass budget. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ts ∈ TwistedTerm(I, C)*; c ∈ C, assume ∀ t ∈ ts, 0 ≤ t.magnitude ∧ ‖ t.left‖ = 1 ∧ ‖ t.right‖ = 1. Then

𝔼ᵢ [(‖ extractedLeftFeatures(ts, c, i)‖)²] ≤ sum((TwistedTerm.magnitude_*ts)) / |I| ∧ 𝔼ᵢ [(‖ extractedRightFeatures(ts, c, i)‖)²] ≤ sum((TwistedTerm.magnitude_*ts)) / |I|.
-/
theorem extractedFeatures_uniform_energy_le (ts : List (TwistedTerm I C))
    (ht : ∀ t ∈ ts, 0 ≤ t.magnitude ∧ ‖t.left‖ = 1 ∧ ‖t.right‖ = 1) (c : C) :
    uavg (fun i => ‖extractedLeftFeatures ts c i‖ ^ 2) ≤
      (ts.map TwistedTerm.magnitude).sum / Fintype.card I ∧
    uavg (fun i => ‖extractedRightFeatures ts c i‖ ^ 2) ≤
      (ts.map TwistedTerm.magnitude).sum / Fintype.card I := by
  constructor
  · simpa only [uavg, div_eq_mul_inv, mul_comm] using
      div_le_div_of_nonneg_right
        (extractedLeftFeatures_total_le ts (fun t hm => ⟨(ht t hm).1, (ht t hm).2.1⟩) c)
        (Nat.cast_nonneg (α := ℝ) (Fintype.card I))
  · simpa only [uavg, div_eq_mul_inv, mul_comm] using
      div_le_div_of_nonneg_right
        (extractedRightFeatures_total_le ts (fun t hm => ⟨(ht t hm).1, (ht t hm).2.2⟩) c)
        (Nat.cast_nonneg (α := ℝ) (Fintype.card I))

/-- The support isolation bound in uniform operator normalization. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For χ ∈ C → ℂ^(I × I); ts ∈ TwistedTerm(I, C)*; A, E ∈ ℂ^(I × I); β, δ, H ∈ ℝ; c ∈ C, assume I ≠ ∅; C is finite; ∀ c, i, j, ‖ χ(c, i, j)‖ = 1; ∀ t ∈ ts, 0 ≤ t.magnitude; A = sum((TwistedTerm.value(χ)_*ts)) + E; ∀ c, χ(c) ⊙ A = A; 0 ≤ δ; 0 ≤ H; ∀ c, opNorm((χ(c) ⊙ E)) ≤ β; ∀ c, d, (c ≠ d) ⇒ opNorm((χ(c) ⊙ inversePhase(χ(d)))) ≤ δ; ∀ i, sum((((t ↦ (‖ t.leftFeature(i)‖)²))_*ts)) ≤ H; ∀ j, sum((((t ↦ (‖ t.rightFeature(j)‖)²))_*ts)) ≤ H. Then

opNorm(extractedBlock(ts, c)) ≤ opNorm(A) + β + |C| · δ · H.
-/
theorem extractedBlock_uniform_norm_le [Nonempty I] [Fintype C]
    (χ : C → Matrix I I ℂ) (hχ : ∀ c i j, ‖χ c i j‖ = 1)
    (ts : List (TwistedTerm I C)) (ht : ∀ t ∈ ts, 0 ≤ t.magnitude)
    (A E : Matrix I I ℂ) (hd : A = (ts.map (TwistedTerm.value χ)).sum + E)
    (hsupport : ∀ c, χ c ⊙ A = A) (β δ H : ℝ) (hδ : 0 ≤ δ) (hH : 0 ≤ H)
    (hE : ∀ c, opNorm (χ c ⊙ E) ≤ β)
    (hcross : ∀ c d, c ≠ d → opNorm (χ c ⊙ inversePhase (χ d)) ≤ δ)
    (hleft : ∀ i, (ts.map (fun t => ‖t.leftFeature i‖ ^ 2)).sum ≤ H)
    (hright : ∀ j, (ts.map (fun t => ‖t.rightFeature j‖ ^ 2)).sum ≤ H) (c : C) :
    opNorm (extractedBlock ts c) ≤ opNorm A + β + Fintype.card C * δ * H := by
  have hcard : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := extractedBlock_norm_le χ hχ ts ht A E hd hsupport
    (β * Fintype.card I) (δ * Fintype.card I) H (mul_nonneg hδ hcard.le) hH
    (fun c => (div_le_iff₀ hcard).1 (hE c))
    (fun c d hcd => (div_le_iff₀ hcard).1 (hcross c d hcd)) hleft hright c
  apply (div_le_iff₀ hcard).2
  convert h using 1 <;> unfold opNorm <;> field_simp <;> ring

end

end CircuitCompiler
