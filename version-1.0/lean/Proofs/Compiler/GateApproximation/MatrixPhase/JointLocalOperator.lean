import Proofs.Compiler.GateApproximation.MatrixPhase.JointBlockRestriction
import Proofs.Compiler.GateApproximation.MatrixPhase.JointGraphDecomposition



/-!
# Local graph operator bound from actual spectral extraction

The only input hypotheses are the support, row, column, entry, and energy bounds furnished by trimming and capping. All extraction, mixing, and four-cycle estimates are applied to the actual shared-matrix graph.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler

open Refresh MatrixRefresh TableAnalysis GateTruncation

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X a set; m ∈ ℕ; ψ ∈ AddChar(F, ℂ); a, b ∈ X → U(F, m); c, d ∈ F, assume X is finite. Then

graphPhase(ψ, a, b, c) ⊙ inversePhase(graphPhase(ψ, a, b, d)) = graphPhase(ψ, a, b, (c - d)).
-/
lemma graphPhase_quotient {X : Type*} [Fintype X] [DecidableEq X] {m : ℕ}
    (ψ : AddChar F ℂ) (a b : X → U F m) (c d : F) :
    graphPhase ψ a b c ⊙ inversePhase (graphPhase ψ a b d) = graphPhase ψ a b (c - d) := by
  ext i j
  simp only [graphPhase, Matrix.hadamard_apply, inversePhase, sub_mul,
    AddChar.map_sub_eq_div, div_eq_mul_inv]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ψ ∈ AddChar(F, ℂ); c ∈ F, assume 2 ≤ n; ψ.IsPrimitive; c ≠ 0. Then

opNorm(graphPhase(ψ, inputTensor(F = F, n = n), inputTensor, c)) ≤ 2 / √(|F|^(n · n)).
-/
lemma tensor_graphPhase_uniform_norm_le (hn : 2 ≤ n) (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (c : F) (hc : c ≠ 0) :
    opNorm (graphPhase ψ (inputTensor (F := F) (n := n)) inputTensor c) ≤
      2 / Real.sqrt (vectorCard F (n * n) : ℝ) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  have h := jointTwistMatrix_uniform_norm_le
    (fun x y : U F n × U F n => dot (inputTensor x).val (inputTensor y).val)
    (n * n) ψ hψ c hc
  have he : (fieldCard F ^ (n * n) : ℕ) = vectorCard F (n * n) := rfl
  have hQ := vectorCard_real_ge_four (F := F) (by nlinarith : 2 ≤ n * n)
  have hQnat : 1 ≤ vectorCard F (n * n) := by exact_mod_cast (show (1 : ℝ) ≤ vectorCard F (n * n) by linarith)
  rw [he, Nat.cast_sub hQnat, Nat.cast_one] at h
  have h' : opNorm (graphPhase ψ (inputTensor (F := F) (n := n)) inputTensor c) ≤
      Real.sqrt (vectorCard F (n * n) : ℝ) / ((vectorCard F (n * n) : ℝ) - 1) := by
    have heq : graphPhase ψ (inputTensor (F := F) (n := n)) inputTensor c =
        jointTwistMatrix (fun x y : U F n × U F n => dot (inputTensor x).val (inputTensor y).val)
          (n*n) ψ c := rfl
    rw [heq]
    simpa only [opNorm, Fintype.card_prod, Nat.cast_mul] using h
  exact h'.trans (sqrt_div_sub_one_le _ (by linarith))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X a set; m ∈ ℕ; ψ ∈ AddChar(F, ℂ); a, b ∈ X → U(F, m); A ∈ ℂ^((X × U(F, m)) × (X × U(F, m))); c ∈ F, assume X is finite; ∀ i, j, (graphConstraint(a, b, i, j) ≠ 0) ⇒ A(i, j) = 0. Then

graphPhase(ψ, a, b, c) ⊙ A = A.
-/
lemma graphPhase_fixes_supported {X : Type*} [Fintype X] [DecidableEq X] {m : ℕ}
    (ψ : AddChar F ℂ) (a b : X → U F m)
    (A : Matrix (X × U F m) (X × U F m) ℂ)
    (hsupport : ∀ i j, graphConstraint a b i j ≠ 0 → A i j = 0) (c : F) :
    graphPhase ψ a b c ⊙ A = A := by
  ext i j
  by_cases h : graphConstraint a b i j = 0
  · simp [Matrix.hadamard_apply, graphPhase, h]
  · simp [Matrix.hadamard_apply, hsupport i j h]

/-
Mathematical definition (normal notation): For F a set; n ∈ ℕ; H, G ∈ ℝ, assume F is a field; F is finite. define

jointGramCost(n, H, G) := 2 · √G · √(√(2 · jointVarianceCoefficient(F, n) · H · G)) + √(2 · jointVarianceCoefficient(F, n) · H · G).
-/
def jointGramCost (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) (H G : ℝ) : ℝ :=
  2 * Real.sqrt G * Real.sqrt (Real.sqrt (2 * jointVarianceCoefficient F n * H * G)) +
    Real.sqrt (2 * jointVarianceCoefficient F n * H * G)

/-
Mathematical definition (normal notation): For F a set; n ∈ ℕ; R, L, β, H ∈ ℝ, assume F is a field; F is finite. define

jointOperatorError(n, R, L, β, H) := |F| · jointGramCost(F, n, (R² / β), (H / β)) + (|F| · √β · fourthRoot(H) + (fourthRoot(tensorCycleErrorConstant(F)) / √(|F|ⁿ)) · (L + R² / β)).
-/
def jointOperatorError (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) (R L β H : ℝ) : ℝ :=
  (fieldCard F : ℝ) * jointGramCost F n (R ^ 2 / β) (H / β) +
    ((fieldCard F : ℝ) * Real.sqrt β * fourthRoot H +
      (fourthRoot (tensorCycleErrorConstant F) / Real.sqrt (vectorCard F n : ℝ)) * (L + R ^ 2 / β))

/-- Actual capped, supported tables have a small expected excess above a fixed leading operator term. The excess form permits arbitrary bounded matrix-dependent rectangle weights in the final dual pairing. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ψ ∈ AddChar(F, ℂ); A ∈ ℂ^(((U(F, n) × U(F, n)) × U(F, (n · n))) × ((U(F, n) × U(F, n)) × U(F, (n · n)))); R, L, β, H ∈ ℝ, assume 2 ≤ n; ψ.IsPrimitive; 0 ≤ L; 0 < β; 0 ≤ H; ∀ i, rowEnergy(A, i) ≤ R²; ∀ j, columnEnergy(A, j) ≤ R²; ∀ i, j, ‖ A(i, j)‖ ≤ L; energy(A) ≤ H; ∀ i, j, (graphConstraint(inputTensor, inputTensor, i, j) ≠ 0) ⇒ A(i, j) = 0. Then

Let d := opNorm(A) + β + |F| · (2 / √(|F|^(n · n))) · (R² / β); 𝔼_(M ∈ GL_(n · n)(F)) [max{(opNorm(graphRestriction(inputTensor, inputTensor, A, M)) - |F| · d), 0}] ≤ jointOperatorError(F, n, R, L, β, H).
-/
theorem joint_supported_graph_excess (hn : 2 ≤ n) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (A : Matrix ((U F n × U F n) × U F (n * n)) ((U F n × U F n) × U F (n * n)) ℂ)
    (R L β H : ℝ) (hL : 0 ≤ L) (hβ : 0 < β) (hH : 0 ≤ H)
    (hrow : ∀ i, rowEnergy A i ≤ R ^ 2) (hcol : ∀ j, columnEnergy A j ≤ R ^ 2)
    (hentry : ∀ i j, ‖A i j‖ ≤ L) (henergy : energy A ≤ H)
    (hsupport : ∀ i j, graphConstraint inputTensor inputTensor i j ≠ 0 → A i j = 0) :
    let d := opNorm A + β + (fieldCard F : ℝ) * (2 / Real.sqrt (vectorCard F (n * n) : ℝ)) * (R ^ 2 / β)
    uavg (fun M : Refresh.«GL» F (n * n) =>
      max (opNorm (graphRestriction inputTensor inputTensor A M) - (fieldCard F : ℝ) * d) 0) ≤
      jointOperatorError F n R L β H := by
  intro d
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  letI : Nonempty (U F (n * n)) := ⟨unitShare ⟨0, by nlinarith⟩⟩
  let χ := graphPhase ψ (inputTensor (F := F) (n := n)) inputTensor
  have hχ : ∀ c i j, ‖χ c i j‖ = 1 := fun c i j => ψ.norm_apply _
  obtain ⟨ts, E, ht, hdec, htwist, hresEnergy, hmass, hleft, hright⟩ :=
    exists_uniform_twisted_extraction χ hχ β hβ A
  have hleft' (i) : (ts.map (fun t => ‖t.leftFeature i‖ ^ 2)).sum ≤ R ^ 2 / β :=
    (hleft i).trans (div_le_div_of_nonneg_right (hrow i) hβ.le)
  have hright' (j) : (ts.map (fun t => ‖t.rightFeature j‖ ^ 2)).sum ≤ R ^ 2 / β :=
    (hright j).trans (div_le_div_of_nonneg_right (hcol j) hβ.le)
  have hmass' := hmass.trans (div_le_div_of_nonneg_right henergy hβ.le)
  have hblock (c : F) : opNorm (extractedBlock ts c) ≤ d := by
    exact extractedBlock_uniform_norm_le χ hχ ts (fun t hm => (ht t hm).1) A E hdec
      (graphPhase_fixes_supported ψ inputTensor inputTensor A hsupport)
      β (2 / Real.sqrt (vectorCard F (n * n) : ℝ)) (R ^ 2 / β) (by positivity) (by positivity)
      htwist (by
        intro c e hce
        change opNorm (graphPhase ψ inputTensor inputTensor c ⊙ inversePhase
          (graphPhase ψ inputTensor inputTensor e)) ≤ _
        rw [graphPhase_quotient]
        exact tensor_graphPhase_uniform_norm_le hn ψ hψ (c - e) (sub_ne_zero.mpr hce))
      hleft' hright' c
  have hblockMean (c : F) : uavg (fun M =>
      max (opNorm (graphRestriction inputTensor inputTensor (extractedBlock ts c) M) - d) 0) ≤
      jointGramCost F n (R ^ 2 / β) (H / β) :=
    joint_extractedBlock_graph_excess_mean hn ts ht c _ _ d (by positivity)
      hleft' hright' hmass' (hblock c)
  have hEentry := extracted_residual_entry_le χ hχ ts (fun t hm => (ht t hm).1)
    A E hdec L (R ^ 2 / β) hentry hleft' hright'
  have hEmean : uavg (fun M => opNorm (graphRestriction inputTensor inputTensor E M)) ≤
      (fieldCard F : ℝ) * Real.sqrt β * fourthRoot H +
      (fourthRoot (tensorCycleErrorConstant F) / Real.sqrt (vectorCard F n : ℝ)) * (L + R ^ 2 / β) := by
    have h := tensor_graph_norm_mean hn ψ hψ E (L + R ^ 2 / β) β (by positivity) hβ.le
      hEentry (fun c => htwist c)
    rw [← uniform_complex_energy] at h
    exact h.trans (add_le_add
      (mul_le_mul_of_nonneg_left (fourthRoot_mono (hresEnergy.trans henergy)) (by positivity)) le_rfl)
  have hdec' : A = (∑ c, inversePhase (χ c) ⊙ extractedBlock ts c) + E := by
    rw [← extractedBlock_decomposition]
    exact hdec
  have hpoint (M : Refresh.«GL» F (n * n)) :
      max (opNorm (graphRestriction inputTensor inputTensor A M) - (fieldCard F : ℝ) * d) 0 ≤
        (∑ c, max (opNorm (graphRestriction inputTensor inputTensor (extractedBlock ts c) M) - d) 0) +
          opNorm (graphRestriction inputTensor inputTensor E M) := by
    have hd := graphRestriction_decomposition_norm ψ inputTensor inputTensor A E
      (extractedBlock ts) hdec' M
    change opNorm (graphRestriction inputTensor inputTensor A M) ≤
      (∑ c, opNorm (graphRestriction inputTensor inputTensor (extractedBlock ts c) M)) +
        opNorm (graphRestriction inputTensor inputTensor E M) at hd
    have hs : (∑ c, opNorm (graphRestriction inputTensor inputTensor (extractedBlock ts c) M)) ≤
        (fieldCard F : ℝ) * d + ∑ c, max
          (opNorm (graphRestriction inputTensor inputTensor (extractedBlock ts c) M) - d) 0 := by
      calc
        _ ≤ ∑ c, (d + max
            (opNorm (graphRestriction inputTensor inputTensor (extractedBlock ts c) M) - d) 0) :=
          Finset.sum_le_sum (fun c _ => by
            have hh := le_max_left
              (opNorm (graphRestriction inputTensor inputTensor (extractedBlock ts c) M) - d) 0
            linarith)
        _ = _ := by rw [Finset.sum_add_distrib]; simp [fieldCard]
    apply max_le
    · linarith
    · unfold opNorm
      positivity
  have hav := uavg_mono hpoint
  rw [uavg_add, uavg_sum] at hav
  exact hav.trans (add_le_add
    ((Finset.sum_le_sum (fun c _ => hblockMean c)).trans_eq (by simp [fieldCard])) hEmean)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For S a set; f, w ∈ S → ℝ; d, e ∈ ℝ, assume S is finite; ∀ s, 0 ≤ w(s); ∀ s, w(s) ≤ 1; 𝔼ₛ [max{(f(s) - d), 0}] ≤ e. Then

𝔼ₛ [w(s) · f(s)] ≤ d · 𝔼ᵤ [w(u)] + e.
-/
lemma uniform_weighted_bound_of_excess {S : Type*} [Fintype S]
    (f w : S → ℝ) (d e : ℝ) (hw0 : ∀ s, 0 ≤ w s) (hw1 : ∀ s, w s ≤ 1)
    (he : uavg (fun s => max (f s - d) 0) ≤ e) :
    uavg (fun s => w s * f s) ≤ d * uavg w + e := by
  have hp (s : S) : w s * f s ≤ d * w s + max (f s - d) 0 := by
    have h := mul_le_mul_of_nonneg_left (le_max_left (f s - d) 0) (hw0 s)
    have h' := mul_le_mul_of_nonneg_right (hw1 s) (le_max_right (f s - d) 0)
    nlinarith
  have h := uavg_mono hp
  rw [uavg_add, uavg_const_mul] at h
  linarith

/-- The complete capped-table operator estimate, already weighted by any matrix-dependent rectangle norm in `[0,1]`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ψ ∈ AddChar(F, ℂ); A ∈ ℂ^(((U(F, n) × U(F, n)) × U(F, (n · n))) × ((U(F, n) × U(F, n)) × U(F, (n · n)))); R, L, β, H, t ∈ ℝ; w ∈ GL_(n · n)(F) → ℝ, assume 2 ≤ n; ψ.IsPrimitive; 0 < L; 0 < β; 0 ≤ H; energy(A) ≤ H; opNorm(A) ≤ t; ∀ i, j, (graphConstraint(inputTensor, inputTensor, i, j) ≠ 0) ⇒ A(i, j) = 0; ∀ M, 0 ≤ w(M); ∀ M, w(M) ≤ 1. Then

𝔼_M [w(M) · opNorm(graphRestriction(inputTensor, inputTensor, capped(A, R, L), M))] ≤ |F| · (t + R² / L + β + |F| · (2 / √(|F|^(n · n))) · (R² / β)) · 𝔼ᵤ [w(u)] + jointOperatorError(F, n, R, L, β, H).
-/
theorem joint_capped_graph_weighted (hn : 2 ≤ n) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (A : Matrix ((U F n × U F n) × U F (n * n)) ((U F n × U F n) × U F (n * n)) ℂ)
    (R L β H t : ℝ) (hL : 0 < L) (hβ : 0 < β) (hH : 0 ≤ H)
    (henergy : energy A ≤ H) (hop : opNorm A ≤ t)
    (hsupport : ∀ i j, graphConstraint inputTensor inputTensor i j ≠ 0 → A i j = 0)
    (w : Refresh.«GL» F (n * n) → ℝ) (hw0 : ∀ M, 0 ≤ w M) (hw1 : ∀ M, w M ≤ 1) :
    uavg (fun M => w M * opNorm (graphRestriction inputTensor inputTensor (capped A R L) M)) ≤
      (fieldCard F : ℝ) * (t + R ^ 2 / L + β +
        (fieldCard F : ℝ) * (2 / Real.sqrt (vectorCard F (n * n) : ℝ)) * (R ^ 2 / β)) * uavg w +
          jointOperatorError F n R L β H := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  letI : Nonempty (U F (n * n)) := ⟨unitShare ⟨0, by nlinarith⟩⟩
  have h := joint_supported_graph_excess hn ψ hψ (capped A R L) R L β H hL.le hβ hH
    (capped_rowEnergy_le A R L hL.le) (capped_columnEnergy_le A R L hL.le)
    (capped_entry_le A R L hL.le) ((capped_energy_le A R L hL.le).trans henergy)
    (fun i j hij => capped_preserves_zero A R L i j (hsupport i j hij))
  have hw := uniform_weighted_bound_of_excess _ w _ _ hw0 hw1 h
  apply hw.trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_right _ (uavg_nonneg hw0)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hc := (capped_opNorm_le A R L hL).trans (add_le_add hop le_rfl)
  linarith

end

end CircuitCompiler
