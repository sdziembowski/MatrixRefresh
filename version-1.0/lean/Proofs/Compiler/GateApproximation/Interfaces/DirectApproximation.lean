import Proofs.Compiler.GateApproximation.Interfaces.DirectResidual
import Proofs.Compiler.GateApproximation.Interfaces.FourCycle
import Proofs.Compiler.GateApproximation.Interfaces.NuclearBound



/-!
# Direct approximation for the actual answer table

The complete analytic argument uses the actual strict truncation, the actual conditional answer distribution, and the proved invertible-matrix fourth moment. The absolute constants are deliberately rounded up; no local approximation, nuclear budget, moment, or residual-error premise is assumed at the endpoint.
-/
set_option autoImplicit false

set_option maxHeartbeats 2200000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.AnswerApproximation

open Refresh MatrixRefresh TableAnalysis RefreshAnalysis SingularTruncation

noncomputable section

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D, β ∈ ℝ, assume 0 < D; 0 < β; β ≤ 1; 1 ≤ D · β³. Then

1 / (D · β) ≤ β² ∧ 1 / D ≤ β² ∧ 1 / (D² · β²) ≤ β².
-/
theorem threshold_inverse_bounds (D β : ℝ) (hD : 0 < D) (hβ : 0 < β)
    (hβone : β ≤ 1) (hthreshold : 1 ≤ D * β ^ 3) :
    1 / (D * β) ≤ β ^ 2 ∧ 1 / D ≤ β ^ 2 ∧
      1 / (D ^ 2 * β ^ 2) ≤ β ^ 2 := by
  have h₁ : 1 / (D * β) ≤ β ^ 2 := by
    apply (div_le_iff₀ (mul_pos hD hβ)).2
    nlinarith [hthreshold]
  have hb : β ^ 2 ≤ 1 := by nlinarith
  have h₂ : 1 / D ≤ β ^ 2 := by
    have h := mul_le_mul_of_nonneg_right h₁ hβ.le
    have he : 1 / (D * β) * β = 1 / D := by field_simp
    rw [he] at h
    exact h.trans (by nlinarith)
  have h₃ : 1 / (D ^ 2 * β ^ 2) ≤ β ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (D * β)) h₁ 2
    have he : (1 / (D * β)) ^ 2 = 1 / (D ^ 2 * β ^ 2) := by ring
    rw [he] at h
    exact h.trans (by nlinarith [sq_nonneg (β^2 - 1)])
  exact ⟨h₁, h₂, h₃⟩

variable {F X Z : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Z] {m : ℕ}

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m), assume 2 ≤ m; a is injective. Then

2 / (|F|ᵐ - 2) ≤ 3 / |X|.
-/
theorem feature_density_error_coefficient (hm : 2 ≤ m)
    (a : X → U F m) (ha : Function.Injective a) :
    2 / ((vectorCard F m : ℝ) - 2) ≤ 3 / (Fintype.card X : ℝ) := by
  have hQ := vectorCard_real_ge_four (F := F) hm
  have hD : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc : (Fintype.card X : ℝ) ≤ (vectorCard F m : ℝ) - 1 := by
    rw [← card_U_real F m]
    exact_mod_cast Fintype.card_le_of_injective a ha
  apply (div_le_div_iff₀ (by linarith : 0 < (vectorCard F m : ℝ) - 2) hD).2
  linarith

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a, b ∈ X → U(F, m); A ∈ ℝ^((X × U(F, m)) × (X × U(F, m))); β ∈ ℝ, assume |F| = 2; 2 ≤ m; a is injective; b is injective; ∀ x, y, |A(x, y)| ≤ 1; 0 < β; β ≤ 1; 1 ≤ |X| · β³. Then

‖ approximationResidual(refreshConsistent(a, b), A, β)‖ₒₚ ≤ 3 · β.
-/
theorem feature_strict_residual_op (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (A : Matrix (X × U F m) (X × U F m) ℝ) (hA : ∀ x y, |A x y| ≤ 1)
    (β : ℝ) (hβ : 0 < β) (hβone : β ≤ 1)
    (hthreshold : 1 ≤ (Fintype.card X : ℝ) * β ^ 3) :
    largestSingularCoefficient (approximationResidual (refreshConsistent a b) A β) ≤ 3 * β := by
  letI : Nonempty (U F m) := ⟨a (Classical.choice inferInstance)⟩
  have hD : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  have hi := (threshold_inverse_bounds _ β hD hβ hβone hthreshold).1
  have hs := div_le_div_of_nonneg_right (injective_consistency_sign_op hq hm a b ha hb) hβ.le
  have he : (2 / (Fintype.card X : ℝ)) / β = 2 * (1 / ((Fintype.card X : ℝ) * β)) := by ring
  rw [he] at hs
  have h := approximationResidual_op (refreshConsistent a b) A β hβ hA
  nlinarith

-- Auxiliary lemma (local approximation); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Over the binary field, let m ≥ 2 and injective a,b:X → 𝔽₂ᵐ ∖ {0}. Let A be supported on consistent tuples, with every entry of absolute value at most one. If 0<β ≤ 1 and |X|β³ ≥ 1, put E = A-2 · project(A^(>β)). Then

𝔼_(M ← GLₘ) [‖E^M‖ₒₚ⁴] ≤ 8⁴ · β² · ‖E‖₂².
-/
theorem feature_strict_residual_fourth (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (A : Matrix (X × U F m) (X × U F m) ℝ)
    (hA : ∀ x y, |A x y| ≤ 1)
    (hsupport : ∀ x y, ¬refreshConsistent a b x y → A x y = 0)
    (β : ℝ) (hβ : 0 < β) (hβone : β ≤ 1)
    (hthreshold : 1 ≤ (Fintype.card X : ℝ) * β ^ 3) :
    let E := approximationResidual (refreshConsistent a b) A β
    uavg (fun M : Refresh.«GL» F m => largestSingularCoefficient (refreshTable a b E M)^4) ≤
      (8 : ℝ)^4 * (β * tableL2Norm E)^2 := by
  letI : Nonempty (U F m) := ⟨a (Classical.choice inferInstance)⟩
  let E := approximationResidual (refreshConsistent a b) A β
  let D := (Fintype.card X : ℝ)
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast (Fintype.card_pos (α := X))
  have hs : ∀ x y, dot (a x.1).val (b y.1).val ≠ dot x.2.val y.2.val → E x y = 0 := by
    intro x y h
    exact approximationResidual_supported _ A β hsupport x y (Ne.symm h)
  have hmom := FourCycleEstimate.refreshTable_op_four_sharp hq hm a b ha hb E hs
    (3/β) 4 D (by positivity) (approximationResidual_entry _ A β hβ hβone hA)
    (by intro x; change _ ≤ (4 : ℝ)^2; norm_num; exact approximationResidual_row_sq (refreshConsistent a b) A β hA x)
    (by intro y; change _ ≤ (4 : ℝ)^2; norm_num; exact approximationResidual_column_sq (refreshConsistent a b) A β hA y)
    hD le_rfl (feature_card_geometry a ha).2
  have hc (M : Refresh.«GL» F m) :
      GateTruncation.opNorm (fun x y => (refreshTable a b E M x y : ℂ)) =
        largestSingularCoefficient (refreshTable a b E M) := refreshTable_op_complex a b E M
  simp_rw [hc] at hmom
  have henergy : uavg (fun x => uavg (fun y => E x y ^ 2)) = tableL2Norm E ^ 2 := by
    rw [tableL2Norm_sq, signedL2Sq]
    exact (uavg_prod (fun xy => E xy.1 xy.2 ^ 2)).symm
  rw [henergy] at hmom
  have hop := feature_strict_residual_op hq hm a b ha hb A hA β hβ hβone hthreshold
  have hcyc := (fourCycle_le_op_sq_l2_sq E).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (largestSingularCoefficient_nonneg E) hop 2) (sq_nonneg _))
  have hi := threshold_inverse_bounds D β hD hβ hβone hthreshold
  have h₁ := mul_le_mul_of_nonneg_right hi.2.1 (sq_nonneg (tableL2Norm E))
  have h₂ := mul_le_mul_of_nonneg_right hi.2.2 (sq_nonneg (tableL2Norm E))
  have he₁ : (32 / D) * (4 : ℝ)^2 * tableL2Norm E^2 = 512 * (1 / D * tableL2Norm E^2) := by ring
  have he₂ : (72 / D^2) * (3/β)^2 * tableL2Norm E^2 =
      648 * (1 / (D^2 * β^2) * tableL2Norm E^2) := by ring
  rw [he₁, he₂] at hmom
  change _ ≤ (8 : ℝ)^4 * (β * tableL2Norm E)^2
  nlinarith [mul_nonneg (sq_nonneg β) (sq_nonneg (tableL2Norm E))]

/-- Direct approximation for every answer of the actual common-matrix experiment. All matrix, mask, nuclear and moment estimates are proved inputs. -/

/-
Mathematical statement (normal notation): Let the field be binary, let m ≥ 2, and let a,b:X → 𝔽₂ᵐ ∖ {0} be injective. For every leakage partition and every answer z, write A = prob_z for its supported answer table. If 0<β ≤ 1 and |X| · β³ ≥ 1, then

‖A-2 · project(A^(>β))‖₂ ≤ 66 · β^(1/3).

All table norms use uniform row and column measures. This is the generalized local error estimate; ordinary refreshing is the case a = b = id.
-/
theorem feature_answer_strict_error (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a b : X → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (p : TableRectanglePartition X (Refresh.«GL» F m) Z) (z : Z)
    (β : ℝ) (hβ : 0 < β) (hβone : β ≤ 1)
    (hthreshold : 1 ≤ (Fintype.card X : ℝ) * β ^ 3) :
    tableL2Norm (approximationResidual (refreshConsistent a b) (answerProb a b p z) β) ≤
      66 * β ^ (1 / 3 : ℝ) := by
  letI : Nonempty (U F m) := ⟨a (Classical.choice inferInstance)⟩
  let A := answerProb a b p z
  let H := strictTruncation A β
  let E := approximationResidual (refreshConsistent a b) A β
  let D := (Fintype.card X : ℝ)
  let t := tableL2Norm E
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast (Fintype.card_pos (α := X))
  have ht : 0 ≤ t := tableL2Norm_nonneg E
  have hA : ∀ x y, |A x y| ≤ 1 := answerProb_le_one a b p z
  have hs : ∀ x y, ¬refreshConsistent a b x y → A x y = 0 := answerProb_supported a b p z
  have hmom := feature_strict_residual_fourth hq hm a b ha hb A hA hs β hβ hβone hthreshold
  have hmean := residual_mean_of_fourth_moment (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F m))
    (fun M => largestSingularCoefficient (refreshTable a b E M)) 8 (β*t)
    (fun M => largestSingularCoefficient_nonneg _) (by norm_num) (mul_nonneg hβ.le ht)
    (by simpa only [← uavg_eq_expect_uniform] using hmom)
  rw [← uavg_eq_expect_uniform, Real.sqrt_mul hβ.le] at hmean
  have hp := feature_answer_pairing_le_graph_op hq hm a b p z E (3/β)
    (by positivity) (approximationResidual_entry _ A β hβ hβone hA)
  have hd := mul_le_mul_of_nonneg_right (feature_density_error_coefficient hm a ha)
    (by positivity : 0 ≤ 3/β)
  have hcross := normalized_pairing_duality H (refreshSign (refreshConsistent a b) ⊙ H)
  have hn := TruncatedAnswerNorm.feature_answer_strict_nuclear_le_four hq hm a b ha hb p z
    β hβ hβone hthreshold
  have hop := (strictPart_schur A (refreshSign (refreshConsistent a b)) β hβ hA).trans
    (div_le_div_of_nonneg_right (injective_consistency_sign_op hq hm a b ha hb) hβ.le)
  have hcross' : |pairing H (refreshSign (refreshConsistent a b) ⊙ H)| ≤ 8 / (D*β) := by
    apply hcross.trans
    calc
      _ ≤ 4 * ((2 / D) / β) := mul_le_mul hn hop (largestSingularCoefficient_nonneg _) (by norm_num)
      _ = _ := by ring
  have hid := approximationResidual_exact_identity (refreshConsistent a b) A β hs
  have hinv := (threshold_inverse_bounds D β hD hβ hβone hthreshold).1
  have hbeta : t^2 ≤ 32 * Real.sqrt β * Real.sqrt t + 32 * β^2 := by
    have he : (3 / D) * (3 / β) = 9 / (D*β) := by ring
    rw [he] at hd
    have h₁ := le_abs_self (pairing A E)
    have h₂ := le_abs_self (pairing H (refreshSign (refreshConsistent a b) ⊙ H))
    change t^2 = pairing A E + 2 * pairing H (refreshSign (refreshConsistent a b) ⊙ H) at hid
    have hroot : 0 ≤ Real.sqrt β * Real.sqrt t := by positivity
    have h41 := mul_le_mul_of_nonneg_left hinv (by norm_num : (0:ℝ)≤41)
    have he41 : 41 * (1 / (D*β)) = 41 / (D*β) := by ring
    rw [he41] at h41
    change 2 * |pairing A E| ≤ _ at hp
    simp only [div_eq_mul_inv] at hp hd hcross' h41
    nlinarith
  have h := residual_error_bootstrap β t 32 hβ hβone ht (by norm_num) hbeta
  norm_num at h
  exact h

end

end CircuitCompiler.AnswerApproximation
