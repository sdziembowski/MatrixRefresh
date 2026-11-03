import Proofs.Compiler.GateApproximation.MatrixPhase.ComplexRectangle
import Proofs.Compiler.GateApproximation.MatrixPhase.GateDual
import Proofs.Compiler.GateApproximation.MatrixPhase.JointLocalRates



/-!
# The summed capped dual bound for the actual matrix leakage probability table
-/
set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical

namespace CircuitCompiler

open Refresh MatrixRefresh TableAnalysis GateTruncation

noncomputable section

variable {F Z : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype Z]

/-
Mathematical definition (normal notation): For F a set; H ∈ ℝ, assume F is a field; F is finite. define

jointDualRateConstant(H) := (|F|)⁻¹ · jointGraphRateConstant(F, H) + 2 · √((|F| + 1) · H).
-/
def jointDualRateConstant (F : Type*) [Field F] [Fintype F] [DecidableEq F] (H : ℝ) : ℝ :=
  (fieldCard F : ℝ)⁻¹ * jointGraphRateConstant F H + 2 * Real.sqrt (((fieldCard F : ℝ)+1)*H)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For H ∈ ℝ, we have

0 ≤ jointDualRateConstant(F, H).
-/
theorem jointDualRateConstant_nonneg (H : ℝ) : 0 ≤ jointDualRateConstant F H := by
  unfold jointDualRateConstant
  exact add_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (jointGraphRateConstant_nonneg H)) (by positivity)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For I a set; A ∈ ℂ^(I × I); R, L, H ∈ ℝ, assume I is finite; 0 ≤ L; energy(A) ≤ H. Then

𝔼ₓ [𝔼_y [(re(capped(A, R, L, x, y)))²]] ≤ H.
-/
theorem capped_real_energy_le {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (R L H : ℝ) (hL : 0 ≤ L) (hA : energy A ≤ H) :
    uavg (fun x => uavg (fun y => ((capped A R L x y).re)^2)) ≤ H := by
  refine le_trans ?_ ((capped_energy_le A R L hL).trans hA)
  apply uavg_mono
  intro x
  apply uavg_mono
  intro y
  have h := Complex.abs_re_le_norm (capped A R L x y)
  have hsq := mul_self_le_mul_self (abs_nonneg _) h
  simpa only [← pow_two, sq_abs] using hsq

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; A ∈ ℂ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))); R, L ∈ ℝ; x, y ∈ GateSide(F, n, (n · n)), assume ∀ i, j, (graphConstraint(inputTensor, inputTensor, i, j) ≠ 0) ⇒ A(i, j) = 0; ((x)₂ · (y)₂) ≠ portProduct(x, y). Then

re(capped(A, R, L, x, y)) = 0.
-/
theorem capped_real_supported {n : ℕ}
    (A : Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℂ) (R L : ℝ)
    (hA : ∀ i j, graphConstraint inputTensor inputTensor i j ≠ 0 → A i j = 0)
    (x y : GateSide F n (n*n))
    (hxy : dot x.2.val y.2.val ≠ portProduct x y) :
    (capped A R L x y).re = 0 := by
  have h : graphConstraint inputTensor inputTensor x y ≠ 0 := by
    change dot (tensorVector x.1.1.val x.1.2.val) (tensorVector y.1.1.val y.1.2.val) -
      dot x.2.val y.2.val ≠ 0
    rw [tensorVector_dot]
    exact sub_ne_zero.mpr (Ne.symm hxy)
  rw [capped_preserves_zero A R L x y (hA x y h)]
  rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; r ∈ ℝ, assume 2 ≤ n; 1 ≤ r; |F|ⁿ = r¹⁰. Then

1 / (|F|^(n · n) - 1) ≤ 2 / r.
-/
theorem long_inverse_count_le {n : ℕ} (hn : 2 ≤ n) (r : ℝ)
    (hr : 1 ≤ r) (hN : (vectorCard F n : ℝ) = r^10) :
    1 / ((vectorCard F (n*n) : ℝ)-1) ≤ 2/r := by
  have hQ := tensor_card_square_le (F:=F) hn
  have hN4 := vectorCard_real_ge_four (F:=F) hn
  have hrN : r ≤ (vectorCard F n : ℝ) := by
    rw [hN]
    simpa only [pow_one] using pow_le_pow_right₀ hr (by decide : 1 ≤ 10)
  apply (div_le_div_iff₀ (by nlinarith : 0 < (vectorCard F (n*n) : ℝ)-1) (by linarith : 0 < r)).2
  nlinarith

/-- One actual leakage leaf, after trimming and capping its supported test. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; ψ ∈ AddChar(F, ℂ); p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z); z ∈ Z; A ∈ ℂ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))); r, H, T ∈ ℝ, assume 2 ≤ n; ψ.IsPrimitive; 1 ≤ r; |F|ⁿ = r¹⁰; 0 ≤ H; energy(A) ≤ H; opNorm(A) ≤ T; ∀ i, j, (graphConstraint(inputTensor, inputTensor, i, j) ≠ 0) ⇒ A(i, j) = 0. Then

𝔼ₓ [𝔼_y [groupedMatrixAnswerProb(p, z, x, y) · re(capped(A, r, (r³), x, y))]] ≤ T · 𝔼_M [rectangleWeight(p.leftIndicator(z, M), p.rightIndicator(z, M))] + jointDualRateConstant(F, H) / r.
-/
theorem capped_answer_table_pairing_bound {n : ℕ} (hn : 2 ≤ n)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n)) Z) (z : Z)
    (A : Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℂ)
    (r H T : ℝ) (hr : 1 ≤ r) (hN : (vectorCard F n : ℝ) = r^10) (hH : 0 ≤ H)
    (henergy : energy A ≤ H) (hop : opNorm A ≤ T)
    (hsupport : ∀ i j, graphConstraint inputTensor inputTensor i j ≠ 0 → A i j = 0) :
    uavg (fun x => uavg (fun y => groupedMatrixAnswerProb p z x y *
      (capped A r (r^3) x y).re)) ≤
      T * uavg (fun M => rectangleWeight (p.leftIndicator z M) (p.rightIndicator z M)) +
        jointDualRateConstant F H / r := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  have hr0 : 0 < r := by linarith
  have hm : 2 ≤ n*n := by nlinarith
  let w := fun M => rectangleWeight (p.leftIndicator z M) (p.rightIndicator z M)
  let V := capped A r (r^3)
  let B := fun M => uavg (fun x => uavg (fun y =>
    p.leftIndicator z M x * p.rightIndicator z M y *
      (V (x,rowRefresh (inputTensor x) M) (y,columnRefresh (inputTensor y) M)).re))
  have hprob := supported_answer_table_uniform_error hn hm p z (fun x y => (V x y).re)
    (capped_real_supported A r (r^3) hsupport) H
    (capped_real_energy_le A r (r^3) H (by positivity) henergy)
  have hrect (M : Refresh.«GL» F (n*n)) : B M ≤
      w M * opNorm (graphRestriction inputTensor inputTensor V M) := by
    exact (le_abs_self _).trans (complex_rectangle_pairing (p.leftIndicator z M)
      (p.rightIndicator z M) (graphRestriction inputTensor inputTensor V M))
  have hgraph := joint_capped_graph_weighted_rate hn ψ hψ A r H T hr hN hH henergy hop
    hsupport w (fun _ => rectangleWeight_nonneg _ _) (fun M => gate_rectangle_weight_le_one p M z)
  have hmean := (uavg_mono hrect).trans hgraph
  have hscale := mul_le_mul_of_nonneg_left hmean (inv_nonneg.mpr (fieldCard_cast_pos (F:=F)).le)
  have hprob' := (le_abs_self _).trans hprob
  have he := mul_le_mul_of_nonneg_left (long_inverse_count_le hn r hr hN)
    (Real.sqrt_nonneg (((fieldCard F : ℝ)+1)*H))
  have hcancel : (fieldCard F : ℝ)⁻¹ * ((fieldCard F : ℝ)*T*uavg w + jointGraphRateConstant F H/r) =
      T*uavg w + (fieldCard F : ℝ)⁻¹*jointGraphRateConstant F H/r := by
    field_simp [(fieldCard_cast_pos (F:=F)).ne']
  rw [hcancel] at hscale
  dsimp [jointDualRateConstant]
  change _ ≤ T*uavg w + _
  dsimp only [B, V] at hscale
  dsimp only [V] at hprob'
  simp only [div_eq_mul_inv] at he hscale hprob' ⊢
  nlinarith

/-- Summing a complete answer partition costs `sqrt(K)` on the leading operator norm; every error costs at most one term per answer. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; ψ ∈ AddChar(F, ℂ); p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z); A ∈ Z → ℂ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))); r, H, T ∈ ℝ, assume 2 ≤ n; ψ.IsPrimitive; 1 ≤ r; |F|ⁿ = r¹⁰; 0 ≤ H; 0 ≤ T; ∀ z, energy(A(z)) ≤ H; ∀ z, opNorm(A(z)) ≤ T; ∀ z, i, j, (graphConstraint(inputTensor, inputTensor, i, j) ≠ 0) ⇒ A(z, i, j) = 0. Then

(∑_z (𝔼ₓ [𝔼_y [groupedMatrixAnswerProb(p, z, x, y) · re(capped(A(z), r, (r³), x, y))]])) ≤ √(|Z|) · T + |Z| · jointDualRateConstant(F, H) / r.
-/
theorem capped_answer_table_family_bound {n : ℕ} (hn : 2 ≤ n)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n)) Z)
    (A : Z → Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℂ)
    (r H T : ℝ) (hr : 1 ≤ r) (hN : (vectorCard F n : ℝ) = r^10) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (henergy : ∀ z, energy (A z) ≤ H) (hop : ∀ z, opNorm (A z) ≤ T)
    (hsupport : ∀ z i j, graphConstraint inputTensor inputTensor i j ≠ 0 → A z i j = 0) :
    (∑ z, uavg (fun x => uavg (fun y => groupedMatrixAnswerProb p z x y *
      (capped (A z) r (r^3) x y).re))) ≤
      Real.sqrt (Fintype.card Z : ℝ)*T + (Fintype.card Z : ℝ)*jointDualRateConstant F H/r := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun z _ =>
    capped_answer_table_pairing_bound hn ψ hψ p z (A z) r H T hr hN hH
      (henergy z) (hop z) (hsupport z))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← uavg_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have hw := uavg_mono (fun M : Refresh.«GL» F (n*n) => gate_rectangle_weights_sum p M)
  rw [uavg_const] at hw
  have hlead := mul_le_mul_of_nonneg_left hw hT
  simp only [uavg_sum] at h hlead
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith

end

end CircuitCompiler
