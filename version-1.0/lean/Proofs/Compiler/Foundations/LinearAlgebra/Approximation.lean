import Proofs.Compiler.Foundations.LinearAlgebra.GramBounds
import Proofs.Compiler.Foundations.LinearAlgebra.Induction
import Proofs.Compiler.Foundations.LinearAlgebra.NuclearDiscrepancy
import Proofs.Compiler.Foundations.LinearAlgebra.StateDensity



/-!
# Forward signed approximations and norm recurrences

The compression procedure is an explicit argument at this modular layer. The actual one-round compression theorem supplies that procedure at the final assembly. No numeric induction theorem is mistaken for a protocol security theorem here.
-/

set_option autoImplicit false

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace TableAnalysis

open MatrixRefresh Refresh

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

‖ ((x, x ∈ ι ↦ 1))‖_(*,count) ≤ |ι|.
-/
theorem nuclearNorm_one_le_card : nuclearNorm (fun _ _ : ι => (1 : ℝ)) ≤
    (Fintype.card ι : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg _)
  intro W
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ => 1)
  have hv : ‖v‖ ^ 2 = Fintype.card ι := by
    simp [v, EuclideanSpace.norm_sq_eq]
  have hp : countingPairing (Matrix.of fun _ _ : ι => (1 : ℝ)) W =
      inner ℝ v (W.toEuclideanLin v) := by
    simp [countingPairing, PiLp.inner_apply, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, v]
  have hi := (abs_real_inner_le_norm v (W.toEuclideanLin v)).trans
    (mul_le_mul_of_nonneg_left
      (W.toEuclideanLin.toContinuousLinearMap.le_opNorm v) (norm_nonneg v))
  change |countingPairing (Matrix.of fun _ _ : ι => (1 : ℝ)) W| ≤
    (Fintype.card ι : ℝ) * ‖W‖
  rw [hp]
  calc
    _ ≤ ‖v‖ * (‖W‖ * ‖v‖) := by
      simpa only [Matrix.l2_opNorm_def, LinearEquiv.trans_apply,
        LinearMap.coe_toContinuousLinearMap'] using hi
    _ = ‖v‖ ^ 2 * ‖W‖ := by ring
    _ = (Fintype.card ι : ℝ) * ‖W‖ := by rw [hv]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume ι ≠ ∅. Then

‖ ((x, x ∈ ι ↦ 1))‖_* ≤ 1.
-/
theorem tableNuclearNorm_one_le [Nonempty ι] :
    tableNuclearNorm (fun _ _ : ι => (1 : ℝ)) ≤ 1 := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold tableNuclearNorm
  rw [div_le_iff₀ hd, one_mul]
  exact nuclearNorm_one_le_card

section Actual

variable {F Z : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype Z] {n : ℕ}

variable {i : ℕ}

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ State(F, n) → ℝ, we have

‖ A‖₂ = ‖ A‖₂.
-/
theorem stateMatrix_HS (A : State F n → ℝ) :
    tableL2Norm (stateMatrix A) = signedL2 A := by
  rw [tableL2Norm_eq_signedL2]
  unfold signedL2 signedL2Sq
  congr 1
  exact (uavg_equiv (stateEquivProd F n)
    (fun p => (stateMatrix A p.1 p.2) ^ 2)).symm

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ State(F, n) → ℝ, we have

tableL1(A) = signedL1(A).
-/
theorem stateMatrix_L1 (A : State F n → ℝ) :
    tableL1 (stateMatrix A) = signedL1 A := by
  unfold tableL1 signedL1
  exact (uavg_equiv (stateEquivProd F n)
    (fun p => |stateMatrix A p.1 p.2|)).symm

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X a set; A, B ∈ X → ℝ, assume X is finite. Then

signedL1(((x ↦ A(x) + B(x)))) ≤ signedL1(A) + signedL1(B).
-/
theorem signedL1_triangle {X : Type*} [Fintype X] (A B : X → ℝ) :
    signedL1 (fun x => A x + B x) ≤ signedL1 A + signedL1 B := by
  unfold signedL1
  rw [← uavg_add]
  exact uavg_mono (fun x => abs_add_le _ _)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B ∈ State(F, n) → ℝ, we have

signedL1(B) ≤ signedL1(A) + signedL1(((x ↦ A(x) - B(x)))).
-/
theorem signedL1_approx_mass (A B : State F n → ℝ) :
    signedL1 B ≤ signedL1 A + signedL1 (fun x => A x - B x) := by
  unfold signedL1
  rw [← uavg_add]
  apply uavg_mono
  intro x
  have h := abs_sub (A x) (A x - B x)
  simpa only [sub_sub_cancel] using h

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ GLRectanglePartition(F, n, Z); A, B ∈ State(F, n) → ℝ, we have

glRoundOp(p, ((x ↦ A(x) - B(x)))) = (z, x ↦ glRoundOp(p, A, z, x) - glRoundOp(p, B, z, x)).
-/
theorem glRoundOp_sub (p : GLRectanglePartition F n Z) (A B : State F n → ℝ) :
    glRoundOp p (fun x => A x - B x) = fun z x => glRoundOp p A z x - glRoundOp p B z x := by
  funext z x
  unfold glRoundOp roundOp
  simp_rw [sub_mul]
  exact uavg_sub _ _

/-- Output contract of the genuine one-round compression procedure. -/
/-
Mathematical definition (normal notation): A compression step for A provides output tables G_z. Put K := |Z|, p := p_min, c := ‖A‖₂, b := ‖A‖_*, and m := ‖A‖₁. It certifies

∑_z ‖G_z‖_* ≤ √K · ‖A‖ₒₚ, ‖G_z‖₂ ≤ ‖𝒯_z(A)‖₂,

and

∑_z ‖𝒯_z(A)-G_z‖₁ ≤ θ√K((2c+√cb)/√p+2m/p+2√K c).

Here 𝒯_z is the leakage-restricted round operator.
-/
structure CompressionStep (θ : ℝ) (p : GLRectanglePartition F n Z)
    (A : State F n → ℝ) where
  output : Z → State F n → ℝ
  nuclear : (∑ z, tableNuclearNorm (stateMatrix (output z))) ≤
    Real.sqrt (Fintype.card Z) * largestSingularCoefficient (stateMatrix A)
  l2_bound : ∀ z, signedL2 (output z) ≤ signedL2 (glRoundOp p A z)
  error : (∑ z, signedL1 (fun x => glRoundOp p A z x - output z x)) ≤
    compressionIncrement (Fintype.card Z) (minSecretProbability F n) θ
      (signedL2 A) (tableNuclearNorm (stateMatrix A)) (signedL1 A)

/-
Mathematical definition (normal notation): For F a set; n ∈ ℕ; Z a set; θ ∈ ℝ, assume F is a field; F is finite; Z is finite. define

CompressionProcedure(n, θ) := ∏_(p ∈ GLRectanglePartition(F, n, Z)) ∏_(A ∈ State(F, n) → ℝ) CompressionStep(θ, p, A).
-/
abbrev CompressionProcedure (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) (Z : Type*) [Fintype Z] (θ : ℝ) :=
  (p : GLRectanglePartition F n Z) → (A : State F n → ℝ) → CompressionStep θ p A

/- Mathematical definition (normal notation): Define G_(0,∅) := 1. If a history extends as h‖z, let G_(i+1,h‖z) be the zth output of the specified compression procedure applied to G_(i,h) with the round partition selected by h. -/
def approximateDensity (p : RectangleProtocol F n Z) (θ : ℝ)
    (compress : CompressionProcedure F n Z θ) :
    (i : ℕ) → PublicHistory Z i → State F n → ℝ
  | 0, _, _ => 1
  | i + 1, h, x =>
      (compress (p i (Fin.init h))
        (approximateDensity p θ compress i (Fin.init h))).output (h (Fin.last i)) x

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); θ ∈ ℝ; compress ∈ CompressionProcedure(F, n, Z, θ); i ∈ ℕ; h ∈ PublicHistory(Z, i); z ∈ Z, we have

approximateDensity(p, θ, compress, (i + 1), Fin.snoc(h, z)) = output(compress(p(i, h), approximateDensity(p, θ, compress, i, h)))(z).
-/
@[simp] theorem approximateDensity_snoc (p : RectangleProtocol F n Z) (θ : ℝ)
    (compress : CompressionProcedure F n Z θ) (i : ℕ) (h : PublicHistory Z i) (z : Z) :
    approximateDensity p θ compress (i + 1) (Fin.snoc h z) =
      (compress (p i h) (approximateDensity p θ compress i h)).output z := by
  funext x
  have hi : Fin.init (Fin.snoc (α := fun _ : Fin (i + 1) => Z) h z) = h :=
    @Fin.init_snoc i (fun _ : Fin (i + 1) => Z) z h
  simp only [approximateDensity, Fin.snoc_last]
  rw [hi]

/-
Mathematical definition (normal notation): For P, G ∈ PublicHistory(Z, i) → State(F, n) → ℝ, define

approximationError(P, G) := ∑ₕ (signedL1(((x ↦ P(h, x) - G(h, x))))).
-/
def approximationError (P G : PublicHistory Z i → State F n → ℝ) : ℝ :=
  ∑ h, signedL1 (fun x => P h x - G h x)

/-
Mathematical definition (normal notation): For G ∈ PublicHistory(Z, i) → State(F, n) → ℝ, define

approximationL2(G) := ∑ₕ (‖ G(h)‖₂).
-/
def approximationL2 (G : PublicHistory Z i → State F n → ℝ) : ℝ :=
  ∑ h, signedL2 (G h)

/-
Mathematical definition (normal notation): For G ∈ PublicHistory(Z, i) → State(F, n) → ℝ, define

approximationNuclear(G) := ∑ₕ (‖ G(h)‖_*).
-/
def approximationNuclear (G : PublicHistory Z i → State F n → ℝ) : ℝ :=
  ∑ h, tableNuclearNorm (stateMatrix (G h))

/-
Mathematical definition (normal notation): For G ∈ PublicHistory(Z, i) → State(F, n) → ℝ, define

approximationMass(G) := ∑ₕ (signedL1(G(h))).
-/
def approximationMass (G : PublicHistory Z i → State F n → ℝ) : ℝ :=
  ∑ h, signedL1 (G h)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); i ∈ ℕ; G ∈ PublicHistory(Z, i) → State(F, n) → ℝ, assume 2 ≤ n. Then

approximationMass(G) ≤ 1 + approximationError(currentDensity(p, i), G).
-/
theorem approximationMass_le (hn : 2 ≤ n) (p : RectangleProtocol F n Z) (i : ℕ)
    (G : PublicHistory Z i → State F n → ℝ) :
    approximationMass G ≤ 1 + approximationError (currentDensity p i) G := by
  unfold approximationMass approximationError
  calc
    _ ≤ ∑ h, (signedL1 (currentDensity p i h) +
        signedL1 (fun x => currentDensity p i h x - G h x)) :=
      Finset.sum_le_sum (fun h _ => signedL1_approx_mass _ _)
    _ = _ := by rw [Finset.sum_add_distrib, currentDensity_L1_mass hn p i]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For G ∈ PublicHistory(Z, i) → State(F, n) → ℝ, we have

0 ≤ approximationNuclear(G).
-/
theorem approximationNuclear_nonneg (G : PublicHistory Z i → State F n → ℝ) :
    0 ≤ approximationNuclear G :=
  Finset.sum_nonneg (fun _ _ => tableNuclearNorm_nonneg _)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P, G ∈ PublicHistory(Z, i) → State(F, n) → ℝ, assume 2 ≤ n. Then

approximationError(P, G) = terminalError(independentStateDistribution(F, n), P, G).
-/
theorem approximationError_eq_terminalError (hn : 2 ≤ n)
    (P G : PublicHistory Z i → State F n → ℝ) :
    approximationError P G = terminalError (independentStateDistribution F n hn) P G := by
  letI := state_nonempty (F := F) hn
  simp only [approximationError, terminalError, signedL1, uavg_eq_expect_uniform,
    uniform_state_eq_independent hn]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); θ ∈ ℝ; compress ∈ CompressionProcedure(F, n, Z, θ), we have

approximationError(currentDensity(p, 0), approximateDensity(p, θ, compress, 0)) = 0.
-/
theorem approximateDensity_initial_error (p : RectangleProtocol F n Z) (θ : ℝ)
    (compress : CompressionProcedure F n Z θ) :
    approximationError (currentDensity p 0) (approximateDensity p θ compress 0) = 0 := by
  simp [approximationError, currentDensity, approximateDensity, signedL1]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); θ ∈ ℝ; compress ∈ CompressionProcedure(F, n, Z, θ), assume 2 ≤ n. Then

approximationL2(approximateDensity(p, θ, compress, 0)) = 1.
-/
theorem approximateDensity_initial_l2 (hn : 2 ≤ n) (p : RectangleProtocol F n Z)
    (θ : ℝ) (compress : CompressionProcedure F n Z θ) :
    approximationL2 (approximateDensity p θ compress 0) = 1 := by
  letI := state_nonempty (F := F) hn
  simp [approximationL2, approximateDensity, signedL2, signedL2Sq]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); θ ∈ ℝ; compress ∈ CompressionProcedure(F, n, Z, θ), assume 2 ≤ n. Then

approximationNuclear(approximateDensity(p, θ, compress, 0)) ≤ 1.
-/
theorem approximateDensity_initial_nuclear (hn : 2 ≤ n) (p : RectangleProtocol F n Z)
    (θ : ℝ) (compress : CompressionProcedure F n Z θ) :
    approximationNuclear (approximateDensity p θ compress 0) ≤ 1 := by
  letI : Nonempty (U F n) := ⟨(Classical.choice (state_nonempty (F := F) hn)).L⟩
  convert! (tableNuclearNorm_one_le (ι := U F n)) using 1 <;>
    simp [approximationNuclear, approximateDensity, stateMatrix]
  congr 1

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): For n ≥ 2, the recursively compressed density family satisfies ∑_(h ∈ Zⁱ⁺¹) ‖G_(i+1,h)‖₂ ≤ √(|Z|/p_min) · ∑_(h ∈ Zⁱ) ‖G_(i,h)‖₁, where p_min is the least secret-fiber probability under independent uniform shares. -/
theorem approximateDensity_l2_step (hn : 2 ≤ n) (p : RectangleProtocol F n Z)
    (θ : ℝ) (compress : CompressionProcedure F n Z θ) (i : ℕ) :
    approximationL2 (approximateDensity p θ compress (i + 1)) ≤
      Real.sqrt ((Fintype.card Z : ℝ) / minSecretProbability F n) *
        approximationMass (approximateDensity p θ compress i) := by
  unfold approximationL2 approximationMass
  rw [sum_publicHistory_snoc]
  simp_rw [approximateDensity_snoc]
  calc
    _ ≤ ∑ h : PublicHistory Z i, ∑ z,
        signedL2 (glRoundOp (p i h) (approximateDensity p θ compress i h) z) := by
      apply Finset.sum_le_sum
      intro h _
      exact Finset.sum_le_sum (fun z _ => (compress _ _).l2_bound z)
    _ ≤ ∑ h : PublicHistory Z i,
        Real.sqrt ((Fintype.card Z : ℝ) / minSecretProbability F n) *
          signedL1 (approximateDensity p θ compress i h) :=
      Finset.sum_le_sum (fun h _ => gl_sum_signedL2_roundOp_le hn _ _)
    _ = _ := (Finset.mul_sum _ _ _).symm

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); θ ∈ ℝ; compress ∈ CompressionProcedure(F, n, Z, θ); i ∈ ℕ, we have

approximationNuclear(approximateDensity(p, θ, compress, (i + 1))) ≤ √(|Z|) · approximationL2(approximateDensity(p, θ, compress, i)).
-/
theorem approximateDensity_nuclear_step (p : RectangleProtocol F n Z)
    (θ : ℝ) (compress : CompressionProcedure F n Z θ) (i : ℕ) :
    approximationNuclear (approximateDensity p θ compress (i + 1)) ≤
      Real.sqrt (Fintype.card Z : ℝ) *
        approximationL2 (approximateDensity p θ compress i) := by
  unfold approximationNuclear approximationL2
  rw [sum_publicHistory_snoc]
  simp_rw [approximateDensity_snoc]
  calc
    _ ≤ ∑ h : PublicHistory Z i, Real.sqrt (Fintype.card Z : ℝ) *
        largestSingularCoefficient (stateMatrix (approximateDensity p θ compress i h)) :=
      Finset.sum_le_sum (fun h _ => (compress _ _).nuclear)
    _ ≤ ∑ h : PublicHistory Z i, Real.sqrt (Fintype.card Z : ℝ) *
        signedL2 (approximateDensity p θ compress i h) := by
      apply Finset.sum_le_sum
      intro h _
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      rw [← stateMatrix_HS]
      exact largestSingularCoefficient_le_tableL2Norm _
    _ = _ := (Finset.mul_sum _ _ _).symm

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For H a set; K, pMin, θ ∈ ℝ; c, b, m ∈ H → ℝ, assume H is finite; 0 < pMin; 0 ≤ θ; ∀ h, 0 ≤ c(h); ∀ h, 0 ≤ b(h). Then

(∑ₕ (compressionIncrement(K, pMin, θ, c(h), b(h), m(h)))) ≤ compressionIncrement(K, pMin, θ, (∑ₕ (c(h))), (∑ₕ (b(h))), (∑ₕ (m(h)))).
-/
theorem sum_compressionIncrement_le {H : Type*} [Fintype H]
    (K pMin θ : ℝ) (c b m : H → ℝ) (hpMin : 0 < pMin) (hθ : 0 ≤ θ)
    (hc : ∀ h, 0 ≤ c h) (hb : ∀ h, 0 ≤ b h) :
    (∑ h, compressionIncrement K pMin θ (c h) (b h) (m h)) ≤
      compressionIncrement K pMin θ (∑ h, c h) (∑ h, b h) (∑ h, m h) := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.univ : Finset H)
    (r := fun h => Real.sqrt (c h * b h)) (f := c) (g := b)
    (fun h _ => hc h) (fun h _ => hb h)
    (fun h _ => Real.sq_sqrt (mul_nonneg (hc h) (hb h)))
  have hs : (∑ h, Real.sqrt (c h * b h)) ≤ Real.sqrt ((∑ h, c h) * ∑ h, b h) :=
    Real.le_sqrt_of_sq_le hcs
  calc
    _ = θ * Real.sqrt K *
        ((2 * (∑ h, c h) + (∑ h, Real.sqrt (c h * b h))) / Real.sqrt pMin +
          2 * (∑ h, m h) / pMin + 2 * Real.sqrt K * (∑ h, c h)) := by
      let ac := θ * Real.sqrt K * (2 / Real.sqrt pMin + 2 * Real.sqrt K)
      let ab := θ * Real.sqrt K / Real.sqrt pMin
      let am := θ * Real.sqrt K * 2 / pMin
      have hexp (h : H) : compressionIncrement K pMin θ (c h) (b h) (m h) =
          ac * c h + ab * Real.sqrt (c h * b h) + am * m h := by
        dsimp [compressionIncrement, ac, ab, am]
        ring
      simp_rw [hexp]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      dsimp [ac, ab, am]
      ring
    _ ≤ _ := by unfold compressionIncrement; gcongr

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); θ ∈ ℝ; compress ∈ CompressionProcedure(F, n, Z, θ); i ∈ ℕ, assume 2 ≤ n; 0 ≤ θ. Then

approximationError(currentDensity(p, (i + 1)), approximateDensity(p, θ, compress, (i + 1))) ≤ approximationError(currentDensity(p, i), approximateDensity(p, θ, compress, i)) + compressionIncrement(|Z|, minSecretProbability(F, n), θ, approximationL2(approximateDensity(p, θ, compress, i)), approximationNuclear(approximateDensity(p, θ, compress, i)), approximationMass(approximateDensity(p, θ, compress, i))).
-/
theorem approximateDensity_error_step (hn : 2 ≤ n) (p : RectangleProtocol F n Z)
    (θ : ℝ) (hθ : 0 ≤ θ) (compress : CompressionProcedure F n Z θ) (i : ℕ) :
    approximationError (currentDensity p (i + 1))
        (approximateDensity p θ compress (i + 1)) ≤
      approximationError (currentDensity p i) (approximateDensity p θ compress i) +
        compressionIncrement (Fintype.card Z) (minSecretProbability F n) θ
          (approximationL2 (approximateDensity p θ compress i))
          (approximationNuclear (approximateDensity p θ compress i))
          (approximationMass (approximateDensity p θ compress i)) := by
  let P := currentDensity p i
  let G := approximateDensity p θ compress i
  have hone (h : PublicHistory Z i) :
      (∑ z, signedL1 (fun x => glRoundOp (p i h) (P h) z x -
        (compress (p i h) (G h)).output z x)) ≤
      signedL1 (fun x => P h x - G h x) +
        compressionIncrement (Fintype.card Z) (minSecretProbability F n) θ
          (signedL2 (G h)) (tableNuclearNorm (stateMatrix (G h))) (signedL1 (G h)) := by
    calc
      _ ≤ ∑ z, (signedL1 (glRoundOp (p i h) (fun x => P h x - G h x) z) +
          signedL1 (fun x => glRoundOp (p i h) (G h) z x -
            (compress (p i h) (G h)).output z x)) := by
        apply Finset.sum_le_sum
        intro z _
        have heq : (fun x => glRoundOp (p i h) (P h) z x -
            (compress (p i h) (G h)).output z x) =
          fun x => glRoundOp (p i h) (fun x => P h x - G h x) z x +
            (glRoundOp (p i h) (G h) z x - (compress (p i h) (G h)).output z x) := by
          funext x
          rw [glRoundOp_sub]
          ring
        rw [heq]
        exact signedL1_triangle _ _
      _ = (∑ z, signedL1 (glRoundOp (p i h) (fun x => P h x - G h x) z)) +
          ∑ z, signedL1 (fun x => glRoundOp (p i h) (G h) z x -
            (compress (p i h) (G h)).output z x) := Finset.sum_add_distrib
      _ ≤ _ := add_le_add (gl_sum_signedL1_roundOp_le _ _) (compress _ _).error
  unfold approximationError
  rw [sum_publicHistory_snoc]
  simp_rw [show ∀ h z, currentDensity p (i + 1) (Fin.snoc h z) =
      glRoundOp (p i h) (P h) z from by intro h z; funext x; exact currentDensity_snoc p i h z x,
    approximateDensity_snoc]
  calc
    _ ≤ ∑ h, (signedL1 (fun x => P h x - G h x) +
        compressionIncrement (Fintype.card Z) (minSecretProbability F n) θ
          (signedL2 (G h)) (tableNuclearNorm (stateMatrix (G h))) (signedL1 (G h))) :=
      Finset.sum_le_sum (fun h _ => hone h)
    _ = (∑ h, signedL1 (fun x => P h x - G h x)) +
        ∑ h, compressionIncrement (Fintype.card Z) (minSecretProbability F n) θ
          (signedL2 (G h)) (tableNuclearNorm (stateMatrix (G h))) (signedL1 (G h)) :=
      Finset.sum_add_distrib
    _ ≤ _ := add_le_add (le_refl _)
      (sum_compressionIncrement_le (Fintype.card Z) (minSecretProbability F n) θ
        (fun h => signedL2 (G h)) (fun h => tableNuclearNorm (stateMatrix (G h)))
        (fun h => signedL1 (G h)) (minSecretProbability_pos hn) hθ
        (fun h => signedL2_nonneg (G h)) (fun _ => tableNuclearNorm_nonneg _))

end Actual

end

end TableAnalysis
