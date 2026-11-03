import Proofs.Compiler.GateApproximation.MatrixPhase.Counting
import Proofs.Compiler.GateApproximation.MatrixPhase.SVDGram



/-!
# Supported residual of the concrete SVD cutoff
-/
set_option autoImplicit false

set_option maxHeartbeats 1500000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

/-
Mathematical definition (normal notation): For any real table A, define the consistency projection entrywise:

project(A)(i,j) := { A(i,j), if (i,j) is valid,; 0, otherwise }

The predicate specifying validity is an argument of the construction.
-/
def project (valid : I → I → Prop) [DecidableRel valid] (A : Matrix I I ℝ) :
    Matrix I I ℝ := fun i j => if valid i j then A i j else 0

/- Mathematical definition (normal notation): The consistency sign table has value 1 on valid pairs and -1 on invalid pairs. Equivalently, its entries are twice the consistency mask minus one. -/
def refreshSign (valid : I → I → Prop) [DecidableRel valid] : Matrix I I ℝ :=
  fun i j => if valid i j then 1 else -1

/-
Mathematical definition (normal notation): For the auxiliary non-strict spectral part, define

Δ^(≥ β) := A-2 · project(A^(≥ β)).

The validity predicate specifies the projection. This definition uses ≥ β, whereas the current strict residual uses >β.
-/
def refreshSVDResidual (A : Matrix I I ℝ) (β : ℝ)
    (valid : I → I → Prop) [DecidableRel valid] : Matrix I I ℝ :=
  A - (2 : ℝ) • project valid (refreshSVDPart A β)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For valid ∈ I → I → Prop; A ∈ ℝ^(I × I), assume DecidableRel(valid). Then

‖ project(valid, A)‖₂ ≤ ‖ A‖₂.
-/
theorem project_l2 (valid : I → I → Prop) [DecidableRel valid]
    (A : Matrix I I ℝ) : tableL2Norm (project valid A) ≤ tableL2Norm A := by
  have hsq : tableL2Norm (project valid A) ^ 2 ≤ tableL2Norm A ^ 2 := by
    simp only [tableL2Norm_sq, signedL2Sq]
    apply uavg_mono
    intro p
    simp only [project]
    split_ifs
    · rfl
    · simpa only [zero_pow (by decide : (2:ℕ) ≠ 0)] using sq_nonneg (A p.1 p.2)
  exact (sq_le_sq₀ (tableL2Norm_nonneg _) (tableL2Norm_nonneg _)).1 hsq

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c ∈ ℝ; A ∈ ℝ^(I × I), we have

‖ (c · A)‖₂ = |c| · ‖ A‖₂ .
-/
theorem tableL2Norm_smul (c : ℝ) (A : Matrix I I ℝ) : tableL2Norm (c • A) = |c| * tableL2Norm A := by
  have he : entryVector (c • A) = c • entryVector A := rfl
  simp only [tableL2Norm, he, norm_smul, Real.norm_eq_abs, mul_div_assoc]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; valid ∈ I → I → Prop; i, j ∈ I, assume DecidableRel(valid); ∀ i, j, ¬ (valid(i, j)) → A(i, j) = 0; ¬ (valid(i, j)). Then

refreshSVDResidual(A, β, valid, i, j) = 0.
-/
theorem refreshSVDResidual_supported (A : Matrix I I ℝ) (β : ℝ)
    (valid : I → I → Prop) [DecidableRel valid]
    (hA : ∀ i j, ¬valid i j → A i j = 0) (i j : I) (hij : ¬valid i j) :
    refreshSVDResidual A β valid i j = 0 := by
  simp [refreshSVDResidual, project, hij, hA i j hij]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; valid ∈ I → I → Prop; i, j ∈ I, assume 0 < β; DecidableRel(valid); ∀ i, j, |A(i, j)| ≤ 1. Then

|refreshSVDResidual(A, β, valid, i, j)| ≤ 1 + 2 / β.
-/
theorem refreshSVDResidual_entry (A : Matrix I I ℝ) (β : ℝ) (hβ : 0 < β)
    (valid : I → I → Prop) [DecidableRel valid]
    (hA : ∀ i j, |A i j| ≤ 1) (i j : I) :
    |refreshSVDResidual A β valid i j| ≤ 1 + 2 / β := by
  have hH := refreshSVDPart_entry A β hβ hA i j
  have hmask : |project valid (refreshSVDPart A β) i j| ≤ 1 / β := by
    unfold project
    split_ifs
    · exact hH
    · simp; positivity
  change |A i j - 2 * project valid (refreshSVDPart A β) i j| ≤ _
  have h := (abs_sub (A i j) (2 * project valid (refreshSVDPart A β) i j)).trans
    (add_le_add (hA i j) (by simpa only [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] using
      mul_le_mul_of_nonneg_left hmask (by norm_num : (0:ℝ)≤2)))
  exact h.trans_eq (by ring)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; valid ∈ I → I → Prop, assume DecidableRel(valid); ∀ i, j, |A(i, j)| ≤ 1. Then

‖ refreshSVDResidual(A, β, valid)‖₂ ≤ 3.
-/
theorem refreshSVDResidual_l2 (A : Matrix I I ℝ) (β : ℝ)
    (valid : I → I → Prop) [DecidableRel valid] (hA : ∀ i j, |A i j| ≤ 1) :
    tableL2Norm (refreshSVDResidual A β valid) ≤ 3 := by
  have hA2 := tableL2Norm_le_one_of_entry_bound A hA
  have hH2 := (project_l2 valid (refreshSVDPart A β)).trans
    ((refreshSVDPart_l2 A β).trans hA2)
  have htri : tableL2Norm (refreshSVDResidual A β valid) ≤
      tableL2Norm A + tableL2Norm ((-2 : ℝ) • project valid (refreshSVDPart A β)) := by
    convert tableL2Norm_add_le A ((-2 : ℝ) • project valid (refreshSVDPart A β)) using 1
    congr 1
    ext i j
    simp [refreshSVDResidual]
    ring
  rw [tableL2Norm_smul] at htri
  norm_num at htri
  linarith

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; valid ∈ I → I → Prop, assume DecidableRel(valid). Then

refreshSVDResidual(A, β, valid) = (A - refreshSVDPart(A, β)) - refreshSign(valid) ⊙ refreshSVDPart(A, β).
-/
theorem refreshSVDResidual_split (A : Matrix I I ℝ) (β : ℝ)
    (valid : I → I → Prop) [DecidableRel valid] :
    refreshSVDResidual A β valid =
      (A - refreshSVDPart A β) - refreshSign valid ⊙ refreshSVDPart A β := by
  ext i j
  simp only [refreshSVDResidual, project, refreshSign, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.hadamard_apply]
  split_ifs <;> ring

/-- The feature Schur bound applies to the actual retained singular vectors. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B ∈ ℝ^(I × I); β ∈ ℝ, assume 0 < β; ∀ i, j, |A(i, j)| ≤ 1. Then

‖ (B ⊙ refreshSVDPart(A, β))‖ₒₚ ≤ ‖ B‖ₒₚ / β.
-/
theorem refreshSVDPart_schur (A B : Matrix I I ℝ) (β : ℝ) (hβ : 0 < β)
    (hA : ∀ i j, |A i j| ≤ 1) :
    largestSingularCoefficient (B ⊙ refreshSVDPart A β) ≤ largestSingularCoefficient B / β := by
  have hpart : refreshSVDPart A β = innerProductTable (refreshSVDLeft A β) (refreshSVDRight A β) := by
    ext i j
    exact refreshSVDPart_factorization A β i j
  have hleft : ∀ i, ‖refreshSVDLeft A β i‖ ≤ Real.sqrt (1 / β) := fun i =>
    Real.le_sqrt_of_sq_le (refreshSVDLeft_energy A β hβ hA i)
  have hright : ∀ i, ‖refreshSVDRight A β i‖ ≤ Real.sqrt (1 / β) := fun i =>
    Real.le_sqrt_of_sq_le (refreshSVDRight_energy A β hβ hA i)
  have h := schur_multiplier_norm_le_of_bounds (refreshSVDLeft A β) (refreshSVDRight A β)
    B (Real.sqrt (1 / β)) (Real.sqrt (1 / β)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hleft hright
  rw [← hpart, Matrix.hadamard_comm] at h
  have hs : Real.sqrt (1 / β) * Real.sqrt (1 / β) = 1 / β :=
    Real.mul_self_sqrt (by positivity)
  rw [hs] at h
  exact (div_le_div_of_nonneg_right h (Nat.cast_nonneg _)).trans_eq (by
    unfold largestSingularCoefficient
    ring)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(I × I); β ∈ ℝ; valid ∈ I → I → Prop, assume 0 < β; DecidableRel(valid); ∀ i, j, |A(i, j)| ≤ 1. Then

‖ refreshSVDResidual(A, β, valid)‖ₒₚ ≤ β + ‖ refreshSign(valid)‖ₒₚ / β.
-/
theorem refreshSVDResidual_op (A : Matrix I I ℝ) (β : ℝ) (hβ : 0 < β)
    (valid : I → I → Prop) [DecidableRel valid] (hA : ∀ i j, |A i j| ≤ 1) :
    largestSingularCoefficient (refreshSVDResidual A β valid) ≤ β + largestSingularCoefficient (refreshSign valid) / β := by
  rw [refreshSVDResidual_split]
  have h := div_le_div_of_nonneg_right
    (norm_sub_le (A - refreshSVDPart A β) (refreshSign valid ⊙ refreshSVDPart A β))
    (Nat.cast_nonneg (Fintype.card I) : (0 : ℝ) ≤ _)
  change largestSingularCoefficient _ ≤ _ at h
  rw [add_div] at h
  exact h.trans (add_le_add (refreshSVDPart_tail A β hβ)
    (refreshSVDPart_schur A (refreshSign valid) β hβ hA))

section Binary

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For x ∈ F, assume |F| = 2. Then

fieldCharacter(F, x) = { 1 if x = 0,; -(1) otherwise }.
-/
theorem binary_fieldCharacter (hq : fieldCard F = 2) (x : F) :
    fieldCharacter F x = if x = 0 then 1 else -1 := by
  have hn : fieldCharacter F ≠ 1 := by
    simpa using fieldCharacter_primitive (F := F) (a := 1) one_ne_zero
  have hs := AddChar.sum_eq_zero_of_ne_one hn
  have hu : (Finset.univ : Finset F) = {0, 1} := by
    ext a
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr (binary_nonzero_eq_one hq a ha)
  rw [hu] at hs
  simp only [Finset.sum_pair zero_ne_one, AddChar.map_zero_eq_one] at hs
  have h1 : fieldCharacter F 1 = -1 := by linear_combination hs
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg hx, binary_nonzero_eq_one hq x hx, h1]

/-- The binary consistency mask is half the identity plus a small sign table. The old-share relation is arbitrary; no independence premise is needed here. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ I → I → F; m ∈ ℕ, assume |F| = 2. Then

‖ refreshSign(((x, y ∈ I × U(F, m) ↦ ((x)₂ · (y)₂) = s((x)₁, (y)₁))))‖ₒₚ ≤ √((|F|)ᵐ) / (|F|)ᵐ - 1.
-/
theorem refreshSign_binary_op (hq : fieldCard F = 2) (s : I → I → F) (m : ℕ) :
    largestSingularCoefficient (refreshSign (fun x y : I × U F m => dot x.2.val y.2.val = s x.1 y.1)) ≤
      Real.sqrt (fieldCard F ^ m : ℕ) / ((fieldCard F ^ m - 1 : ℕ) : ℝ) := by
  let valid := fun x y : I × U F m => dot x.2.val y.2.val = s x.1 y.1
  have he : (refreshSign valid).map Complex.ofReal = jointTwistMatrix s m (fieldCharacter F) 1 := by
    ext x y
    simp only [Matrix.map_apply, refreshSign, jointTwistMatrix, one_mul, binary_fieldCharacter hq,
      sub_eq_zero, valid]
    by_cases h : dot x.2.val y.2.val = s x.1 y.1
    · simp [h]
    · simp [h, Ne.symm h]
  have h := jointTwistMatrix_uniform_norm_le s m (fieldCharacter F)
    fieldCharacter_primitive 1 one_ne_zero
  rw [← he, complexMatrix_ofReal_norm] at h
  simpa only [largestSingularCoefficient, Fintype.card_prod, Nat.cast_mul, valid] using h

/-
Mathematical definition (normal notation): An endpoint tuple ((x,u),(y,v)) is consistent precisely when

a(x) · b(y) = u · v.

This is the inner-product equality preserved by the refresh equations.
-/
def refreshConsistent {m : ℕ} (a b : I → U F m)
    (x y : I × U F m) : Prop := dot x.2.val y.2.val = dot (a x.1).val (b y.1).val

instance refreshConsistent_decidable {m : ℕ} (a b : I → U F m) :
    DecidableRel (refreshConsistent a b) := fun x y => inferInstanceAs (Decidable (_ = _))

/-
Mathematical definition (normal notation): For m ∈ ℕ; a, b ∈ I → U(F, m); A ∈ ℝ^((I × U(F, m)) × (I × U(F, m))); β ∈ ℝ, define

supportedSVDResidual(a, b, A, β) := refreshSVDResidual(A, β, refreshConsistent(a, b)).
-/
def supportedSVDResidual {m : ℕ} (a b : I → U F m)
    (A : Matrix (I × U F m) (I × U F m) ℝ) (β : ℝ) :=
  refreshSVDResidual A β (refreshConsistent a b)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; a, b ∈ I → U(F, m); A ∈ ℝ^((I × U(F, m)) × (I × U(F, m))); β ∈ ℝ, assume |F| = 2; 0 < β; ∀ i, j, |A(i, j)| ≤ 1. Then

‖ supportedSVDResidual(a, b, A, β)‖ₒₚ ≤ β + (√((|F|)ᵐ) / (|F|)ᵐ - 1) / β.
-/
theorem supportedSVDResidual_op {m : ℕ} (hq : fieldCard F = 2) (a b : I → U F m)
    (A : Matrix (I × U F m) (I × U F m) ℝ) (β : ℝ) (hβ : 0 < β)
    (hA : ∀ i j, |A i j| ≤ 1) :
    largestSingularCoefficient (supportedSVDResidual a b A β) ≤
      β + (Real.sqrt (fieldCard F ^ m : ℕ) / ((fieldCard F ^ m - 1 : ℕ) : ℝ)) / β := by
  letI : Nonempty (U F m) := ⟨a (Classical.choice inferInstance)⟩
  exact (refreshSVDResidual_op A β hβ (refreshConsistent a b) hA).trans
    (add_le_add le_rfl (div_le_div_of_nonneg_right
      (refreshSign_binary_op hq (fun x y => dot (a x).val (b y).val) m) hβ.le))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; a, b ∈ I → U(F, m); A ∈ ℝ^((I × U(F, m)) × (I × U(F, m))); β ∈ ℝ, assume ∀ i, j, |A(i, j)| ≤ 1. Then

‖ supportedSVDResidual(a, b, A, β)‖₂ ≤ 3.
-/
theorem supportedSVDResidual_l2 {m : ℕ} (a b : I → U F m)
    (A : Matrix (I × U F m) (I × U F m) ℝ) (β : ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) :
    tableL2Norm (supportedSVDResidual a b A β) ≤ 3 := by
  letI : Nonempty (U F m) := ⟨a (Classical.choice inferInstance)⟩
  exact refreshSVDResidual_l2 A β (refreshConsistent a b) hA

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; a, b ∈ I → U(F, m); A ∈ ℝ^((I × U(F, m)) × (I × U(F, m))); β ∈ ℝ, assume ∀ i, j, |A(i, j)| ≤ 1. Then

𝔼ₓ [𝔼_y [(supportedSVDResidual(a, b, A, β, x, y))²]] ≤ 9.
-/
theorem supportedSVDResidual_energy {m : ℕ} (a b : I → U F m)
    (A : Matrix (I × U F m) (I × U F m) ℝ) (β : ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) :
    uavg (fun x => uavg (fun y => supportedSVDResidual a b A β x y ^ 2)) ≤ 9 := by
  have h := supportedSVDResidual_l2 a b A β hA
  have hs := pow_le_pow_left₀ (tableL2Norm_nonneg _) h 2
  rw [tableL2Norm_sq, signedL2Sq, uavg_prod] at hs
  norm_num at hs
  exact hs

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; a, b ∈ I → U(F, m); A ∈ ℝ^((I × U(F, m)) × (I × U(F, m))); β ∈ ℝ; i, j ∈ I × U(F, m), assume 0 < β; ∀ i, j, |A(i, j)| ≤ 1. Then

|supportedSVDResidual(a, b, A, β, i, j)| ≤ 1 + 2 / β .
-/
theorem supportedSVDResidual_entry {m : ℕ} (a b : I → U F m)
    (A : Matrix (I × U F m) (I × U F m) ℝ) (β : ℝ) (hβ : 0 < β)
    (hA : ∀ i j, |A i j| ≤ 1) (i j : I × U F m) :
    |supportedSVDResidual a b A β i j| ≤ 1 + 2 / β := by
  letI : Nonempty (U F m) := ⟨a (Classical.choice inferInstance)⟩
  exact refreshSVDResidual_entry A β hβ (refreshConsistent a b) hA i j

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; a, b ∈ I → U(F, m); A ∈ ℝ^((I × U(F, m)) × (I × U(F, m))); β ∈ ℝ; i, j ∈ I × U(F, m), assume ∀ i, j, ¬ (refreshConsistent(a, b, i, j)) → A(i, j) = 0; ¬ (refreshConsistent(a, b, i, j)). Then

supportedSVDResidual(a, b, A, β, i, j) = 0.
-/
theorem supportedSVDResidual_support {m : ℕ} (a b : I → U F m)
    (A : Matrix (I × U F m) (I × U F m) ℝ) (β : ℝ)
    (hA : ∀ i j, ¬refreshConsistent a b i j → A i j = 0)
    (i j : I × U F m) (hij : ¬refreshConsistent a b i j) :
    supportedSVDResidual a b A β i j = 0 := by
  letI : Nonempty (U F m) := ⟨a (Classical.choice inferInstance)⟩
  exact refreshSVDResidual_supported A β (refreshConsistent a b) hA i j hij

/-- Restriction makes the consistency mask identically one, so the supported residual gives the exact decomposition on every actual refresh graph. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; a, b ∈ I → U(F, m); A ∈ ℝ^((I × U(F, m)) × (I × U(F, m))); β ∈ ℝ; M ∈ GLₘ(F), we have

graphRestriction(a, b, (Complex.ofReal_*A), M) = 2 · graphRestriction(a, b, (Complex.ofReal_*refreshSVDPart(A, β)), M) + graphRestriction(a, b, (Complex.ofReal_*supportedSVDResidual(a, b, A, β)), M).
-/
theorem supportedSVDResidual_graph_split {m : ℕ} (a b : I → U F m)
    (A : Matrix (I × U F m) (I × U F m) ℝ) (β : ℝ) (M : Refresh.«GL» F m) :
    graphRestriction a b (A.map Complex.ofReal) M =
      (2 : ℝ) • graphRestriction a b ((refreshSVDPart A β).map Complex.ofReal) M +
        graphRestriction a b ((supportedSVDResidual a b A β).map Complex.ofReal) M := by
  ext x y
  have hvalid : refreshConsistent a b (x, rowRefresh (a x) M) (y, columnRefresh (b y) M) := by
    unfold refreshConsistent
    rw [rowRefresh_val, columnRefresh_val, shared_pairing]
  simp only [graphRestriction, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    supportedSVDResidual, refreshSVDResidual, Matrix.sub_apply, smul_eq_mul,
    project, hvalid, if_true]
  push_cast
  simp only [Complex.real_smul]
  norm_num

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; a, b ∈ I → U(F, m); A ∈ ℝ^((I × U(F, m)) × (I × U(F, m))); β ∈ ℝ; M ∈ GLₘ(F), we have

GateTruncation.opNorm(graphRestriction(a, b, (Complex.ofReal_*A), M)) ≤ 2 · GateTruncation.opNorm(graphRestriction(a, b, (Complex.ofReal_*refreshSVDPart(A, β)), M)) + GateTruncation.opNorm(graphRestriction(a, b, (Complex.ofReal_*supportedSVDResidual(a, b, A, β)), M)).
-/
theorem supportedSVDResidual_graph_triangle {m : ℕ} (a b : I → U F m)
    (A : Matrix (I × U F m) (I × U F m) ℝ) (β : ℝ) (M : Refresh.«GL» F m) :
    GateTruncation.opNorm (graphRestriction a b (A.map Complex.ofReal) M) ≤
      2 * GateTruncation.opNorm
        (graphRestriction a b ((refreshSVDPart A β).map Complex.ofReal) M) +
      GateTruncation.opNorm
        (graphRestriction a b ((supportedSVDResidual a b A β).map Complex.ofReal) M) := by
  rw [supportedSVDResidual_graph_split a b A β M]
  have h := div_le_div_of_nonneg_right (norm_add_le
    ((2 : ℝ) • graphRestriction a b ((refreshSVDPart A β).map Complex.ofReal) M)
    (graphRestriction a b ((supportedSVDResidual a b A β).map Complex.ofReal) M))
    (Nat.cast_nonneg (Fintype.card I) : (0 : ℝ) ≤ _)
  simpa only [GateTruncation.opNorm, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), add_div, mul_div_assoc] using h

end Binary

end

end CircuitCompiler.RefreshAnalysis
