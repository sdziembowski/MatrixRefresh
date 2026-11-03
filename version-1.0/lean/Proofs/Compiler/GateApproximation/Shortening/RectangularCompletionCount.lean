import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Proofs.Compiler.GateApproximation.Shortening.RectangularShortening



/-!
# Counting full-row-rank rectangular matrices and their affine fibers

These counts justify a constant expected number of rank-test trials when sampling a completion by uniform free entries and rejecting rank failure.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace CircuitCompiler.Rectangular

open Refresh MatrixRefresh

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; H ∈ F^({0,…,n−1} × {0,…,m−1}), we have

FullRowRank(H) ⇔ LinearIndependent(F, H).
-/
theorem fullRowRank_iff_linearIndependent {n m : ℕ}
    (H : Matrix (Fin n) (Fin m) F) :
    FullRowRank H ↔ LinearIndependent F H := by
  change FullRowRank H ↔ LinearIndependent F H.row
  rw [← Matrix.vecMul_injective_iff]
  constructor
  · rintro ⟨J,hJ⟩ x y h
    have he := congrArg (fun z => Matrix.vecMul z J) h
    simpa only [Matrix.vecMul_vecMul,hJ,Matrix.vecMul_one] using he
  · intro h
    obtain ⟨g,hg⟩ := H.vecMulLinear.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr h)
    refine ⟨g.toMatrixRight',?_⟩
    have hm := congrArg LinearMap.toMatrixRight' hg
    have he : H.vecMulLinear.toMatrixRight' = H :=
      LinearEquiv.apply_symm_apply LinearMap.toMatrixRight' H
    simpa only [LinearMap.toMatrixRight'_comp,LinearMap.toMatrixRight'_id,he] using hm

/-
Mathematical definition (normal notation): For n, m ∈ ℕ, define

fullRankEquivIndependent(n, m) := Equiv.subtypeEquivRight(((H ↦ fullRowRank_iff_linearIndependent(H)))).
-/
def fullRankEquivIndependent (n m : ℕ) :
    FullRank F n m ≃ {H : Fin n → V F m // LinearIndependent F H} :=
  Equiv.subtypeEquivRight (fun H => fullRowRank_iff_linearIndependent H)

omit [DecidableEq F] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ, assume n ≤ m. Then

|FullRank(F, n, m)| = ∏_(i ∈ {0,…,n−1}) (((|F|)ᵐ - (|F|)ⁱ)).
-/
theorem fullRank_card {n m : ℕ} (hnm : n ≤ m) :
    Fintype.card (FullRank F n m) = ∏ i ∈ Finset.range n, (fieldCard F ^ m - fieldCard F ^ i) := by
  letI : Fintype {H : Fin n → V F m // LinearIndependent F H} := Fintype.ofFinite _
  rw [Fintype.card_congr (fullRankEquivIndependent (F := F) n m), ← Nat.card_eq_fintype_card]
  have hc := card_linearIndependent (K := F) (V := V F m) (k := n)
    (by simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using hnm)
  rw [Finset.prod_range]
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin,fieldCard] using hc

omit [DecidableEq F] in
/-- The full-row-rank proportion is the usual independent-row product. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ, assume n ≤ m. Then

|FullRank(F, n, m)| / |F^({0,…,n−1} × {0,…,m−1})| = ∏_(i ∈ {0,…,n−1}) ((1 - (|F|)ⁱ / (|F|)ᵐ)).
-/
theorem fullRank_probability_eq_product {n m : ℕ} (hnm : n ≤ m) :
    (Fintype.card (FullRank F n m) : ℝ) /
      Fintype.card (Matrix (Fin n) (Fin m) F) =
      ∏ i ∈ Finset.range n, (1 - (fieldCard F : ℝ) ^ i / (fieldCard F : ℝ) ^ m) := by
  rw [fullRank_card hnm, Nat.cast_prod]
  have hcard : Fintype.card (Matrix (Fin n) (Fin m) F) = fieldCard F ^ (m*n) := by
    simp only [Matrix,Fintype.card_fun,Fintype.card_fin,fieldCard,← pow_mul]
  rw [hcard,Nat.cast_pow]
  have hcast : ∀ i ∈ Finset.range n,
      ((fieldCard F ^ m - fieldCard F ^ i : ℕ) : ℝ) = (fieldCard F : ℝ)^m - (fieldCard F : ℝ)^i := by
    intro i hi
    rw [Nat.cast_sub (Nat.pow_le_pow_right
      (show 0 < fieldCard F from Fintype.card_pos) ((Finset.mem_range.mp hi).le.trans hnm))]
    simp
  rw [Finset.prod_congr rfl hcast]
  have hden : (fieldCard F : ℝ) ^ (m*n) = ∏ _i ∈ Finset.range n, (fieldCard F : ℝ)^m := by
    simp [pow_mul]
  rw [hden,← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hq : (0 : ℝ) < fieldCard F := by exact_mod_cast Fintype.card_pos (α := F)
  rw [sub_div,div_self (by positivity)]

omit [DecidableEq F] in
/-- Sampling independent uniform entries and rejecting rank failure succeeds with probability at least one quarter, independent of both dimensions. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ, assume n ≤ m. Then

1 / 4 ≤ |FullRank(F, n, m)| / |F^({0,…,n−1} × {0,…,m−1})|.
-/
theorem fullRank_probability_ge_quarter {n m : ℕ} (hnm : n ≤ m) :
    (1/4 : ℝ) ≤ (Fintype.card (FullRank F n m) : ℝ) /
      Fintype.card (Matrix (Fin n) (Fin m) F) := by
  rw [fullRank_probability_eq_product hnm]
  have hq : (2 : ℝ) ≤ fieldCard F := by exact_mod_cast Fintype.one_lt_card (α := F)
  refine (invertibility_product_ge (fieldCard F) hq n).trans ?_
  apply Finset.prod_le_prod₀
  · intro i hi
    apply sub_nonneg.mpr
    apply (div_le_one (by positivity)).mpr
    exact pow_le_pow_right₀ (by linarith) (Finset.mem_range.mp hi).le
  · intro i hi
    apply sub_le_sub_left
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_right₀ (by linarith) hnm)

/-- A nonzero short row has nonzero image under a full-row-rank matrix. -/
/-
Mathematical definition (normal notation): For n, m ∈ ℕ; a ∈ U(F, n); H ∈ FullRank(F, n, m), define

fullRankImage(a, H) := Matrix.vecMul(a, H).
-/
def fullRankImage {n m : ℕ} (a : U F n) (H : FullRank F n m) : U F m :=
  ⟨Matrix.vecMul a.val H.val,by
    intro hz
    obtain ⟨J,hJ⟩ := H.property
    have he := congrArg (fun z => Matrix.vecMul z J) hz
    apply a.property
    simpa only [Matrix.vecMul_vecMul,hJ,Matrix.vecMul_one,Matrix.zero_vecMul] using he⟩

/- Mathematical definition (normal notation): For invertible M, right multiplication H ↦ H · M bijects full-row-rank completions of a · H = u with completions of a · H = u · M. Its inverse is multiplication by M⁻¹. -/
def completionTargetEquiv {n m : ℕ} (u : U F m) (a : U F n) (M : Refresh.«GL» F m) :
    Completion u a ≃ Completion (rowRefresh u M) a where
  toFun H := ⟨⟨H.val.val * M.val,fullRowRank_right H.val M⟩,by
    change Matrix.vecMul a.val (H.val.val * M.val) = Matrix.vecMul u.val M.val
    rw [← Matrix.vecMul_vecMul,H.property]⟩
  invFun H := ⟨⟨H.val.val * (M⁻¹).val,fullRowRank_right H.val M⁻¹⟩,by
    change Matrix.vecMul a.val (H.val.val * (M⁻¹).val) = u.val
    rw [← Matrix.vecMul_vecMul,H.property]
    simp [rowRefresh,Matrix.vecMul_vecMul]⟩
  left_inv H := by apply Subtype.ext; apply Subtype.ext; simp [Matrix.mul_assoc]
  right_inv H := by apply Subtype.ext; apply Subtype.ext; simp [Matrix.mul_assoc]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; u, v ∈ U(F, m); a ∈ U(F, n), we have

|Completion(u, a)| = |Completion(v, a)|.
-/
theorem completion_target_card_eq {n m : ℕ} (u v : U F m) (a : U F n) :
    Fintype.card (Completion u a) = Fintype.card (Completion v a) := by
  obtain ⟨M,hM⟩ := exists_rowRefresh_eq u v
  rw [← hM]
  exact Fintype.card_congr (completionTargetEquiv u a M)

/-
Mathematical definition (normal notation): For n, m ∈ ℕ; a ∈ U(F, n), define

fullRankEquivCompletions(a) := symm.trans(Equiv.sigmaFiberEquiv(fullRankImage(a)))(Equiv.sigmaCongrRight(((u ↦ Equiv.subtypeEquivRight(((H ↦ ))))))).
-/
def fullRankEquivCompletions {n m : ℕ} (a : U F n) :
    FullRank F n m ≃ ((u : U F m) × Completion u a) :=
  (Equiv.sigmaFiberEquiv (fullRankImage a)).symm.trans
    (Equiv.sigmaCongrRight (fun u => Equiv.subtypeEquivRight (fun H => by
      exact Subtype.ext_iff)))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; u ∈ U(F, m); a ∈ U(F, n), we have

|FullRank(F, n, m)| = ((|F|)ᵐ - 1) · |Completion(u, a)|.
-/
theorem fullRank_card_eq_completions {n m : ℕ} (u : U F m) (a : U F n) :
    Fintype.card (FullRank F n m) =
      (fieldCard F ^ m - 1) * Fintype.card (Completion u a) := by
  rw [Fintype.card_congr (fullRankEquivCompletions a),Fintype.card_sigma]
  simp_rw [completion_target_card_eq _ u a]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,nonzero_vector_card]

/-- The rank test on a uniformly sampled affine completion succeeds with probability at least one quarter. The denominator counts its free entries. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; u ∈ U(F, m); a ∈ U(F, n), assume n ≤ m. Then

1 / 4 ≤ |Completion(u, a)| / (|F|)^((n − 1) · m).
-/
theorem completion_probability_ge_quarter {n m : ℕ} (hnm : n ≤ m)
    (u : U F m) (a : U F n) :
    (1/4 : ℝ) ≤ (Fintype.card (Completion u a) : ℝ) /
      (fieldCard F : ℝ)^((n-1)*m) := by
  have hn : 1 ≤ n := by
    by_contra h
    have hz : n = 0 := by omega
    subst n
    apply a.property
    ext i
    exact Fin.elim0 i
  have hq : (0 : ℝ) < fieldCard F := by exact_mod_cast Fintype.card_pos (α := F)
  have hqNat : 1 ≤ fieldCard F ^ m := Nat.one_le_pow _ _ Fintype.card_pos
  have hcount := fullRank_card_eq_completions u a
  have hreal : (Fintype.card (FullRank F n m) : ℝ) =
      ((fieldCard F : ℝ)^m-1) * Fintype.card (Completion u a) := by
    exact_mod_cast hcount
  have hdim : m*n = m+(n-1)*m := by
    calc m*n = m*((n-1)+1) := by rw [Nat.sub_add_cancel hn]
         _ = m+(n-1)*m := by ring
  have hcard : (Fintype.card (Matrix (Fin n) (Fin m) F) : ℝ) =
      (fieldCard F : ℝ)^m * (fieldCard F : ℝ)^((n-1)*m) := by
    simp only [Matrix,Fintype.card_fun,Fintype.card_fin,fieldCard,← pow_mul,
      hdim,pow_add]
    push_cast
    rfl
  have hlower := fullRank_probability_ge_quarter (F := F) hnm
  rw [hcard] at hlower
  have hlarge := (le_div_iff₀ (by positivity : 0 <
    (fieldCard F : ℝ)^m * (fieldCard F : ℝ)^((n-1)*m))).mp hlower
  apply (le_div_iff₀ (by positivity : 0 < (fieldCard F : ℝ)^((n-1)*m))).mpr
  have hC : (0 : ℝ) ≤ Fintype.card (Completion u a) := Nat.cast_nonneg _
  have hbound : (Fintype.card (FullRank F n m) : ℝ) ≤
      (fieldCard F : ℝ)^m * Fintype.card (Completion u a) := by rw [hreal]; nlinarith
  have hp : 0 < (fieldCard F : ℝ)^m := by positivity
  nlinarith

end

end CircuitCompiler.Rectangular
