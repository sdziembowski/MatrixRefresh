import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Proofs.Compiler.Foundations.MatrixRefreshing.Analysis.Tables
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Discrepancy
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Transitivity
import Proofs.Compiler.Foundations.MatrixRefreshing.Probability.FiniteDistribution



/-!
# Orbits of ordered row pairs under GL

Two ordered linearly independent nonzero row pairs lie in the same GL orbit. The proof extends each independent pair to a basis, matches the complement indices by their equal finite cardinalities, and writes the resulting linear equivalence as an invertible right-action matrix.  All fields here are arbitrary finite fields, rather than only prime fields.
-/

set_option autoImplicit false

open scoped BigOperators

namespace TableAnalysis

open Refresh MatrixRefresh Module

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; v ∈ {0,…,2-1} → V(F, n); i ∈ {0,…,2-1}, assume LinearIndependent(F, v). Then

Basis.sumExtend(Sum.inl(i)) = v(i).
-/
private lemma sumExtend_inl {n : ℕ} (v : Fin 2 → V F n)
    (hv : LinearIndependent F v) (i : Fin 2) :
    Basis.sumExtend hv (Sum.inl i) = v i := by
  classical
  simp [Basis.sumExtend]
  rfl

instance sumExtendIndexFintype {n : ℕ} {v : Fin 2 → V F n}
    (hv : LinearIndependent F v) : Fintype (Basis.sumExtendIndex hv) :=
  Fintype.ofFinite _

omit [DecidableEq F] in
/-- The complement in a basis extension of an independent pair has `n-2` indices. This statement does not need a separate dimension hypothesis. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; v ∈ {0,…,2-1} → V(F, n), assume LinearIndependent(F, v). Then

|Basis.sumExtendIndex| = n - 2.
-/
lemma card_sumExtendIndex {n : ℕ} (v : Fin 2 → V F n)
    (hv : LinearIndependent F v) :
    Fintype.card (Basis.sumExtendIndex hv) = n - 2 := by
  classical
  have hd := Module.finrank_eq_card_basis (Basis.sumExtend hv)
  simp only [Module.finrank_pi, Fintype.card_fin, Fintype.card_sum] at hd
  omega

omit [DecidableEq F] in
/-- Ordered independent pairs admit a linear equivalence carrying both specified input vectors to their respective output vectors. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; v, w ∈ {0,…,2-1} → V(F, n), assume LinearIndependent(F, v); LinearIndependent(F, w). Then

∃ e ∈ V(F, n) —linear over F→ V(F, n), ∀ i, e(v(i)) = w(i).
-/
theorem exists_linearEquiv_pair_eq {n : ℕ} (v w : Fin 2 → V F n)
    (hv : LinearIndependent F v) (hw : LinearIndependent F w) :
    ∃ e : V F n ≃ₗ[F] V F n, ∀ i, e (v i) = w i := by
  classical
  let b := Basis.sumExtend hv
  let b' := Basis.sumExtend hw
  have hcard : Fintype.card (Basis.sumExtendIndex hv) =
      Fintype.card (Basis.sumExtendIndex hw) := by
    rw [card_sumExtendIndex v hv, card_sumExtendIndex w hw]
  let j := Fintype.equivOfCardEq hcard
  let e := Equiv.sumCongr (Equiv.refl (Fin 2)) j
  refine ⟨b.equiv b' e, ?_⟩
  intro i
  rw [← sumExtend_inl v hv i]
  change b.equiv b' e (b (Sum.inl i)) = w i
  rw [Basis.equiv_apply]
  exact sumExtend_inl w hw i

/-- Matrix representation of a linear equivalence, for rows acting on the right. Its inverse is the matrix of the inverse linear equivalence. -/
/- Mathematical definition (normal notation): For a linear automorphism e of the vector space, take its row-action matrix M, so v · M = e(v). The matrix for e⁻¹ is the inverse of M. -/
def rowMatrixUnit {n : ℕ} (e : V F n ≃ₗ[F] V F n) : Refresh.«GL» F n where
  val := LinearMap.toMatrixRight' e.toLinearMap
  inv := LinearMap.toMatrixRight' e.symm.toLinearMap
  val_inv := by
    rw [← LinearMap.toMatrixRight'_comp]
    have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      ext v
      simp
    rw [h, LinearMap.toMatrixRight'_id]
  inv_val := by
    rw [← LinearMap.toMatrixRight'_comp]
    have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
      ext v
      simp
    rw [h, LinearMap.toMatrixRight'_id]

omit [Fintype F] [DecidableEq F] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; e ∈ V(F, n) —linear over F→ V(F, n); v ∈ V(F, n), we have

Matrix.vecMul(v, rowMatrixUnit(e)) = e(v).
-/
@[simp] lemma vecMul_rowMatrixUnit {n : ℕ} (e : V F n ≃ₗ[F] V F n)
    (v : V F n) : Matrix.vecMul v (rowMatrixUnit e).val = e v := by
  change (LinearMap.toMatrixRight'.symm (LinearMap.toMatrixRight' e.toLinearMap)) v = e v
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- GL acts transitively on ordered linearly independent nonzero row pairs, with the first and second rows kept in their given order. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; l, k, l', k' ∈ U(F, n), assume LinearIndependent(F, (l, k)); LinearIndependent(F, (l', k')). Then

∃ M ∈ GLₙ(F), rowRefresh(l, M) = l' ∧ rowRefresh(k, M) = k'.
-/
theorem exists_rowRefresh_pair_eq {n : ℕ} (l k l' k' : U F n)
    (hi : LinearIndependent F ![l.val, k.val])
    (hi' : LinearIndependent F ![l'.val, k'.val]) :
    ∃ M : Refresh.«GL» F n, rowRefresh l M = l' ∧ rowRefresh k M = k' := by
  obtain ⟨e, he⟩ := exists_linearEquiv_pair_eq ![l.val, k.val] ![l'.val, k'.val] hi hi'
  refine ⟨rowMatrixUnit e, ?_, ?_⟩
  · apply Subtype.ext
    rw [rowRefresh_val, vecMul_rowMatrixUnit]
    simpa using he 0
  · apply Subtype.ext
    rw [rowRefresh_val, vecMul_rowMatrixUnit]
    simpa using he 1

/-- The orbit of a proportional ordered pair retains the scalar ratio. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; l, k, l', k' ∈ U(F, n); c ∈ F, assume k = c · l; k' = c · l'. Then

∃ M ∈ GLₙ(F), rowRefresh(l, M) = l' ∧ rowRefresh(k, M) = k'.
-/
theorem exists_rowRefresh_proportional_pair_eq {n : ℕ} (l k l' k' : U F n)
    (c : F) (hk : k.val = c • l.val) (hk' : k'.val = c • l'.val) :
    ∃ M : Refresh.«GL» F n, rowRefresh l M = l' ∧ rowRefresh k M = k' := by
  obtain ⟨M, hM⟩ := exists_rowRefresh_eq l l'
  refine ⟨M, hM, ?_⟩
  apply Subtype.ext
  rw [rowRefresh_val, hk, Matrix.smul_vecMul]
  have hv := congrArg Subtype.val hM
  rw [rowRefresh_val] at hv
  rw [hv]
  exact hk'.symm

omit [Fintype F] [DecidableEq F] in
/-- Invertible row actions preserve linear independence. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; l, k ∈ U(F, n); M ∈ GLₙ(F), assume LinearIndependent(F, (l, k)). Then

LinearIndependent(F, (rowRefresh(l, M), rowRefresh(k, M))).
-/
theorem rowRefresh_pair_independent {n : ℕ} (l k : U F n)
    (hi : LinearIndependent F ![l.val, k.val]) (M : Refresh.«GL» F n) :
    LinearIndependent F ![(rowRefresh l M).val, (rowRefresh k M).val] := by
  let f : V F n →ₗ[F] V F n := Matrix.vecMulLinear M.val
  have hinj : Function.Injective f := by
    intro a b h
    have h' := congrArg (fun v : V F n => Matrix.vecMul v (M⁻¹).val) h
    simpa [f] using h'
  have hf : f ∘ ![l.val, k.val] =
      ![(rowRefresh l M).val, (rowRefresh k M).val] := by
    funext i
    fin_cases i <;> rfl
  rw [← hf]
  exact hi.map' f (LinearMap.ker_eq_bot.mpr hinj)

/-- The finite carrier of ordered independent nonzero row pairs. -/
/-
Mathematical definition (normal notation): For F a set; n ∈ ℕ, assume F is a field. define

IndependentRowPair(n) := {p ∈ U(F, n) × U(F, n) | LinearIndependent(F, ((p)₁, (p)₂))}.
-/
abbrev IndependentRowPair (F : Type*) [Field F] (n : ℕ) :=
  {p : U F n × U F n // LinearIndependent F ![p.1.val, p.2.val]}

instance independentRowPairFintype (n : ℕ) : Fintype (IndependentRowPair F n) :=
  Fintype.ofFinite _

instance independentRowPairDecidableEq (n : ℕ) : DecidableEq (IndependentRowPair F n) :=
  inferInstanceAs (DecidableEq {p : U F n × U F n //
    LinearIndependent F ![p.1.val, p.2.val]})

/-
Mathematical definition (normal notation): For n ∈ ℕ; p ∈ IndependentRowPair(F, n); M ∈ GLₙ(F), define

independentPairRefresh(p, M) := (rowRefresh((p)₁, M), rowRefresh((p)₂, M)).
-/
def independentPairRefresh {n : ℕ} (p : IndependentRowPair F n)
    (M : Refresh.«GL» F n) : IndependentRowPair F n :=
  ⟨(rowRefresh p.val.1 M, rowRefresh p.val.2 M),
    rowRefresh_pair_independent p.val.1 p.val.2 p.property M⟩

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ IndependentRowPair(F, n), we have

independentPairRefresh(p, 1) = p.
-/
@[simp] lemma independentPairRefresh_one {n : ℕ} (p : IndependentRowPair F n) :
    independentPairRefresh p 1 = p := by
  apply Subtype.ext
  simp [independentPairRefresh]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ IndependentRowPair(F, n); M, A ∈ GLₙ(F), we have

independentPairRefresh(independentPairRefresh(p, M), A) = independentPairRefresh(p, (M · A)).
-/
lemma independentPairRefresh_mul {n : ℕ} (p : IndependentRowPair F n)
    (M A : Refresh.«GL» F n) :
    independentPairRefresh (independentPairRefresh p M) A =
      independentPairRefresh p (M * A) := by
  apply Subtype.ext
  simp [independentPairRefresh, rowRefresh_mul]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p, p' ∈ IndependentRowPair(F, n), we have

∃ M ∈ GLₙ(F), independentPairRefresh(p, M) = p'.
-/
theorem independentPairRefresh_transitive {n : ℕ} (p p' : IndependentRowPair F n) :
    ∃ M : Refresh.«GL» F n, independentPairRefresh p M = p' := by
  obtain ⟨M, hM, hM'⟩ := exists_rowRefresh_pair_eq p.val.1 p.val.2 p'.val.1 p'.val.2
    p.property p'.property
  refine ⟨M, ?_⟩
  apply Subtype.ext
  exact Prod.ext hM hM'

/-
Mathematical definition (normal notation): For n ∈ ℕ; p, p' ∈ IndependentRowPair(F, n), define

PairTransporter(p, p') := {M ∈ GLₙ(F) | independentPairRefresh(p, M) = p'}.
-/
abbrev PairTransporter {n : ℕ} (p p' : IndependentRowPair F n) :=
  {M : Refresh.«GL» F n // independentPairRefresh p M = p'}

instance pairTransporterFintype {n : ℕ} (p p' : IndependentRowPair F n) :
    Fintype (PairTransporter p p') := Fintype.ofFinite _

/-- Right matrix multiplication identifies the transporters to two outputs related by an invertible row action. -/
/- Mathematical definition (normal notation): The map M ↦ M · A bijects matrices sending an independent row pair p to p' with matrices sending p to p' · A. Its inverse multiplies by A⁻¹. -/
def pairTransporterEquiv {n : ℕ} (p p' : IndependentRowPair F n) (A : Refresh.«GL» F n) :
    PairTransporter p p' ≃ PairTransporter p (independentPairRefresh p' A) where
  toFun M := ⟨M.val * A, by rw [← independentPairRefresh_mul, M.property]⟩
  invFun M := ⟨M.val * A⁻¹, by
    rw [← independentPairRefresh_mul, M.property, independentPairRefresh_mul,
      mul_inv_cancel, independentPairRefresh_one]⟩
  left_inv M := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv M := by
    apply Subtype.ext
    simp [mul_assoc]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p, p', p'' ∈ IndependentRowPair(F, n), we have

|PairTransporter(p, p')| = |PairTransporter(p, p'')|.
-/
theorem pairTransporter_card_eq {n : ℕ} (p p' p'' : IndependentRowPair F n) :
    Fintype.card (PairTransporter p p') = Fintype.card (PairTransporter p p'') := by
  obtain ⟨A, hA⟩ := independentPairRefresh_transitive p' p''
  rw [← hA]
  exact Fintype.card_congr (pairTransporterEquiv p p' A)

/-- A uniform group element sends a fixed independent ordered pair to the uniform distribution on all independent ordered pairs. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ IndependentRowPair(F, n), assume IndependentRowPair(F, n) ≠ ∅. Then

(independentPairRefresh(p)_*𝒰_(GLₙ(F))) = 𝒰_(IndependentRowPair(F, n)).
-/
theorem independentPair_uniform {n : ℕ} [Nonempty (IndependentRowPair F n)]
    (p : IndependentRowPair F n) :
    (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F n)).map (independentPairRefresh p) =
      (FiniteDistribution.uniform : FiniteDistribution (IndependentRowPair F n)) := by
  apply FiniteDistribution.uniform_map_of_fiber_card _ (Fintype.card (PairTransporter p p))
  intro p'
  convert pairTransporter_card_eq p p' p using 1
  exact @Fintype.card_congr _ _ (Subtype.fintype _) (pairTransporterFintype p p')
    (Equiv.refl _)

/-- Expectation form of uniformity on the independent-pair orbit. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ IndependentRowPair(F, n); f ∈ IndependentRowPair(F, n) → ℝ, we have

𝔼_(M ∈ GLₙ(F)) [f(independentPairRefresh(p, M))] = 𝔼ᵤ [f(u)].
-/
theorem uavg_independentPairRefresh {n : ℕ} (p : IndependentRowPair F n)
    (f : IndependentRowPair F n → ℝ) :
    uavg (fun M : Refresh.«GL» F n => f (independentPairRefresh p M)) = uavg f := by
  letI : Nonempty (IndependentRowPair F n) := ⟨p⟩
  rw [uavg_eq_expect_uniform, uavg_eq_expect_uniform]
  rw [← MatrixRefresh.expect_map, independentPair_uniform]

end

end TableAnalysis
