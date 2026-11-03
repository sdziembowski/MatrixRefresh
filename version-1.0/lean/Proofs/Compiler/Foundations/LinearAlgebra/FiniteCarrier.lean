import Mathlib.Analysis.Normed.Operator.NormedSpace
import Proofs.Compiler.Foundations.LinearAlgebra.GramMixing
import Proofs.Compiler.Foundations.LinearAlgebra.Mixing
import Proofs.Compiler.Foundations.LinearAlgebra.TableGeometry



/-!
# Transport of finite table carriers

Coordinate equivalences preserve the counting matrix norms and all uniform table norms. Refresh permutations and their analytic hypotheses can therefore be transported from actual shares to finite matrix indices.
-/

set_option autoImplicit false

set_option maxHeartbeats 1500000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace TableAnalysis

open MatrixRefresh Refresh

noncomputable section

variable {X Y G Z : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- Move matrix entries forward along independent row and column equivalences. -/
/-
Mathematical definition (normal notation): For A ∈ ℝ^(X × X); e, f ∈ X ≃ Y, define

reindexTable(A, e, f) := (i, j ↦ A((e)⁻¹(i), (f)⁻¹(j))).
-/
def reindexTable (A : Matrix X X ℝ) (e f : X ≃ Y) : Matrix Y Y ℝ :=
  fun i j => A (e.symm i) (f.symm j)

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(X × X); e, f ∈ X ≃ Y, we have

reindexTable(reindexTable(A, e, f), (e)⁻¹, (f)⁻¹) = A.
-/
@[simp] theorem reindexTable_inverse (A : Matrix X X ℝ) (e f : X ≃ Y) :
    reindexTable (reindexTable A e f) e.symm f.symm = A := by
  ext i j
  simp [reindexTable]

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(Y × Y); e, f ∈ X ≃ Y, we have

reindexTable(reindexTable(A, (e)⁻¹, (f)⁻¹), e, f) = A.
-/
@[simp] theorem reindexTable_inverse_forward (A : Matrix Y Y ℝ) (e f : X ≃ Y) :
    reindexTable (reindexTable A e.symm f.symm) e f = A := by
  ext i j
  simp [reindexTable]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(X × X); e, f ∈ X ≃ Y, we have

‖ reindexTable(A, e, f)‖ ≤ ‖ A‖.
-/
theorem reindexTable_operator_norm_le (A : Matrix X X ℝ) (e f : X ≃ Y) :
    ‖reindexTable A e f‖ ≤ ‖A‖ := by
  let E := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  let F := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ f
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro v
  have hmul : Matrix.toEuclideanCLM (n := Y) (𝕜 := ℝ) (reindexTable A e f) v =
      E (Matrix.toEuclideanCLM (n := X) (𝕜 := ℝ) A (F.symm v)) := by
    ext y
    simp only [E, F, LinearIsometryEquiv.piLpCongrLeft_symm,
      LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft',
      Matrix.ofLp_toEuclideanCLM]
    change (∑ y', A (e.symm y) (f.symm y') * v y') =
      ∑ x', A (e.symm y) x' * v (f x')
    simpa only [Equiv.apply_symm_apply] using
      f.symm.sum_comp (fun x' => A (e.symm y) x' * v (f x'))
  rw [hmul, E.norm_map]
  simpa only [F.symm.norm_map, Matrix.l2_opNorm_toEuclideanCLM] using
    (Matrix.toEuclideanCLM (n := X) (𝕜 := ℝ) A).le_opNorm (F.symm v)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(X × X); e, f ∈ X ≃ Y, we have

‖ reindexTable(A, e, f)‖ = ‖ A‖ .
-/
theorem reindexTable_operator_norm (A : Matrix X X ℝ) (e f : X ≃ Y) :
    ‖reindexTable A e f‖ = ‖A‖ := by
  apply le_antisymm (reindexTable_operator_norm_le A e f)
  simpa only [reindexTable_inverse] using
    reindexTable_operator_norm_le (reindexTable A e f) e.symm f.symm

omit [DecidableEq X] [DecidableEq Y] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, B ∈ ℝ^(X × X); e, f ∈ X ≃ Y, we have

countingPairing(reindexTable(A, e, f), reindexTable(B, e, f)) = countingPairing(A, B).
-/
theorem reindexTable_countingPairing (A B : Matrix X X ℝ) (e f : X ≃ Y) :
    countingPairing (reindexTable A e f) (reindexTable B e f) = countingPairing A B := by
  unfold countingPairing reindexTable
  calc
    _ = ∑ i : Y, ∑ j : X, A (e.symm i) j * B (e.symm i) j := by
      apply Finset.sum_congr rfl
      intro i _
      exact f.symm.sum_comp (fun j => A (e.symm i) j * B (e.symm i) j)
    _ = _ := e.symm.sum_comp (fun i => ∑ j, A i j * B i j)

omit [DecidableEq X] [DecidableEq Y] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(X × X); B ∈ ℝ^(Y × Y); e, f ∈ X ≃ Y, we have

countingPairing(reindexTable(A, e, f), B) = countingPairing(A, reindexTable(B, (e)⁻¹, (f)⁻¹)).
-/
theorem reindexTable_countingPairing_right (A : Matrix X X ℝ)
    (B : Matrix Y Y ℝ) (e f : X ≃ Y) :
    countingPairing (reindexTable A e f) B =
      countingPairing A (reindexTable B e.symm f.symm) := by
  simpa only [reindexTable_inverse_forward] using
    reindexTable_countingPairing A (reindexTable B e.symm f.symm) e f

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(X × X); e, f ∈ X ≃ Y, we have

‖ reindexTable(A, e, f)‖_(*,count) ≤ ‖ A‖_(*,count).
-/
theorem reindexTable_nuclearNorm_le (A : Matrix X X ℝ) (e f : X ≃ Y) :
    nuclearNorm (reindexTable A e f) ≤ nuclearNorm A := by
  apply ContinuousLinearMap.opNorm_le_bound _ (nuclearNorm_nonneg A)
  intro B
  rw [countingPairingDual_apply, Real.norm_eq_abs, reindexTable_countingPairing_right]
  simpa only [reindexTable_operator_norm] using
    abs_countingPairing_le A (reindexTable B e.symm f.symm)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(X × X); e, f ∈ X ≃ Y, we have

‖ reindexTable(A, e, f)‖_(*,count) = ‖ A‖_(*,count).
-/
theorem reindexTable_nuclearNorm (A : Matrix X X ℝ) (e f : X ≃ Y) :
    nuclearNorm (reindexTable A e f) = nuclearNorm A := by
  apply le_antisymm (reindexTable_nuclearNorm_le A e f)
  simpa only [reindexTable_inverse] using
    reindexTable_nuclearNorm_le (reindexTable A e f) e.symm f.symm

omit [DecidableEq X] [DecidableEq Y] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(X × X); e, f ∈ X ≃ Y, we have

‖ entryVector(reindexTable(A, e, f))‖ = ‖ entryVector(A)‖.
-/
theorem reindexTable_entryVector_norm (A : Matrix X X ℝ) (e f : X ≃ Y) :
    ‖entryVector (reindexTable A e f)‖ = ‖entryVector A‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [entryVector_norm_sq, entryVector_norm_sq]
  unfold reindexTable
  calc
    _ = ∑ i : Y, ∑ j : X, A (e.symm i) j ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact f.symm.sum_comp (fun j => A (e.symm i) j ^ 2)
    _ = _ := e.symm.sum_comp (fun i => ∑ j, A i j ^ 2)

omit [DecidableEq X] [DecidableEq Y] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(X × X); e, f ∈ X ≃ Y, we have

‖ reindexTable(A, e, f)‖₂ = ‖ A‖₂.
-/
theorem reindexTable_tableL2Norm (A : Matrix X X ℝ) (e f : X ≃ Y) :
    tableL2Norm (reindexTable A e f) = tableL2Norm A := by
  simp only [tableL2Norm, reindexTable_entryVector_norm, Fintype.card_congr e]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(X × X); e, f ∈ X ≃ Y, we have

‖ reindexTable(A, e, f)‖ₒₚ = ‖ A‖ₒₚ.
-/
theorem reindexTable_largestSingularCoefficient (A : Matrix X X ℝ) (e f : X ≃ Y) :
    largestSingularCoefficient (reindexTable A e f) = largestSingularCoefficient A := by
  simp only [largestSingularCoefficient, reindexTable_operator_norm, Fintype.card_congr e]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(X × X); e, f ∈ X ≃ Y, we have

‖ reindexTable(A, e, f)‖_* = ‖ A‖_*.
-/
theorem reindexTable_tableNuclearNorm (A : Matrix X X ℝ) (e f : X ≃ Y) :
    tableNuclearNorm (reindexTable A e f) = tableNuclearNorm A := by
  simp only [tableNuclearNorm, reindexTable_nuclearNorm, Fintype.card_congr e]

omit [DecidableEq X] [DecidableEq Y] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ ℝ^(X × X); e, f ∈ X ≃ Y, we have

tableL1(reindexTable(A, e, f)) = tableL1(A).
-/
theorem reindexTable_tableL1 (A : Matrix X X ℝ) (e f : X ≃ Y) :
    tableL1 (reindexTable A e f) = tableL1 A := by
  exact uavg_equiv (e.symm.prodCongr f.symm) (fun p => |A p.1 p.2|)

section RefreshTransport

variable [Fintype G] [Fintype Z]

/-- Conjugate every sampled permutation by the carrier equivalence. -/
/-
Mathematical definition (normal notation): For e ∈ X ≃ Y; a ∈ FiniteRefresh(X, G), define

transportRefresh(e, a) := (g ↦ trans(e.symm.trans(a(g)))(e)) .
-/
def transportRefresh (e : X ≃ Y) (a : FiniteRefresh X G) : FiniteRefresh Y G :=
  fun g => (e.symm.trans (a g)).trans e

/-
Mathematical definition (normal notation): For e ∈ X ≃ Y; F ∈ SignedTable(X), define

transportSigned(e, F) := (y ↦ F((e)⁻¹(y))).
-/
def transportSigned (e : X ≃ Y) (F : SignedTable X) : SignedTable Y :=
  fun y => F (e.symm y)

omit [DecidableEq X] [DecidableEq Y] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ X ≃ Y; F ∈ SignedTable(X), we have

signedL1(transportSigned(e, F)) = signedL1(F).
-/
theorem transportSigned_signedL1 (e : X ≃ Y) (F : SignedTable X) :
    signedL1 (transportSigned e F) = signedL1 F :=
  uavg_equiv e.symm (fun x => |F x|)

omit [DecidableEq X] [DecidableEq Y] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ X ≃ Y; F ∈ SignedTable(X), we have

‖ transportSigned(e, F)‖₂² = ‖ F‖₂².
-/
theorem transportSigned_signedL2Sq (e : X ≃ Y) (F : SignedTable X) :
    signedL2Sq (transportSigned e F) = signedL2Sq F :=
  uavg_equiv e.symm (fun x => F x ^ 2)

omit [DecidableEq X] [DecidableEq Y] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ X ≃ Y; F ∈ SignedTable(X), we have

‖ transportSigned(e, F)‖₂ = ‖ F‖₂.
-/
theorem transportSigned_signedL2 (e : X ≃ Y) (F : SignedTable X) :
    signedL2 (transportSigned e F) = signedL2 F := by
  unfold signedL2
  rw [transportSigned_signedL2Sq]

/- Mathematical definition (normal notation): For a bijection e:X → Y, transport an answer partition by setting p_z^Y(g,y) := p_z^X(g,e⁻¹(y)). Nonnegativity and the sum-to-one property are preserved. -/
def transportPartition (e : X ≃ Y) (p : RoundPartition X G Z) : RoundPartition Y G Z where
  weight z g y := p.weight z g (e.symm y)
  nonneg z g y := p.nonneg z g (e.symm y)
  complete g y := p.complete g (e.symm y)

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ X ≃ Y; a ∈ FiniteRefresh(X, G); p ∈ RoundPartition(X, G, Z); F ∈ SignedTable(X); z ∈ Z, we have

roundOp(transportRefresh(e, a), transportPartition(e, p), transportSigned(e, F), z) = transportSigned(e, roundOp(a, p, F, z)).
-/
theorem transport_roundOp (e : X ≃ Y) (a : FiniteRefresh X G)
    (p : RoundPartition X G Z) (F : SignedTable X) (z : Z) :
    roundOp (transportRefresh e a) (transportPartition e p) (transportSigned e F) z =
      transportSigned e (roundOp a p F z) := by
  funext y
  simp [roundOp, transportRefresh, transportPartition, transportSigned]

omit [DecidableEq X] [DecidableEq Y] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ X ≃ Y; a ∈ FiniteRefresh(X, G), assume UniformOnPoints(a). Then

UniformOnPoints(transportRefresh(e, a)).
-/
theorem transportRefresh_uniformOnPoints (e : X ≃ Y) (a : FiniteRefresh X G)
    (ha : UniformOnPoints a) : UniformOnPoints (transportRefresh e a) := by
  intro y f
  change uavg (fun g => f (e (a g (e.symm y)))) = uavg f
  rw [ha (e.symm y) (fun x => f (e x))]
  exact uavg_equiv e f

omit [DecidableEq X] [DecidableEq Y] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ X ≃ Y; a ∈ FiniteRefresh(X, G); κ ∈ ℝ, assume VarianceMixing(a, κ). Then

VarianceMixing(transportRefresh(e, a), κ).
-/
theorem transportRefresh_varianceMixing (e : X ≃ Y) (a : FiniteRefresh X G)
    (κ : ℝ) (ha : VarianceMixing a κ) : VarianceMixing (transportRefresh e a) κ := by
  intro u v
  have h := ha (fun x => u (e x)) (fun x => v (e x))
  have hcorr (g : G) :
      uavg (fun x => u (e x) * v (e (a g x))) =
        uavg (fun y => u y * v (transportRefresh e a g y)) := by
    simpa [transportRefresh] using
      uavg_equiv e (fun y => u y * v (transportRefresh e a g y))
  simp_rw [hcorr, uavg_equiv e u, uavg_equiv e v,
    uavg_equiv e (fun y => u y ^ 2), uavg_equiv e (fun y => v y ^ 2)] at h
  exact h

omit [DecidableEq X] [DecidableEq Y] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ X ≃ Y; a ∈ FiniteRefresh(X, G); pMin ∈ ℝ, assume X ≠ ∅; Y ≠ ∅; G ≠ ∅; TransitionDensityBound(a, pMin). Then

TransitionDensityBound(transportRefresh(e, a), pMin).
-/
theorem transportRefresh_transitionDensityBound [Nonempty X] [Nonempty Y] [Nonempty G]
    (e : X ≃ Y) (a : FiniteRefresh X G) (pMin : ℝ) (ha : TransitionDensityBound a pMin) :
    TransitionDensityBound (transportRefresh e a) pMin := by
  intro y y'
  have hmap : ((FiniteDistribution.uniform : FiniteDistribution G).map
      (fun g => (transportRefresh e a g).symm y)) =
      (((FiniteDistribution.uniform : FiniteDistribution G).map (fun g => (a g).symm (e.symm y))).map e) := by
    rw [FiniteDistribution.map_map]
    congr 1
  rw [hmap, FiniteDistribution.map_equiv_weight]
  simpa only [FiniteDistribution.uniform, Fintype.card_congr e] using ha (e.symm y) (e.symm y')

end RefreshTransport

section ActualGL

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- The canonical finite index carrier for the actual nonzero shares. -/
/- Mathematical definition (normal notation): Choose a bijective enumeration of the finite share set U by the integers 0,…,|U|-1. -/
def shareIndexEquiv : U F n ≃ Fin (Fintype.card (U F n)) := Fintype.equivFin _

/-
Mathematical definition (normal notation): Define

indexedRowRefresh := transportRefresh(shareIndexEquiv, ((M ↦ rowEquiv(M)))).
-/
def indexedRowRefresh : FiniteRefresh (Fin (Fintype.card (U F n))) (Refresh.«GL» F n) :=
  transportRefresh shareIndexEquiv (fun M => rowEquiv M)

/-
Mathematical definition (normal notation): Define

indexedColumnRefresh := transportRefresh(shareIndexEquiv, ((M ↦ columnEquiv(M)))).
-/
def indexedColumnRefresh : FiniteRefresh (Fin (Fintype.card (U F n))) (Refresh.«GL» F n) :=
  transportRefresh shareIndexEquiv (fun M => columnEquiv M)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

UniformOnPoints(indexedRowRefresh(F = F, n = n)).
-/
theorem indexedRowRefresh_uniformOnPoints : UniformOnPoints (indexedRowRefresh (F := F) (n := n)) :=
  transportRefresh_uniformOnPoints shareIndexEquiv _ row_uniformOnPoints

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

UniformOnPoints(indexedColumnRefresh(F = F, n = n)) .
-/
theorem indexedColumnRefresh_uniformOnPoints :
    UniformOnPoints (indexedColumnRefresh (F := F) (n := n)) :=
  transportRefresh_uniformOnPoints shareIndexEquiv _ column_uniformOnPoints

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

VarianceMixing(indexedRowRefresh(F = F, n = n), mixingCoefficient(F, n)).
-/
theorem indexedRowRefresh_varianceMixing (hn : 2 ≤ n) :
    VarianceMixing (indexedRowRefresh (F := F) (n := n)) (mixingCoefficient F n) :=
  transportRefresh_varianceMixing shareIndexEquiv _ _ (row_varianceMixing hn)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

VarianceMixing(indexedColumnRefresh(F = F, n = n), mixingCoefficient(F, n)).
-/
theorem indexedColumnRefresh_varianceMixing (hn : 2 ≤ n) :
    VarianceMixing (indexedColumnRefresh (F := F) (n := n)) (mixingCoefficient F n) :=
  transportRefresh_varianceMixing shareIndexEquiv _ _ (column_varianceMixing hn)

/-
Mathematical definition (normal notation): Define

stateIndexEquiv := trans(stateEquivProd(F, n))(shareIndexEquiv.prodCongr(shareIndexEquiv)) .
-/
def stateIndexEquiv : State F n ≃
    Fin (Fintype.card (U F n)) × Fin (Fintype.card (U F n)) :=
  (stateEquivProd F n).trans (shareIndexEquiv.prodCongr shareIndexEquiv)

/-
Mathematical definition (normal notation): Define

indexedGLRefresh := transportRefresh(stateIndexEquiv, glRefreshEquiv(F = F, n = n)).
-/
def indexedGLRefresh : FiniteRefresh
    (Fin (Fintype.card (U F n)) × Fin (Fintype.card (U F n))) (Refresh.«GL» F n) :=
  transportRefresh stateIndexEquiv (glRefreshEquiv (F := F) (n := n))

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For M ∈ GLₙ(F), we have

indexedGLRefresh(M) = prodCongr(indexedRowRefresh(M))(indexedColumnRefresh(M)) .
-/
theorem indexedGLRefresh_eq_prod (M : Refresh.«GL» F n) :
    indexedGLRefresh M = (indexedRowRefresh M).prodCongr (indexedColumnRefresh M) := by
  ext p <;> rfl

variable [Nonempty (U F n)]

local instance indexedShareNonempty : Nonempty (Fin (Fintype.card (U F n))) :=
  ⟨shareIndexEquiv (Classical.choice ‹Nonempty (U F n)›)⟩

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Assume 2 ≤ n. Then

TransitionDensityBound(indexedGLRefresh(F = F, n = n), minSecretProbability(F, n)).
-/
theorem indexedGLRefresh_transitionDensityBound (hn : 2 ≤ n) :
    TransitionDensityBound (indexedGLRefresh (F := F) (n := n)) (minSecretProbability F n) := by
  letI := state_nonempty (F := F) hn
  exact transportRefresh_transitionDensityBound stateIndexEquiv _ _ (gl_transitionDensityBound hn)

end ActualGL

end

end TableAnalysis
