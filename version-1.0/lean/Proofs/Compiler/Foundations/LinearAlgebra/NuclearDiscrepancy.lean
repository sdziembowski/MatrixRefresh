import Proofs.Compiler.Foundations.LinearAlgebra.Conditioning
import Proofs.Compiler.Foundations.LinearAlgebra.NuclearIdentification
import Proofs.Compiler.Foundations.LinearAlgebra.TableGeometry



/-!
# Static secret discrepancy for the actual nuclear norm

The SVD here is constructed from the spectral theorem, rather than required as a hypothesis. Rescaling its Euclidean singular vectors by the square root of the share count gives the paper's normalized L2 singular vectors.
-/

set_option autoImplicit false

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace TableAnalysis

open MatrixRefresh Refresh

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- Mathematical definition (normal notation): Choose a Euclidean singular-value decomposition of the real square matrix A, indexed by |ι| directions. The chosen coefficients are nonnegative and both direction families are full orthonormal bases. -/
def finiteMatrixSVD (A : Matrix ι ι ℝ) :
    RealSVD A.toEuclideanLin (Fintype.card ι) :=
  Classical.choice (exists_realSVD A.toEuclideanLin (by simp))

/-
Mathematical definition (normal notation): For m ∈ ℕ; b ∈ OrthonormalBasis({0,…,m-1}, ℝ, EuclideanSpace(ℝ, ι)); k ∈ {0,…,m-1}; i ∈ ι, define

uniformBasisCoordinate(b, k, i) := √(|ι|) · b(k, i).
-/
def uniformBasisCoordinate {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ ι)) (k : Fin m) (i : ι) : ℝ :=
  Real.sqrt (Fintype.card ι) * b k i

omit [DecidableEq ι] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; b ∈ OrthonormalBasis({0,…,m-1}, ℝ, EuclideanSpace(ℝ, ι)); k ∈ {0,…,m-1}, assume ι ≠ ∅. Then

𝔼ᵢ [(uniformBasisCoordinate(b, k, i))²] = 1.
-/
theorem uniformBasisCoordinate_secondMoment [Nonempty ι] {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ ι)) (k : Fin m) :
    uavg (fun i => uniformBasisCoordinate b k i ^ 2) = 1 := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnorm : (∑ i, b k i ^ 2) = 1 := by
    have h := b.norm_eq_one k
    have hs := EuclideanSpace.norm_sq_eq (b k)
    simp only [Real.norm_eq_abs, sq_abs, h, one_pow] at hs
    exact hs.symm
  simp only [uavg, uniformBasisCoordinate, mul_pow, Real.sq_sqrt hd.le,
    ← Finset.mul_sum, hnorm, mul_one, inv_mul_cancel₀ hd.ne']

section Encoding

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-
Mathematical definition (normal notation): For G ∈ State(F, n) → ℝ, define

stateMatrix(G) := (l, r ↦ G((l, r))) .
-/
def stateMatrix (G : State F n → ℝ) : Matrix (U F n) (U F n) ℝ :=
  fun l r => G ⟨l, r⟩

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; b ∈ OrthonormalBasis({0,…,m-1}, ℝ, EuclideanSpace(ℝ, U(F, n))); k ∈ {0,…,m-1}, assume 2 ≤ n. Then

‖ uniformBasisCoordinate(b, k)‖₂ = 1.
-/
theorem uniformBasisCoordinate_shareL2 {m : ℕ}
    (hn : 2 ≤ n) (b : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (U F n)))
    (k : Fin m) : shareL2 (uniformBasisCoordinate b k) = 1 := by
  letI : Nonempty (U F n) := ⟨(Classical.choice (state_nonempty (F := F) hn)).L⟩
  have h := uniformBasisCoordinate_secondMoment b k
  unfold shareL2
  have hcard : Fintype.card (U F n) = shareCard F n := by
    simpa only [shareCard, vectorCard] using nonzero_vector_card (F := F) n
  rw [show (1 / (shareCard F n : ℝ)) * (∑ l, uniformBasisCoordinate b k l ^ 2) = 1 from by
    simpa only [uavg, hcard, one_div] using h]
  exact Real.sqrt_one

/-- Two-secret discrepancy for the actual encoding distributions, bounded by the normalized nuclear norm. No decomposition premise is required. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s, t ∈ F; G ∈ State(F, n) → ℝ, assume 2 ≤ n. Then

|𝔼_(u ← μₛ) [G(u)] - 𝔼_(v ← μₜ) [G(v)]| ≤ zeta(F, n) · ‖ G‖_*.
-/
theorem nuclear_secret_discrepancy (hn : 2 ≤ n) (s t : F) (G : State F n → ℝ) :
    |(mu F n hn s).expect G - (mu F n hn t).expect G| ≤
      zeta F n * tableNuclearNorm (stateMatrix G) := by
  letI : Nonempty (U F n) := ⟨(Classical.choice (state_nonempty (F := F) hn)).L⟩
  let A := stateMatrix G
  let sv := finiteMatrixSVD A
  let c := fun k => sv.sigma k / (Fintype.card (U F n) : ℝ)
  let a := uniformBasisCoordinate sv.left
  let b := uniformBasisCoordinate sv.right
  have hd : 0 < (Fintype.card (U F n) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hG (x : State F n) : G x = ∑ k, c k * (a k (stateLeftShare x) * b k (stateRightShare x)) := by
    change A (stateLeftShare x) (stateRightShare x) = _
    rw [sv.matrix_entry]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [c, a, b, uniformBasisCoordinate]
    have hs := Real.sq_sqrt hd.le
    field_simp
    ring_nf
    rw [hs]
  have ha (k) : shareL2 (a k) = 1 := uniformBasisCoordinate_shareL2 hn sv.left k
  have hb (k) : shareL2 (b k) = 1 := uniformBasisCoordinate_shareL2 hn sv.right k
  have h := decomposition_secret_discrepancy hn s t c a b G hG ha hb
  have hsum : (∑ k, |c k|) = tableNuclearNorm A := by
    simp only [c, abs_div, abs_of_nonneg (sv.nonneg _), abs_of_pos hd]
    rw [← Finset.sum_div, ← sv.nuclearNorm_eq_sum_sigma]
    rfl
  rw [hsum] at h
  exact h

/-- The terminal distance bound combines signed approximation error with normalized nuclear norms; disjoint secret fibers supply the factor two. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For H a set; s, t ∈ F; P, G ∈ H → State(F, n) → ℝ, assume H is finite; 2 ≤ n; s ≠ t. Then

terminalDistance(μₛ, μₜ, P) ≤ terminalError(independentStateDistribution(F, n), P, G) / (2 · minSecretProbability(F, n)) + |F| / √(|F|ⁿ) · ∑ₕ (‖ G(h)‖_*).
-/
theorem actual_terminal_nuclear_bound {H : Type*} [Fintype H]
    (hn : 2 ≤ n) (s t : F) (hst : s ≠ t)
    (P G : H → State F n → ℝ) :
    terminalDistance (mu F n hn s) (mu F n hn t) P ≤
      terminalError (independentStateDistribution F n hn) P G / (2 * minSecretProbability F n) +
        (fieldCard F : ℝ) / Real.sqrt (vectorCard F n) * ∑ h, tableNuclearNorm (stateMatrix (G h)) := by
  calc
    _ ≤ terminalError (independentStateDistribution F n hn) P G / (2 * minSecretProbability F n) +
        (1 / 2 : ℝ) * ∑ h, |(mu F n hn s).expect (G h) -
          (mu F n hn t).expect (G h)| :=
      actual_terminal_conditioning_bound hn s t hst P G
    _ ≤ terminalError (independentStateDistribution F n hn) P G / (2 * minSecretProbability F n) +
        (1 / 2 : ℝ) * ∑ h, zeta F n * tableNuclearNorm (stateMatrix (G h)) := by
      gcongr with h
      exact nuclear_secret_discrepancy hn s t (G h)
    _ = _ := by rw [← Finset.mul_sum]; unfold zeta; ring

end Encoding

end

end TableAnalysis
