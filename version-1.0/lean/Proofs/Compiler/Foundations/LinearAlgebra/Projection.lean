import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Tactic



/-!
# Block contraction of a closest point in an inner-product space

For a finite `PiLp 2` tuple of complete real inner-product spaces, projection onto a nonempty closed convex set exists. If the feasible set remains feasible after zeroing any one block, every closest point decreases the norm of each block separately.

The proof uses the projection variational inequality with the feasible point obtained by zeroing the block. It does not use singular values or a nuclear norm. The nuclear-ball application only needs to prove `ZeroBlockStable` separately.
-/

set_option autoImplicit false

open scoped BigOperators

namespace TableAnalysis

noncomputable section

variable {Z : Type*} {β : Z → Type*}

section Zeroing

variable [∀ z, Zero (β z)]

/-- Zero exactly one block of an `L²` tuple, retaining every other block. -/
/- Mathematical definition (normal notation): For a family G = (G_w)_(w ∈ Z) in the finite L₂ direct sum, replace its zth block by zero and leave every other block unchanged. -/
def zeroBlock (z : Z) (G : PiLp 2 β) : PiLp 2 β := by
  classical
  exact WithLp.toLp 2 (fun w => if w = z then 0 else G w)

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For z ∈ Z; G ∈ PiLp(2, β), we have

zeroBlock(z, G, z) = 0.
-/
@[simp] theorem zeroBlock_apply_same (z : Z) (G : PiLp 2 β) :
    zeroBlock z G z = 0 := by
  classical
  simp [zeroBlock]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For z, w ∈ Z; G ∈ PiLp(2, β), assume w ≠ z. Then

zeroBlock(z, G, w) = G(w).
-/
@[simp] theorem zeroBlock_apply_ne (z w : Z) (G : PiLp 2 β) (h : w ≠ z) :
    zeroBlock z G w = G w := by
  classical
  simp [zeroBlock, h]

/-- The feasibility condition sufficient for contraction of each block. -/
/-
Mathematical definition (normal notation): For S ∈ Set(PiLp(2, β)), define

ZeroBlockStable(S) := ∀ G ∈ S, ∀ z, zeroBlock(z, G) ∈ S.
-/
def ZeroBlockStable (S : Set (PiLp 2 β)) : Prop :=
  ∀ G ∈ S, ∀ z, zeroBlock z G ∈ S

end Zeroing

section RealInnerProduct

variable [Fintype Z]

variable [∀ z, NormedAddCommGroup (β z)] [∀ z, InnerProductSpace ℝ (β z)]

/-- The displacement obtained by zeroing a block has inner product supported on that block alone. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A, G ∈ PiLp(2, β); z ∈ Z, we have

inner(ℝ, (A - G), (zeroBlock(z, G) - G)) = inner(ℝ, (A(z) - G(z)), -(G(z))).
-/
theorem inner_zeroBlock_sub (A G : PiLp 2 β) (z : Z) :
    inner ℝ (A - G) (zeroBlock z G - G) =
      inner ℝ (A z - G z) (-G z) := by
  classical
  rw [PiLp.inner_apply, Finset.sum_eq_single z]
  · simp
  · intro w _ hw
    simp [hw]
  · simp

/-- The closest-point variational inequality along the zeroed block gives the stronger blockwise estimate `‖G_z‖² ≤ ⟪A_z,G_z⟫`. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For S ∈ Set(PiLp(2, β)); hconv ∈ Convex(ℝ, S); A, G ∈ PiLp(2, β); z ∈ Z, assume ZeroBlockStable(S); G ∈ S; ‖ A - G‖ = inf_(W ∈ S) (‖ A - W‖). Then

(‖ G(z)‖)² ≤ inner(ℝ, A(z), G(z)).
-/
theorem nearestPoint_block_inner {S : Set (PiLp 2 β)} (hconv : Convex ℝ S)
    (hstable : ZeroBlockStable S) {A G : PiLp 2 β} (hG : G ∈ S)
    (hnearest : ‖A - G‖ = ⨅ W : S, ‖A - W‖) (z : Z) :
    ‖G z‖ ^ 2 ≤ inner ℝ (A z) (G z) := by
  have hvar := (norm_eq_iInf_iff_real_inner_le_zero hconv hG).1 hnearest
    (zeroBlock z G) (hstable G hG z)
  rw [inner_zeroBlock_sub, inner_neg_right, inner_sub_left,
    real_inner_self_eq_norm_sq] at hvar
  linarith

/-- Any closest point in a zero-block-stable convex set contracts the norm of each block separately. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For S ∈ Set(PiLp(2, β)); hconv ∈ Convex(ℝ, S); A, G ∈ PiLp(2, β); z ∈ Z, assume ZeroBlockStable(S); G ∈ S; ‖ A - G‖ = inf_(W ∈ S) (‖ A - W‖). Then

‖ G(z)‖ ≤ ‖ A(z)‖.
-/
theorem nearestPoint_block_norm_le {S : Set (PiLp 2 β)} (hconv : Convex ℝ S)
    (hstable : ZeroBlockStable S) {A G : PiLp 2 β} (hG : G ∈ S)
    (hnearest : ‖A - G‖ = ⨅ W : S, ‖A - W‖) (z : Z) :
    ‖G z‖ ≤ ‖A z‖ := by
  have hsq := (nearestPoint_block_inner hconv hstable hG hnearest z).trans
    (real_inner_le_norm (A z) (G z))
  nlinarith [norm_nonneg (A z), norm_nonneg (G z)]

variable [∀ z, CompleteSpace (β z)]

/-- A nonempty closed convex feasible set admits a closest point, and zero-block feasibility supplies both the blockwise inner-product estimate and contraction of every block norm. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For S ∈ Set(PiLp(2, β)); hconv ∈ Convex(ℝ, S); A ∈ PiLp(2, β), assume S.Nonempty; IsClosed(S); ZeroBlockStable(S). Then

∃ G ∈ S, (‖ A - G‖ = inf_(W ∈ S) (‖ A - W‖)) ∧ (∀ z, (‖ G(z)‖)² ≤ inner(ℝ, A(z), G(z))) ∧ (∀ z, ‖ G(z)‖ ≤ ‖ A(z)‖).
-/
theorem exists_nearestPoint_block_contraction (S : Set (PiLp 2 β))
    (hne : S.Nonempty) (hclosed : IsClosed S) (hconv : Convex ℝ S)
    (hstable : ZeroBlockStable S) (A : PiLp 2 β) :
    ∃ G ∈ S, (‖A - G‖ = ⨅ W : S, ‖A - W‖) ∧
      (∀ z, ‖G z‖ ^ 2 ≤ inner ℝ (A z) (G z)) ∧
      (∀ z, ‖G z‖ ≤ ‖A z‖) := by
  obtain ⟨G, hG, hnearest⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconv A
  exact ⟨G, hG, hnearest,
    fun z => nearestPoint_block_inner hconv hstable hG hnearest z,
    fun z => nearestPoint_block_norm_le hconv hstable hG hnearest z⟩

end RealInnerProduct

end

end TableAnalysis
