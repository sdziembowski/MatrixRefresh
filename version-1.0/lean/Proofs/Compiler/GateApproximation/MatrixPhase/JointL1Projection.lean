import Proofs.Compiler.GateApproximation.MatrixPhase.JointProjection



/-! Bounded-test separation for density-weighted L1 error. Zero density entries are allowed. The proof projects onto a compact convex sum of the weighted nuclear ball and an entrywise L1 ball, so it introduces no inverse density. -/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Pointwise

namespace CircuitCompiler

open TableAnalysis

noncomputable section

variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype Z]

/-
Mathematical definition (normal notation): For A ∈ MatrixTuple(Z, ι), define

entryL1(A) := ∑_z (∑ₚ (|A(z, p)|)).
-/
def entryL1 (A : MatrixTuple Z ι) : ℝ := ∑ z, ∑ p, |A z p|

omit [DecidableEq ι] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

Continuous(entryL1(Z = Z, ι = ι)).
-/
theorem continuous_entryL1 : Continuous (entryL1 (Z := Z) (ι := ι)) := by
  unfold entryL1
  exact continuous_finset_sum _ (fun z _ => continuous_finset_sum _ (fun p _ =>
    ((PiLp.continuous_apply 2 _ p).comp (PiLp.continuous_apply 2 _ z)).abs))

omit [DecidableEq ι] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A ∈ MatrixTuple(Z, ι); z ∈ Z; p ∈ ι × ι, we have

|A(z, p)| ≤ entryL1(A).
-/
theorem entryL1_coord_le (A : MatrixTuple Z ι) (z : Z) (p : ι × ι) :
    |A z p| ≤ entryL1 A := by
  exact (Finset.single_le_sum (fun j _ => abs_nonneg (A z j)) (Finset.mem_univ p)).trans
    (Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun q _ => abs_nonneg (A j q)))
      (Finset.mem_univ z))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ ℝ, we have

IsCompact({A ∈ MatrixTuple(Z, ι) | entryL1(A) ≤ e}).
-/
theorem entryL1Ball_compact (e : ℝ) :
    IsCompact {A : MatrixTuple Z ι | entryL1 A ≤ e} := by
  have he := LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr (entryTupleLinear_injective (Z := Z) (ι := ι)))
  have hc := he.isProperMap.isCompact_preimage
    (isCompact_univ_pi (fun _ : Z => isCompact_univ_pi (fun _ : ι × ι =>
      isCompact_Icc (a := -e) (b := e))))
  apply hc.of_isClosed_subset (isClosed_le continuous_entryL1 continuous_const)
  intro A hA z _ p _
  exact abs_le.mp ((entryL1_coord_le A z p).trans hA)

omit [DecidableEq ι] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ ℝ, we have

Convex(ℝ, {A ∈ MatrixTuple(Z, ι) | entryL1(A) ≤ e}).
-/
theorem entryL1Ball_convex (e : ℝ) :
    Convex ℝ {A : MatrixTuple Z ι | entryL1 A ≤ e} := by
  intro A hA B hB a b ha hb hab
  change entryL1 (a • A + b • B) ≤ e
  calc
    entryL1 (a • A + b • B) ≤ ∑ z, ∑ p, (a * |A z p| + b * |B z p|) := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro p _
      change |a * A z p + b * B z p| ≤ _
      simpa only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using
        abs_add_le (a * A z p) (b * B z p)
    _ = a * entryL1 A + b * entryL1 B := by
      simp [entryL1, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ a * e + b * e := add_le_add (mul_le_mul_of_nonneg_left hA ha)
      (mul_le_mul_of_nonneg_left hB hb)
    _ = e := by rw [← add_mul, hab, one_mul]

/-- A coordinate of absolute value one exposes the L1 ball with support e. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ ℝ; W ∈ MatrixTuple(Z, ι); z ∈ Z; p ∈ ι × ι, assume 0 ≤ e; |W(z, p)| = 1. Then

∃ E ∈ MatrixTuple(Z, ι), entryL1(E) ≤ e ∧ inner(ℝ, E, W) = e.
-/
theorem entryL1_support_witness (e : ℝ) (he : 0 ≤ e) (W : MatrixTuple Z ι)
    (z : Z) (p : ι × ι) (hWp : |W z p| = 1) :
    ∃ E : MatrixTuple Z ι, entryL1 E ≤ e ∧ inner ℝ E W = e := by
  classical
  let E : MatrixTuple Z ι := WithLp.toLp 2 (fun j => WithLp.toLp 2
    (fun q => if j = z ∧ q = p then e * W z p else 0))
  refine ⟨E, ?_, ?_⟩
  · simp [entryL1, E, ite_and, apply_ite abs, abs_mul, abs_of_nonneg he, hWp]
  · have hsq : W z p * W z p = 1 := by nlinarith [sq_abs (W z p)]
    simp [PiLp.inner_apply, RCLike.inner_apply, E, ite_and]
    calc
      W z p * (e * W z p) = e * (W z p * W z p) := by ring
      _ = e := by rw [hsq, mul_one]

/-- The unnormalized finite-coordinate L1 projection certificate. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For w ∈ Z → ι × ι → ℝ; R, e ∈ ℝ; A ∈ MatrixTuple(Z, ι), assume ι ≠ ∅; Z ≠ ∅; 0 ≤ R; 0 ≤ e; ∀ W ∈ MatrixTuple(Z, ι), (∀ z, p, |W(z, p)| ≤ 1) → inner(ℝ, weightTuple(w, A), W) ≤ R · tupleOperatorNorm(weightTuple(w, W)) + e. Then

∃ G ∈ jointNuclearBall(Z = Z, ι = ι, R), entryL1(weightTuple(w, (A - G))) ≤ e.
-/
theorem exists_weighted_jointNuclearProjection_L1 [Nonempty ι] [Nonempty Z]
    (w : Z → ι × ι → ℝ) (R e : ℝ) (hR : 0 ≤ R) (he : 0 ≤ e)
    (A : MatrixTuple Z ι)
    (htest : ∀ W : MatrixTuple Z ι, (∀ z p, |W z p| ≤ 1) →
      inner ℝ (weightTuple w A) W ≤ R * tupleOperatorNorm (weightTuple w W) + e) :
    ∃ G ∈ jointNuclearBall (Z := Z) (ι := ι) R,
      entryL1 (weightTuple w (A - G)) ≤ e := by
  classical
  let T := weightTuple w
  let B := jointNuclearBall (Z := Z) (ι := ι) R
  let E := {A : MatrixTuple Z ι | entryL1 A ≤ e}
  let S := T '' B + E
  have hEzero : (0 : MatrixTuple Z ι) ∈ E := by simpa [E, entryL1] using he
  have hcompact : IsCompact S :=
    ((jointNuclearBall_compact R).image T.continuous).add (entryL1Ball_compact e)
  have hnonempty : S.Nonempty :=
    ((jointNuclearBall_nonempty R hR).image T).add ⟨0, hEzero⟩
  have hconv : Convex ℝ S :=
    ((jointNuclearBall_convex R).linear_image T.toLinearMap).add (entryL1Ball_convex e)
  obtain ⟨P, hP, hnearest⟩ := exists_norm_eq_iInf_of_complete_convex
    hnonempty hcompact.isClosed.isComplete hconv (T A)
  have hAP : T A = P := by
    by_contra hne
    let Y := T A - P
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
      (fun q : Z × (ι × ι) => |Y q.1 q.2|) Finset.univ_nonempty
    let c := |Y j.1 j.2|
    have hmax : ∀ z p, |Y z p| ≤ c := fun z p => hj (z, p) (Finset.mem_univ _)
    have hc : 0 < c := by
      have hcz : 0 ≤ c := abs_nonneg _
      by_contra h
      have hc0 : c = 0 := le_antisymm (le_of_not_gt h) hcz
      have hY : Y = 0 := by
        ext z p
        have hp := hmax z p
        rw [hc0] at hp
        exact abs_eq_zero.mp (le_antisymm hp (abs_nonneg _))
      exact hne (sub_eq_zero.mp hY)
    let W := c⁻¹ • Y
    have hW : ∀ z p, |W z p| ≤ 1 := by
      intro z p
      change |c⁻¹ * Y z p| ≤ 1
      rw [abs_mul, abs_inv, abs_of_pos hc]
      exact (inv_mul_le_iff₀ hc).2 (by simpa using hmax z p)
    have hWj : |W j.1 j.2| = 1 := by
      change |c⁻¹ * Y j.1 j.2| = 1
      rw [abs_mul, abs_inv, abs_of_pos hc]
      exact inv_mul_cancel₀ hc.ne'
    obtain ⟨G, hG, hsupport⟩ := jointNuclearBall_support_witness R hR (T W)
    obtain ⟨E₀, hE₀, hpairE⟩ := entryL1_support_witness e he W j.1 j.2 hWj
    have hsum : T G + E₀ ∈ S := Set.add_mem_add ⟨G, hG, rfl⟩ hE₀
    have hvar := (norm_eq_iInf_iff_real_inner_le_zero hconv hP).1 hnearest
      (T G + E₀) hsum
    have hvarW : inner ℝ (T G + E₀) W ≤ inner ℝ P W := by
      dsimp [W]
      rw [real_inner_smul_right, real_inner_smul_right]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
      have hv : inner ℝ Y (T G + E₀ - P) ≤ 0 := hvar
      rw [inner_sub_right] at hv
      simpa only [real_inner_comm] using sub_nonpos.mp hv
    have ht := htest W hW
    have hp : inner ℝ (T G + E₀) W = R * tupleOperatorNorm (T W) + e := by
      rw [inner_add_left, weightTuple_self_adjoint, hsupport, hpairE]
    have hbad : inner ℝ Y W ≤ 0 := by
      change inner ℝ (T A - P) W ≤ 0
      rw [inner_sub_left]
      linarith
    have hYnorm : 0 < ‖Y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hpos : 0 < inner ℝ Y W := by
      dsimp [W]
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      exact mul_pos (inv_pos.mpr hc) (sq_pos_of_pos hYnorm)
    linarith
  obtain ⟨x, ⟨G, hG, rfl⟩, E₀, hE₀, hsum⟩ := Set.mem_add.mp hP
  refine ⟨G, hG, ?_⟩
  have hdiff : T (A - G) = E₀ := by rw [map_sub, hAP, ← hsum]; abel
  rw [hdiff]
  exact hE₀

section Tables

variable [Nonempty ι] [Nonempty Z]

/-- The paper's bounded-test criterion: the error is weighted L1, and its support may omit arbitrary invalid tuples. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For D ∈ ℝ^(ι × ι); R, e ∈ ℝ; A ∈ Z → ℝ^(ι × ι), assume ∀ i, j, 0 ≤ D(i, j); 0 ≤ R; 0 ≤ e; ∀ W ∈ Z → ℝ^(ι × ι), (∀ z, i, j, |W(z, i, j)| ≤ 1) → densityTablePair(D, A, W) ≤ R · ‖ (z ↦ ‖ (D ⊙ W(z))‖ₒₚ)‖ + e. Then

∃ G ∈ Z → ℝ^(ι × ι), (∑_z (‖ G(z)‖_*)) ≤ R ∧ (∑_z (MatrixRefresh.uavg(((p ∈ ι × ι ↦ D((p)₁, (p)₂) · |A(z, (p)₁, (p)₂) - G(z, (p)₁, (p)₂)|))))) ≤ e.
-/
theorem exists_density_tableNuclearNormProjection_L1
    (D : Matrix ι ι ℝ) (hD : ∀ i j, 0 ≤ D i j)
    (R e : ℝ) (hR : 0 ≤ R) (he : 0 ≤ e) (A : Z → Matrix ι ι ℝ)
    (htest : ∀ W : Z → Matrix ι ι ℝ, (∀ z i j, |W z i j| ≤ 1) →
      densityTablePair D A W ≤ R * ‖fun z => largestSingularCoefficient (D ⊙ W z)‖ + e) :
    ∃ G : Z → Matrix ι ι ℝ, (∑ z, tableNuclearNorm (G z)) ≤ R ∧
      (∑ z, MatrixRefresh.uavg (fun p : ι × ι =>
        D p.1 p.2 * |A z p.1 p.2 - G z p.1 p.2|)) ≤ e := by
  let d : ℝ := Fintype.card ι
  let w := fun _ : Z => fun p : ι × ι => D p.1 p.2 / d
  obtain ⟨P, hP, herr⟩ := exists_weighted_jointNuclearProjection_L1 w R e hR he
    (uniformTuple A) (by
      intro X hX
      let W : Z → Matrix ι ι ℝ := fun z i j => X z (i, j)
      have hpair : inner ℝ (weightTuple w (uniformTuple A)) X = densityTablePair D A W := by
        unfold densityTablePair MatrixRefresh.uavg
        simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fintype.card_prod,
          Nat.cast_mul]
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        change X z p * ((D p.1 p.2 / d) * (d⁻¹ * A z p.1 p.2)) =
          (d * d)⁻¹ * (D p.1 p.2 * A z p.1 p.2 * X z p)
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      have hop : weightTuple w X = uniformTuple (fun z => D ⊙ W z) := by
        ext z p
        change (D p.1 p.2 / d) * X z p = d⁻¹ * (D p.1 p.2 * X z p)
        ring
      rw [hpair, hop, uniformTuple_operatorNorm]
      exact htest W (fun z i j => hX z (i, j)))
  let G : Z → Matrix ι ι ℝ := fun z => d • entryMatrix (P z)
  have hG : uniformTuple G = P := uniformTuple_recover P
  refine ⟨G, ?_, ?_⟩
  · rw [← uniformTuple_jointNuclearNorm, hG]
    exact hP
  · have heq : entryL1 (weightTuple w (uniformTuple A - P)) =
        ∑ z, MatrixRefresh.uavg (fun p : ι × ι =>
          D p.1 p.2 * |A z p.1 p.2 - G z p.1 p.2|) := by
      rw [← hG, ← uniformTuple_sub]
      unfold entryL1 MatrixRefresh.uavg
      simp only [Fintype.card_prod, Nat.cast_mul]
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      change |(D p.1 p.2 / d) * (d⁻¹ * (A z p.1 p.2 - G z p.1 p.2))| =
        (d * d)⁻¹ * (D p.1 p.2 * |A z p.1 p.2 - G z p.1 p.2|)
      have hd : 0 ≤ d := Nat.cast_nonneg _
      rw [abs_mul, abs_of_nonneg (div_nonneg (hD _ _) hd), abs_mul,
        abs_of_nonneg (inv_nonneg.mpr hd)]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rwa [heq] at herr

end Tables

end

end CircuitCompiler
