import Proofs.Compiler.LocalComparisons.FactorEnergies
import Proofs.Compiler.GateApproximation.Shortening.Transport



/-!
# Chosen product factors transported through rectangular shortening
-/
set_option autoImplicit false

set_option maxHeartbeats 2200000

open scoped BigOperators

namespace CircuitCompiler.ShorteningTransport

open Refresh MatrixRefresh TableAnalysis Shortening Rectangular AveragedEnergyComparison

noncomputable section

variable {F O Z : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [DecidableEq O] [Nonempty O] [Fintype Z]

variable {n t : ℕ} [Nonempty (U F n)] [Nonempty (U F (n+t))]
  [Nonempty (FullRank F n (n+t))]

variable {G : (O × U F (n+t)) → (O × U F (n+t)) → ℝ}

/-- The left output factor indexed by the full-rank matrix and an input factor. -/
/-
Mathematical definition (normal notation): For a full-rank shortening matrix H, input factor j, and left short input x = (o,ℓ), define

a'_(H,j)(x) := √(Pr[H]) · aⱼ(o,ℓ · H) · f_(L,z)^H(x).

The matrix is uniform over the full-rank matrices, and f_(L,z)^H is the left fractional leakage mask.
-/
def outputLeft (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (a : Factors G) (z : Z) (p : FullRank F n (n+t) × Fin a.rank)
    (x : O × U F n) : ℝ :=
  Real.sqrt ((FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).weight p.1) *
    (a.left (x.1,leftShare p.1 x.2) p.2 * (r p.1).left z x)

/-- The right output factor averages over the exact affine fiber of the short right share. Its index and square-root matrix weight match the left factor. -/
/-
Mathematical definition (normal notation): For the same matrix/factor index (H,j), define

b'_(H,j)(o,r) := √(Pr[H]) · 𝔼_(k ← ker H) [bⱼ(o,lift_H(r,k)) · f_(R,z)^H((o,r),k)].

The affine lift ranges uniformly over long right shares mapping to r, and the matrix weight matches the left factor.
-/
def outputRight (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (a : Factors G) (z : Z) (p : FullRank F n (n+t) × Fin a.rank)
    (y : O × U F n) : ℝ :=
  Real.sqrt ((FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).weight p.1) *
    (FiniteDistribution.uniform : FiniteDistribution (Kernel p.1)).expect (fun k =>
      a.right (y.1,rightLift p.1 y.2 k) p.2 * (r p.1).right z (y,k))

/-- These are factors of the same transported table, not a separately chosen representation for each plaintext. -/

/-
Mathematical statement (normal notation): If G = ∑ⱼ aⱼ · bⱼᵀ, the explicitly transported factors, indexed by a full-rank shortening matrix H and an input factor j, satisfy at every (x,y)

𝒯_z(G)(x,y) = ∑_(H,j) a'_(H,j)(x) · b'_(H,j)(y).

This is one representation of the transported table, shared by all secrets.
-/
theorem output_reconstruct
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (a : Factors G) (z : Z) (x y : O × U F n) :
    Fractional.transport r G z x y =
      ∑ p : FullRank F n (n+t) × Fin a.rank, outputLeft r a z p x * outputRight r a z p y := by
  have hH (H : FullRank F n (n+t)) :
      (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect (fun k =>
        G (x.1,leftShare H x.2) (y.1,rightLift H y.2 k) *
          ((r H).left z x * (r H).right z (y,k))) =
      ∑ j, (a.left (x.1,leftShare H x.2) j * (r H).left z x) *
        (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect (fun k =>
          a.right (y.1,rightLift H y.2 k) j * (r H).right z (y,k)) := by
    simp only [a.reconstruct, Finset.sum_mul, expect_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← expect_smul]
    apply congrArg (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect
    funext k
    ring
  unfold Fractional.transport
  simp_rw [hH]
  rw [Fintype.sum_prod_type]
  change (∑ H, (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).weight H *
    ∑ j, (a.left (x.1,leftShare H x.2) j * (r H).left z x) *
      (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect (fun k =>
        a.right (y.1,rightLift H y.2 k) j * (r H).right z (y,k))) = _
  apply Finset.sum_congr rfl
  intro H _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hs := Real.sq_sqrt ((FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).nonneg H)
  dsimp only [outputLeft, outputRight]
  have hs' := congrArg (fun w : ℝ => w *
    (a.left (x.1,leftShare H x.2) j * (r H).left z x *
      (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect (fun k =>
        a.right (y.1,rightLift H y.2 k) j * (r H).right z (y,k)))) hs
  nlinarith [hs']

/-- The explicit output left energy is bounded by the averaged input energy. -/
-- Auxiliary lemma (shortening); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); a ∈ Factors(G); z ∈ Z; x ∈ O × U(F, n), we have

(∑_(p ∈ FullRank(F, n, (n + t)) × {0,…,a.rank−1}) ((outputLeft(r, a, z, p, x))²)) ≤ 𝔼_(H ← 𝒰_(FullRank(F, n, (n + t)))) [a.leftEnergy(((x)₁, leftShare(H, (x)₂)))].
-/
theorem output_left_energy_le
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (a : Factors G) (z : Z) (x : O × U F n) :
    (∑ p : FullRank F n (n+t) × Fin a.rank, outputLeft r a z p x ^ 2) ≤
      (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
        a.leftEnergy (x.1,leftShare H x.2)) := by
  simp only [Fintype.sum_prod_type, outputLeft, mul_pow,
    Real.sq_sqrt (FiniteDistribution.nonneg _ _), Factors.leftEnergy, FiniteDistribution.expect, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro H _
  apply Finset.sum_le_sum
  intro j _
  have hm : (r H).left z x ^ 2 ≤ 1 := by
    nlinarith [(r H).left_nonneg z x, (r H).left_le_one z x]
  have h := mul_le_mul_of_nonneg_left hm
    (mul_nonneg ((FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).nonneg H)
      (sq_nonneg (a.left (x.1,leftShare H x.2) j)))
  simpa only [mul_one, mul_assoc] using h

/-- Jensen on each right fiber gives the analogous right-energy bound. -/
-- Auxiliary lemma (shortening); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); a ∈ Factors(G); z ∈ Z; y ∈ O × U(F, n), we have

(∑_(p ∈ FullRank(F, n, (n + t)) × {0,…,a.rank−1}) ((outputRight(r, a, z, p, y))²)) ≤ 𝔼_(H ← 𝒰_(FullRank(F, n, (n + t)))) [𝔼_(k ← 𝒰_(Kernel(H))) [a.rightEnergy(((y)₁, rightLift(H, (y)₂, k)))]].
-/
theorem output_right_energy_le
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (a : Factors G) (z : Z) (y : O × U F n) :
    (∑ p : FullRank F n (n+t) × Fin a.rank, outputRight r a z p y ^ 2) ≤
      (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
        (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect (fun k =>
          a.rightEnergy (y.1,rightLift H y.2 k))) := by
  have hH (H : FullRank F n (n+t)) :
      (∑ j, ((FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect (fun k =>
        a.right (y.1,rightLift H y.2 k) j * (r H).right z (y,k))) ^ 2) ≤
      (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect (fun k =>
        a.rightEnergy (y.1,rightLift H y.2 k)) := by
    unfold Factors.rightEnergy
    rw [expect_sum]
    apply Finset.sum_le_sum
    intro j _
    exact masked_expect_sq_le (FiniteDistribution.uniform : FiniteDistribution (Kernel H))
      (fun k => a.right (y.1,rightLift H y.2 k) j)
      (fun k => (r H).right z (y,k))
      (fun k => (r H).right_nonneg z (y,k)) (fun k => (r H).right_le_one z (y,k))
  calc
    _ = (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
        ∑ j, ((FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect (fun k =>
          a.right (y.1,rightLift H y.2 k) j * (r H).right z (y,k))) ^ 2) := by
      simp only [Fintype.sum_prod_type, outputRight, mul_pow,
        Real.sq_sqrt (FiniteDistribution.nonneg _ _)]
      change (∑ H, ∑ j, (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).weight H * _) =
        ∑ H, (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).weight H * ∑ j, _
      simp only [Finset.mul_sum]
    _ ≤ _ := FiniteDistribution.expect_mono _ hH

/-- Reindex the explicit (matrix,factor) family by `Fin`, as required by the comparison interface. -/
/- Mathematical definition (normal notation): Package the explicit transported factors a'_(H,j),b'_(H,j) into a product representation of 𝒯_z(G), indexing them by a full-rank matrix H and an input factor j. The representation is shared across all encoded secrets. -/
def outputFactors
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (a : Factors G) (z : Z) : Factors (Fractional.transport r G z) where
  rank := Fintype.card (FullRank F n (n+t) × Fin a.rank)
  left x j := outputLeft r a z ((Fintype.equivFin _).symm j) x
  right y j := outputRight r a z ((Fintype.equivFin _).symm j) y
  reconstruct x y := by
    rw [← Equiv.sum_comp (Fintype.equivFin (FullRank F n (n+t) × Fin a.rank))]
    simp only [Equiv.symm_apply_apply]
    exact output_reconstruct r a z x y

-- Auxiliary lemma (shortening); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); a ∈ Factors(G); z ∈ Z; x ∈ O × U(F, n), we have

leftEnergy(outputFactors(r, a, z))(x) = ∑_(p ∈ FullRank(F, n, (n + t)) × {0,…,a.rank−1}) ((outputLeft(r, a, z, p, x))²).
-/
theorem outputFactors_leftEnergy
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (a : Factors G) (z : Z) (x : O × U F n) :
    (outputFactors r a z).leftEnergy x =
      ∑ p : FullRank F n (n+t) × Fin a.rank, outputLeft r a z p x ^ 2 := by
  unfold Factors.leftEnergy outputFactors
  rw [← Equiv.sum_comp (Fintype.equivFin (FullRank F n (n+t) × Fin a.rank))]
  simp only [Equiv.symm_apply_apply]

-- Auxiliary lemma (shortening); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); a ∈ Factors(G); z ∈ Z; y ∈ O × U(F, n), we have

rightEnergy(outputFactors(r, a, z))(y) = ∑_(p ∈ FullRank(F, n, (n + t)) × {0,…,a.rank−1}) ((outputRight(r, a, z, p, y))²).
-/
theorem outputFactors_rightEnergy
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (a : Factors G) (z : Z) (y : O × U F n) :
    (outputFactors r a z).rightEnergy y =
      ∑ p : FullRank F n (n+t) × Fin a.rank, outputRight r a z p y ^ 2 := by
  unfold Factors.rightEnergy outputFactors
  rw [← Equiv.sum_comp (Fintype.equivFin (FullRank F n (n+t) × Fin a.rank))]
  simp only [Equiv.symm_apply_apply]

/-- Chosen left energies retain any common pointwise upper bound. -/

/- Mathematical statement (normal notation): If the input representation has Φ(x) ≤ A everywhere, then the explicitly transported representation satisfies Φ'(x) ≤ A at every short-side input. Rectangular shortening preserves this pointwise energy bound for each answer z. -/
theorem outputFactors_left_max
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (a : Factors G) (z : Z) (A : ℝ) (hA : ∀ x, a.leftEnergy x ≤ A)
    (x : O × U F n) : (outputFactors r a z).leftEnergy x ≤ A := by
  rw [outputFactors_leftEnergy]
  exact (output_left_energy_le r a z x).trans
    (FiniteDistribution.expect_le_const _ (fun H => hA (x.1,leftShare H x.2)))

/-- Chosen right energies retain any common pointwise upper bound. -/

/- Mathematical statement (normal notation): If the input representation has Ψ(y) ≤ A everywhere, then the explicitly transported representation satisfies Ψ'(y) ≤ A at every short-side input. Rectangular shortening preserves this pointwise energy bound for each answer z. -/
theorem outputFactors_right_max
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (a : Factors G) (z : Z) (A : ℝ) (hA : ∀ y, a.rightEnergy y ≤ A)
    (y : O × U F n) : (outputFactors r a z).rightEnergy y ≤ A := by
  rw [outputFactors_rightEnergy]
  exact (output_right_energy_le r a z y).trans
    (FiniteDistribution.expect_le_const _ (fun H =>
      FiniteDistribution.expect_le_const _ (fun k => hA (y.1,rightLift H y.2 k))))

/-- The exact uniform left marginal preserves the mean of the chosen factors before masks; the masks can only reduce it. -/

/-
Mathematical statement (normal notation): For each shortening answer z, the transported left factor energy has no larger uniform mean than the input energy:

𝔼_(x ∈ O × Uₙ) [Φ'(x)] ≤ 𝔼_(x ∈ O × Uₙ₊ₜ) [Φ(x)].

Here U_d = 𝔽ᵈ ∖ {0} and O is the old-data carrier.
-/
theorem outputFactors_left_mean
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (a : Factors G) (z : Z) :
    (FiniteDistribution.uniform : FiniteDistribution (O × U F n)).expect (outputFactors r a z).leftEnergy ≤
      (FiniteDistribution.uniform : FiniteDistribution (O × U F (n+t))).expect a.leftEnergy := by
  calc
    _ ≤ (FiniteDistribution.uniform : FiniteDistribution (O × U F n)).expect (fun x =>
        (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
          a.leftEnergy (x.1,leftShare H x.2))) := by
      apply FiniteDistribution.expect_mono
      intro x
      rw [outputFactors_leftEnergy]
      exact output_left_energy_le r a z x
    _ = _ := by
      simp only [uniform_prod, expect_prod]
      apply congrArg (FiniteDistribution.uniform : FiniteDistribution O).expect
      funext o
      rw [expect_comm]
      exact left_pullback_expect (fun u => a.leftEnergy (o,u))

/-- The exact uniform right marginal likewise preserves the chosen mean energy. -/

/-
Mathematical statement (normal notation): For each shortening answer z, the transported right factor energy has no larger uniform mean than the input energy:

𝔼_(y ∈ O × Uₙ) [Ψ'(y)] ≤ 𝔼_(y ∈ O × Uₙ₊ₜ) [Ψ(y)].

Here U_d = 𝔽ᵈ ∖ {0} and O is the old-data carrier.
-/
theorem outputFactors_right_mean
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (a : Factors G) (z : Z) :
    (FiniteDistribution.uniform : FiniteDistribution (O × U F n)).expect (outputFactors r a z).rightEnergy ≤
      (FiniteDistribution.uniform : FiniteDistribution (O × U F (n+t))).expect a.rightEnergy := by
  calc
    _ ≤ (FiniteDistribution.uniform : FiniteDistribution (O × U F n)).expect (fun y =>
        (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
          (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect (fun k =>
            a.rightEnergy (y.1,rightLift H y.2 k)))) := by
      apply FiniteDistribution.expect_mono
      intro y
      rw [outputFactors_rightEnergy]
      exact output_right_energy_le r a z y
    _ = _ := by
      simp only [uniform_prod, expect_prod]
      apply congrArg (FiniteDistribution.uniform : FiniteDistribution O).expect
      funext o
      rw [expect_comm]
      exact right_pullback_expect (fun v => a.rightEnergy (o,v))

/-- The nuclear norm of a given factor representation is controlled by its separate mean energies. -/

/-
Mathematical statement (normal notation): For any product representation of a real square table F, with energies Φ,Ψ,

‖F‖_* ≤ √(𝔼ₓ [Φ(x)]) · √(𝔼_y [Ψ(y)]).

Both expectations are uniform; the representation need not be orthogonal or minimizing.
-/
theorem factors_nuclear_le_mean {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {f : I → I → ℝ} (a : Factors f) :
    tableNuclearNorm f ≤
      Real.sqrt ((FiniteDistribution.uniform : FiniteDistribution I).expect a.leftEnergy) *
      Real.sqrt ((FiniteDistribution.uniform : FiniteDistribution I).expect a.rightEnergy) := by
  have he : f = ∑ j, (fun x y => a.left x j * a.right y j) := by
    ext x y
    simpa only [Finset.sum_apply] using a.reconstruct x y
  have h₁ := tableNuclearNorm_sum_le (fun j => fun x y => a.left x j * a.right y j)
  have h₂ := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => rankOne_tableNuclearNorm_le (fun x => a.left x j) (fun y => a.right y j))
  exact (congrArg tableNuclearNorm he).le.trans
    (h₁.trans (h₂.trans (a.cost_le FiniteDistribution.uniform FiniteDistribution.uniform)))

/-- The same output representation gives the nuclear bound, with no answer cardinality loss and no balancing requirement. -/

/-
Mathematical statement (normal notation): For any chosen factors of the long table G, shortening with answer z satisfies

‖𝒯_z(G)‖_* ≤ √(𝔼ₓ [Φ_G(x)]) · √(𝔼_y [Ψ_G(y)]).

The expectations are over the long input-side carriers. Both energies refer to the same chosen representation of G.
-/
theorem outputFactors_nuclear_le
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (a : Factors G) (z : Z) :
    tableNuclearNorm (Fractional.transport r G z) ≤
      Real.sqrt ((FiniteDistribution.uniform : FiniteDistribution (O × U F (n+t))).expect a.leftEnergy) *
      Real.sqrt ((FiniteDistribution.uniform : FiniteDistribution (O × U F (n+t))).expect a.rightEnergy) := by
  apply (factors_nuclear_le_mean (outputFactors r a z)).trans
  exact mul_le_mul (Real.sqrt_le_sqrt (outputFactors_left_mean r a z))
    (Real.sqrt_le_sqrt (outputFactors_right_mean r a z))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end

end CircuitCompiler.ShorteningTransport
