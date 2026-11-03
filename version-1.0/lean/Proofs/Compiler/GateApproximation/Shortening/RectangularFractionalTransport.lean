import Proofs.Compiler.GateApproximation.Shortening.RectangularFractional
import Proofs.Compiler.GateApproximation.Shortening.RectangularL1



/-!
# Rectangular shortening with fractional leakage masks

All bounds apply to specified local conditional answer probabilities. The underlying implementation's conditional sampler-tape distribution is not inferred. The Boolean transport is a special case of this common linear operator.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.Rectangular.Fractional

open Refresh MatrixRefresh TableAnalysis Shortening

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

variable {O Z : Type*} [Fintype O] [DecidableEq O] [Nonempty O] [Fintype Z]

variable {n t : ℕ} [Nonempty (U F n)] [Nonempty (U F (n+t))]
  [Nonempty (FullRank F n (n+t))]

/-- The masks may depend on the communicated shortening matrix. All old operand shares are retained in `O`; no plaintext is selected in this definition. -/
/-
Mathematical definition (normal notation): For r ∈ ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); G ∈ ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))); z ∈ Z, define

transport(r, G, z) := (x, y ↦ 𝔼_(H ← 𝒰_(FullRank(F, n, (n + t)))) [𝔼_(k ← 𝒰_(Kernel(H))) [G(((x)₁, leftShare(H, (x)₂)), ((y)₁, rightLift(H, (y)₂, k))) · (left(r(H))(z, x) · right(r(H))(z, (y, k)))]]).
-/
def transport
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (G : Matrix (O × U F (n+t)) (O × U F (n+t)) ℝ)
    (z : Z) : Matrix (O × U F n) (O × U F n) ℝ := fun x y =>
  (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect fun H =>
    (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect fun k =>
      G (x.1,leftShare H x.2) (y.1,rightLift H y.2 k) *
        ((r H).left z x * (r H).right z (y,k))

/-- The transport operator is linear in its input table. -/
/-
Mathematical definition (normal notation): For fixed shortening leakage masks, the map from a long real table G to its family of short answer tables (𝒯_z(G))_z is real-linear:

𝒯_z(G+H) = 𝒯_z(G)+𝒯_z(H), 𝒯_z(c · G) = c · 𝒯_z(G).

This construction packages those identities as a linear map.
-/
def transportLinear
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H)) :
    Matrix (O × U F (n+t)) (O × U F (n+t)) ℝ →ₗ[ℝ]
      (Z → Matrix (O × U F n) (O × U F n) ℝ) where
  toFun := transport r
  map_add' G H := by
    ext z x y
    simp only [transport, Matrix.add_apply, Pi.add_apply, add_mul, expect_add]
  map_smul' c G := by
    ext z x y
    simp only [transport, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, mul_assoc, expect_smul]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); a, b ∈ O × U(F, (n + t)) → ℝ; z ∈ Z, we have

transport(r, ((x, y ↦ a(x) · b(y))), z) = (x, y ↦ 𝔼_(H ← 𝒰_(FullRank(F, n, (n + t)))) [(leftFactor(a, H, x) · left(r(H))(z, x)) · 𝔼_(k ← 𝒰_(Kernel(H))) [rightFactor(b, H, (y, k)) · right(r(H))(z, (y, k))]]).
-/
theorem transport_rankOne
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (a b : O × U F (n+t) → ℝ) (z : Z) :
    transport r (fun x y => a x * b y) z = fun x y =>
      (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
        (leftFactor a H x * (r H).left z x) *
          (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect
            (fun k => rightFactor b H (y,k) * (r H).right z (y,k))) := by
  ext x y
  apply congrArg (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect
  funext H
  rw [← expect_smul]
  apply congrArg (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect
  funext k
  dsimp [leftFactor, rightFactor]
  ring

/-- The rank-one bound uses Cauchy--Schwarz over the random matrix after the two marginal identities have removed all pullback energy costs. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); a, b ∈ O × U(F, (n + t)) → ℝ, we have

(∑_z (‖ transport(r, ((x, y ↦ a(x) · b(y))), z)‖_*)) ≤ √(|Z|) · ‖ a‖_(2,𝒰_(O × U(F, (n + t)))) · ‖ b‖_(2,𝒰_(O × U(F, (n + t)))).
-/
theorem rankOne_transport_nuclear
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H)) (a b : O × U F (n+t) → ℝ) :
    (∑ z, tableNuclearNorm (transport r (fun x y => a x * b y) z)) ≤
      Real.sqrt (Fintype.card Z) * rms (FiniteDistribution.uniform : FiniteDistribution (O × U F (n+t))) a *
        rms (FiniteDistribution.uniform : FiniteDistribution (O × U F (n+t))) b := by
  let P : FiniteDistribution (FullRank F n (n+t)) := FiniteDistribution.uniform
  let L : FiniteDistribution (O × U F n) := FiniteDistribution.uniform
  let u := fun H => rms L (leftFactor a H)
  let v := fun H => rms (L.prod (FiniteDistribution.uniform : FiniteDistribution (Kernel H))) (rightFactor b H)
  have hu : rms P u = rms (FiniteDistribution.uniform : FiniteDistribution (O × U F (n+t))) a := by
    apply (sq_eq_sq₀ (rms_nonneg _ _) (rms_nonneg _ _)).1
    rw [rms_sq]
    exact leftFactor_energy a
  have hv : rms P v = rms (FiniteDistribution.uniform : FiniteDistribution (O × U F (n+t))) b := by
    apply (sq_eq_sq₀ (rms_nonneg _ _) (rms_nonneg _ _)).1
    rw [rms_sq]
    exact rightFactor_energy b
  have hcs : P.expect (fun H => u H * v H) ≤ rms P u * rms P v :=
    (le_abs_self _).trans (abs_expect_mul_le_rms_mul_rms P u v)
  rw [hu,hv] at hcs
  simp_rw [transport_rankOne]
  calc
    _ ≤ ∑ z, P.expect (fun H => tableNuclearNorm (fun x y =>
        (leftFactor a H x * (r H).left z x) *
          (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect
            (fun k => rightFactor b H (y,k) * (r H).right z (y,k)))) :=
      Finset.sum_le_sum (fun z _ => tableNuclearNorm_expect_le P _)
    _ ≤ P.expect (fun H => Real.sqrt (Fintype.card Z) * u H * v H) := by
      rw [← expect_sum]
      exact P.expect_mono (fun H => FractionalRectanglePartition.rectangle_nuclear_budget (r H) _ _ _)
    _ = Real.sqrt (Fintype.card Z) * P.expect (fun H => u H * v H) := by
      simp only [mul_assoc,expect_smul]
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcs (Real.sqrt_nonneg _)

/-- The paper's dimension-free family nuclear bound for the concrete rectangular table operator, with no analytic premises. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); G ∈ ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))), we have

(∑_z (‖ transport(r, G, z)‖_*)) ≤ √(|Z|) · ‖ G‖_*.
-/
theorem transport_nuclear
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (G : Matrix (O × U F (n+t)) (O × U F (n+t)) ℝ) :
    (∑ z, tableNuclearNorm (transport r G z)) ≤ Real.sqrt (Fintype.card Z) * tableNuclearNorm G :=
  linear_transport_nuclear_bound (transportLinear r) _ (rankOne_transport_nuclear r) G

/-- The previous Boolean operator is recovered without changing any tables. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ∏_(H ∈ FullRank(F, n, (n + t))) RectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); G ∈ ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))), we have

transport(((H ↦ FractionalRectanglePartition.ofBoolean(r(H)))), G) = Rectangular.transport(r, G).
-/
theorem transport_ofBoolean
    (r : (H : FullRank F n (n+t)) → RectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (G : Matrix (O × U F (n+t)) (O × U F (n+t)) ℝ) :
    transport (fun H => FractionalRectanglePartition.ofBoolean (r H)) G =
      Rectangular.transport r G := by
  ext z x y
  apply congrArg (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect
  funext H
  apply congrArg (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect
  funext k
  cases hl : (r H).left z x <;> cases hr : (r H).right z (y,k) <;>
    simp [FractionalRectanglePartition.ofBoolean, hl, hr]

/-- Summing all conditional answer probabilities removes fractional masks. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); E ∈ ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))); x, y ∈ O × U(F, n), we have

(∑_z (|transport(r, E, z, x, y)|)) ≤ 𝔼_(H ← 𝒰_(FullRank(F, n, (n + t)))) [𝔼_(k ← 𝒰_(Kernel(H))) [|E(((x)₁, leftShare(H, (x)₂)), ((y)₁, rightLift(H, (y)₂, k)))|]].
-/
theorem transport_abs_sum
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (E : Matrix (O × U F (n+t)) (O × U F (n+t)) ℝ)
    (x y : O × U F n) :
    (∑ z, |transport r E z x y|) ≤
      (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
        (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect (fun k =>
          |E (x.1,leftShare H x.2) (y.1,rightLift H y.2 k)|)) := by
  unfold transport
  calc
    _ ≤ ∑ z, (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
        (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect (fun k =>
          |E (x.1,leftShare H x.2) (y.1,rightLift H y.2 k) *
            ((r H).left z x * (r H).right z (y,k))|)) := by
      apply Finset.sum_le_sum
      intro z _
      apply (abs_expect_le_expect_abs _ _).trans
      exact FiniteDistribution.expect_mono _ (fun H => abs_expect_le_expect_abs _ _)
    _ = _ := by
      rw [← expect_sum]
      apply congrArg (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect
      funext H
      rw [← expect_sum]
      apply congrArg (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect
      funext k
      simp_rw [abs_mul, abs_of_nonneg ((r H).left_nonneg _ _),
        abs_of_nonneg ((r H).right_nonneg _ _)]
      rw [← Finset.mul_sum, (r H).partition, mul_one]

/-- Arbitrary correlations among the old operands are retained in `old`. The short and long output encodings have their exact uniform fiber distributions. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); E ∈ ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))); old ∈ 𝒟((O × O)); s ∈ F, assume Fiber(F, n, s) ≠ ∅; Fiber(F, (n + t), s) ≠ ∅. Then

𝔼_(op ← (old ⊗ 𝒰_(Fiber(F, n, s)))) [∑_z (|transport(r, E, z, (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R))|)] ≤ 𝔼_(op ← (old ⊗ 𝒰_(Fiber(F, (n + t), s)))) [|E((((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R))|].
-/
theorem transport_L1
    (r : (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (E : Matrix (O × U F (n+t)) (O × U F (n+t)) ℝ)
    (old : FiniteDistribution (O × O)) (s : F) [Nonempty (Fiber F n s)]
    [Nonempty (Fiber F (n+t) s)] :
    (old.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s))).expect (fun op =>
      ∑ z, |transport r E z (op.1.1,op.2.val.L) (op.1.2,op.2.val.R)|) ≤
    (old.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) s))).expect (fun op =>
      |E (op.1.1,op.2.val.L) (op.1.2,op.2.val.R)|) := by
  simp only [expect_prod]
  apply old.expect_mono
  intro o
  calc
    _ ≤ (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s)).expect (fun p =>
        (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
          (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect (fun k =>
            |E (o.1,leftShare H p.val.L) (o.2,rightLift H p.val.R k)|))) :=
      by
        apply FiniteDistribution.expect_mono
        intro p
        exact transport_abs_sum r E (o.1,p.val.L) (o.2,p.val.R)
    _ = _ := by
      have h := backward_expect_kernel s (fun p => |E (o.1,p.val.L) (o.2,p.val.R)|)
      exact h

/-- The very same approximating tables satisfy both the nuclear estimate and the mean-error estimate; they are not chosen separately for each secret. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A a set; r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); k, G ∈ A → ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))); old ∈ 𝒟((O × O)); s ∈ F, assume A is finite; Fiber(F, n, s) ≠ ∅; Fiber(F, (n + t), s) ≠ ∅. Then

(∑ₐ (∑_z (‖ transport(r(a), G(a), z)‖_*))) ≤ √(|Z|) · (∑ₐ (‖ G(a)‖_*)) ∧ (∑ₐ (𝔼_(op ← (old ⊗ 𝒰_(Fiber(F, n, s)))) [∑_z (|transport(r(a), k(a), z, (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R)) - transport(r(a), G(a), z, (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R))|)])) ≤ ∑ₐ (𝔼_(op ← (old ⊗ 𝒰_(Fiber(F, (n + t), s)))) [|k(a, (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R)) - G(a, (((op)₁)₁, op.2.val.L), (((op)₁)₂, op.2.val.R))|]).
-/
theorem transport_approximation {A : Type*} [Fintype A]
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (k G : A → Matrix (O × U F (n+t)) (O × U F (n+t)) ℝ)
    (old : FiniteDistribution (O × O)) (s : F) [Nonempty (Fiber F n s)]
    [Nonempty (Fiber F (n+t) s)] :
    (∑ a, ∑ z, tableNuclearNorm (transport (r a) (G a) z)) ≤
      Real.sqrt (Fintype.card Z) * (∑ a, tableNuclearNorm (G a)) ∧
    (∑ a, (old.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s))).expect (fun op =>
      ∑ z, |transport (r a) (k a) z (op.1.1,op.2.val.L) (op.1.2,op.2.val.R) -
        transport (r a) (G a) z (op.1.1,op.2.val.L) (op.1.2,op.2.val.R)|)) ≤
    ∑ a, (old.prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) s))).expect (fun op =>
      |k a (op.1.1,op.2.val.L) (op.1.2,op.2.val.R) -
        G a (op.1.1,op.2.val.L) (op.1.2,op.2.val.R)|) := by
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ => transport_nuclear (r a) (G a))
  · apply Finset.sum_le_sum
    intro a _
    have he : transport (r a) (k a - G a) = transport (r a) (k a) - transport (r a) (G a) :=
      (transportLinear (r a)).map_sub _ _
    have h := transport_L1 (r a) (k a - G a) old s
    simpa only [he,Pi.sub_apply,Matrix.sub_apply] using h

end

end CircuitCompiler.Rectangular.Fractional
