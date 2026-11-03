import Proofs.Compiler.GateApproximation.MatrixPhase.NuclearTransportLift
import Proofs.Compiler.GateApproximation.Shortening.RectangularReverse



/-!
# Nuclear transport through rectangular shortening

The same linear table operator is defined for every long input table. Uniform-fiber averaging and the genuine nuclear norm give the square-root answer-count bound, with no dimension or pivot loss.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler.Rectangular

open Refresh MatrixRefresh TableAnalysis Shortening

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

variable {O Z : Type*} [Fintype O] [DecidableEq O] [Nonempty O] [Fintype Z]

variable {n t : ℕ} [Nonempty (U F n)] [Nonempty (U F (n+t))]
  [Nonempty (FullRank F n (n+t))]

/-
Mathematical definition (normal notation): For a ∈ O × U(F, (n + t)) → ℝ; H ∈ FullRank(F, n, (n + t)); x ∈ O × U(F, n), define

leftFactor(a, H, x) := a(((x)₁, leftShare(H, (x)₂))).
-/
def leftFactor (a : O × U F (n+t) → ℝ) (H : FullRank F n (n+t))
    (x : O × U F n) : ℝ := a (x.1,leftShare H x.2)

/-
Mathematical definition (normal notation): For b ∈ O × U(F, (n + t)) → ℝ; H ∈ FullRank(F, n, (n + t)); yk ∈ (O × U(F, n)) × Kernel(H), define

rightFactor(b, H, yk) := b((((yk)₁)₁, rightLift(H, ((yk)₁)₂, (yk)₂))).
-/
def rightFactor (b : O × U F (n+t) → ℝ) (H : FullRank F n (n+t))
    (yk : (O × U F n) × Kernel H) : ℝ := b (yk.1.1,rightLift H yk.1.2 yk.2)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ O × U(F, (n + t)) → ℝ, we have

𝔼_(H ← 𝒰_(FullRank(F, n, (n + t)))) [(‖ leftFactor(a, H)‖_(2,𝒰_(O × U(F, n))))²] = (‖ a‖_(2,𝒰_(O × U(F, (n + t)))))².
-/
theorem leftFactor_energy (a : O × U F (n+t) → ℝ) :
    (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
      rms (FiniteDistribution.uniform : FiniteDistribution (O × U F n)) (leftFactor a H)^2) =
      rms (FiniteDistribution.uniform : FiniteDistribution (O × U F (n+t))) a ^ 2 := by
  simp only [rms_sq,uniform_prod,expect_prod,leftFactor]
  rw [expect_comm]
  apply congrArg (FiniteDistribution.uniform : FiniteDistribution O).expect
  funext o
  exact left_pullback_expect (fun u => a (o,u)^2)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For b ∈ O × U(F, (n + t)) → ℝ, we have

𝔼_(H ← 𝒰_(FullRank(F, n, (n + t)))) [(‖ rightFactor(b, H)‖_(2,(𝒰_(O × U(F, n)) ⊗ 𝒰_(Kernel(H)))))²] = (‖ b‖_(2,𝒰_(O × U(F, (n + t)))))².
-/
theorem rightFactor_energy (b : O × U F (n+t) → ℝ) :
    (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
      rms ((FiniteDistribution.uniform : FiniteDistribution (O × U F n)).prod
        (FiniteDistribution.uniform : FiniteDistribution (Kernel H))) (rightFactor b H)^2) =
      rms (FiniteDistribution.uniform : FiniteDistribution (O × U F (n+t))) b ^ 2 := by
  simp only [rms_sq,uniform_prod,expect_prod,rightFactor]
  rw [expect_comm]
  apply congrArg (FiniteDistribution.uniform : FiniteDistribution O).expect
  funext o
  exact right_pullback_expect (fun v => b (o,v)^2)

/-- The masks may depend on the communicated shortening matrix. All old operand shares are retained in `O`; no plaintext is selected in this definition. -/
/-
Mathematical definition (normal notation): For r ∈ ∏_(H ∈ FullRank(F, n, (n + t))) RectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); G ∈ ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))); z ∈ Z, define

transport(r, G, z) := (x, y ↦ 𝔼_(H ← 𝒰_(FullRank(F, n, (n + t)))) [𝔼_(k ← 𝒰_(Kernel(H))) [{ G(((x)₁, leftShare(H, (x)₂)), ((y)₁, rightLift(H, (y)₂, k))) if left(r(H))(z, x) ∧ right(r(H))(z, (y, k)),; 0 otherwise }]]).
-/
def transport
    (r : (H : FullRank F n (n+t)) → RectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (G : Matrix (O × U F (n+t)) (O × U F (n+t)) ℝ)
    (z : Z) : Matrix (O × U F n) (O × U F n) ℝ := fun x y =>
  (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect fun H =>
    (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect fun k =>
      if (r H).left z x && (r H).right z (y,k) then
        G (x.1,leftShare H x.2) (y.1,rightLift H y.2 k) else 0

/-- The transport operator is linear in its input table. -/
/-
Mathematical definition (normal notation): For fixed shortening leakage masks, the map from a long real table G to its family of short answer tables (𝒯_z(G))_z is real-linear:

𝒯_z(G+H) = 𝒯_z(G)+𝒯_z(H), 𝒯_z(c · G) = c · 𝒯_z(G).

This construction packages those identities as a linear map.
-/
def transportLinear
    (r : (H : FullRank F n (n+t)) → RectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H)) :
    Matrix (O × U F (n+t)) (O × U F (n+t)) ℝ →ₗ[ℝ]
      (Z → Matrix (O × U F n) (O × U F n) ℝ) where
  toFun := transport r
  map_add' G H := by
    ext z x y
    simp only [transport,Matrix.add_apply,Pi.add_apply]
    have hi (b : Bool) (x y : ℝ) : (if b then x+y else 0) =
        (if b then x else 0)+(if b then y else 0) := by cases b <;> simp
    simp_rw [hi,expect_add]
  map_smul' c G := by
    ext z x y
    simp only [transport,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    have hi (b : Bool) (x : ℝ) : (if b then c*x else 0) = c*(if b then x else 0) := by
      cases b <;> simp
    simp_rw [hi,expect_smul]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ∏_(H ∈ FullRank(F, n, (n + t))) RectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); a, b ∈ O × U(F, (n + t)) → ℝ; z ∈ Z, we have

transport(r, ((x, y ↦ a(x) · b(y))), z) = (x, y ↦ 𝔼_(H ← 𝒰_(FullRank(F, n, (n + t)))) [({ leftFactor(a, H, x) if left(r(H))(z, x),; 0 otherwise }) · 𝔼_(k ← 𝒰_(Kernel(H))) [{ rightFactor(b, H, (y, k)) if right(r(H))(z, (y, k)),; 0 otherwise }]]).
-/
theorem transport_rankOne
    (r : (H : FullRank F n (n+t)) → RectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (a b : O × U F (n+t) → ℝ) (z : Z) :
    transport r (fun x y => a x * b y) z = fun x y =>
      (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
        (if (r H).left z x then leftFactor a H x else 0) *
          (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect
            (fun k => if (r H).right z (y,k) then rightFactor b H (y,k) else 0)) := by
  ext x y
  apply congrArg (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect
  funext H
  rw [← expect_smul]
  apply congrArg (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect
  funext k
  cases hl : (r H).left z x <;> cases hr : (r H).right z (y,k) <;>
    simp [hl,hr,leftFactor,rightFactor]

/-- The rank-one bound uses Cauchy--Schwarz over the random matrix after the two marginal identities have removed all pullback energy costs. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ∏_(H ∈ FullRank(F, n, (n + t))) RectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); a, b ∈ O × U(F, (n + t)) → ℝ, we have

(∑_z (‖ transport(r, ((x, y ↦ a(x) · b(y))), z)‖_*)) ≤ √(|Z|) · ‖ a‖_(2,𝒰_(O × U(F, (n + t)))) · ‖ b‖_(2,𝒰_(O × U(F, (n + t)))).
-/
theorem rankOne_transport_nuclear
    (r : (H : FullRank F n (n+t)) → RectanglePartition Z
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
        (if (r H).left z x then leftFactor a H x else 0) *
          (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect
            (fun k => if (r H).right z (y,k) then rightFactor b H (y,k) else 0))) :=
      Finset.sum_le_sum (fun z _ => tableNuclearNorm_expect_le P _)
    _ ≤ P.expect (fun H => Real.sqrt (Fintype.card Z) * u H * v H) := by
      rw [← expect_sum]
      exact P.expect_mono (fun H => rectangle_nuclear_budget (r H) _ _ _)
    _ = Real.sqrt (Fintype.card Z) * P.expect (fun H => u H * v H) := by
      simp only [mul_assoc,expect_smul]
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcs (Real.sqrt_nonneg _)

/-- The paper's dimension-free family nuclear bound for the concrete rectangular table operator, with no analytic premises. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For r ∈ ∏_(H ∈ FullRank(F, n, (n + t))) RectanglePartition(Z, (O × U(F, n)), ((O × U(F, n)) × Kernel(H))); G ∈ ℝ^((O × U(F, (n + t))) × (O × U(F, (n + t)))), we have

(∑_z (‖ transport(r, G, z)‖_*)) ≤ √(|Z|) · ‖ G‖_*.
-/
theorem transport_nuclear
    (r : (H : FullRank F n (n+t)) → RectanglePartition Z
      (O × U F n) ((O × U F n) × Kernel H))
    (G : Matrix (O × U F (n+t)) (O × U F (n+t)) ℝ) :
    (∑ z, tableNuclearNorm (transport r G z)) ≤ Real.sqrt (Fintype.card Z) * tableNuclearNorm G :=
  linear_transport_nuclear_bound (transportLinear r) _ (rankOne_transport_nuclear r) G

end

end CircuitCompiler.Rectangular
