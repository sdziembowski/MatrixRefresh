import Proofs.Compiler.GateApproximation.Interfaces.Gadget.Approximation
import Proofs.Compiler.GateApproximation.Shortening.RectangularFractionalAugmentedApproximation
import Proofs.Compiler.GateApproximation.Shortening.Factors



/-!
# The direct local interface after physical rectangular shortening

The chosen factors and both per-answer `L₂` estimates are transported by the actual accepted shortening operator. No factor from the answer alphabet is introduced. The last theorem uses the physical conditional answer distribution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2200000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical

namespace CircuitCompiler.GadgetApproximation

open Refresh MatrixRefresh TableAnalysis RefreshAnalysis SingularTruncation

open AveragedEnergyComparison ShorteningTransport Shortening Rectangular

noncomputable section

/-
Mathematical definition (normal notation): For I,J a set; e ∈ I ≃ J; G ∈ I → I → ℝ; a ∈ Factors(G), define

reindexFactors(e, a) := a.restrict((e)⁻¹, (e)⁻¹).
-/
def reindexFactors {I J : Type*} (e : I ≃ J) {G : I → I → ℝ} (a : Factors G) :
    Factors (fun x y => G (e.symm x) (e.symm y)) := a.restrict e.symm e.symm

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For I,J a set; e ∈ I ≃ J; G ∈ I → I → ℝ; a ∈ Factors(G); x ∈ J, we have

leftEnergy(reindexFactors(e, a))(x) = a.leftEnergy((e)⁻¹(x)).
-/
theorem reindexFactors_leftEnergy {I J : Type*} (e : I ≃ J) {G : I → I → ℝ}
    (a : Factors G) (x : J) :
    (reindexFactors e a).leftEnergy x = a.leftEnergy (e.symm x) :=
  rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For I,J a set; e ∈ I ≃ J; G ∈ I → I → ℝ; a ∈ Factors(G); y ∈ J, we have

rightEnergy(reindexFactors(e, a))(y) = a.rightEnergy((e)⁻¹(y)).
-/
theorem reindexFactors_rightEnergy {I J : Type*} (e : I ≃ J) {G : I → I → ℝ}
    (a : Factors G) (y : J) :
    (reindexFactors e a).rightEnergy y = a.rightEnergy (e.symm y) :=
  rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For I,J a set; e ∈ I ≃ J; G ∈ I → I → ℝ; a ∈ Factors(G), assume I is finite; J is finite. Then

𝔼ᵤ [leftEnergy(reindexFactors(e, a))(u)] = 𝔼ᵥ [a.leftEnergy(v)].
-/
theorem reindexFactors_left_mean {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) {G : I → I → ℝ} (a : Factors G) :
    uavg (reindexFactors e a).leftEnergy = uavg a.leftEnergy :=
  uavg_equiv e.symm a.leftEnergy

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For I,J a set; e ∈ I ≃ J; G ∈ I → I → ℝ; a ∈ Factors(G), assume I is finite; J is finite. Then

𝔼ᵤ [rightEnergy(reindexFactors(e, a))(u)] = 𝔼ᵥ [a.rightEnergy(v)].
-/
theorem reindexFactors_right_mean {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) {G : I → I → ℝ} (a : Factors G) :
    uavg (reindexFactors e a).rightEnergy = uavg a.rightEnergy :=
  uavg_equiv e.symm a.rightEnergy

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; s, t, v ∈ F; G ∈ ℝ^(GateSide(F, n, m) × GateSide(F, n, m)), assume 2 ≤ n; 2 ≤ m; Fiber(F, m, v) ≠ ∅. Then

‖ ((ou ↦ G((((ou)₁)₁, ou.2.val.L), (((ou)₁)₂, ou.2.val.R))))‖_(2,(oldLabelDistribution(s, t) ⊗ 𝒰_(Fiber(F, m, v)))) = ‖ ((xy ↦ G((xy)₁, (xy)₂)))‖_(2,independentLabelledPortDistribution(s, t, v)).
-/
theorem fiberTable_rms_eq_labelled {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (s t v : F) [Nonempty (Fiber F m v)]
    (G : Matrix (GateSide F n m) (GateSide F n m) ℝ) :
    rms ((oldLabelDistribution hn s t).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F m v)))
      (fun ou => G (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)) =
      rms (independentLabelledPortDistribution hn hm s t v) (fun xy => G xy.1 xy.2) := by
  unfold rms
  congr 1
  exact independentLabelledPortDistribution_fiber_expect hn hm s t v (fun x y => G x y ^ 2)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m, k ∈ ℕ; s, t, v ∈ F; G ∈ ℝ^(GateSide(F, n, m) × GateSide(F, n, m)), assume m = k; 2 ≤ n; Fiber(F, m, v) ≠ ∅; Fiber(F, k, v) ≠ ∅. Then

‖ ((ou ↦ reindexGateTable(G, (((ou)₁)₁, ou.2.val.L), (((ou)₁)₂, ou.2.val.R))))‖_(2,(oldLabelDistribution(s, t) ⊗ 𝒰_(Fiber(F, k, v)))) = ‖ ((ou ↦ G((((ou)₁)₁, ou.2.val.L), (((ou)₁)₂, ou.2.val.R))))‖_(2,(oldLabelDistribution(s, t) ⊗ 𝒰_(Fiber(F, m, v)))).
-/
theorem fiberTable_rms_reindex {n m k : ℕ} (h : m = k) (hn : 2 ≤ n)
    (s t v : F) [Nonempty (Fiber F m v)] [Nonempty (Fiber F k v)]
    (G : Matrix (GateSide F n m) (GateSide F n m) ℝ) :
    rms ((oldLabelDistribution hn s t).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F k v)))
      (fun ou => reindexGateTable h G (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)) =
    rms ((oldLabelDistribution hn s t).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F m v)))
      (fun ou => G (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)) := by
  subst k
  rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m, k ∈ ℕ; s, t, v ∈ F; P, G ∈ ℝ^(GateSide(F, n, m) × GateSide(F, n, m)), assume m = k; 2 ≤ n; 2 ≤ m; Fiber(F, m, v) ≠ ∅; Fiber(F, k, v) ≠ ∅. Then

‖ ((ou ↦ reindexGateTable(P, (((ou)₁)₁, ou.2.val.L), (((ou)₁)₂, ou.2.val.R)) - reindexGateTable(G, (((ou)₁)₁, ou.2.val.L), (((ou)₁)₂, ou.2.val.R))))‖_(2,(oldLabelDistribution(s, t) ⊗ 𝒰_(Fiber(F, k, v)))) = ‖ ((xy ↦ P((xy)₁, (xy)₂) - G((xy)₁, (xy)₂)))‖_(2,independentLabelledPortDistribution(s, t, v)).
-/
theorem fiberTable_rms_reindex_sub {n m k : ℕ} (h : m = k) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (s t v : F) [Nonempty (Fiber F m v)] [Nonempty (Fiber F k v)]
    (P G : Matrix (GateSide F n m) (GateSide F n m) ℝ) :
    rms ((oldLabelDistribution hn s t).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F k v)))
      (fun ou => reindexGateTable h P (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R) -
        reindexGateTable h G (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)) =
    rms (independentLabelledPortDistribution hn hm s t v)
      (fun xy => P xy.1 xy.2 - G xy.1 xy.2) := by
  subst k
  exact fiberTable_rms_eq_labelled hn hm s t v (fun x y => P x y - G x y)

variable {A B : Type*} [Fintype A] [Fintype B] {n t : ℕ}

variable [Nonempty (U F n)] [Nonempty (U F (n+t))]
  [Nonempty (FullRank F n (n+t))]

/-
Mathematical definition (normal notation): For c ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n + 1)(F), A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(B, GateSide(F, n, n), (GateSide(F, n, n) × Kernel(H))); z ∈ A × B; β ∈ ℝ, assume n · n + 1 = n + t. define

shortenedApproximation(c, p, r, z, β) := Fractional.transport(r((z)₁), reindexGateTable(augmentedApproximation(c, p, (z)₁, β)), (z)₂).
-/
def shortenedApproximation (hdim : n*n+1 = n+t) (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (GateSide F n n) ((GateSide F n n) × Kernel H)) (z : A × B) (β : ℝ) :
    Matrix (GateSide F n n) (GateSide F n n) ℝ :=
  Fractional.transport (r z.1) (reindexGateTable hdim (augmentedApproximation c p z.1 β)) z.2

/-
Mathematical definition (normal notation): For c ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n + 1)(F), A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(B, GateSide(F, n, n), (GateSide(F, n, n) × Kernel(H))); z ∈ A × B; β ∈ ℝ, assume n · n + 1 = n + t. define

shortenedFactors(c, p, r, z, β) := outputFactors(r((z)₁), reindexFactors(sideDimensionEquiv(n), augmentedFactors(c, p, (z)₁, β)), (z)₂).
-/
def shortenedFactors (hdim : n*n+1 = n+t) (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (GateSide F n n) ((GateSide F n n) × Kernel H)) (z : A × B) (β : ℝ) :
    Factors (shortenedApproximation hdim c p r z β) :=
  outputFactors (r z.1) (reindexFactors (sideDimensionEquiv n hdim)
    (augmentedFactors c p z.1 β)) z.2

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n + 1)(F), A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(B, GateSide(F, n, n), (GateSide(F, n, n) × Kernel(H))); z ∈ A × B; β ∈ ℝ, assume 2 ≤ n; n · n + 1 = n + t; 0 < β. Then

(∀ x, leftEnergy(shortenedFactors(c, p, r, z, β))(x) ≤ 2 / β) ∧ (∀ y, rightEnergy(shortenedFactors(c, p, r, z, β))(y) ≤ 2 / β).
-/
theorem shortenedFactors_pointwise (hn : 2 ≤ n) (hdim : n*n+1 = n+t) (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (GateSide F n n) ((GateSide F n n) × Kernel H))
    (z : A × B) (β : ℝ) (hβ : 0 < β) :
    (∀ x, (shortenedFactors hdim c p r z β).leftEnergy x ≤ 2 / β) ∧
      (∀ y, (shortenedFactors hdim c p r z β).rightEnergy y ≤ 2 / β) := by
  have h := augmentedFactors_pointwise hn c p z.1 β hβ
  exact ⟨outputFactors_left_max (r z.1) _ z.2 (2/β) (fun x => h.1 _),
    outputFactors_right_max (r z.1) _ z.2 (2/β) (fun y => h.2 _)⟩

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n + 1)(F), A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(B, GateSide(F, n, n), (GateSide(F, n, n) × Kernel(H))); z ∈ A × B; β ∈ ℝ, assume |F| = 2; 2 ≤ n; n · n + 1 = n + t; 0 < β; β ≤ 1; 1 ≤ |(U(F, n) × U(F, n))| · β³. Then

𝔼ᵤ [leftEnergy(shortenedFactors(c, p, r, z, β))(u)] ≤ 8 ∧ 𝔼ᵥ [rightEnergy(shortenedFactors(c, p, r, z, β))(v)] ≤ 8.
-/
theorem shortenedFactors_mean (hq : fieldCard F = 2) (hn : 2 ≤ n) (hdim : n*n+1 = n+t) (c : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (GateSide F n n) ((GateSide F n n) × Kernel H))
    (z : A × B) (β : ℝ) (hβ : 0 < β) (hβone : β ≤ 1)
    (hthreshold : 1 ≤ (Fintype.card (U F n × U F n) : ℝ) * β ^ 3) :
    uavg (shortenedFactors hdim c p r z β).leftEnergy ≤ 8 ∧
      uavg (shortenedFactors hdim c p r z β).rightEnergy ≤ 8 := by
  let a := reindexFactors (sideDimensionEquiv n hdim) (augmentedFactors c p z.1 β)
  have hl := outputFactors_left_mean (r z.1) a z.2
  have hr := outputFactors_right_mean (r z.1) a z.2
  rw [← uavg_eq_expect_uniform, ← uavg_eq_expect_uniform] at hl hr
  have h := augmentedFactors_mean hq hn c p z.1 β hβ hβone hthreshold
  exact ⟨hl.trans ((reindexFactors_left_mean _ _).le.trans h.1),
    hr.trans ((reindexFactors_right_mean _ _).le.trans h.2)⟩

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c, s₁, s₂, v ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n + 1)(F), A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(B, GateSide(F, n, n), (GateSide(F, n, n) × Kernel(H))); z ∈ A × B; β ∈ ℝ, assume |F| = 2; 2 ≤ n; n · n + 1 = n + t; Fiber(F, n, v) ≠ ∅; Fiber(F, (n + t), v) ≠ ∅. Then

‖ ((ou ↦ shortenedApproximation(c, p, r, z, β, (((ou)₁)₁, ou.2.val.L), (((ou)₁)₂, ou.2.val.R))))‖_(2,(oldLabelDistribution(s₁, s₂) ⊗ 𝒰_(Fiber(F, n, v)))) ≤ 12 .
-/
theorem shortenedApproximation_arbitrary_labels (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (hdim : n*n+1 = n+t) (c s₁ s₂ v : F)
    [Nonempty (Fiber F n v)] [Nonempty (Fiber F (n+t) v)]
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (GateSide F n n) ((GateSide F n n) × Kernel H)) (z : A × B) (β : ℝ) :
    rms ((oldLabelDistribution hn s₁ s₂).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F n v)))
      (fun ou => shortenedApproximation hdim c p r z β
        (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)) ≤ 12 := by
  letI := encoding_fiber_nonempty (show 2 ≤ n*n+1 by nlinarith) v
  have h := transport_L2 (r z.1)
    (reindexGateTable hdim (augmentedApproximation c p z.1 β)) z.2 (oldLabelDistribution hn s₁ s₂) v
  refine h.trans ?_
  rw [fiberTable_rms_reindex hdim hn s₁ s₂ v]
  rw [fiberTable_rms_eq_labelled hn (by nlinarith) s₁ s₂ v]
  exact augmentedApproximation_arbitrary_labels hq hn c s₁ s₂ v p z.1 β

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c, s₁, s₂ ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n + 1)(F), A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(B, GateSide(F, n, n), (GateSide(F, n, n) × Kernel(H))); z ∈ A × B; β ∈ ℝ, assume |F| = 2; 2 ≤ n; n · n + 1 = n + t; Fiber(F, n, (s₁ · s₂ + c)) ≠ ∅; Fiber(F, (n + t), (s₁ · s₂ + c)) ≠ ∅; 0 < β; β ≤ 1; 1 ≤ |(U(F, n) × U(F, n))| · β³. Then

‖ ((ou ↦ Fractional.transport(r((z)₁), reindexGateTable(augmentedProbability(c, p, (z)₁)), (z)₂, (((ou)₁)₁, ou.2.val.L), (((ou)₁)₂, ou.2.val.R)) - shortenedApproximation(c, p, r, z, β, (((ou)₁)₁, ou.2.val.L), (((ou)₁)₂, ou.2.val.R))))‖_(2,(oldLabelDistribution(s₁, s₂) ⊗ 𝒰_(Fiber(F, n, (s₁ · s₂ + c))))) ≤ 396 · β^(1 / 3).
-/
theorem shortenedApproximation_valid_table_error (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (hdim : n*n+1 = n+t) (c s₁ s₂ : F)
    [Nonempty (Fiber F n (s₁*s₂+c))] [Nonempty (Fiber F (n+t) (s₁*s₂+c))]
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (GateSide F n n) ((GateSide F n n) × Kernel H))
    (z : A × B) (β : ℝ) (hβ : 0 < β) (hβone : β ≤ 1)
    (hthreshold : 1 ≤ (Fintype.card (U F n × U F n) : ℝ) * β ^ 3) :
    rms ((oldLabelDistribution hn s₁ s₂).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (s₁*s₂+c))))
      (fun ou => Fractional.transport (r z.1)
        (reindexGateTable hdim (augmentedProbability c p z.1)) z.2
          (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R) -
        shortenedApproximation hdim c p r z β (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)) ≤
      396 * β ^ (1 / 3 : ℝ) := by
  letI := encoding_fiber_nonempty (show 2 ≤ n*n+1 by nlinarith) (s₁*s₂+c)
  have h := transport_approximation_L2 (r z.1)
    (reindexGateTable hdim (augmentedProbability c p z.1))
    (reindexGateTable hdim (augmentedApproximation c p z.1 β)) z.2
    (oldLabelDistribution hn s₁ s₂) (s₁*s₂+c)
  refine h.trans ?_
  rw [fiberTable_rms_reindex_sub hdim hn (show 2 ≤ n*n+1 by nlinarith) s₁ s₂ (s₁*s₂+c)]
  exact augmentedApproximation_valid_error hq hn c s₁ s₂ p z.1 β hβ hβone hthreshold

/-- Per-answer approximation of the actual accepted physical gadget, including the matrix answer and shortening answer. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For c, s₁, s₂ ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n + 1)(F), A); r ∈ A → ∏_(H ∈ FullRank(F, n, (n + t))) FractionalRectanglePartition(B, GateSide(F, n, n), (GateSide(F, n, n) × Kernel(H))); z ∈ A × B; β ∈ ℝ, assume |F| = 2; 2 ≤ n; n · n + 1 = n + t; Fiber(F, n, (s₁ · s₂ + c)) ≠ ∅; Fiber(F, (n + t), (s₁ · s₂ + c)) ≠ ∅; 0 < β; β ≤ 1; 1 ≤ |(U(F, n) × U(F, n))| · β³. Then

‖ ((ou ↦ Fractional.shortenedAnswerDistribution(((o, (, u, :, Fiber, F, (, n, +, t,), (, s₁, *, s₂, +, c,), ) ↦ augmentedLongAnswerDistribution(c, p, o, u))), r, (ou)₁, (ou)₂)(z) - shortenedApproximation(c, p, r, z, β, (((ou)₁)₁, ou.2.val.L), (((ou)₁)₂, ou.2.val.R))))‖_(2,(oldLabelDistribution(s₁, s₂) ⊗ 𝒰_(Fiber(F, n, (s₁ · s₂ + c))))) ≤ 396 · β^(1 / 3).
-/
theorem shortenedApproximation_physical_error (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (hdim : n*n+1 = n+t) (c s₁ s₂ : F)
    [Nonempty (Fiber F n (s₁*s₂+c))] [Nonempty (Fiber F (n+t) (s₁*s₂+c))]
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n+1)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (GateSide F n n) ((GateSide F n n) × Kernel H))
    (z : A × B) (β : ℝ) (hβ : 0 < β) (hβone : β ≤ 1)
    (hthreshold : 1 ≤ (Fintype.card (U F n × U F n) : ℝ) * β ^ 3) :
    rms ((oldLabelDistribution hn s₁ s₂).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (s₁*s₂+c))))
      (fun ou => (Fractional.shortenedAnswerDistribution
        (fun o (u : Fiber F (n+t) (s₁*s₂+c)) => augmentedLongAnswerDistribution hdim c p o u.val)
        r ou.1 ou.2).weight z -
        shortenedApproximation hdim c p r z β (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)) ≤
      396 * β ^ (1 / 3 : ℝ) := by
  have he : rms ((oldLabelDistribution hn s₁ s₂).prod
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (s₁*s₂+c))))
      (fun ou => (Fractional.shortenedAnswerDistribution
        (fun o (u : Fiber F (n+t) (s₁*s₂+c)) => augmentedLongAnswerDistribution hdim c p o u.val)
        r ou.1 ou.2).weight z -
        shortenedApproximation hdim c p r z β (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)) =
      rms ((oldLabelDistribution hn s₁ s₂).prod
        (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (s₁*s₂+c))))
        (fun ou => Fractional.transport (r z.1)
          (reindexGateTable hdim (augmentedProbability c p z.1)) z.2
            (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R) -
          shortenedApproximation hdim c p r z β (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)) := by
    unfold rms
    congr 1
    unfold FiniteDistribution.expect
    apply Finset.sum_congr rfl
    intro ou _
    by_cases ho : (oldLabelDistribution hn s₁ s₂).weight ou.1 = 0
    · simp [FiniteDistribution.prod, FiniteDistribution.joint, ho]
    · dsimp only
      rw [show z = (z.1,z.2) from rfl,
        Fractional.shortenedAnswerDistribution_weight _ r
          (fun a => reindexGateTable hdim (augmentedProbability c p a)) ou.1
          (fun a u => augmentedLongAnswerDistribution_on_support hn hdim c s₁ s₂ p ou.1 ho u a)]
  rw [he]
  exact shortenedApproximation_valid_table_error hq hn hdim c s₁ s₂ p r z β hβ hβone hthreshold

end

end CircuitCompiler.GadgetApproximation
