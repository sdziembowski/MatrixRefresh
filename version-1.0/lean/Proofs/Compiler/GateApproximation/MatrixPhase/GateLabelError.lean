import Proofs.Compiler.GateApproximation.MatrixPhase.GateDual



/-!
# Joint-port approximation on fixed old labels and a typed new fiber
-/
set_option autoImplicit false

open scoped BigOperators Classical

namespace CircuitCompiler

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {F Z : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype Z]

/-
Mathematical definition (normal notation): For n ∈ ℕ; s, t ∈ F, assume 2 ≤ n. define

oldLabelDistribution(s, t) := (oldPortRegroup(n)_*(μₛ ⊗ μₜ)).
-/
def oldLabelDistribution {n : ℕ} (hn : 2 ≤ n) (s t : F) :
    FiniteDistribution ((U F n × U F n) × (U F n × U F n)) :=
  ((mu F n hn s).prod (mu F n hn t)).map (oldPortRegroup n)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s, t ∈ F; ab ∈ State(F, n) × State(F, n), assume 2 ≤ n; (μₛ ⊗ μₜ)(ab) ≠ 0. Then

secret((ab)₁) = s ∧ secret((ab)₂) = t.
-/
private theorem old_labels_of_weight_ne_zero {n : ℕ} (hn : 2 ≤ n) (s t : F)
    (ab : State F n × State F n)
    (h : ((mu F n hn s).prod (mu F n hn t)).weight ab ≠ 0) :
    secret ab.1 = s ∧ secret ab.2 = t := by
  change (mu F n hn s).weight ab.1 * (mu F n hn t).weight ab.2 ≠ 0 at h
  exact ⟨mu_supports n hn s ab.1 (mul_ne_zero_iff.mp h).1,
    mu_supports n hn t ab.2 (mul_ne_zero_iff.mp h).2⟩

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; s, t ∈ F, assume 2 ≤ n; 2 ≤ m. Then

joint((μₛ ⊗ μₜ))(((ab ↦ μ_(secret((ab)₁) · secret((ab)₂))))) = ((μₛ ⊗ μₜ) ⊗ μ_(s · t)).
-/
private theorem old_joint_eq_prod {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (s t : F) :
    ((mu F n hn s).prod (mu F n hn t)).joint
      (fun ab => mu F m hm (secret ab.1 * secret ab.2)) =
    ((mu F n hn s).prod (mu F n hn t)).prod (mu F m hm (s*t)) := by
  ext abu
  change ((mu F n hn s).prod (mu F n hn t)).weight abu.1 *
      (mu F m hm (secret abu.1.1 * secret abu.1.2)).weight abu.2 =
    ((mu F n hn s).prod (mu F n hn t)).weight abu.1 * (mu F m hm (s*t)).weight abu.2
  by_cases h : ((mu F n hn s).prod (mu F n hn t)).weight abu.1 = 0
  · simp [h]
  · obtain ⟨hs,ht⟩ := old_labels_of_weight_ne_zero hn s t abu.1 h
    rw [hs,ht]

/-- Presampling the fixed output fiber gives exactly the labeled joint-port reference distribution. This keeps both original operands as explicit variables. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; s, t ∈ F; f ∈ GateSide(F, n, m) → GateSide(F, n, m) → ℝ, assume 2 ≤ n; 2 ≤ m; Fiber(F, m, (s · t)) ≠ ∅. Then

𝔼_(ou ← (oldLabelDistribution(s, t) ⊗ 𝒰_(Fiber(F, m, (s · t))))) [f((((ou)₁)₁, ou.2.val.L), (((ou)₁)₂, ou.2.val.R))] = 𝔼_(xy ← labelledPortDistribution(s, t)) [f((xy)₁, (xy)₂)].
-/
theorem oldLabelDistribution_fiber_expect {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (s t : F)
    [Nonempty (Fiber F m (s*t))]
    (f : GateSide F n m → GateSide F n m → ℝ) :
    ((oldLabelDistribution hn s t).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F m (s*t)))).expect
      (fun ou => f (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)) =
      (labelledPortDistribution hn hm s t).expect (fun xy => f xy.1 xy.2) := by
  rw [labelledPortDistribution, old_joint_eq_prod hn hm s t, expect_map, expect_prod]
  rw [expect_prod, oldLabelDistribution, expect_map]
  simp only [mu, expect_map]
  rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A a set; P ∈ 𝒟(A); f, g ∈ A → ℝ, assume A is finite; ∀ a, (P(a) ≠ 0) ⇒ f(a) = g(a). Then

𝔼_(u ← P) [f(u)] = 𝔼_(v ← P) [g(v)].
-/
private theorem expect_congr_on_support {A : Type*} [Fintype A]
    (P : FiniteDistribution A) (f g : A → ℝ) (h : ∀ a, P.weight a ≠ 0 → f a = g a) :
    P.expect f = P.expect g := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : P.weight a = 0
  · simp [ha]
  · rw [h a ha]

/-- Squared error for the genuine conditional matrix-answer probability table, on arbitrary fixed input labels. The factor `2q` is the exact bound used to pass the ambient joint-port estimate to the shortening theorem. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s, t ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z); G ∈ Z → ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))); eta ∈ ℝ, assume 2 ≤ n; 2 ≤ n · n; Fiber(F, (n · n), (s · t)) ≠ ∅; 𝔼ₓ [𝔼_y [gateDensity(x, y) · ∑_z ((groupedMatrixAnswerProb(p, z, x, y) - G(z, x, y))²)]] ≤ eta². Then

𝔼_(ou ← (oldLabelDistribution(s, t) ⊗ 𝒰_(Fiber(F, (n · n), (s · t))))) [∑_z ((matrixAnswerDistribution(p, ((((ou)₁)₁)₁, (((ou)₁)₂)₁), ((((ou)₁)₁)₂, (((ou)₁)₂)₂), (ou)₂)(z) - G(z, (((ou)₁)₁, ou.2.val.L), (((ou)₁)₂, ou.2.val.R)))²)] ≤ (2 · |F| · eta)².
-/
theorem matrixAnswerDistribution_fixed_labels_L2 {n : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ n*n)
    (s t : F) [Nonempty (Fiber F (n*n) (s*t))]
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n)) Z)
    (G : Z → Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℝ)
    (eta : ℝ)
    (herr : uavg (fun x => uavg (fun y => gateDensity x y *
      ∑ z, (groupedMatrixAnswerProb p z x y - G z x y)^2)) ≤ eta^2) :
    ((oldLabelDistribution hn s t).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n*n) (s*t)))).expect
      (fun ou => ∑ z, ((matrixAnswerDistribution p ⟨ou.1.1.1,ou.1.2.1⟩ ⟨ou.1.1.2,ou.1.2.2⟩ ou.2.val).weight z -
        G z (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R))^2) ≤ (2*(fieldCard F : ℝ)*eta)^2 := by
  let err := fun z (x y : GateSide F n (n*n)) => groupedMatrixAnswerProb p z x y-G z x y
  have he : ((oldLabelDistribution hn s t).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n*n) (s*t)))).expect
      (fun ou => ∑ z, ((matrixAnswerDistribution p ⟨ou.1.1.1,ou.1.2.1⟩ ⟨ou.1.1.2,ou.1.2.2⟩ ou.2.val).weight z -
        G z (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R))^2) =
    (labelledPortDistribution hn hm s t).expect (fun xy => ∑ z, err z xy.1 xy.2 ^ 2) := by
    rw [← oldLabelDistribution_fiber_expect hn hm s t (fun x y => ∑ z, err z x y ^ 2)]
    rw [expect_prod, expect_prod, oldLabelDistribution, expect_map, expect_map]
    apply expect_congr_on_support
    intro ab hab
    obtain ⟨hs,ht⟩ := old_labels_of_weight_ne_zero hn s t ab hab
    apply Finset.sum_congr rfl
    intro u _
    congr 1
    apply Finset.sum_congr rfl
    intro z _
    have hsecret : secret u.val = secret ab.1 * secret ab.2 := by rw [hs,ht]; exact u.property
    simp only [err, groupedMatrixAnswerProb, oldPortRegroup, Equiv.coe_fn_mk,
      matrixAnswerProb, hsecret, if_pos]
  rw [he]
  have h := labelledPortDistribution_expect_le hn hm s t (fun x y => ∑ z, err z x y^2)
    (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have h' := h.trans (mul_le_mul_of_nonneg_left herr (by positivity : 0 ≤ 4*(fieldCard F : ℝ)^2))
  nlinarith

/-- Conditioning the common absolute error on the two old labels has only a field-dependent cost. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s, t ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z); G ∈ Z → ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))); eta ∈ ℝ, assume 2 ≤ n; 2 ≤ n · n; Fiber(F, (n · n), (s · t)) ≠ ∅; 𝔼ₓ [𝔼_y [gateDensity(x, y) · ∑_z (|groupedMatrixAnswerProb(p, z, x, y) - G(z, x, y)|)]] ≤ eta. Then

𝔼_(ou ← (oldLabelDistribution(s, t) ⊗ 𝒰_(Fiber(F, (n · n), (s · t))))) [∑_z (|matrixAnswerDistribution(p, ((((ou)₁)₁)₁, (((ou)₁)₂)₁), ((((ou)₁)₁)₂, (((ou)₁)₂)₂), (ou)₂)(z) - G(z, (((ou)₁)₁, ou.2.val.L), (((ou)₁)₂, ou.2.val.R))|)] ≤ 4 · (|F|)² · eta.
-/
theorem matrixAnswerDistribution_fixed_labels_L1 {n : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ n*n)
    (s t : F) [Nonempty (Fiber F (n*n) (s*t))]
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n)) Z)
    (G : Z → Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℝ)
    (eta : ℝ)
    (herr : uavg (fun x => uavg (fun y => gateDensity x y *
      ∑ z, |groupedMatrixAnswerProb p z x y - G z x y|)) ≤ eta) :
    ((oldLabelDistribution hn s t).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n*n) (s*t)))).expect
      (fun ou => ∑ z, |(matrixAnswerDistribution p ⟨ou.1.1.1,ou.1.2.1⟩ ⟨ou.1.1.2,ou.1.2.2⟩ ou.2.val).weight z -
        G z (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)|) ≤ 4*(fieldCard F : ℝ)^2*eta := by
  let err := fun z (x y : GateSide F n (n*n)) => groupedMatrixAnswerProb p z x y-G z x y
  have he : ((oldLabelDistribution hn s t).prod (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n*n) (s*t)))).expect
      (fun ou => ∑ z, |(matrixAnswerDistribution p ⟨ou.1.1.1,ou.1.2.1⟩ ⟨ou.1.1.2,ou.1.2.2⟩ ou.2.val).weight z -
        G z (ou.1.1,ou.2.val.L) (ou.1.2,ou.2.val.R)|) =
    (labelledPortDistribution hn hm s t).expect (fun xy => ∑ z, |err z xy.1 xy.2|) := by
    rw [← oldLabelDistribution_fiber_expect hn hm s t (fun x y => ∑ z, |err z x y|)]
    rw [expect_prod, expect_prod, oldLabelDistribution, expect_map, expect_map]
    apply expect_congr_on_support
    intro ab hab
    obtain ⟨hs,ht⟩ := old_labels_of_weight_ne_zero hn s t ab hab
    apply Finset.sum_congr rfl
    intro u _
    congr 1
    apply Finset.sum_congr rfl
    intro z _
    have hsecret : secret u.val = secret ab.1 * secret ab.2 := by rw [hs,ht]; exact u.property
    simp only [err, groupedMatrixAnswerProb, oldPortRegroup, Equiv.coe_fn_mk,
      matrixAnswerProb, hsecret, if_pos]
  rw [he]
  have h := labelledPortDistribution_expect_le hn hm s t (fun x y => ∑ z, |err z x y|)
    (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have h' := h.trans (mul_le_mul_of_nonneg_left herr (by positivity : 0 ≤ 4*(fieldCard F : ℝ)^2))
  nlinarith

end

end CircuitCompiler
