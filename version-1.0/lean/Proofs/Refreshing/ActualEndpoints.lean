import Proofs.Refreshing.BoundaryHybrids

/-!
# The actual probability-distribution endpoints of the signed hybrid chain
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RefreshingProof
open Refreshing

/-- Independent finite averaging allows the old endpoint to be averaged inside the one-round answer kernel. -/
theorem one_round_window_factorization {X B Z : Type*}
    [Fintype X] [Fintype B] [Fintype Z] (μX : PMF X) (μB : PMF B)
    (f : X → B → Z → ℝ) (tail : B → Z → ℝ) :
    pmfMean μX (fun x => pmfMean μB (fun b => ∑ z, f x b z * tail b z)) =
      pmfMean μB (fun b => ∑ z, pmfMean μX (fun x => f x b z) * tail b z) := by
  rw [pmfMean_comm]
  simp_rw [pmfMean_sum, pmfMean_mul_const]

/-- Average the first round’s actual conditional-answer probability over its uniform secret-zero old endpoint. -/
def firstTrueKernel {n T leakage : ℕ} [Nonempty (Encoding n (0 : Bit))]
    (A : Strategy n T leakage) (hT : 1 ≤ T) (z : Answer leakage)
    (b : Encoding n (0 : Bit)) : ℝ :=
  pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun a =>
    (conditionalAnswer (A ⟨0, by omega⟩ Fin.elim0) a b z).toReal)

/-- Average the first signed table over its uniform secret-one old endpoint. -/
def firstSignedKernel {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (G : SignedTables n T leakage) (hT : 1 ≤ T) (z : Answer leakage)
    (b : Encoding n (0 : Bit)) : ℝ :=
  pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun a =>
    G ⟨0, by omega⟩ Fin.elim0 z a.val b.val)

/-- The difference between the first actual endpoint kernel and its signed comparison kernel. -/
def firstKernelError {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (G : SignedTables n T leakage) (hT : 1 ≤ T)
    (z : Answer leakage) (b : Encoding n (0 : Bit)) : ℝ :=
  firstTrueKernel A hT z b - firstSignedKernel G hT z b

/-- Propagate a first-round endpoint kernel through the actual canonical continuation to a fixed final transcript. -/
def firstEndpointDifference {n T leakage : ℕ} [Nonempty (Encoding n (0 : Bit))]
    (A : Strategy n T leakage) (hT : 1 ≤ T)
    (E : Answer leakage → Encoding n (0 : Bit) → ℝ) (final : History leakage T) : ℝ :=
  pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun b => ∑ z,
    E z b * (canonicalContinuation A 1 hT b (appendAnswer Fin.elim0 z) final).toReal)

/-- The secret-zero transcript probability equals the first actual endpoint kernel followed by its canonical continuation. -/
theorem first_actual_normalform {n T leakage : ℕ} [Nonempty (Encoding n (0 : Bit))]
    (hn : 2 ≤ n) (A : Strategy n T leakage) (hT : 1 ≤ T) (final : History leakage T) :
    (transcriptDistribution hn A 0 final).toReal =
      firstEndpointDifference A hT (firstTrueKernel A hT) final := by
  rw [← canonicalCutView_eq_transcriptDistribution 0 hn A 0 (by omega)]
  unfold canonicalCutView
  rw [pmf_bind_toReal]
  change pmfMean (canonicalPrefix 0 A 0 (by omega))
    (fun c => (canonicalContinuation A 0 (by omega) c.1 c.2 final).toReal) = _
  rw [pmfMean_canonicalPrefix_zero]
  simp_rw [canonicalContinuation_toReal_step A 0 (by omega)]
  unfold firstEndpointDifference
  exact one_round_window_factorization
    (uniformPMF (Encoding n (0 : Bit))) (uniformPMF (Encoding n (0 : Bit)))
    (fun a b z => (conditionalAnswer (A ⟨0, by omega⟩ Fin.elim0) a b z).toReal)
    (fun b z => (canonicalContinuation A 1 hT b (appendAnswer Fin.elim0 z) final).toReal)

/-- The first signed hybrid equals the signed endpoint kernel followed by the same continuation. -/
theorem first_signed_normalform {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (G : SignedTables n T leakage) (hT : 1 ≤ T)
    (final : History leakage T) :
    signedHybrid A G ⟨0, by omega⟩ final =
      firstEndpointDifference A hT (firstSignedKernel G hT) final := by
  rw [signedHybrid_as_pmfMean, pmfMean_canonicalPrefix_zero]
  unfold firstEndpointDifference
  exact one_round_window_factorization
    (uniformPMF (Encoding n (1 : Bit))) (uniformPMF (Encoding n (0 : Bit)))
    (fun a b z => G ⟨0, by omega⟩ Fin.elim0 z a.val b.val)
    (fun b z => (canonicalContinuation A 1 hT b (appendAnswer Fin.elim0 z) final).toReal)

/-- Propagating the difference of first-round kernels equals the difference of their propagated contributions. -/
theorem firstEndpointDifference_sub {n T leakage : ℕ} [Nonempty (Encoding n (0 : Bit))]
    (A : Strategy n T leakage) (hT : 1 ≤ T)
    (E F : Answer leakage → Encoding n (0 : Bit) → ℝ) (final : History leakage T) :
    firstEndpointDifference A hT (fun z b => E z b - F z b) final =
      firstEndpointDifference A hT E final - firstEndpointDifference A hT F final := by
  unfold firstEndpointDifference
  simp only [sub_mul, Finset.sum_sub_distrib, pmfMean_sub]

/-- Initial actual-to-signed endpoint. It applies also when T = 1. -/
theorem first_endpoint_l1_le {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (hn : 2 ≤ n) (A : Strategy n T leakage) (G : SignedTables n T leakage)
    (hT : 1 ≤ T) (δ : ℝ) (hδ : 0 ≤ δ)
    (hlocal : ∀ z, pmfMean (uniformPMF (Encoding n (0 : Bit)))
      (fun b => |firstKernelError A G hT z b|) ≤ δ) :
    massL1 (fun h => (transcriptDistribution hn A 0 h).toReal)
      (signedHybrid A G ⟨0, by omega⟩) ≤ (K leakage : ℝ) ^ 3 * δ := by
  have heq (final : History leakage T) :
      (transcriptDistribution hn A 0 final).toReal - signedHybrid A G ⟨0, by omega⟩ final =
        firstEndpointDifference A hT (firstKernelError A G hT) final := by
    rw [first_actual_normalform hn A hT, first_signed_normalform A G hT]
    exact (firstEndpointDifference_sub A hT _ _ final).symm
  unfold massL1
  simp_rw [heq]
  have hb := oneRoundNoPrefix_l1_bound (uniformPMF (Encoding n (0 : Bit)))
    (firstKernelError A G hT)
    (fun b z => canonicalContinuation A 1 hT b (appendAnswer Fin.elim0 z)) δ hδ hlocal
  simpa only [firstEndpointDifference, answer_card_eq_K] using hb

/-- The final signed kernel averaged over its uniform secret-zero new state. -/
def lastSignedKernel {n t leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (G : SignedTables n (t + 1) leakage) (h : History leakage t)
    (a : Encoding n (1 : Bit)) (z : Answer leakage) : ℝ :=
  pmfMean (uniformPMF (Encoding n (0 : Bit))) (fun b =>
    G ⟨t, by omega⟩ h z a.val b.val)

/-- Average the last actual conditional-answer probability over its uniform secret-one new endpoint. -/
def lastTrueKernel {n t leakage : ℕ} [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n (t + 1) leakage) (h : History leakage t)
    (a : Encoding n (1 : Bit)) (z : Answer leakage) : ℝ :=
  pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun b =>
    (conditionalAnswer (A ⟨t, by omega⟩ h) a b z).toReal)

/-- The difference between the last signed endpoint kernel and its actual counterpart. -/
def lastKernelError {n t leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n (t + 1) leakage) (G : SignedTables n (t + 1) leakage)
    (h : History leakage t) (a : Encoding n (1 : Bit)) (z : Answer leakage) : ℝ :=
  lastSignedKernel G h a z - lastTrueKernel A h a z

/-- Average a final-round endpoint kernel over the canonical prefix and append its last answer. -/
def lastEndpointDifference {n t leakage : ℕ} [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n (t + 1) leakage)
    (E : History leakage t → Encoding n (1 : Bit) → Answer leakage → ℝ)
    (final : History leakage (t + 1)) : ℝ :=
  pmfMean (canonicalPrefix 1 A t (by omega)) (fun c => ∑ z,
    E c.2 c.1 z * (PMF.pure (appendAnswer c.2 z) final).toReal)

/-- The final signed hybrid equals its final endpoint-kernel representation. -/
theorem last_signed_normalform {n t leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n (t + 1) leakage) (G : SignedTables n (t + 1) leakage)
    (final : History leakage (t + 1)) :
    signedHybrid A G ⟨t, by omega⟩ final = lastEndpointDifference A (lastSignedKernel G) final := by
  rw [signedHybrid_as_pmfMean]
  simp_rw [canonicalContinuation_terminal]
  unfold lastEndpointDifference
  apply congrArg (pmfMean (canonicalPrefix 1 A t (by omega)))
  funext c
  simp_rw [pmfMean_sum, pmfMean_mul_const]
  rfl

/-- The secret-one transcript probability equals its final actual endpoint-kernel representation. -/
theorem last_actual_normalform {n t leakage : ℕ} [Nonempty (Encoding n (1 : Bit))]
    (hn : 2 ≤ n) (A : Strategy n (t + 1) leakage) (final : History leakage (t + 1)) :
    (transcriptDistribution hn A 1 final).toReal = lastEndpointDifference A (lastTrueKernel A) final := by
  rw [← canonicalCutView_eq_transcriptDistribution 1 hn A t (by omega)]
  unfold canonicalCutView
  rw [pmf_bind_toReal]
  change pmfMean (canonicalPrefix 1 A t (by omega))
    (fun c => (canonicalContinuation A t (by omega) c.1 c.2 final).toReal) = _
  simp_rw [canonicalContinuation_toReal_step A t (by omega), canonicalContinuation_terminal]
  unfold lastEndpointDifference
  apply congrArg (pmfMean (canonicalPrefix 1 A t (by omega)))
  funext c
  change pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun b => ∑ z,
    (conditionalAnswer (A ⟨t, by omega⟩ c.2) c.1 b z).toReal *
      (PMF.pure (appendAnswer c.2 z) final).toReal) = _
  simp_rw [pmfMean_sum, pmfMean_mul_const]
  rfl

/-- Propagating the difference of final-round kernels equals the difference of their propagated contributions. -/
theorem lastEndpointDifference_sub {n t leakage : ℕ} [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n (t + 1) leakage)
    (E F : History leakage t → Encoding n (1 : Bit) → Answer leakage → ℝ)
    (final : History leakage (t + 1)) :
    lastEndpointDifference A (fun h a z => E h a z - F h a z) final =
      lastEndpointDifference A E final - lastEndpointDifference A F final := by
  unfold lastEndpointDifference
  simp only [sub_mul, Finset.sum_sub_distrib, pmfMean_sub]

/-- Terminal error accounting, splitting out T = 1 before exposing a preceding round. Every unsigned prefix factor comes from an actual conditional PMF. -/
theorem lastEndpointDifference_l1_le {n t leakage : ℕ} [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n (t + 1) leakage)
    (E : History leakage t → Encoding n (1 : Bit) → Answer leakage → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hlocal : ∀ h z, pmfMean (uniformPMF (Encoding n (1 : Bit))) (fun a => |E h a z|) ≤ δ) :
    ∑ h, |lastEndpointDifference A E h| ≤ (K leakage : ℝ) ^ 3 * δ := by
  cases t with
  | zero =>
      unfold lastEndpointDifference
      simp_rw [pmfMean_canonicalPrefix_zero]
      have hb := oneRoundNoPrefix_l1_bound (uniformPMF (Encoding n (1 : Bit)))
        (fun z a => E Fin.elim0 a z) (fun _ z => PMF.pure (appendAnswer Fin.elim0 z))
        δ hδ (fun z => hlocal Fin.elim0 z)
      simpa only [answer_card_eq_K] using hb
  | succ i =>
      unfold lastEndpointDifference
      simp_rw [pmfMean_canonicalPrefix_succ 1 A i (by omega)]
      have hb := oneRoundPrefix_l1_bound (canonicalPrefix 1 A i (by omega))
        (uniformPMF (Encoding n (1 : Bit)))
        (fun c a => conditionalAnswer (A ⟨i, by omega⟩ c.2) c.1 a)
        (fun c z₀ z₁ a => E (appendAnswer c.2 z₀) a z₁)
        (fun c z₀ _ z₁ => PMF.pure (appendAnswer (appendAnswer c.2 z₀) z₁))
        δ hδ (fun c z₀ z₁ => hlocal (appendAnswer c.2 z₀) z₁)
      simpa only [answer_card_eq_K] using hb

/-- Final signed-to-actual endpoint, covering every T ≥ 1. -/
theorem last_endpoint_l1_le {n t leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (hn : 2 ≤ n) (A : Strategy n (t + 1) leakage) (G : SignedTables n (t + 1) leakage)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hlocal : ∀ h z, pmfMean (uniformPMF (Encoding n (1 : Bit)))
      (fun a => |lastKernelError A G h a z|) ≤ δ) :
    massL1 (signedHybrid A G ⟨t, by omega⟩)
      (fun h => (transcriptDistribution hn A 1 h).toReal) ≤ (K leakage : ℝ) ^ 3 * δ := by
  have heq (final : History leakage (t + 1)) :
      signedHybrid A G ⟨t, by omega⟩ final - (transcriptDistribution hn A 1 final).toReal =
        lastEndpointDifference A (lastKernelError A G) final := by
    rw [last_signed_normalform A G, last_actual_normalform hn A]
    exact (lastEndpointDifference_sub A _ _ final).symm
  unfold massL1
  simp_rw [heq]
  exact lastEndpointDifference_l1_le A _ δ hδ hlocal

end RefreshingProof
