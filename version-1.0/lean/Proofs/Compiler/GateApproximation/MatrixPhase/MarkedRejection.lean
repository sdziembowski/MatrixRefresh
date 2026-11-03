import Proofs.Compiler.GateApproximation.MatrixPhase.RejectionPrefix
import Proofs.Compiler.Construction.Parameters



/-!
# Rejection sampling with internal marks on every proposal

An outer proposal has a finite public result and a possibly countable private internal tape. Conditional marks are sampled independently at each attempt. The normalized complete trace has exactly the independent-proposal mass, retaining the marks on rejected attempts as well as on the successful attempt.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ENNReal Classical

namespace CircuitCompiler.Sampling.Unbounded

open Refresh

noncomputable section



variable {α β : Type*} [Fintype α]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; R ∈ α → PMF(β); t ∈ StoppedTape(α); marks ∈ Tape(β, (t)₁) × β, assume 0 < acceptance(P, accept). Then

markedDistribution(P, accept, R, (t, marks)) = distribution(P, accept, t) · prefixMarks(R, (t)₁, ((t)₂)₁, (marks)₁) · R(((t)₂)₂, (marks)₂).
-/
@[simp] theorem markedDistribution_apply (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (R : α → PMF β)
    (t : StoppedTape α) (marks : Tape β t.1 × β) :
    markedDistribution P accept hp R ⟨t,marks⟩ =
      distribution P accept hp t * prefixMarks R t.1 t.2.1 marks.1 * R t.2.2 marks.2 := by
  change distribution P accept hp t *
    (prefixMarks R t.1 t.2.1 marks.1 * R t.2.2 marks.2) = _
  ring

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; R ∈ α → PMF(β), assume 0 < acceptance(P, accept). Then

((Sigma)₁_*markedDistribution(P, accept, R)) = distribution(P, accept).
-/
theorem markedDistribution_forget (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (R : α → PMF β) :
    (markedDistribution P accept hp R).map Sigma.fst = distribution P accept hp :=
  sigmaPMF_fst _ _

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; P ∈ 𝒟(α); accept ∈ α → Bool; R ∈ α → PMF(β); f ∈ MarkedTape(α, β) → V, assume 0 < acceptance(P, accept). Then

(f_*markedDistribution(P, accept, R)) = bind(distribution(P, accept), ((t ↦ (((marks ↦ f((t, marks))))_*traceMarks(R, t))))).
-/
theorem markedDistribution_observation {V : Type*} (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (R : α → PMF β) (f : MarkedTape α β → V) :
    (markedDistribution P accept hp R).map f = (distribution P accept hp).bind
      (fun t => (traceMarks R t).map (fun marks => f ⟨t,marks⟩)) :=
  sigmaPMF_observation _ _ _

/-- Product of the genuine enriched proposal masses along a finite prefix. -/
/- Mathematical definition (normal notation): For a proposal prefix (aᵢ)ᵢ₌₁ᵏ and mark prefix (bᵢ)ᵢ₌₁ᵏ, the joint independent mass is ∏ᵢ₌₁ ᵏ P(aᵢ)R(aᵢ,bᵢ). The empty prefix has mass one. -/
def enrichedPrefixWeight (P : FiniteDistribution α) (R : α → PMF β) :
    (k : ℕ) → Tape α k → Tape β k → ℝ≥0∞
  | 0, _, _ => 1
  | k+1, a, b => (toPMF P a.1 * R a.1 b.1) * enrichedPrefixWeight P R k a.2 b.2

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); R ∈ α → PMF(β); k ∈ ℕ; a ∈ Tape(α, k); b ∈ Tape(β, k), we have

enrichedPrefixWeight(P, R, k, a, b) = ENNReal.ofReal(tapeDistribution(P, k)(a)) · prefixMarks(R, k, a, b).
-/
theorem enrichedPrefixWeight_eq (P : FiniteDistribution α) (R : α → PMF β)
    (k : ℕ) (a : Tape α k) (b : Tape β k) :
    enrichedPrefixWeight P R k a b =
      ENNReal.ofReal ((tapeDistribution P k).weight a) * prefixMarks R k a b := by
  induction k with
  | zero =>
    cases a
    cases b
    simp [enrichedPrefixWeight, prefixMarks, tapeDistribution, Tape, FiniteDistribution.pure]
  | succ k ih =>
    change (_ * _) * enrichedPrefixWeight P R k a.2 b.2 =
      ENNReal.ofReal (P.weight a.1 * (tapeDistribution P k).weight a.2) *
        (R a.1 b.1 * prefixMarks R k a.2 b.2)
    rw [ih, ENNReal.ofReal_mul (P.nonneg a.1)]
    simp only [toPMF_apply]
    ring

/-- Every valid marked trace has precisely the product of the enriched iid proposal probabilities. Thus the mark construction is an actual rejection loop over internal tapes, not an assumption about a conditional leakage distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; R ∈ α → PMF(β); t ∈ StoppedTape(α); marks ∈ Tape(β, (t)₁) × β, assume 0 < acceptance(P, accept); AllRejected(accept, (t)₁, ((t)₂)₁); accept(((t)₂)₂) = true. Then

markedDistribution(P, accept, R, (t, marks)) = enrichedPrefixWeight(P, R, (t)₁, ((t)₂)₁, (marks)₁) · (toPMF(P, ((t)₂)₂) · R(((t)₂)₂, (marks)₂)).
-/
theorem markedDistribution_eq_iid (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (R : α → PMF β)
    (t : StoppedTape α) (marks : Tape β t.1 × β)
    (hprefix : AllRejected accept t.1 t.2.1) (hlast : accept t.2.2 = true) :
    markedDistribution P accept hp R ⟨t,marks⟩ =
      enrichedPrefixWeight P R t.1 t.2.1 marks.1 * (toPMF P t.2.2 * R t.2.2 marks.2) := by
  rw [markedDistribution_apply, distribution_apply, traceWeight_eq_iid P accept t hprefix hlast,
    ENNReal.ofReal_mul ((tapeDistribution P t.1).nonneg _), enrichedPrefixWeight_eq]
  simp only [toPMF_apply]
  ring

end

end CircuitCompiler.Sampling.Unbounded
