import Proofs.Compiler.GateApproximation.MatrixPhase.ConditionedExecution
import Proofs.Compiler.GateApproximation.MatrixPhase.GateAnswerProbabilities
import Proofs.Compiler.GateApproximation.Shortening.ShorteningCoupling



/-!
# The actual tensor, shared-matrix, and shortening gate

The matrix answer is sampled before its tape is erased. The continuation retains that answer, both old operand encodings, and the actual long encoding, but receives no matrix argument. Exact conditioning followed by the proved shortening coupling gives a fresh canonical short output, including all ordinary-branch and fallback leakage.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

open scoped BigOperators Classical

namespace CircuitCompiler

open Refresh Shortening TableAnalysis

noncomputable section

variable {F A B : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype A] [Fintype B]

/-- Reindex a fiber along the exact long-dimension equality. -/
/-
Mathematical definition (normal notation): For m, k ∈ ℕ; z ∈ F, assume m = k. define

fiberDimensionEquiv(z) := Equiv.cast(congrArg(((d ↦ Fiber(F, d, z))))).
-/
def fiberDimensionEquiv {m k : ℕ} (h : m = k) (z : F) : Fiber F m z ≃ Fiber F k z :=
  Equiv.cast (congrArg (fun d => Fiber F d z) h)

/- Mathematical definition (normal notation): Tensor the two operand encodings, apply the chosen invertible refresh matrix, and identify the long dimension n² with n+t through the supplied equality. The resulting long pair encodes the product of the operand secrets. -/
def longGateValue {n t : ℕ} (hdim : n * n = n + t) (a b : State F n)
    (M : Refresh.«GL» F (n * n)) : Fiber F (n + t) (secret a * secret b) :=
  fiberDimensionEquiv hdim _ (refreshInFiber (tensorFiber a b) M)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; a, b ∈ State(F, n), assume n · n = n + t; Fiber(F, (n + t), (secret(a) · secret(b))) ≠ ∅. Then

(longGateValue(a, b)_*𝒰_(GL_(n · n)(F))) = 𝒰_(Fiber(F, (n + t), (secret(a) · secret(b)))).
-/
theorem longGateValue_uniform {n t : ℕ} (hdim : n * n = n + t) (a b : State F n)
    [Nonempty (Fiber F (n + t) (secret a * secret b))] :
    (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n * n))).map (longGateValue hdim a b) =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n + t) (secret a * secret b))) := by
  letI : Nonempty (Fiber F (n * n) (secret a * secret b)) := ⟨tensorFiber a b⟩
  change (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n * n))).map
    (fiberDimensionEquiv hdim _ ∘ refreshInFiber (tensorFiber a b)) = _
  rw [← FiniteDistribution.map_map, refreshedTensor_uniform_fiber]
  ext u
  rw [FiniteDistribution.map_equiv_weight]
  simp only [FiniteDistribution.uniform]
  rw [Fintype.card_congr (fiberDimensionEquiv hdim (secret a * secret b))]

/-- Conditional matrix-answer distribution given the actual typed long encoding. -/
/- Mathematical definition (normal notation): For fixed operand encodings and a proposed long output encoding, condition the uniform refresh matrix on producing that output and average the actual matrix answer over this conditional distribution. The supplied dimension equality only reindexes the same long encoding. -/
def typedMatrixAnswerDistribution {n t : ℕ} (hdim : n * n = n + t)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (a b : State F n) (u : Fiber F (n + t) (secret a * secret b)) : FiniteDistribution A :=
  (conditional (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n * n)))
    (longGateValue hdim a b) u).bind (matrixAnswer p a b)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Ω,X,Y a set; P ∈ 𝒟(Ω); v ∈ Ω → X; e ∈ X → Y; x ∈ X, assume Ω is finite; X is finite; Y is finite; e is injective. Then

conditional(P, ((ω ↦ e(v(ω)))), e(x)) = conditional(P, v, x).
-/
theorem conditional_comp_injective {Ω X Y : Type*} [Fintype Ω] [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (P : FiniteDistribution Ω) (v : Ω → X)
    (e : X → Y) (he : Function.Injective e) (x : X) :
    conditional P (fun ω => e (v ω)) (e x) = conditional P v x := by
  simp only [conditional, he.eq_iff]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); a, b ∈ State(F, n); u ∈ Fiber(F, (n + t), (secret(a) · secret(b))), assume n · n = n + t. Then

typedMatrixAnswerDistribution(p, a, b, u) = matrixAnswerDistribution(p, a, b, (fiberDimensionEquiv(x))⁻¹(u)).
-/
theorem typedMatrixAnswerDistribution_eq_matrixAnswerDistribution {n t : ℕ} (hdim : n * n = n + t)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (a b : State F n) (u : Fiber F (n + t) (secret a * secret b)) :
    typedMatrixAnswerDistribution hdim p a b u =
      matrixAnswerDistribution p a b ((fiberDimensionEquiv hdim _).symm u).val := by
  let e := fiberDimensionEquiv hdim (secret a * secret b)
  have he := conditional_comp_injective
    (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n * n))) (refreshInFiber (tensorFiber a b))
    e e.injective (e.symm u)
  rw [e.apply_symm_apply] at he
  have hv := conditional_comp_injective
    (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n * n))) (refreshInFiber (tensorFiber a b))
    Subtype.val (Subtype.val_injective) (e.symm u)
  exact congrArg (fun Q => Q.bind (matrixAnswer p a b)) (he.trans hv.symm)

/-- Extend the genuine conditional distribution to auxiliary zero-right points. Its arbitrary value there is a normalized real matrix-answer distribution. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); a, b ∈ State(F, n); u ∈ Auxiliary(F, (n + t), (secret(a) · secret(b))), assume n · n = n + t. define

auxiliaryMatrixAnswerDistribution(p, a, b, u) := { typedMatrixAnswerDistribution(p, a, b, (((u)₁, ((u)₂, h)), u.2.property)) if (u)₂ ≠ 0,; matrixAnswer(p, a, b, 1) otherwise }.
-/
def auxiliaryMatrixAnswerDistribution {n t : ℕ} (hdim : n * n = n + t)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (a b : State F n) (u : Auxiliary F (n + t) (secret a * secret b)) : FiniteDistribution A :=
  if h : u.2.val ≠ 0 then
    typedMatrixAnswerDistribution hdim p a b ⟨⟨u.1, ⟨u.2.val, h⟩⟩, u.2.property⟩
  else matrixAnswer p a b 1

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); a, b ∈ State(F, n); u ∈ Fiber(F, (n + t), (secret(a) · secret(b))), assume n · n = n + t. Then

auxiliaryMatrixAnswerDistribution(p, a, b, actualEmbedding((secret(a) · secret(b)), u)) = typedMatrixAnswerDistribution(p, a, b, u).
-/
@[simp] theorem auxiliaryMatrixAnswerDistribution_actual {n t : ℕ} (hdim : n * n = n + t)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (a b : State F n) (u : Fiber F (n + t) (secret a * secret b)) :
    auxiliaryMatrixAnswerDistribution hdim p a b (actualEmbedding (secret a * secret b) u) =
      typedMatrixAnswerDistribution hdim p a b u := by
  simp [auxiliaryMatrixAnswerDistribution, actualEmbedding, u.val.R.property]

/-- Continuation after matrix erasure. The earlier matrix answer is preserved as part of the complete answer, including in the correct fallback branch. -/
/- Mathematical definition (normal notation): After the matrix answer α, run the shortening step. If it returns an encoding v, sample the shortening answer β from its specified distribution and return (v,(α,β)). Otherwise sample the caller's correct fallback output and answer. In both cases the matrix answer is retained and the output encodes c+ε z. -/
def gateContinuation {n t : ℕ} (c ε z : F)
    (leak : Auxiliary F (n + t) z → A → FiniteDistribution B)
    (fallback : Auxiliary F (n + t) z → A → FiniteDistribution (Fiber F n (c + ε * z) × B))
    (u : Auxiliary F (n + t) z) (α : A) : FiniteDistribution (Fiber F n (c + ε * z) × (A × B)) :=
  match run c ε z u with
  | some v => (leak u α).map (fun β => (v, (α, β)))
  | none => (fallback u α).map (fun vβ => (vβ.1, (α, vβ.2)))

/-- The complete actual gate executes tensor refresh, observes the real shared-matrix answer, erases the matrix, and executes shortening once. -/
/- Mathematical definition (normal notation): Sample the tensor refresh matrix uniformly, sample its actual matrix-phase answer, erase the matrix, and execute the specified shortening continuation once. Return the short encoding and both phase answers; the output secret is c+ε s₁s₂. -/
def fullGateExecution {n t : ℕ} (hdim : n * n = n + t) (c ε : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (a b : State F n)
    (leak : Auxiliary F (n + t) (secret a * secret b) → A → FiniteDistribution B)
    (fallback : Auxiliary F (n + t) (secret a * secret b) → A →
      FiniteDistribution (Fiber F n (c + ε * (secret a * secret b)) × B)) :
    FiniteDistribution (Fiber F n (c + ε * (secret a * secret b)) × (A × B)) :=
  (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n * n))).bind (fun M =>
    (matrixAnswer p a b M).bind (gateContinuation c ε (secret a * secret b) leak fallback
      (actualEmbedding _ (longGateValue hdim a b M))))

/-
Mathematical definition (normal notation): For n, t ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); a, b ∈ State(F, n); leak ∈ Auxiliary(F, (n + t), (secret(a) · secret(b))) → A → 𝒟(B); u ∈ Auxiliary(F, (n + t), (secret(a) · secret(b))), assume n · n = n + t. define

fullGateAnswer(p, a, b, leak, u) := joint(auxiliaryMatrixAnswerDistribution(p, a, b, u))(leak(u)).
-/
def fullGateAnswer {n t : ℕ} (hdim : n * n = n + t)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (a b : State F n)
    (leak : Auxiliary F (n + t) (secret a * secret b) → A → FiniteDistribution B)
    (u : Auxiliary F (n + t) (secret a * secret b)) : FiniteDistribution (A × B) :=
  (auxiliaryMatrixAnswerDistribution hdim p a b u).joint (leak u)

/-
Mathematical definition (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); a, b ∈ State(F, n); fallback ∈ Auxiliary(F, (n + t), (secret(a) · secret(b))) → A → 𝒟((Fiber(F, n, (c + ε · (secret(a) · secret(b)))) × B)); u ∈ Auxiliary(F, (n + t), (secret(a) · secret(b))), assume n · n = n + t. define

fullGateFallback(c, ε, p, a, b, fallback, u) := bind(auxiliaryMatrixAnswerDistribution(p, a, b, u), ((α ↦ (((vβ ↦ ((vβ)₁, (α, (vβ)₂))))_*fallback(u, α))))).
-/
def fullGateFallback {n t : ℕ} (hdim : n * n = n + t) (c ε : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (a b : State F n)
    (fallback : Auxiliary F (n + t) (secret a * secret b) → A →
      FiniteDistribution (Fiber F n (c + ε * (secret a * secret b)) × B))
    (u : Auxiliary F (n + t) (secret a * secret b)) :
    FiniteDistribution (Fiber F n (c + ε * (secret a * secret b)) × (A × B)) :=
  (auxiliaryMatrixAnswerDistribution hdim p a b u).bind (fun α =>
    (fallback u α).map (fun vβ => (vβ.1, (α, vβ.2))))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); a, b ∈ State(F, n); leak ∈ Auxiliary(F, (n + t), (secret(a) · secret(b))) → A → 𝒟(B); fallback ∈ Auxiliary(F, (n + t), (secret(a) · secret(b))) → A → 𝒟((Fiber(F, n, (c + ε · (secret(a) · secret(b)))) × B)); u ∈ Auxiliary(F, (n + t), (secret(a) · secret(b))), assume n · n = n + t. Then

bind(auxiliaryMatrixAnswerDistribution(p, a, b, u), gateContinuation(c, ε, (secret(a) · secret(b)), leak, fallback, u)) = observedRun(c, ε, (secret(a) · secret(b)), fullGateAnswer(p, a, b, leak), fullGateFallback(c, ε, p, a, b, fallback), u).
-/
theorem continuation_eq_observedRun {n t : ℕ} (hdim : n * n = n + t) (c ε : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (a b : State F n)
    (leak : Auxiliary F (n + t) (secret a * secret b) → A → FiniteDistribution B)
    (fallback : Auxiliary F (n + t) (secret a * secret b) → A →
      FiniteDistribution (Fiber F n (c + ε * (secret a * secret b)) × B))
    (u : Auxiliary F (n + t) (secret a * secret b)) :
    (auxiliaryMatrixAnswerDistribution hdim p a b u).bind
      (gateContinuation c ε (secret a * secret b) leak fallback u) =
    observedRun c ε (secret a * secret b) (fullGateAnswer hdim p a b leak)
      (fullGateFallback hdim c ε p a b fallback) u := by
  unfold gateContinuation observedRun
  cases h : run c ε (secret a * secret b) u with
  | none => rfl
  | some v =>
    ext w
    simp only [fullGateAnswer, FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.joint,
      Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- Exact disintegration of the actual complete gate, before applying any statistical estimate. Conditioning preserves the earlier matrix answer and every allowed continuation after erasure. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); a, b ∈ State(F, n); leak ∈ Auxiliary(F, (n + t), (secret(a) · secret(b))) → A → 𝒟(B); fallback ∈ Auxiliary(F, (n + t), (secret(a) · secret(b))) → A → 𝒟((Fiber(F, n, (c + ε · (secret(a) · secret(b)))) × B)), assume n · n = n + t; Fiber(F, (n + t), (secret(a) · secret(b))) ≠ ∅. Then

fullGateExecution(c, ε, p, a, b, leak, fallback) = bind((actualEmbedding((secret(a) · secret(b)))_*𝒰_(Fiber(F, (n + t), (secret(a) · secret(b))))), observedRun(c, ε, (secret(a) · secret(b)), fullGateAnswer(p, a, b, leak), fullGateFallback(c, ε, p, a, b, fallback))).
-/
theorem fullGateExecution_eq_observed {n t : ℕ} (hdim : n * n = n + t) (c ε : F)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (a b : State F n) [Nonempty (Fiber F (n + t) (secret a * secret b))]
    (leak : Auxiliary F (n + t) (secret a * secret b) → A → FiniteDistribution B)
    (fallback : Auxiliary F (n + t) (secret a * secret b) → A →
      FiniteDistribution (Fiber F n (c + ε * (secret a * secret b)) × B)) :
    fullGateExecution hdim c ε p a b leak fallback =
      (((FiniteDistribution.uniform : FiniteDistribution (Fiber F (n + t) (secret a * secret b))).map
        (actualEmbedding (secret a * secret b))).bind
          (observedRun c ε (secret a * secret b) (fullGateAnswer hdim p a b leak)
            (fullGateFallback hdim c ε p a b fallback))) := by
  unfold fullGateExecution
  rw [conditional_execution _ (longGateValue hdim a b) (matrixAnswer p a b)
    (fun u => gateContinuation c ε (secret a * secret b) leak fallback
      (actualEmbedding _ u)), longGateValue_uniform, bind_after_map]
  apply congrArg (FiniteDistribution.bind (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n + t) (secret a * secret b))))
  funext u
  rw [← continuation_eq_observedRun, auxiliaryMatrixAnswerDistribution_actual]
  rfl

/-- The canonical gate samples one fresh short output and then its complete conditional leakage distribution. The distribution retains the old operand encodings. -/
/- Mathematical definition (normal notation): For fixed operand encodings of secrets s₁,s₂, sample the short output uniformly from μ_(c+ε s₁s₂), then sample the complete matrix and shortening answer from the corresponding accepted conditional answer distribution. The operand encodings remain parameters of that distribution. -/
def fullGateCanonical {n t : ℕ} (hn : 2 ≤ n) (hdim : n * n = n + t)
    (c ε : F) (hε : ε ≠ 0)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (a b : State F n)
    (leak : Auxiliary F (n + t) (secret a * secret b) → A → FiniteDistribution B) :
    FiniteDistribution (Fiber F n (c + ε * (secret a * secret b)) × (A × B)) := by
  letI := encoding_fiber_nonempty hn (c + ε * (secret a * secret b))
  letI := accepted_nonempty (n := n) (t := t) c ε (secret a * secret b) hε
  exact (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (c + ε * (secret a * secret b)))).joint
    (acceptedAnswerDistribution c ε (secret a * secret b) (fullGateAnswer hdim p a b leak))

/-- A normalized common-carrier version of the actual canonical answer distribution. Its off-fiber value is irrelevant to the uniform output distribution. -/
/- Mathematical definition (normal notation): Extend the canonical conditional answer distribution to every proposed output encoding u. If u encodes c+ε s₁s₂, use its accepted conditional answer distribution. Otherwise use the unconditional answer marginal of the canonical gate. Thus every input gives a normalized answer distribution; the off-fiber branch is never sampled by the canonical output distribution. -/
def ambientGateAnswerDistribution {n t : ℕ} (hn : 2 ≤ n) (hdim : n * n = n + t)
    (c ε : F) (hε : ε ≠ 0)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (a b : State F n)
    (leak : Auxiliary F (n + t) (secret a * secret b) → A → FiniteDistribution B)
    (u : State F n) : FiniteDistribution (A × B) := by
  letI := encoding_fiber_nonempty hn (c + ε * (secret a * secret b))
  letI := accepted_nonempty (n := n) (t := t) c ε (secret a * secret b) hε
  exact if hu : secret u = c + ε * (secret a * secret b) then
    acceptedAnswerDistribution c ε (secret a * secret b) (fullGateAnswer hdim p a b leak) ⟨u, hu⟩
  else (fullGateCanonical hn hdim c ε hε p a b leak).map Prod.snd

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); a, b ∈ State(F, n); leak ∈ Auxiliary(F, (n + t), (secret(a) · secret(b))) → A → 𝒟(B); u ∈ Fiber(F, n, (c + ε · (secret(a) · secret(b)))), assume 2 ≤ n; n · n = n + t; ε ≠ 0; Accepted(F, n, t, c, ε, (secret(a) · secret(b))) ≠ ∅. Then

ambientGateAnswerDistribution(c, ε, p, a, b, leak, u) = acceptedAnswerDistribution(c, ε, (secret(a) · secret(b)), fullGateAnswer(p, a, b, leak), u).
-/
@[simp] theorem ambientGateAnswerDistribution_fiber {n t : ℕ} (hn : 2 ≤ n) (hdim : n * n = n + t)
    (c ε : F) (hε : ε ≠ 0)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (a b : State F n)
    (leak : Auxiliary F (n + t) (secret a * secret b) → A → FiniteDistribution B)
    [Nonempty (Accepted F n t c ε (secret a * secret b))]
    (u : Fiber F n (c + ε * (secret a * secret b))) :
    ambientGateAnswerDistribution hn hdim c ε hε p a b leak u.val =
      acceptedAnswerDistribution c ε (secret a * secret b) (fullGateAnswer hdim p a b leak) u := by
  simp [ambientGateAnswerDistribution, u.property]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X,Y,Z a set; P ∈ 𝒟(X); f ∈ X → Y; K ∈ Y → 𝒟(Z), assume X is finite; Y is finite; Z is finite. Then

(((xz ↦ (f((xz)₁), (xz)₂)))_*P.joint(((x ↦ K(f(x)))))) = joint((f_*P))(K).
-/
theorem map_joint_fst {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (P : FiniteDistribution X) (f : X → Y) (K : Y → FiniteDistribution Z) :
    (P.joint (fun x => K (f x))).map (fun xz => (f xz.1, xz.2)) =
      (P.map f).joint K := by
  classical
  ext ⟨y, z⟩
  simp only [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.joint, FiniteDistribution.pure,
    Fintype.sum_prod_type, Prod.mk.injEq, ite_and, mul_ite, mul_one, mul_zero,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : f x = y
  · simp [h, eq_comm]
  · simp [h, Ne.symm h]

/-- The exact ambient canonical transition used by the circuit runner. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); a, b ∈ State(F, n); leak ∈ Auxiliary(F, (n + t), (secret(a) · secret(b))) → A → 𝒟(B), assume 2 ≤ n; n · n = n + t; ε ≠ 0. Then

(((v ↦ ((v)₁, (v)₂)))_*fullGateCanonical(c, ε, p, a, b, leak)) = joint(μ_(c + ε · (secret(a) · secret(b))))(ambientGateAnswerDistribution(c, ε, p, a, b, leak)).
-/
theorem fullGateCanonical_ambient {n t : ℕ} (hn : 2 ≤ n) (hdim : n * n = n + t)
    (c ε : F) (hε : ε ≠ 0)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (a b : State F n)
    (leak : Auxiliary F (n + t) (secret a * secret b) → A → FiniteDistribution B) :
    (fullGateCanonical hn hdim c ε hε p a b leak).map (fun v => (v.1.val, v.2)) =
      (mu F n hn (c + ε * (secret a * secret b))).joint
        (ambientGateAnswerDistribution hn hdim c ε hε p a b leak) := by
  letI := encoding_fiber_nonempty hn (c + ε * (secret a * secret b))
  letI := accepted_nonempty (n := n) (t := t) c ε (secret a * secret b) hε
  have h := map_joint_fst (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (c + ε * (secret a * secret b))))
    Subtype.val (ambientGateAnswerDistribution hn hdim c ε hε p a b leak)
  simpa only [fullGateCanonical, mu, ambientGateAnswerDistribution_fiber] using h

/-- The complete concrete gate, including its real shared-matrix leakage and correct fallback, has the local canonical-coupling error used in composition. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); a, b ∈ State(F, n); leak ∈ Auxiliary(F, (n + t), (secret(a) · secret(b))) → A → 𝒟(B); fallback ∈ Auxiliary(F, (n + t), (secret(a) · secret(b))) → A → 𝒟((Fiber(F, n, (c + ε · (secret(a) · secret(b)))) × B)), assume 2 ≤ n; n · n = n + t; ε ≠ 0. Then

δ(fullGateExecution(c, ε, p, a, b, leak, fallback), fullGateCanonical(c, ε, p, a, b, leak)) ≤ 1 / (|F|)^(n + t − 1) + (|F| + 1) / (|F|)ⁿ.
-/
theorem fullGate_canonical_distance {n t : ℕ} (hn : 2 ≤ n) (hdim : n * n = n + t)
    (c ε : F) (hε : ε ≠ 0)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (a b : State F n)
    (leak : Auxiliary F (n + t) (secret a * secret b) → A → FiniteDistribution B)
    (fallback : Auxiliary F (n + t) (secret a * secret b) → A →
      FiniteDistribution (Fiber F n (c + ε * (secret a * secret b)) × B)) :
    statisticalDistance (fullGateExecution hdim c ε p a b leak fallback)
      (fullGateCanonical hn hdim c ε hε p a b leak) ≤
      1 / (fieldCard F : ℝ) ^ (n + t - 1) + ((fieldCard F : ℝ) + 1) / (fieldCard F : ℝ) ^ n := by
  letI := encoding_fiber_nonempty hn (c + ε * (secret a * secret b))
  letI := accepted_nonempty (n := n) (t := t) c ε (secret a * secret b) hε
  letI := encoding_fiber_nonempty (by omega : 2 ≤ n + t) (secret a * secret b)
  letI := auxiliary_nonempty (m := n + t) (secret a * secret b)
  rw [fullGateExecution_eq_observed]
  exact observed_actual_canonical_distance hn c ε (secret a * secret b) hε
    (fullGateAnswer hdim p a b leak) (fullGateFallback hdim c ε p a b fallback)

/-- The same local coupling on ambient states, suitable for the topological circuit runner whose output value varies with the old operand states. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); a, b ∈ State(F, n); leak ∈ Auxiliary(F, (n + t), (secret(a) · secret(b))) → A → 𝒟(B); fallback ∈ Auxiliary(F, (n + t), (secret(a) · secret(b))) → A → 𝒟((Fiber(F, n, (c + ε · (secret(a) · secret(b)))) × B)), assume 2 ≤ n; n · n = n + t; ε ≠ 0. Then

δ((((v ↦ ((v)₁, (v)₂)))_*fullGateExecution(c, ε, p, a, b, leak, fallback)), (((v ↦ ((v)₁, (v)₂)))_*fullGateCanonical(c, ε, p, a, b, leak))) ≤ 1 / (|F|)^(n + t − 1) + (|F| + 1) / (|F|)ⁿ.
-/
theorem fullGate_ambient_distance {n t : ℕ} (hn : 2 ≤ n) (hdim : n * n = n + t)
    (c ε : F) (hε : ε ≠ 0)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (a b : State F n)
    (leak : Auxiliary F (n + t) (secret a * secret b) → A → FiniteDistribution B)
    (fallback : Auxiliary F (n + t) (secret a * secret b) → A →
      FiniteDistribution (Fiber F n (c + ε * (secret a * secret b)) × B)) :
    statisticalDistance
      ((fullGateExecution hdim c ε p a b leak fallback).map (fun v => (v.1.val, v.2)))
      ((fullGateCanonical hn hdim c ε hε p a b leak).map (fun v => (v.1.val, v.2))) ≤
      1 / (fieldCard F : ℝ) ^ (n + t - 1) + ((fieldCard F : ℝ) + 1) / (fieldCard F : ℝ) ^ n :=
  (statisticalDistance_map_le _ _ _).trans
    (fullGate_canonical_distance hn hdim c ε hε p a b leak fallback)

/-- Arbitrary old-state distributions retain both operand encodings in the coupling. The same local cost applies without assuming those old states are independent, even after earlier leakage. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; c, ε ∈ F; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), A); Pold ∈ 𝒟((State(F, n) × State(F, n))); leak ∈ ∏_(a(b) ∈ State(F, n)) Auxiliary(F, (n + t), (secret(a) · secret(b))) → A → 𝒟(B); fallback ∈ ∏_(a(b) ∈ State(F, n)) Auxiliary(F, (n + t), (secret(a) · secret(b))) → A → 𝒟((Fiber(F, n, (c + ε · (secret(a) · secret(b)))) × B)), assume 2 ≤ n; n · n = n + t; ε ≠ 0. Then

δ(Pold.joint(((ab ↦ (((v ↦ ((v)₁, (v)₂)))_*fullGateExecution(c, ε, p, (ab)₁, (ab)₂, leak((ab)₁, (ab)₂), fallback((ab)₁, (ab)₂)))))), Pold.joint(((ab ↦ (((v ↦ ((v)₁, (v)₂)))_*fullGateCanonical(c, ε, p, (ab)₁, (ab)₂, leak((ab)₁, (ab)₂))))))) ≤ 1 / (|F|)^(n + t − 1) + (|F| + 1) / (|F|)ⁿ.
-/
theorem fullGate_retained_distance {n t : ℕ} (hn : 2 ≤ n) (hdim : n * n = n + t)
    (c ε : F) (hε : ε ≠ 0)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n * n)) A)
    (Pold : FiniteDistribution (State F n × State F n))
    (leak : (a b : State F n) → Auxiliary F (n + t) (secret a * secret b) → A → FiniteDistribution B)
    (fallback : (a b : State F n) → Auxiliary F (n + t) (secret a * secret b) → A →
      FiniteDistribution (Fiber F n (c + ε * (secret a * secret b)) × B)) :
    statisticalDistance
      (Pold.joint (fun ab => (fullGateExecution hdim c ε p ab.1 ab.2
        (leak ab.1 ab.2) (fallback ab.1 ab.2)).map (fun v => (v.1.val, v.2))))
      (Pold.joint (fun ab => (fullGateCanonical hn hdim c ε hε p ab.1 ab.2
        (leak ab.1 ab.2)).map (fun v => (v.1.val, v.2)))) ≤
      1 / (fieldCard F : ℝ) ^ (n + t - 1) + ((fieldCard F : ℝ) + 1) / (fieldCard F : ℝ) ^ n := by
  let real := fun ab : State F n × State F n => (fullGateExecution hdim c ε p ab.1 ab.2
    (leak ab.1 ab.2) (fallback ab.1 ab.2)).map (fun v => (v.1.val, v.2))
  let canon := fun ab : State F n × State F n => (fullGateCanonical hn hdim c ε hε p ab.1 ab.2
    (leak ab.1 ab.2)).map (fun v => (v.1.val, v.2))
  have hjoint : statisticalDistance (Pold.joint real) (Pold.joint canon) =
      Pold.expect (fun ab => statisticalDistance (real ab) (canon ab)) :=
    statisticalDistance_joint_mixture Pold real canon
  exact hjoint.le.trans
    (Pold.expect_le_const (fun ab => fullGate_ambient_distance hn hdim c ε hε p ab.1 ab.2
      (leak ab.1 ab.2) (fallback ab.1 ab.2)))

end

end CircuitCompiler
