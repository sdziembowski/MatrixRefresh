import Proofs.EfficientSimulaiton.Sampling.ConditionalSamplingCost
import Proofs.Compiler.GateApproximation.MatrixPhase.MarkedRejection
import Proofs.Compiler.Construction.Parameters



/-!
# Nonnegative cost expectations on complete sampler tapes

All sums are in `ℝ≥0∞`: a divergent running time is infinity, never the zero assigned by a nonsummable real-valued `tsum`. Tower identities below connect the actual marked outer loop to the costs of its real inner tapes.
-/
set_option autoImplicit false

set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal

namespace CircuitCompiler.Sampling.Unbounded

open Refresh

noncomputable section

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α a set; P ∈ PMF(α); C ∈ ℝ ≥ 0∞, we have

workExpectation(P, ((x₁ ↦ C))) = C.
-/
@[simp] theorem workExpectation_const {α : Type*} (P : PMF α) (C : ℝ≥0∞) :
    workExpectation P (fun _ => C) = C := by
  rw [workExpectation,ENNReal.tsum_mul_right,PMF.tsum_coe,one_mul]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α a set; a ∈ α; cost ∈ α → ℝ ≥ 0∞, we have

workExpectation(PMF.pure(a), cost) = cost(a).
-/
@[simp] theorem workExpectation_pure {α : Type*} (a : α) (cost : α → ℝ≥0∞) :
    workExpectation (PMF.pure a) cost = cost a := by
  classical
  simp [workExpectation,PMF.pure_apply]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α a set; P ∈ PMF(α); c, d ∈ α → ℝ ≥ 0∞, assume ∀ a, c(a) ≤ d(a). Then

workExpectation(P, c) ≤ workExpectation(P, d) .
-/
theorem workExpectation_mono {α : Type*} (P : PMF α) {c d : α → ℝ≥0∞}
    (h : ∀ a,c a ≤ d a) : workExpectation P c ≤ workExpectation P d :=
  ENNReal.tsum_le_tsum (fun a => mul_le_mul_right (h a) (P a))

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α a set; P ∈ PMF(α); c, d ∈ α → ℝ ≥ 0∞, we have

workExpectation(P, ((a ↦ c(a) + d(a)))) = workExpectation(P, c) + workExpectation(P, d).
-/
theorem workExpectation_add {α : Type*} (P : PMF α) (c d : α → ℝ≥0∞) :
    workExpectation P (fun a => c a+d a) = workExpectation P c+workExpectation P d := by
  simp only [workExpectation,mul_add,ENNReal.tsum_add]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α a set; P ∈ PMF(α); c ∈ α → ℝ ≥ 0∞; C ∈ ℝ ≥ 0∞, we have

workExpectation(P, ((a ↦ c(a) · C))) = workExpectation(P, c) · C.
-/
theorem workExpectation_mul_right {α : Type*} (P : PMF α) (c : α → ℝ≥0∞) (C : ℝ≥0∞) :
    workExpectation P (fun a => c a*C) = workExpectation P c*C := by
  simp only [workExpectation,← mul_assoc,ENNReal.tsum_mul_right]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α,β a set; P ∈ PMF(α); f ∈ α → β; c ∈ β → ℝ ≥ 0∞, we have

workExpectation((f_*P), c) = workExpectation(P, ((a ↦ c(f(a))))).
-/
theorem workExpectation_map {α β : Type*} (P : PMF α) (f : α → β) (c : β → ℝ≥0∞) :
    workExpectation (P.map f) c = workExpectation P (fun a => c (f a)) := by
  classical
  unfold workExpectation
  simp_rw [PMF.map_apply,← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  simp only [ite_mul,zero_mul]
  rw [tsum_ite_eq]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α,β a set; P ∈ PMF(α); Q ∈ α → PMF(β); c ∈ β → ℝ ≥ 0∞, we have

workExpectation(bind(P, Q), c) = workExpectation(P, ((a ↦ workExpectation(Q(a), c)))).
-/
theorem workExpectation_bind {α β : Type*} (P : PMF α) (Q : α → PMF β) (c : β → ℝ≥0∞) :
    workExpectation (P.bind Q) c = workExpectation P (fun a => workExpectation (Q a) c) := by
  unfold workExpectation
  simp_rw [PMF.bind_apply,← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp only [mul_assoc,ENNReal.tsum_mul_left]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Let P be a discrete distribution on I, let Qᵢ be a conditional distribution on Jᵢ, and let c(i,j) ∈ [0,∞]. Sequential sampling satisfies the tower identity for nonnegative expected work:

𝔼_(i ← P, j ← Qᵢ) [c(i,j)] = 𝔼_(i ← P) [ 𝔼_(j ← Qᵢ) [c(i,j)]].

Infinite expectations are allowed, so no integrability assumption is needed.
-/
theorem workExpectation_sigma {I : Type*} {J : I → Type*} (P : PMF I)
    (Q : ∀ i,PMF (J i)) (c : (Σ i,J i) → ℝ≥0∞) :
    workExpectation (sigmaPMF P Q) c =
      workExpectation P (fun i => workExpectation (Q i) (fun j => c ⟨i,j⟩)) := by
  unfold workExpectation
  rw [ENNReal.tsum_sigma']
  simp only [sigmaPMF_apply,mul_assoc,ENNReal.tsum_mul_left]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α,β a set; P ∈ PMF(α); Q ∈ PMF(β); c ∈ α → ℝ ≥ 0∞; d ∈ β → ℝ ≥ 0∞, we have

workExpectation(productPMF(P, Q), ((z ↦ c((z)₁) + d((z)₂)))) = workExpectation(P, c) + workExpectation(Q, d).
-/
theorem workExpectation_product_add {α β : Type*} (P : PMF α) (Q : PMF β)
    (c : α → ℝ≥0∞) (d : β → ℝ≥0∞) :
    workExpectation (productPMF P Q) (fun z => c z.1+d z.2) =
      workExpectation P c+workExpectation Q d := by
  change (∑' z : α × β, (P z.1*Q z.2)*(c z.1+d z.2)) =
    (∑' a, P a*c a)+(∑' b, Q b*d b)
  rw [ENNReal.tsum_prod']
  simp_rw [mul_add,ENNReal.tsum_add]
  congr 1
  · apply tsum_congr
    intro a
    calc
      _ = ∑' b, (P a*c a)*Q b := by apply tsum_congr; intro b; ring
      _ = _ := by rw [ENNReal.tsum_mul_left,Q.tsum_coe,mul_one]
  · simp only [mul_assoc,ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right,P.tsum_coe,one_mul]

/-
Mathematical definition (normal notation): For α a set; cost ∈ α → ℝ ≥ 0∞; t ∈ StoppedTape(α), define

traceWork(cost, t) := prefixWork(cost, (t)₁, ((t)₂)₁) + cost(((t)₂)₂).
-/
def traceWork {α : Type*} (cost : α → ℝ≥0∞) (t : StoppedTape α) : ℝ≥0∞ :=
  prefixWork cost t.1 t.2.1+cost t.2.2

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α a set; cost ∈ α → ℝ ≥ 0∞; C ∈ ℝ ≥ 0∞; t ∈ StoppedTape(α), assume ∀ a, cost(a) ≤ C. Then

traceWork(cost, t) ≤ (t)₁ + 1 · C.
-/
theorem traceWork_le {α : Type*} (cost : α → ℝ≥0∞) (C : ℝ≥0∞)
    (hc : ∀ a,cost a ≤ C) (t : StoppedTape α) :
    traceWork cost t ≤ (t.1+1:ℕ)*C := by
  have h : ∀ (k : ℕ) (p : Tape α k),prefixWork cost k p ≤ (k:ℝ≥0∞)*C := by
    intro k
    induction k with
    | zero => intro p; simp [prefixWork]
    | succ k ih =>
      intro p
      have hp := add_le_add (hc p.1) (ih p.2)
      simpa only [prefixWork,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm] using hp
  simpa only [traceWork,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using add_le_add (h _ _) (hc _)

variable {α β : Type*} [Fintype α]

/-- Exact expected number of proposals under the actual complete tape PMF. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool, assume 0 < acceptance(P, accept). Then

workExpectation(distribution(P, accept), ((t ↦ (t)₁ + 1))) = ENNReal.ofReal((1 / acceptance(P, accept))).
-/
theorem workExpectation_attempts (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) :
    workExpectation (distribution P accept hp) (fun t => (t.1+1:ℕ)) =
      ENNReal.ofReal (1/acceptance P accept) := by
  rw [← workExpectation_map (distribution P accept hp) Sigma.fst (fun k : ℕ => (k+1:ℕ))]
  have h := expected_attempts P accept hp
  rw [← h.tsum_eq,ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) h.summable]
  unfold workExpectation
  apply tsum_congr
  intro k
  rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
  have hk : ENNReal.ofReal ((k:ℝ)+1) = (k:ℝ≥0∞)+1 := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg k) zero_le_one,
      ENNReal.ofReal_natCast,ENNReal.ofReal_one]
  rw [hk]
  simp [mul_comm]

/-- Nonnegative actual trace expectation; finiteness is a theorem. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; cost ∈ α → ℝ ≥ 0∞; C ∈ ℝ ≥ 0∞, assume 0 < acceptance(P, accept); ∀ a, cost(a) ≤ C. Then

workExpectation(distribution(P, accept), traceWork(cost)) ≤ ENNReal.ofReal((1 / acceptance(P, accept))) · C.
-/
theorem workExpectation_trace_le (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (cost : α → ℝ≥0∞) (C : ℝ≥0∞)
    (hc : ∀ a,cost a ≤ C) :
    workExpectation (distribution P accept hp) (traceWork cost) ≤
      ENNReal.ofReal (1/acceptance P accept)*C := by
  calc
    _ ≤ workExpectation (distribution P accept hp) (fun t => (t.1+1:ℕ)*C) :=
      workExpectation_mono _ (traceWork_le cost C hc)
    _ = _ := by rw [workExpectation_mul_right,workExpectation_attempts]

/-- Marks contribute their actual individual costs on all rejected attempts. -/
/- Mathematical definition (normal notation): The work of a marked rejected prefix is ∑ᵢ c(aᵢ,bᵢ), charging the actual proposal and private mark at each position. -/
def markedPrefixWork (cost : α → β → ℝ≥0∞) :
    (k : ℕ) → Tape α k → Tape β k → ℝ≥0∞
  | 0,_,_ => 0
  | k+1,a,b => cost a.1 b.1+markedPrefixWork cost k a.2 b.2

/-
Mathematical definition (normal notation): For cost ∈ α → β → ℝ ≥ 0∞; t ∈ MarkedTape(α, β), define

markedTraceWork(cost, t) := markedPrefixWork(cost, ((t)₁)₁, (((t)₁)₂)₁, ((t)₂)₁) + cost((((t)₁)₂)₂, ((t)₂)₂).
-/
def markedTraceWork (cost : α → β → ℝ≥0∞) (t : MarkedTape α β) : ℝ≥0∞ :=
  markedPrefixWork cost t.1.1 t.1.2.1 t.2.1+cost t.1.2.2 t.2.2

omit [Fintype α] in
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For R ∈ α → PMF(β); cost ∈ α → β → ℝ ≥ 0∞; k ∈ ℕ; a ∈ Tape(α, k), we have

workExpectation(prefixMarks(R, k, a), markedPrefixWork(cost, k, a)) = prefixWork(((x ↦ workExpectation(R(x), cost(x)))), k, a).
-/
theorem prefixMarks_work (R : α → PMF β) (cost : α → β → ℝ≥0∞)
    (k : ℕ) (a : Tape α k) :
    workExpectation (prefixMarks R k a) (markedPrefixWork cost k a) =
      prefixWork (fun x => workExpectation (R x) (cost x)) k a := by
  induction k with
  | zero => simp [prefixWork,markedPrefixWork,workExpectation_const]
  | succ k ih =>
    change workExpectation (productPMF _ _) (fun b => _+_) = _
    rw [workExpectation_product_add,ih]
    rfl

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For R ∈ α → PMF(β); cost ∈ α → β → ℝ ≥ 0∞; t ∈ StoppedTape(α), we have

workExpectation(traceMarks(R, t), ((marks ↦ markedTraceWork(cost, (t, marks))))) = traceWork(((a ↦ workExpectation(R(a), cost(a)))), t).
-/
theorem traceMarks_work (R : α → PMF β) (cost : α → β → ℝ≥0∞) (t : StoppedTape α) :
    workExpectation (traceMarks R t) (fun marks => markedTraceWork cost ⟨t,marks⟩) =
      traceWork (fun a => workExpectation (R a) (cost a)) t := by
  change workExpectation (productPMF _ _) (fun marks => _+_) = _
  dsimp only
  rw [workExpectation_product_add,prefixMarks_work]
  rfl

/-- Tower/Fubini identity on the literal complete marked tape. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; R ∈ α → PMF(β); cost ∈ α → β → ℝ ≥ 0∞, assume 0 < acceptance(P, accept). Then

workExpectation(markedDistribution(P, accept, R), markedTraceWork(cost)) = workExpectation(distribution(P, accept), traceWork(((a ↦ workExpectation(R(a), cost(a)))))).
-/
theorem markedDistribution_work (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (R : α → PMF β) (cost : α → β → ℝ≥0∞) :
    workExpectation (markedDistribution P accept hp R) (markedTraceWork cost) =
      workExpectation (distribution P accept hp) (traceWork (fun a => workExpectation (R a) (cost a))) := by
  rw [markedDistribution,workExpectation_sigma]
  simp_rw [traceMarks_work]

/-- A uniform conditional inner-work bound lifts through all outer retries. This statement includes the literal private marks at every failed attempt. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; R ∈ α → PMF(β); cost ∈ α → β → ℝ ≥ 0∞; C ∈ ℝ ≥ 0∞, assume 0 < acceptance(P, accept); ∀ a, workExpectation(R(a), cost(a)) ≤ C. Then

workExpectation(markedDistribution(P, accept, R), markedTraceWork(cost)) ≤ ENNReal.ofReal((1 / acceptance(P, accept))) · C.
-/
theorem markedDistribution_work_le (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (R : α → PMF β) (cost : α → β → ℝ≥0∞)
    (C : ℝ≥0∞) (hC : ∀ a,workExpectation (R a) (cost a) ≤ C) :
    workExpectation (markedDistribution P accept hp R) (markedTraceWork cost) ≤
      ENNReal.ofReal (1/acceptance P accept)*C := by
  rw [markedDistribution_work]
  exact workExpectation_trace_le P accept hp _ C hC

/-- Conditioning on the returned value leaves the same geometric prefix count. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool, assume 0 < acceptance(P, accept). Then

workExpectation(prefixDistribution(P, accept), ((t ↦ (t)₁ + 1))) = ENNReal.ofReal((1 / acceptance(P, accept))).
-/
theorem prefixDistribution_expected_attempts (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) :
    workExpectation (prefixDistribution P accept hp) (fun t => (t.1+1:ℕ)) =
      ENNReal.ofReal (1/acceptance P accept) := by
  have h := workExpectation_attempts P accept hp
  rw [distribution_eq_prefix_bind,workExpectation_bind] at h
  simp_rw [workExpectation_map,joinPrefix,workExpectation_const] at h
  exact h

/-- Actual rejected-prefix expectation after fixing the final accepted proposal. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; cost ∈ α → ℝ ≥ 0∞; C ∈ ℝ ≥ 0∞; a ∈ α, assume 0 < acceptance(P, accept); ∀ a, cost(a) ≤ C. Then

workExpectation(prefixDistribution(P, accept), ((p ↦ traceWork(cost, joinPrefix(p, a))))) ≤ ENNReal.ofReal((1 / acceptance(P, accept))) · C.
-/
theorem prefixDistribution_traceWork_le (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (cost : α → ℝ≥0∞) (C : ℝ≥0∞)
    (hc : ∀ a,cost a ≤ C) (a : α) :
    workExpectation (prefixDistribution P accept hp) (fun p => traceWork cost (joinPrefix p a)) ≤
      ENNReal.ofReal (1/acceptance P accept)*C := by
  calc
    _ ≤ workExpectation (prefixDistribution P accept hp) (fun p => (p.1+1:ℕ)*C) :=
      workExpectation_mono _ (fun p => traceWork_le cost C hc (joinPrefix p a))
    _ = _ := by rw [workExpectation_mul_right,prefixDistribution_expected_attempts]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For γ a set; cost ∈ γ → ℕ; k ∈ ℕ; t ∈ Tape(γ, k), we have

prefixNatWork(cost, k, t) = prefixWork(((a ↦ cost(a))), k, t).
-/
@[simp] theorem prefixNatWork_cast {γ : Type*} (cost : γ → ℕ) (k : ℕ) (t : Tape γ k) :
    (prefixNatWork cost k t : ℝ≥0∞) = prefixWork (fun a => (cost a : ℝ≥0∞)) k t := by
  induction k with
  | zero => simp only [prefixNatWork,prefixWork,Nat.cast_zero]
  | succ k ih => simp only [prefixNatWork,prefixWork,Nat.cast_add,ih]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For γ a set; cost ∈ γ → ℕ; t ∈ StoppedTape(γ), we have

traceNatWork(cost, t) = traceWork(((a ↦ cost(a))), t).
-/
@[simp] theorem traceNatWork_cast {γ : Type*} (cost : γ → ℕ) (t : StoppedTape γ) :
    (traceNatWork cost t : ℝ≥0∞) = traceWork (fun a => (cost a : ℝ≥0∞)) t := by
  simp only [traceNatWork,traceWork,Nat.cast_add,prefixNatWork_cast]

end

end CircuitCompiler.Sampling.Unbounded
