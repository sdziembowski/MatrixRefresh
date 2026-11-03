import Proofs.Compiler.LocalComparisons.Framework.Composition



/-!
# Guard isolation with the signed factors kept inside the patch average

An adaptive execution is split into outer probability factors and local signed factors.  All local factors are moved to the terminal patch error; the latter is bounded only after averaging over the original patch distribution. Consequently no pointwise bound on a fine approximation is needed here.
-/

set_option autoImplicit false

set_option maxHeartbeats 1200000

open scoped BigOperators

namespace CircuitCompiler.AveragedEnergyComparison

open Refresh Composition

/-- An adaptive factorization of every history into outer factors and local factors.  Either family may depend on all previous answers. -/
/- Mathematical definition (normal notation): An adaptive split process is a finite-depth answer tree. At each internal node, the next-answer weight is a product o(x,z) · l(x,z) of an outer factor and a local factor; the continuation may depend on z. At a leaf, a final real-valued weight is applied to the local state x. -/
inductive SplitProcess (A X : Type*) : ℕ → Type _
  | stop (leaf : X → ℝ) : SplitProcess A X 0
  | query {n : ℕ} (outer innerFactor : X → A → ℝ)
      (next : A → SplitProcess A X n) : SplitProcess A X (n + 1)

namespace SplitProcess

variable {A X : Type*} [Fintype A] [Fintype X]

/- Mathematical definition (normal notation): The full weighted process multiplies each outer factor by its local factor. For a fixed answer history, its weight is the leaf weight times the product of all outer and local factors along that history. -/
def full : {n : ℕ} → SplitProcess A X n → ErrorProcess A X n
  | 0, .stop leaf => .stop leaf
  | _ + 1, .query outer innerFactor next =>
      .query (fun x a => outer x a * innerFactor x a) (fun a => full (next a))

/- Mathematical definition (normal notation): The local process deletes all outer factors while preserving the adaptive answer tree and leaf weights. Its history weight is the product of the local factors along that history, multiplied by the leaf weight. -/
def localPart : {n : ℕ} → SplitProcess A X n → ErrorProcess A X n
  | 0, .stop leaf => .stop leaf
  | _ + 1, .query _ innerFactor next => .query innerFactor (fun a => localPart (next a))

/-- Postpone multiplication by every local factor until the final patch average; all adaptive choices and outer factors are preserved. -/
/- Mathematical definition (normal notation): Move every local factor to the final leaf while preserving the outer factors and adaptive choices. With initial accumulated function a(x), the resulting history weight equals a(x) times the full process's original history weight. -/
def deferred : {n : ℕ} → SplitProcess A X n → (X → ℝ) → ErrorProcess A X n
  | 0, .stop leaf, accumulated => .stop (fun x => accumulated x * leaf x)
  | _ + 1, .query outer innerFactor next, accumulated =>
      .query outer (fun a => deferred (next a) (fun x => accumulated x * innerFactor x a))

-- Auxiliary lemma (hybrid comparison); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; process ∈ SplitProcess(A, X, n); accumulated ∈ X → ℝ; history ∈ Answers(A, n); x ∈ X, we have

weight(process.deferred(accumulated))(history, x) = accumulated(x) · weight(process.full)(history, x) .
-/
theorem deferred_weight {n : ℕ} (process : SplitProcess A X n)
    (accumulated : X → ℝ) (history : Answers A n) (x : X) :
    (process.deferred accumulated).weight history x =
      accumulated x * process.full.weight history x := by
  induction process generalizing accumulated with
  | stop leaf => rfl
  | @query n outer innerFactor next ih =>
      simp only [deferred, full, ErrorProcess.weight]
      rw [ih history.1]
      ring

/-- True outer queries have their ordinary answer-sum budget and are independent of patch encodings outside the guards.  Signed queries will use outer factor one, budget `card A`, and `isGuard=false`. -/
/- Mathematical definition (normal notation): At every node and every previous-answer history, the outer weights satisfy ∑_z |o(x,z)| ≤ bᵢ for every local state x. At nonguard rounds the outer weights must be independent of x; at guard rounds they may depend on x. These conditions are required recursively for every continuation. -/
def OuterControlled : {n : ℕ} → SplitProcess A X n →
    (Fin n → ℝ) → (Fin n → Bool) → Prop
  | 0, .stop _, _, _ => True
  | _ + 1, .query outer _ next, budget, isGuard =>
      (∀ x, (∑ a, |outer x a|) ≤ budget 0) ∧
      (isGuard 0 = false → ∃ fixed : A → ℝ, ∀ x a, outer x a = fixed a) ∧
      ∀ a, OuterControlled (next a) (Fin.tail budget) (Fin.tail isGuard)

-- Auxiliary lemma (hybrid comparison); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; process ∈ SplitProcess(A, X, n); P ∈ 𝒟(X); error ∈ ℝ; accumulated ∈ X → ℝ; budget ∈ {0,…,n-1} → ℝ; isGuard ∈ {0,…,n-1} → Bool, assume process.OuterControlled(budget, isGuard); ∀ history ∈ Answers(A, n), 𝔼_(x ← P) [|accumulated(x) · weight(process.localPart)(history, x)|] ≤ error. Then

Controlled(process.deferred(accumulated))(P, error, budget, isGuard).
-/
theorem deferred_controlled {n : ℕ} (process : SplitProcess A X n)
    (P : FiniteDistribution X) (error : ℝ) (accumulated : X → ℝ)
    (budget : Fin n → ℝ) (isGuard : Fin n → Bool)
    (houter : process.OuterControlled budget isGuard)
    (hlocal : ∀ history : Answers A n,
      P.expect (fun x => |accumulated x * process.localPart.weight history x|) ≤ error) :
    (process.deferred accumulated).Controlled P error budget isGuard := by
  induction process generalizing accumulated with
  | stop leaf => simpa [deferred, localPart, ErrorProcess.Controlled,
      ErrorProcess.weight] using hlocal PUnit.unit
  | @query n outer innerFactor next ih =>
      obtain ⟨hbudget, hindependent, hnext⟩ := houter
      refine ⟨hbudget, hindependent, ?_⟩
      intro a
      apply ih a (fun x => accumulated x * innerFactor x a) (Fin.tail budget)
        (Fin.tail isGuard) (hnext a)
      intro history
      have h := hlocal (a, history)
      change P.expect (fun x =>
        |accumulated x * (innerFactor x a * (next a).localPart.weight history x)|) ≤ error at h
      simpa only [mul_assoc] using h

/-- Guard isolation: only the average of the complete local signed product is bounded.  All outside answers are still summed adaptively. -/
-- Auxiliary lemma (hybrid comparison); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; process ∈ SplitProcess(A, X, n); P ∈ 𝒟(X); error ∈ ℝ; budget ∈ {0,…,n-1} → ℝ; isGuard ∈ {0,…,n-1} → Bool, assume X ≠ ∅; 0 ≤ error; ∀ i, 0 ≤ budget(i); process.OuterControlled(budget, isGuard); ∀ history ∈ Answers(A, n), 𝔼_(x ← P) [|weight(process.localPart)(history, x)|] ≤ error. Then

(∑_history (𝔼_(x ← P) [|weight(process.full)(history, x)|])) ≤ (|A|)^(ErrorProcess.localCount(isGuard)) · (∏ᵢ (budget(i))) · error.
-/
theorem isolate [Nonempty X] {n : ℕ} (process : SplitProcess A X n)
    (P : FiniteDistribution X) (error : ℝ) (herror : 0 ≤ error)
    (budget : Fin n → ℝ) (isGuard : Fin n → Bool)
    (hbudget : ∀ i, 0 ≤ budget i)
    (houter : process.OuterControlled budget isGuard)
    (hlocal : ∀ history : Answers A n,
      P.expect (fun x => |process.localPart.weight history x|) ≤ error) :
    (∑ history, P.expect (fun x => |process.full.weight history x|)) ≤
      (Fintype.card A : ℝ) ^ ErrorProcess.localCount isGuard *
        (∏ i, budget i) * error := by
  have hc := process.deferred_controlled P error (fun _ => 1) budget isGuard houter
    (by simpa only [one_mul] using hlocal)
  have h := ErrorProcess.forced_error_bound P error herror
    (process.deferred (fun _ => 1)) budget isGuard hbudget hc
  simpa only [process.deferred_weight, one_mul] using h

/-- The paper's `K^(number of signed gates + number of guards)` form. -/

/-
Mathematical statement (normal notation): Consider an adaptive split process with answer alphabet of size K, a set S of signed rounds, and a set B of guard rounds. Assume the outer factors have answer-sum bounds K on S and 1 elsewhere, with the prescribed guard behavior. If the local product Lₕ satisfies 𝔼_P [|Lₕ|] ≤ ε for every full answer history h, where ε ≥ 0, then the full products Fₕ satisfy

∑ₕ 𝔼_P [|Fₕ|] ≤ K^(|S|+|B|) · ε.
-/
theorem isolate_pow [Nonempty X] {n : ℕ} (process : SplitProcess A X n)
    (P : FiniteDistribution X) (error : ℝ) (herror : 0 ≤ error)
    (signed guards : Finset (Fin n))
    (houter : process.OuterControlled
      (fun i => if i ∈ signed then (Fintype.card A : ℝ) else 1)
      (fun i => decide (i ∈ guards)))
    (hlocal : ∀ history : Answers A n,
      P.expect (fun x => |process.localPart.weight history x|) ≤ error) :
    (∑ history, P.expect (fun x => |process.full.weight history x|)) ≤
      (Fintype.card A : ℝ) ^ (signed.card + guards.card) * error := by
  classical
  have h := process.isolate P error herror
    (fun i => if i ∈ signed then (Fintype.card A : ℝ) else 1)
    (fun i => decide (i ∈ guards)) (fun i => by split_ifs <;> positivity) houter hlocal
  simpa only [ErrorProcess.localCount_mem, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const, ← pow_add, Nat.add_comm] using h

/-- Recording any observation, including disclosed patch encodings, cannot enlarge the isolated replacement error. -/

/-
Mathematical statement (normal notation): Under the same signed-round, guard-round, and local-error assumptions as the isolation bound, apply any finite observation obs(h,x) to the weighted process. The resulting signed output measure ν satisfies

‖ν‖₁ ≤ K^(|S|+|B|) · ε.

The observation may depend on both the transcript and the sampled local state.
-/
theorem observed_isolate [Nonempty X] {n : ℕ} {V : Type*} [Fintype V]
    (process : SplitProcess A X n) (P : FiniteDistribution X) (error : ℝ) (herror : 0 ≤ error)
    (signed guards : Finset (Fin n))
    (houter : process.OuterControlled
      (fun i => if i ∈ signed then (Fintype.card A : ℝ) else 1)
      (fun i => decide (i ∈ guards)))
    (hlocal : ∀ history : Answers A n,
      P.expect (fun x => |process.localPart.weight history x|) ≤ error)
    (observe : Answers A n × X → V) :
    variationNorm (fun v => ∑ hx : Answers A n × X,
      P.weight hx.2 * process.full.weight hx.1 hx.2 *
        (FiniteDistribution.pure (observe hx)).weight v) ≤
      (Fintype.card A : ℝ) ^ (signed.card + guards.card) * error := by
  have hcontract := variationNorm_stochastic_le
    (fun hx : Answers A n × X => P.weight hx.2 * process.full.weight hx.1 hx.2)
    (fun hx => FiniteDistribution.pure (observe hx))
  have hmass : variationNorm
      (fun hx : Answers A n × X => P.weight hx.2 * process.full.weight hx.1 hx.2) =
        ∑ history, P.expect (fun x => |process.full.weight history x|) := by
    simp [variationNorm, Fintype.sum_prod_type, abs_mul,
      abs_of_nonneg (P.nonneg _), FiniteDistribution.expect]
  rw [hmass] at hcontract
  exact hcontract.trans (process.isolate_pow P error herror signed guards houter hlocal)

end SplitProcess

end CircuitCompiler.AveragedEnergyComparison
