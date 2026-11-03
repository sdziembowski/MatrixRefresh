import Mathlib.Data.Fin.Tuple.Basic
import Proofs.Compiler.Foundations.MatrixRefreshing.Analysis.Scale
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Alphabet
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Freshness



/-!
# The operational protocol and its security target

This file defines the experiment whose transcript is compared in `Security/Main.lean`. `QueryPlan` describes one round, `Strategy` chooses a plan from the preceding answers, and `execution` iterates the resulting finite probability conditional distribution. The matrix is sampled uniformly and independently each round. The choice of which party answers first is part of the plan, so it precedes both current answers; the second query may depend on the first answer.

Query domains include zero vectors even though `State` contains nonzero shares. The full-vector initialization extension can therefore reuse the same strategy. All leakage answers are bit strings: the field `F` determines the share space, but does not change the meaning of the bit budget `ℓ`.

The essential interface for the analysis is `QueryPlan.answer_eq_iff`: after fixing a complete answer, the event splits into a left condition and a right condition. `Endpoints.lean` turns that event into an endpoint table, and `Execution.lean` supplies the prefix and continuation identities used by hybrids.
-/

set_option autoImplicit false

open scoped BigOperators

namespace MatrixRefresh

variable {F : Type*} [Field F]

open Refresh

attribute [local instance] Classical.propDecidable

/-- A local leakage round in either order. Each query sees its own current share and the common refresh matrix; only the second query sees the first answer. -/
/- Mathematical definition (normal notation): A two-query round plan specifies one party to answer first. The first query depends on that party's share and the refresh matrix; the second query depends on the other share, the matrix, and the first answer. Each answer has λ bits. This auxiliary model permits within-round adaptation. -/
inductive QueryPlan (F : Type*) [Field F] (n ℓ : ℕ) where
  | leftFirst
      (leftQuery : V F n → Refresh.«GL» F n → Bits ℓ)
      (rightQuery : V F n → Refresh.«GL» F n → Bits ℓ → Bits ℓ)
  | rightFirst
      (rightQuery : V F n → Refresh.«GL» F n → Bits ℓ)
      (leftQuery : V F n → Refresh.«GL» F n → Bits ℓ → Bits ℓ)

/-- Execute the chosen order, storing the result in left/right order in both cases. -/
/- Mathematical definition (normal notation): Execute the two queries in their specified order and return the party-labelled pair (z_L,z_R). In left-first order, z_L = f_L(ℓ,M) and z_R = f_R(r,M,z_L); in right-first order, z_R = f_R(r,M) and z_L = f_L(ℓ,M,z_R). -/
def QueryPlan.answer {n ℓ : ℕ} (q : QueryPlan F n ℓ)
    (l r : V F n) (M : Refresh.«GL» F n) : Leaf ℓ :=
  match q with
  | .leftFirst leftQuery rightQuery => let z := leftQuery l M; (z, rightQuery r M z)
  | .rightFirst rightQuery leftQuery => let z := rightQuery r M; (leftQuery l M z, z)

/-- The left party's consistency condition for a proposed complete answer `z`. If the left party goes second, the right party's proposed answer is supplied to the left query. -/
/- Mathematical definition (normal notation): A proposed answer pair (z_L,z_R) passes the left consistency test when f_L(ℓ,M) = z_L in left-first order, or f_L(ℓ,M,z_R) = z_L in right-first order. -/
def QueryPlan.matchL {n ℓ : ℕ} (q : QueryPlan F n ℓ)
    (l : V F n) (M : Refresh.«GL» F n) (z : Leaf ℓ) : Prop :=
  match q with
  | .leftFirst leftQuery _ => leftQuery l M = z.1
  | .rightFirst _ leftQuery => leftQuery l M z.2 = z.1

/-- The right party's consistency condition for the same proposed answer; it depends only on the right party's share once the matrix and `z` have been fixed. -/
/- Mathematical definition (normal notation): A proposed answer pair (z_L,z_R) passes the right consistency test when f_R(r,M,z_L) = z_R in left-first order, or f_R(r,M) = z_R in right-first order. -/
def QueryPlan.matchR {n ℓ : ℕ} (q : QueryPlan F n ℓ)
    (r : V F n) (M : Refresh.«GL» F n) (z : Leaf ℓ) : Prop :=
  match q with
  | .leftFirst _ rightQuery => rightQuery r M z.1 = z.2
  | .rightFirst rightQuery _ => rightQuery r M = z.2

/-- Fixing the entire answer separates the two local conditions in either order. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, ℓ ∈ ℕ; q ∈ QueryPlan(F, n, ℓ); l, r ∈ V(F, n); M ∈ GLₙ(F); z ∈ Leaf(ℓ), we have

q.answer(l, r, M) = z ⇔ q.matchL(l, M, z) ∧ q.matchR(r, M, z).
-/
theorem QueryPlan.answer_eq_iff {n ℓ : ℕ} (q : QueryPlan F n ℓ)
    (l r : V F n) (M : Refresh.«GL» F n) (z : Leaf ℓ) :
    q.answer l r M = z ↔ q.matchL l M z ∧ q.matchR r M z := by
  rcases z with ⟨zL, zR⟩
  cases q <;> simp only [answer, matchL, matchR, Prod.mk.injEq] <;>
    constructor <;> rintro ⟨hL, hR⟩ <;> subst_vars <;> exact ⟨rfl, rfl⟩

/-- The complete answer indicator factors into its two local matching indicators. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, ℓ ∈ ℕ; q ∈ QueryPlan(F, n, ℓ); l, r ∈ V(F, n); M ∈ GLₙ(F); z ∈ Leaf(ℓ), we have

({ 1 if q.answer(l, r, M) = z,; 0 otherwise }) = ({ 1 if q.matchL(l, M, z),; 0 otherwise }) · ({ 1 if q.matchR(r, M, z),; 0 otherwise }).
-/
theorem QueryPlan.answer_indicator {n ℓ : ℕ} (q : QueryPlan F n ℓ)
    (l r : V F n) (M : Refresh.«GL» F n) (z : Leaf ℓ) :
    (if q.answer l r M = z then (1 : ℝ) else 0) =
      (if q.matchL l M z then (1 : ℝ) else 0) *
      (if q.matchR r M z then (1 : ℝ) else 0) := by
  classical
  by_cases hL : q.matchL l M z <;>
    by_cases hR : q.matchR r M z <;>
    simp [q.answer_eq_iff, hL, hR]

/-- A deterministic adaptive strategy specifies a query plan at every history, including unreachable ones. This makes later counterfactual continuations total. Randomized adversaries are handled separately by averaging over fixed tapes. -/
/- Mathematical definition (normal notation): An adaptive T-round strategy chooses the round-i query plan as a function of i and the complete public history (z₁,…,zᵢ) from previous rounds. -/
structure Strategy (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n ℓ T : ℕ) where
  plan : (i : Fin T) → History ℓ i.val → QueryPlan F n ℓ

variable [Fintype F] [DecidableEq F]

/-- Extend a public transcript prefix by placing the new complete-round answer in its final position. -/
/-
Mathematical definition (normal notation): For ℓ, i ∈ ℕ; h ∈ History(ℓ, i); z ∈ Leaf(ℓ), define

appendHistory(h, z) := Fin.snoc(h, z).
-/
def appendHistory {ℓ i : ℕ} (h : History ℓ i) (z : Leaf ℓ) : History ℓ (i + 1) :=
  Fin.snoc h z

/-- Splitting a nonempty transcript into its prefix and last answer is a bijection, used later to sum over histories without multiplicities. -/
/- Mathematical definition (normal notation): The bijection (h,z) ↦ h‖z appends one round answer to a length-i history. Its inverse returns the first i answers and the last answer separately. -/
def historyExtension (ℓ i : ℕ) : History ℓ i × Leaf ℓ ≃ History ℓ (i + 1) where
  toFun hz := appendHistory hz.1 hz.2
  invFun h := (Fin.init h, h (Fin.last i))
  left_inv := by intro hz; simp [appendHistory]
  right_inv := by intro h; simp [appendHistory]

/-- Two extended transcripts are equal exactly when their prefixes and their last complete answers are both equal. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ℓ, i ∈ ℕ; h, k ∈ History(ℓ, i); z, w ∈ Leaf(ℓ), we have

appendHistory(h, z) = appendHistory(k, w) ⇔ h = k ∧ z = w.
-/
theorem appendHistory_eq_iff {ℓ i : ℕ} (h k : History ℓ i) (z w : Leaf ℓ) :
    appendHistory h z = appendHistory k w ↔ h = k ∧ z = w := by
  change historyExtension ℓ i (h, z) = historyExtension ℓ i (k, w) ↔ _
  rw [(historyExtension ℓ i).injective.eq_iff, Prod.mk.injEq]

/-- Joint distribution of the updated state and the current leakage answer. Both are computed from the same sampled matrix and the same pre-refresh shares. -/
/-
Mathematical definition (normal notation): For n, ℓ, T ∈ ℕ; adv ∈ Strategy(F, n, ℓ, T); i ∈ {0,…,T-1}; h ∈ History(ℓ, i); u ∈ State(F, n), define

roundDistribution(adv, i, h, u) := ((M ↦ (refresh(u, M), answer(adv.plan(i, h))(L(u), R(u), M)))_*𝒰_(GLₙ(F))).
-/
noncomputable def roundDistribution {n ℓ T : ℕ}
    (adv : Strategy F n ℓ T) (i : Fin T) (h : History ℓ i.val) (u : State F n) :
    FiniteDistribution (State F n × Leaf ℓ) :=
  (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F n)).map fun M =>
    (refresh u M, (adv.plan i h).answer (stateLeftShare u).val (stateRightShare u).val M)

/-- Forgetting the answer recovers the original refresh conditional distribution, independently of the strategy and its history. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, ℓ, T ∈ ℕ; adv ∈ Strategy(F, n, ℓ, T); i ∈ {0,…,T-1}; h ∈ History(ℓ, i); u ∈ State(F, n), we have

((Prod)₁_*roundDistribution(adv, i, h, u)) = (refresh(u)_*𝒰_(GLₙ(F))).
-/
theorem roundDistribution_state_marginal {n ℓ T : ℕ}
    (adv : Strategy F n ℓ T) (i : Fin T) (h : History ℓ i.val) (u : State F n) :
    (roundDistribution adv i h u).map Prod.fst =
      (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F n)).map (refresh u) := by
  rw [roundDistribution, FiniteDistribution.map_map]
  rfl

/-- Freshness of the updated state is an unconditional marginal statement. It does not assert independence of the updated state and the leakage answer. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, ℓ, T ∈ ℕ; adv ∈ Strategy(F, n, ℓ, T); i ∈ {0,…,T-1}; h ∈ History(ℓ, i); s ∈ F; u ∈ State(F, n), assume 2 ≤ n; secret(u) = s. Then

((Prod)₁_*roundDistribution(adv, i, h, u)) = μₛ.
-/
theorem roundDistribution_uniform {n ℓ T : ℕ}
    (adv : Strategy F n ℓ T) (i : Fin T) (h : History ℓ i.val) (hn : 2 ≤ n)
    (s : F) (u : State F n) (hu : secret u = s) :
    (roundDistribution adv i h u).map Prod.fst = mu F n hn s := by
  rw [roundDistribution_state_marginal, refresh_uniform hn s u hu]

/-- The joint round distribution assigns nonzero mass only to updated states encoding the same secret as its input. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, ℓ, T ∈ ℕ; adv ∈ Strategy(F, n, ℓ, T); i ∈ {0,…,T-1}; h ∈ History(ℓ, i); u ∈ State(F, n), we have

Supports(roundDistribution(adv, i, h, u))(((vz ↦ secret((vz)₁) = secret(u)))).
-/
theorem roundDistribution_preserves_secret {n ℓ T : ℕ}
    (adv : Strategy F n ℓ T) (i : Fin T) (h : History ℓ i.val) (u : State F n) :
    (roundDistribution adv i h u).Supports (fun vz => secret vz.1 = secret u) := by
  unfold roundDistribution
  exact FiniteDistribution.map_supports (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F n)) _
    (fun _ => True) (fun vz : State F n × Leaf ℓ => secret vz.1 = secret u)
    (FiniteDistribution.supports_true _)
    (fun M _ => refresh_secret u M)

/-- The only data retained after a round are the updated shares and public history. -/
/-
Mathematical definition (normal notation): For n, ℓ, T ∈ ℕ; adv ∈ Strategy(F, n, ℓ, T); i ∈ {0,…,T-1}; xh ∈ State(F, n) × History(ℓ, i), define

stepDistribution(adv, i, xh) := (((vz ↦ ((vz)₁, appendHistory((xh)₂, (vz)₂))))_*roundDistribution(adv, i, (xh)₂, (xh)₁)).
-/
noncomputable def stepDistribution {n ℓ T : ℕ}
    (adv : Strategy F n ℓ T) (i : Fin T) (xh : State F n × History ℓ i.val) :
    FiniteDistribution (State F n × History ℓ (i.val + 1)) :=
  (roundDistribution adv i xh.2 xh.1).map (fun vz => (vz.1, appendHistory xh.2 vz.2))

/-- Run exactly `i` rounds, retaining both the hidden state and the public answer history. The proof `i ≤ T` only certifies that the strategy has enough rounds; the recursive step samples a fresh matrix through `stepDistribution`. -/
/- Mathematical definition (normal notation): Start with a state sampled from the initial distribution and the empty history. Recursively, at round i, sample the next state and answer according to the strategy selected by the current history, then append that answer. The result is the joint distribution of the state and history after i ≤ T rounds. -/
noncomputable def execution {n ℓ T : ℕ}
    (adv : Strategy F n ℓ T) (initial : FiniteDistribution (State F n)) :
    (i : ℕ) → i ≤ T → FiniteDistribution (State F n × History ℓ i)
  | 0, _ => initial.map (fun x => (x, Fin.elim0))
  | i + 1, hi => (execution adv initial i (by omega)).bind (stepDistribution adv ⟨i, by omega⟩)

/-- The adversary's answer transcript after uniform initialization on secret fiber `s`. The hidden state is discarded only after all rounds have run. -/
/-
Mathematical definition (normal notation): For n, ℓ, T ∈ ℕ; adv ∈ Strategy(F, n, ℓ, T); s ∈ F, assume 2 ≤ n. define

transcriptDistribution(adv, s) := ((Prod)₂_*execution(adv, μₛ, T, le_rfl)).
-/
noncomputable def transcriptDistribution {n ℓ T : ℕ}
    (adv : Strategy F n ℓ T) (hn : 2 ≤ n) (s : F) : FiniteDistribution (History ℓ T) :=
  (execution adv (mu F n hn s) T le_rfl).map Prod.snd

/-- If initialization is supported on one secret fiber, execution remains on that fiber after any permitted number of rounds. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, ℓ, T ∈ ℕ; adv ∈ Strategy(F, n, ℓ, T); initial ∈ 𝒟(State(F, n)); s ∈ F; i ∈ ℕ, assume initial.Supports(((x ↦ secret(x) = s))); i ≤ T. Then

Supports(execution(adv, initial, i))(((xh ↦ secret((xh)₁) = s))).
-/
theorem execution_preserves_secret {n ℓ T : ℕ}
    (adv : Strategy F n ℓ T) (initial : FiniteDistribution (State F n)) (s : F)
    (hs : initial.Supports (fun x => secret x = s)) (i : ℕ) (hi : i ≤ T) :
    (execution adv initial i hi).Supports (fun xh => secret xh.1 = s) := by
  induction i with
  | zero =>
    exact FiniteDistribution.map_supports initial _ _ _ hs (fun x hx => hx)
  | succ i ih =>
    -- Support propagates through the joint state/history conditional distribution. This is the invariant that permits later use of freshness at every reachable state.
    apply FiniteDistribution.bind_supports (execution adv initial i (by omega)) (stepDistribution adv ⟨i, by omega⟩)
      (fun xh : State F n × History ℓ i => secret xh.1 = s)
      (fun yh : State F n × History ℓ (i + 1) => secret yh.1 = s) (ih (by omega))
    intro xh hx
    exact FiniteDistribution.map_supports (roundDistribution adv ⟨i, by omega⟩ xh.2 xh.1)
      (fun vz => (vz.1, appendHistory xh.2 vz.2))
      (fun vz : State F n × Leaf ℓ => secret vz.1 = secret xh.1)
      (fun yh : State F n × History ℓ (i + 1) => secret yh.1 = s)
      (roundDistribution_preserves_secret adv _ _ _) (fun vz hv => hv.trans hx)

/-- Uniform initialization for a secret keeps every later hidden state in that secret’s encoding fiber. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, ℓ, T ∈ ℕ; adv ∈ Strategy(F, n, ℓ, T); s ∈ F; i ∈ ℕ, assume 2 ≤ n; i ≤ T. Then

Supports(execution(adv, μₛ, i))(((xh ↦ secret((xh)₁) = s))).
-/
theorem initialized_execution_preserves_secret {n ℓ T : ℕ}
    (adv : Strategy F n ℓ T) (hn : 2 ≤ n) (s : F) (i : ℕ) (hi : i ≤ T) :
    (execution adv (mu F n hn s) i hi).Supports (fun xh => secret xh.1 = s) :=
  execution_preserves_secret adv _ s (mu_supports n hn s) i hi

end MatrixRefresh
