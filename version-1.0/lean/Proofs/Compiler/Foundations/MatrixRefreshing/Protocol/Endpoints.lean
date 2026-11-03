import Proofs.Compiler.Foundations.MatrixRefreshing.Probability.FiniteDistribution
import Proofs.Compiler.Foundations.MatrixRefreshing.Protocol.Experiment



/-!
# From the round conditional distribution to endpoint answer tables

The analytical proof works with two local endpoints: the left party's old/new shares and the right party's old/new shares. The operational conditional distribution instead takes an old state and returns a new state together with an answer. `stateAnswer` separates the answer from the state marginal, and `endpointAnswer` changes coordinates using `regroup`.

Conditioning here is only on the two states, never on a transcript prefix. The conditional value is defined by real division on all inputs, hence is zero when the state transition has zero mass. Consequently the factorization `roundDistribution_weight_factor` remains valid off the secret fiber as well as on it. Finally `stateAnswer_eq_fiber_average` identifies this operational quantity with the uniform average over compatible matrices needed by the counting argument.
-/

set_option autoImplicit false

open scoped BigOperators

namespace MatrixRefresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open Refresh

/-- The mass of a first-coordinate marginal is the sum of the joint masses over all second-coordinate values. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α,β a set; P ∈ 𝒟((α × β)); a ∈ α, assume α is finite; β is finite. Then

((Prod)₁_*P)(a) = ∑_b (P((a, b))).
-/
theorem map_fst_weight {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteDistribution (α × β)) (a : α) :
    (P.map Prod.fst).weight a = ∑ b, P.weight (a, b) := by
  classical
  simp [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.pure, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

/-- The mass of a second-coordinate marginal is the sum of the joint masses over all first-coordinate values. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α,β a set; P ∈ 𝒟((α × β)); b ∈ β, assume α is finite; β is finite. Then

((Prod)₂_*P)(b) = ∑ₐ (P((a, b))).
-/
theorem map_snd_weight {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteDistribution (α × β)) (b : β) :
    (P.map Prod.snd).weight b = ∑ a, P.weight (a, b) := by
  classical
  simp [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.pure, Fintype.sum_prod_type]

/-- An individual joint atom has mass at most the mass of its first-coordinate marginal atom. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For α,β a set; P ∈ 𝒟((α × β)); a ∈ α; b ∈ β, assume α is finite; β is finite. Then

P((a, b)) ≤ ((Prod)₁_*P)(a).
-/
theorem joint_weight_le_fst {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteDistribution (α × β)) (a : α) (b : β) :
    P.weight (a, b) ≤ (P.map Prod.fst).weight a := by
  rw [map_fst_weight]
  exact Finset.single_le_sum (fun b _ => P.nonneg (a, b)) (Finset.mem_univ b)

/-- Probability that uniform refresh sends `u` to `v`, before observing any leakage. It is positive precisely on the compatible secret fiber. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; u, v ∈ State(F, n), define

outputMass(u, v) := (refresh(u)_*𝒰_(GLₙ(F)))(v).
-/
noncomputable def outputMass {n : ℕ} (u v : State F n) : ℝ :=
  ((FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F n)).map (refresh u)).weight v

/-- Any two states encoding the same secret have a strictly positive transition probability under a uniform invertible matrix. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; u, v ∈ State(F, n), assume secret(u) = secret(v). Then

0 < outputMass(u, v).
-/
theorem outputMass_pos {n : ℕ} (u v : State F n) (hs : secret u = secret v) :
    0 < outputMass u v := by
  obtain ⟨M, hM⟩ := refresh_transitive u v hs
  letI : Nonempty (Transporter u v) := ⟨⟨M, hM⟩⟩
  unfold outputMass
  rw [FiniteDistribution.uniform_map_weight]
  apply div_pos
  · exact_mod_cast Fintype.card_pos (α := Transporter u v)
  · exact_mod_cast Fintype.card_pos (α := Refresh.«GL» F n)

/-- A refresh transition between states encoding different secrets has probability zero. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; u, v ∈ State(F, n), assume secret(u) ≠ secret(v). Then

outputMass(u, v) = 0.
-/
theorem outputMass_eq_zero_of_secret_ne {n : ℕ} (u v : State F n)
    (hs : secret u ≠ secret v) : outputMass u v = 0 := by
  have h : ((FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F n)).map (refresh u)).Supports
      (fun v => secret v = secret u) :=
    FiniteDistribution.map_supports _ _ (fun _ => True) _ (FiniteDistribution.supports_true _)
      (fun M _ => refresh_secret u M)
  by_contra hm
  exact hs (h v hm).symm

/-- Conditional answer probability for a transition from `u` to `v`. The denominator is the unconditional output-state mass; Lean's totalized real division assigns zero when it vanishes, including incompatible secret pairs. -/
/-
Mathematical definition (normal notation): For n, ℓ, T ∈ ℕ; adv ∈ Strategy(F, n, ℓ, T); i ∈ {0,…,T-1}; h ∈ History(ℓ, i); z ∈ Leaf(ℓ); u, v ∈ State(F, n), define

stateAnswer(adv, i, h, z, u, v) := roundDistribution(adv, i, h, u)((v, z)) / outputMass(u, v).
-/
noncomputable def stateAnswer {n ℓ T : ℕ}
    (adv : Strategy F n ℓ T) (i : Fin T) (h : History ℓ i.val) (z : Leaf ℓ)
    (u v : State F n) : ℝ := (roundDistribution adv i h u).weight (v, z) / outputMass u v

/-- The same conditional probability indexed by the parties' local endpoints. The manuscript displays `x = (ell,ell')` and `y = (r,r')`, while `regroup.symm` reconstructs the old and new states `(ell,r)` and `(ell',r')`. Lean keeps the named `State` and `Endpoint` records for those same pairs. This is the paper's answer table. -/
/- Mathematical definition (normal notation): Express the fixed-answer transition weight in endpoint coordinates: regroup ((ℓ,ℓ'),(r,r')) as the old state (ℓ,r) and new state (ℓ',r'), then evaluate the round-i, history-h, answer-z state transition weight. -/
noncomputable def endpointAnswer {n ℓ T : ℕ}
    (adv : Strategy F n ℓ T) (i : Fin T) (h : History ℓ i.val) (z : Leaf ℓ)
    (x y : Endpoint F n) : ℝ :=
  let uv := (regroup F n).symm (x, y)
  stateAnswer adv i h z uv.1 uv.2

/-- Summing the round’s joint mass over all complete answers recovers the unconditional output-state mass. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, ℓ, T ∈ ℕ; adv ∈ Strategy(F, n, ℓ, T); i ∈ {0,…,T-1}; h ∈ History(ℓ, i); u, v ∈ State(F, n), we have

∑_z (roundDistribution(adv, i, h, u)((v, z))) = outputMass(u, v).
-/
theorem roundDistribution_sum_answers {n ℓ T : ℕ}
    (adv : Strategy F n ℓ T) (i : Fin T) (h : History ℓ i.val) (u v : State F n) :
    ∑ z, (roundDistribution adv i h u).weight (v, z) = outputMass u v := by
  rw [← map_fst_weight, roundDistribution_state_marginal]
  rfl

/-- The mass of one output-state and answer pair is at most the mass of that output state before observing an answer. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, ℓ, T ∈ ℕ; adv ∈ Strategy(F, n, ℓ, T); i ∈ {0,…,T-1}; h ∈ History(ℓ, i); u, v ∈ State(F, n); z ∈ Leaf(ℓ), we have

roundDistribution(adv, i, h, u)((v, z)) ≤ outputMass(u, v).
-/
theorem roundDistribution_weight_le_outputMass {n ℓ T : ℕ}
    (adv : Strategy F n ℓ T) (i : Fin T) (h : History ℓ i.val)
    (u v : State F n) (z : Leaf ℓ) :
    (roundDistribution adv i h u).weight (v, z) ≤ outputMass u v := by
  have h := joint_weight_le_fst (roundDistribution adv i h u) v z
  simpa only [roundDistribution_state_marginal, outputMass] using h

/-- Every conditional answer-table entry is nonnegative, including its zero value on impossible transitions. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, ℓ, T ∈ ℕ; adv ∈ Strategy(F, n, ℓ, T); i ∈ {0,…,T-1}; h ∈ History(ℓ, i); z ∈ Leaf(ℓ); u, v ∈ State(F, n), we have

0 ≤ stateAnswer(adv, i, h, z, u, v).
-/
theorem stateAnswer_nonneg {n ℓ T : ℕ}
    (adv : Strategy F n ℓ T) (i : Fin T) (h : History ℓ i.val) (z : Leaf ℓ) (u v : State F n) :
    0 ≤ stateAnswer adv i h z u v :=
  div_nonneg ((roundDistribution adv i h u).nonneg _) ((FiniteDistribution.uniform.map (refresh u)).nonneg v)

/-- Every conditional answer-table entry is at most one; impossible transitions use the totalized value zero. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, ℓ, T ∈ ℕ; adv ∈ Strategy(F, n, ℓ, T); i ∈ {0,…,T-1}; h ∈ History(ℓ, i); z ∈ Leaf(ℓ); u, v ∈ State(F, n), we have

stateAnswer(adv, i, h, z, u, v) ≤ 1.
-/
theorem stateAnswer_le_one {n ℓ T : ℕ}
    (adv : Strategy F n ℓ T) (i : Fin T) (h : History ℓ i.val) (z : Leaf ℓ) (u v : State F n) :
    stateAnswer adv i h z u v ≤ 1 := by
  have hp : 0 ≤ outputMass u v := (FiniteDistribution.uniform.map (refresh u)).nonneg v
  by_cases hz : outputMass u v = 0
  · simp [stateAnswer, hz]
  · exact (div_le_one (lt_of_le_of_ne hp (Ne.symm hz))).mpr
      (roundDistribution_weight_le_outputMass adv i h u v z)

/-- For compatible states the table entries form a probability distribution over complete answers. Compatibility is required because the totalized values sum to zero on impossible state transitions. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, ℓ, T ∈ ℕ; adv ∈ Strategy(F, n, ℓ, T); i ∈ {0,…,T-1}; h ∈ History(ℓ, i); u, v ∈ State(F, n), assume secret(u) = secret(v). Then

∑_z (stateAnswer(adv, i, h, z, u, v)) = 1.
-/
theorem stateAnswer_sum_eq_one {n ℓ T : ℕ}
    (adv : Strategy F n ℓ T) (i : Fin T) (h : History ℓ i.val)
    (u v : State F n) (hs : secret u = secret v) :
    ∑ z, stateAnswer adv i h z u v = 1 := by
  simp_rw [stateAnswer, ← Finset.sum_div]
  rw [roundDistribution_sum_answers, div_self (ne_of_gt (outputMass_pos u v hs))]

/-- The conditional answer table is zero between states encoding different secrets. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, ℓ, T ∈ ℕ; adv ∈ Strategy(F, n, ℓ, T); i ∈ {0,…,T-1}; h ∈ History(ℓ, i); z ∈ Leaf(ℓ); u, v ∈ State(F, n), assume secret(u) ≠ secret(v). Then

stateAnswer(adv, i, h, z, u, v) = 0.
-/
theorem stateAnswer_eq_zero_of_secret_ne {n ℓ T : ℕ}
    (adv : Strategy F n ℓ T) (i : Fin T) (h : History ℓ i.val) (z : Leaf ℓ)
    (u v : State F n) (hs : secret u ≠ secret v) : stateAnswer adv i h z u v = 0 := by
  simp [stateAnswer, outputMass_eq_zero_of_secret_ne u v hs]

/-- Exact operational factorization, including outputs of the wrong secret. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, ℓ, T ∈ ℕ; adv ∈ Strategy(F, n, ℓ, T); i ∈ {0,…,T-1}; h ∈ History(ℓ, i); s ∈ F; u, v ∈ State(F, n); z ∈ Leaf(ℓ), assume 2 ≤ n; secret(u) = s. Then

roundDistribution(adv, i, h, u)((v, z)) = μₛ(v) · stateAnswer(adv, i, h, z, u, v).
-/
theorem roundDistribution_weight_factor {n ℓ T : ℕ}
    (adv : Strategy F n ℓ T) (i : Fin T) (h : History ℓ i.val) (hn : 2 ≤ n)
    (s : F) (u v : State F n) (hu : secret u = s) (z : Leaf ℓ) :
    (roundDistribution adv i h u).weight (v, z) =
      (mu F n hn s).weight v * stateAnswer adv i h z u v := by
  have hmass : outputMass u v = (mu F n hn s).weight v := by
    unfold outputMass
    rw [refresh_uniform hn s u hu]
  -- A zero marginal forces every joint answer mass to vanish. Handling it explicitly avoids a hidden positive-probability premise in the identity.
  by_cases hz : outputMass u v = 0
  · have hzero := le_antisymm ((roundDistribution_weight_le_outputMass adv i h u v z).trans_eq hz)
      ((roundDistribution adv i h u).nonneg _)
    simp [stateAnswer, ← hmass, hz, hzero]
  · rw [stateAnswer, ← hmass]
    field_simp

end MatrixRefresh
