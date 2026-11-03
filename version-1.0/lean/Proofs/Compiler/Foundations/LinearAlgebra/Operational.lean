import Proofs.Compiler.Foundations.LinearAlgebra.Conditioning
import Proofs.Compiler.Foundations.LinearAlgebra.StateDensity



/-!
# Operational meaning of the forward density

This file samples each fresh GL matrix and the local leaf indicators, then updates the stored shares and appends the answer. Its distributions are normalized throughout. The recursively defined current density is proved to give their actual joint state/history weights.
-/

set_option autoImplicit false

open scoped BigOperators

namespace TableAnalysis

open MatrixRefresh Refresh

noncomputable section

attribute [local instance] Classical.propDecidable

variable {X G Z : Type*} [Fintype X] [Fintype G] [Fintype Z]

/- Mathematical definition (normal notation): At fixed refresh choice g and state x, the answer distribution assigns probability p_z(g,x) to z. The answer-partition conditions ensure these probabilities are nonnegative and sum to one. -/
def partitionAnswerDistribution (p : RoundPartition X G Z) (g : G) (u : X) : FiniteDistribution Z where
  weight z := p.weight z g u
  nonneg z := p.nonneg z g u
  total := p.complete g u

/-
Mathematical definition (normal notation): For e ∈ FiniteRefresh(X, G); p ∈ RoundPartition(X, G, Z); u ∈ X, assume G ≠ ∅. define

conditionalRoundDistribution(e, p, u) := bind(𝒰_G, (g ↦ (((z ↦ (e(g, u), z)))_*partitionAnswerDistribution(p, g, u)))).
-/
def conditionalRoundDistribution [Nonempty G] (e : FiniteRefresh X G)
    (p : RoundPartition X G Z) (u : X) : FiniteDistribution (X × Z) :=
  (FiniteDistribution.uniform : FiniteDistribution G).bind fun g =>
    (partitionAnswerDistribution p g u).map (fun z => (e g u, z))

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ FiniteRefresh(X, G); p ∈ RoundPartition(X, G, Z); u, v ∈ X; z ∈ Z, assume G ≠ ∅. Then

conditionalRoundDistribution(e, p, u)((v, z)) = 𝔼_g [{ weight(p)(z, g, u) if e(g, u) = v,; 0 otherwise }].
-/
theorem conditionalRoundDistribution_weight [Nonempty G] (e : FiniteRefresh X G)
    (p : RoundPartition X G Z) (u v : X) (z : Z) :
    (conditionalRoundDistribution e p u).weight (v, z) =
      uavg (fun g => if e g u = v then p.weight z g u else 0) := by
  classical
  simp [conditionalRoundDistribution, partitionAnswerDistribution, FiniteDistribution.bind, FiniteDistribution.map, FiniteDistribution.pure,
    FiniteDistribution.uniform, uavg, Prod.mk.injEq, ite_and, eq_comm, Finset.mul_sum]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For μ ∈ 𝒟(X); e ∈ FiniteRefresh(X, G); p ∈ RoundPartition(X, G, Z); F ∈ X → ℝ; v ∈ X; z ∈ Z, assume G ≠ ∅; ∀ g, x, μ((e(g))⁻¹(x)) = μ(x). Then

(∑ᵤ (μ(u) · F(u) · conditionalRoundDistribution(e, p, u)((v, z)))) = μ(v) · roundOp(e, p, F, z, v).
-/
theorem forward_round_weight [Nonempty G] (μ : FiniteDistribution X)
    (e : FiniteRefresh X G) (p : RoundPartition X G Z) (F : X → ℝ)
    (hinv : ∀ g x, μ.weight ((e g).symm x) = μ.weight x) (v : X) (z : Z) :
    (∑ u, μ.weight u * F u * (conditionalRoundDistribution e p u).weight (v, z)) =
      μ.weight v * roundOp e p F z v := by
  classical
  simp only [conditionalRoundDistribution_weight, uavg, roundOp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  have heq (u : X) : e g u = v ↔ u = (e g).symm v := Equiv.apply_eq_iff_eq_symm_apply _
  simp_rw [heq]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hinv]
  ring

section Actual

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

variable {i : ℕ}

/-
Mathematical definition (normal notation): For p ∈ GLRectanglePartition(F, n, Z); u ∈ State(F, n), define

rectangleRoundDistribution(p, u) := conditionalRoundDistribution(glRefreshEquiv, p.toRoundPartition, u).
-/
def rectangleRoundDistribution (p : GLRectanglePartition F n Z) (u : State F n) :
    FiniteDistribution (State F n × Z) :=
  conditionalRoundDistribution glRefreshEquiv p.toRoundPartition u

/-
Mathematical definition (normal notation): For p ∈ GLRectanglePartition(F, n, Z); h ∈ PublicHistory(Z, i); u ∈ State(F, n), define

rectangleStepDistribution(p, h, u) := (((vz ↦ ((vz)₁, Fin.snoc(h, (vz)₂))))_*rectangleRoundDistribution(p, u)).
-/
def rectangleStepDistribution (p : GLRectanglePartition F n Z)
    (h : PublicHistory Z i) (u : State F n) :
    FiniteDistribution (State F n × PublicHistory Z (i + 1)) :=
  (rectangleRoundDistribution p u).map (fun vz => (vz.1, Fin.snoc h vz.2))

/- Mathematical definition (normal notation): Sample the initial state and begin with the empty history. At each round, use the rectangular partition selected by the previous history, sample the round transition, and append the answer. Return the joint distribution of the current state and full history. -/
def rectangleExecution (p : RectangleProtocol F n Z) (initial : FiniteDistribution (State F n)) :
    (i : ℕ) → FiniteDistribution (State F n × PublicHistory Z i)
  | 0 => initial.map (fun x => (x, Fin.elim0))
  | i + 1 => (rectangleExecution p initial i).bind fun xh =>
      rectangleStepDistribution (p i xh.2) xh.2 xh.1

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ GLRectanglePartition(F, n, Z); h, k ∈ PublicHistory(Z, i); u, v ∈ State(F, n); z ∈ Z, we have

rectangleStepDistribution(p, k, u)((v, Fin.snoc(h, z))) = { rectangleRoundDistribution(p, u)((v, z)) if h = k,; 0 otherwise }.
-/
theorem rectangleStepDistribution_snoc_weight (p : GLRectanglePartition F n Z)
    (h k : PublicHistory Z i) (u v : State F n) (z : Z) :
    (rectangleStepDistribution p k u).weight (v, Fin.snoc h z) =
      if h = k then (rectangleRoundDistribution p u).weight (v, z) else 0 := by
  classical
  simp [rectangleStepDistribution, FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.pure,
    Fintype.sum_prod_type, ite_and]

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); initial ∈ 𝒟(State(F, n)); i ∈ ℕ; h ∈ PublicHistory(Z, i); v ∈ State(F, n); z ∈ Z, we have

rectangleExecution(p, initial, (i + 1))((v, Fin.snoc(h, z))) = ∑ᵤ (rectangleExecution(p, initial, i)((u, h)) · rectangleRoundDistribution(p(i, h), u)((v, z))).
-/
theorem rectangleExecution_snoc_weight (p : RectangleProtocol F n Z)
    (initial : FiniteDistribution (State F n)) (i : ℕ) (h : PublicHistory Z i)
    (v : State F n) (z : Z) :
    (rectangleExecution p initial (i + 1)).weight (v, Fin.snoc h z) =
      ∑ u, (rectangleExecution p initial i).weight (u, h) *
        (rectangleRoundDistribution (p i h) u).weight (v, z) := by
  classical
  simp [rectangleExecution, FiniteDistribution.bind, Fintype.sum_prod_type,
    rectangleStepDistribution_snoc_weight]

/-- The forward current-state table represents the actual joint experiment initialized with the chosen secret. Its approximation remains secret independent. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); s ∈ F; i ∈ ℕ; v ∈ State(F, n); h ∈ PublicHistory(Z, i), assume 2 ≤ n. Then

rectangleExecution(p, μₛ, i)((v, h)) = μₛ(v) · currentDensity(p, i, h, v).
-/
theorem rectangleExecution_weight (hn : 2 ≤ n) (p : RectangleProtocol F n Z)
    (s : F) (i : ℕ) (v : State F n) (h : PublicHistory Z i) :
    (rectangleExecution p (mu F n hn s) i).weight (v, h) =
      (mu F n hn s).weight v * currentDensity p i h v := by
  classical
  induction i generalizing v with
  | zero =>
      have hh : h = Fin.elim0 := Subsingleton.elim _ _
      rw [hh]
      simp [rectangleExecution, FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.pure,
        currentDensity, Prod.mk.injEq]
  | succ i ih =>
      have hh : h = Fin.snoc (Fin.init h) (h (Fin.last i)) := (Fin.snoc_init_self h).symm
      rw [hh, rectangleExecution_snoc_weight]
      simp_rw [ih]
      rw [currentDensity_snoc]
      exact forward_round_weight _ _ _ _
        (fun M x => mu_weight_refresh hn s M⁻¹ x) _ _

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); s ∈ F; i ∈ ℕ; h ∈ PublicHistory(Z, i), assume 2 ≤ n. Then

((Prod)₂_*rectangleExecution(p, μₛ, i))(h) = stateTranscriptDistribution(p, s, i)(h).
-/
theorem rectangleExecution_transcript_weight (hn : 2 ≤ n) (p : RectangleProtocol F n Z)
    (s : F) (i : ℕ) (h : PublicHistory Z i) :
    ((rectangleExecution p (mu F n hn s) i).map Prod.snd).weight h =
      (stateTranscriptDistribution hn p s i).weight h := by
  classical
  simp [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.pure, Fintype.sum_prod_type,
    rectangleExecution_weight, stateTranscriptDistribution, FiniteDistribution.expect]

/-- The table-based terminal expression is the statistical distance between the actual two transcript distributions. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For p ∈ RectangleProtocol(F, n, Z); s, t ∈ F; i ∈ ℕ, assume 2 ≤ n. Then

δ(((Prod)₂_*rectangleExecution(p, μₛ, i)), ((Prod)₂_*rectangleExecution(p, μₜ, i))) = terminalDistance(μₛ, μₜ, currentDensity(p, i)).
-/
theorem rectangleExecution_statisticalDistance (hn : 2 ≤ n)
    (p : RectangleProtocol F n Z) (s t : F) (i : ℕ) :
    statisticalDistance
      ((rectangleExecution p (mu F n hn s) i).map Prod.snd)
      ((rectangleExecution p (mu F n hn t) i).map Prod.snd) =
      terminalDistance (mu F n hn s) (mu F n hn t) (currentDensity p i) := by
  unfold statisticalDistance variationNorm terminalDistance
  simp_rw [rectangleExecution_transcript_weight]
  rfl

end Actual

end

end TableAnalysis
