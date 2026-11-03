import Proofs.Compiler.GateApproximation.Shortening.RectangularTapedSampler
import Proofs.Compiler.Construction.Parameters



/-!
# Raw local sampler views and the fractional gate interface

Each retained mark reconstructs the exact raw row and free-entry proposal tapes. The deterministic observation of these real tapes is equal to the stochastic local-view distribution used by the proven fractional gate theorem.
-/
set_option autoImplicit false

set_option maxHeartbeats 2400000

open scoped BigOperators

namespace CircuitCompiler.Rectangular.Taped

open Refresh MatrixRefresh Sampling Sampling.Unbounded

noncomputable section

variable {F O A BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [Fintype A] [Fintype BL] [Fintype BR]

variable {n t : ℕ}

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u ∈ U(F, (n + t)); p ∈ Attempt(n = n, u); mark ∈ Mark(F, n, (n + t)), we have

rawLocalAttempt(u, p, mark) = rawAttempt(u, p, mark).
-/
theorem rawLocalAttempt_val (u : U F (n+t)) (p : Attempt (n := n) u)
    (mark : Mark F n (n+t)) : rawLocalAttempt u p.val mark = rawAttempt u p mark := by
  unfold rawLocalAttempt rawAttempt
  split_ifs <;> rfl

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u ∈ U(F, (n + t)); k ∈ ℕ; a ∈ Tape(Attempt(n = n, u), k); b ∈ Tape(Mark(F, n, (n + t)), k), we have

rawLocalPrefix(u, k, mapTape(Subtype, k, a), b) = rawPrefix(u, k, a, b).
-/
theorem rawLocalPrefix_map (u : U F (n+t)) (k : ℕ)
    (a : Tape (Attempt (n := n) u) k) (b : Tape (Mark F n (n+t)) k) :
    rawLocalPrefix u k (mapTape Subtype.val k a) b = rawPrefix u k a b := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [mapTape,rawLocalPrefix,rawPrefix,rawLocalAttempt_val,ih] <;> rfl

/-- The left view retains every raw proposal, with no loss of sampling coins. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u ∈ U(F, (n + t)); z ∈ FullTape(n = n, u); marks ∈ Tape(Mark(F, n, (n + t)), (z)₁) × Mark(F, n, (n + t)), we have

rawLeftView(u, leftView(z, marks)) = rawTrace(u, (z, marks)).
-/
theorem rawLeftView_leftView (u : U F (n+t)) (z : FullTape (n := n) u)
    (marks : Tape (Mark F n (n+t)) z.1 × Mark F n (n+t)) :
    rawLeftView u (leftView z marks) = rawTrace u ⟨z,marks⟩ := by
  rcases z with ⟨k,a,p⟩
  simp only [rawLeftView,leftView,mapStopped,rawLocalPrefix_map,rawLocalAttempt_val,rawTrace]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X,Y a set; P ∈ 𝒟(X); y ∈ Y, assume X is finite; Y is finite. Then

(P ⊗ FiniteDistribution.pure(y)) = (((x ↦ (x, y)))_*P).
-/
private theorem prod_pure {X Y : Type*} [Fintype X] [Fintype Y]
    (P : FiniteDistribution X) (y : Y) : P.prod (FiniteDistribution.pure y) = P.map (fun x => (x,y)) := by
  classical
  ext ⟨x,z⟩
  simp [FiniteDistribution.prod,FiniteDistribution.joint,FiniteDistribution.pure,FiniteDistribution.map,FiniteDistribution.bind,ite_and,mul_ite]

/-- Direct deterministic observation of the real marked shortening execution. -/
/-
Mathematical definition (normal notation): For s ∈ F; fallback ∈ Fiber(F, n, s); left ∈ A → O → ∏_(u ∈ U(F, (n + t))) StoppedTape(AttemptSampler.Record(n = n, u)) → BL; right ∈ A → O → U(F, (n + t)) → RightView(F, n, (n + t)) → BR; o ∈ O × O; x ∈ Fiber(F, (n + t), s); α ∈ A, assume 2 ≤ n. define

rawShorteningExecution(fallback, left, right, o, x, α) := toFinite((((z ↦ (returnedOutput(fallback, x, (((z)₁)₂)₂), (α, (left(α, (o)₁, x.val.L, rawTrace(x.val.L, z)), right(α, (o)₂, x.val.R, rightView((z)₁)))))))_*fullTapeDistribution(x.val.L, x.val.R))).
-/
def rawShorteningExecution {s : F} (hn : 2 ≤ n) (fallback : Fiber F n s)
    (left : A → O → (u : U F (n+t)) → StoppedTape (AttemptSampler.Record (n := n) u) → BL)
    (right : A → O → U F (n+t) → RightView F n (n+t) → BR)
    (o : O × O) (x : Fiber F (n+t) s) (α : A) : FiniteDistribution (Fiber F n s × (A × (BL × BR))) :=
  toFinite ((fullTapeDistribution hn x.val.L x.val.R).map (fun z =>
    (returnedOutput fallback x z.1.2.2,
      (α,(left α o.1 x.val.L (rawTrace x.val.L z),right α o.2 x.val.R (rightView z.1))))))

/-- The complete raw-tape distribution is exactly the stochastic interface. The latter is obtained by marginalizing actual local sampler coins, rather than by postulating an input-independent auxiliary randomness distribution. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For s ∈ F; fallback ∈ Fiber(F, n, s); left ∈ A → O → ∏_(u ∈ U(F, (n + t))) StoppedTape(AttemptSampler.Record(n = n, u)) → BL; right ∈ A → O → U(F, (n + t)) → RightView(F, n, (n + t)) → BR; o ∈ O × O; x ∈ Fiber(F, (n + t), s); α ∈ A, assume 2 ≤ n. Then

rawShorteningExecution(fallback, left, right, o, x, α) = Fractional.shorteningExecution(fallback, leakageAnswerDistribution(markDistribution, leftObserver(left), right, o), x, α).
-/
theorem rawShorteningExecution_eq_distribution {s : F} (hn : 2 ≤ n) (fallback : Fiber F n s)
    (left : A → O → (u : U F (n+t)) → StoppedTape (AttemptSampler.Record (n := n) u) → BL)
    (right : A → O → U F (n+t) → RightView F n (n+t) → BR)
    (o : O × O) (x : Fiber F (n+t) s) (α : A) :
    rawShorteningExecution hn fallback left right o x α =
      Fractional.shorteningExecution hn fallback
        (leakageAnswerDistribution (markDistribution hn) (leftObserver left) right o) x α := by
  unfold rawShorteningExecution fullTapeDistribution
  rw [marked_observe_eq_distribution]
  unfold Fractional.shorteningExecution fullTapeAnswerDistribution
  congr 1
  funext z
  unfold leakageAnswerDistribution
  rw [prod_pure,FiniteDistribution.map_map,← toFinite_map,PMF.map_comp]
  congr 1
  congr 1
  funext marks
  simp only [Function.comp_def,leftObserver,rawLeftView_leftView]

end

end CircuitCompiler.Rectangular.Taped
