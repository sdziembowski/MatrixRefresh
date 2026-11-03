import Proofs.Compiler.GateApproximation.MatrixPhase.CountableRejection
import Proofs.Compiler.GateApproximation.Shortening.RectangularTapedSampler
import Proofs.Compiler.Construction.Parameters



/-!
# Direct raw-record rejection semantics of rectangular shortening

The marked representation used in the proof is exactly an ordinary uncapped rejection loop whose proposals are the actual row/completion sampler records. The equality below retains every raw private tape, including failed attempts.
-/
set_option autoImplicit false

set_option maxHeartbeats 2800000

open scoped BigOperators ENNReal Classical

namespace CircuitCompiler.Sampling.Unbounded

open Refresh

noncomputable section

variable {α β : Type*}

/-- Interleave the proposal and private-mark coordinates of a finite prefix. -/
/-
Mathematical definition (normal notation): Combine two length-k tapes coordinatewise:

(a₁,…,aₖ),(b₁,…,bₖ) ↦ ((a₁,b₁),…,(aₖ,bₖ)).
-/
def zipTapes : (k : ℕ) → Tape α k → Tape β k → Tape (α × β) k
  | 0,_,_ => PUnit.unit
  | k+1,a,b => ((a.1,b.1),zipTapes k a.2 b.2)

/-
Mathematical definition (normal notation): Split a length-k tape of pairs into its two coordinate tapes:

((a₁,b₁),…,(aₖ,bₖ)) ↦ ((a₁,…,aₖ),(b₁,…,bₖ)).
-/
def unzipTapes : (k : ℕ) → Tape (α × β) k → Tape α k × Tape β k
  | 0,_ => (PUnit.unit,PUnit.unit)
  | k+1,t => ((t.1.1,(unzipTapes k t.2).1),(t.1.2,(unzipTapes k t.2).2))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For k ∈ ℕ; a ∈ Tape(α, k); b ∈ Tape(β, k), we have

unzipTapes(k, zipTapes(k, a, b)) = (a, b).
-/
@[simp] theorem unzip_zipTapes (k : ℕ) (a : Tape α k) (b : Tape β k) :
    unzipTapes k (zipTapes k a b) = (a,b) := by
  induction k with
  | zero => cases a; cases b; rfl
  | succ k ih => rcases a with ⟨a,as⟩; rcases b with ⟨b,bs⟩; simp only [zipTapes,unzipTapes,ih]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For k ∈ ℕ; z ∈ Tape((α × β), k), we have

zipTapes(k, (unzipTapes(k, z))₁, (unzipTapes(k, z))₂) = z.
-/
@[simp] theorem zip_unzipTapes (k : ℕ) (z : Tape (α × β) k) :
    zipTapes k (unzipTapes k z).1 (unzipTapes k z).2 = z := by
  induction k with
  | zero => cases z; rfl
  | succ k ih => rcases z with ⟨⟨a,b⟩,zs⟩; simp only [zipTapes,unzipTapes,ih] <;> rfl

/-- A marked trace is just an ordinary trace of enriched proposals. -/
/- Mathematical definition (normal notation): A stopped tape with one mark for each rejected and accepted proposal is equivalent to a stopped tape of proposal/mark pairs. The bijection pairs the two prefixes coordinatewise and pairs the final accepted proposal with its final mark. -/
def markedTapeEquiv : MarkedTape α β ≃ StoppedTape (α × β) where
  toFun z := ⟨z.1.1,(zipTapes z.1.1 z.1.2.1 z.2.1,(z.1.2.2,z.2.2))⟩
  invFun z := ⟨⟨z.1,((unzipTapes z.1 z.2.1).1,z.2.2.1)⟩,
    ((unzipTapes z.1 z.2.1).2,z.2.2.2)⟩
  left_inv z := by
    rcases z with ⟨⟨k,a,p⟩,b,q⟩
    exact congrArg (fun ab : Tape α k × Tape β k =>
      (⟨⟨k,(ab.1,p)⟩,(ab.2,q)⟩ : MarkedTape α β)) (unzip_zipTapes k a b)
  right_inv z := by
    rcases z with ⟨k,z,⟨a,b⟩⟩
    simp only [zip_unzipTapes]



-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X,Y a set; P ∈ PMF(X); e ∈ X ≃ Y; y ∈ Y, we have

map(P)(e, y) = P((e)⁻¹(y)) .
-/
private theorem pmf_map_equiv_apply {X Y : Type*} (P : PMF X) (e : X ≃ Y) (y : Y) :
    (P.map e) y = P (e.symm y) := by
  rw [PMF.map_apply,tsum_eq_single (e.symm y)]
  · simp
  · intro x hx
    apply if_neg
    intro h
    exact hx (e.injective (h.symm.trans (e.apply_symm_apply y).symm))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; R ∈ α → PMF(β); k ∈ ℕ; a ∈ Tape(α, k); b ∈ Tape(β, k), assume α is finite. Then

CountableRejection.prefixMass(enrichedProposal(P, R), (accept ∘ (Prod)₁), k, zipTapes(k, a, b)) = ENNReal.ofReal(prefixWeight(P, accept, k, a)) · prefixMarks(R, k, a, b).
-/
theorem enriched_prefixMass [Fintype α] (P : FiniteDistribution α) (accept : α → Bool)
    (R : α → PMF β) (k : ℕ) (a : Tape α k) (b : Tape β k) :
    CountableRejection.prefixMass (enrichedProposal P R) (accept ∘ Prod.fst) k (zipTapes k a b) =
      ENNReal.ofReal (prefixWeight P accept k a) * prefixMarks R k a b := by
  induction k with
  | zero =>
      cases a
      cases b
      simp only [CountableRejection.prefixMass, prefixWeight, prefixMarks,
        ENNReal.ofReal_one, one_mul]
      exact (PMF.pure_apply_self _).symm
  | succ k ih =>
      rcases a with ⟨a,as⟩
      rcases b with ⟨b,bs⟩
      change (if accept a then 0 else enrichedProposal P R (a,b)) *
        CountableRejection.prefixMass (enrichedProposal P R) (accept ∘ Prod.fst) k (zipTapes k as bs) =
        ENNReal.ofReal ((if accept a then 0 else P.weight a) * prefixWeight P accept k as) *
          (R a b * prefixMarks R k as bs)
      rw [ih]
      cases ha : accept a
      · simp only [ha,Bool.false_eq_true,if_false,enrichedProposal_apply,toPMF_apply]
        rw [ENNReal.ofReal_mul (P.nonneg a)]
        ring
      · simp [ha]

/-- Exact equality with direct countable iid rejection, including zero masses for invalid traces. No leakage-specific premise enters this equivalence. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; R ∈ α → PMF(β), assume α is finite; 0 < acceptance(P, accept). Then

(markedTapeEquiv_*markedDistribution(P, accept, R)) = CountableRejection.distribution(enrichedProposal(P, R), (accept ∘ (Prod)₁)).
-/
theorem markedDistribution_eq_countable [Fintype α] (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) (R : α → PMF β) :
    (markedDistribution P accept hp R).map markedTapeEquiv =
      CountableRejection.distribution (enrichedProposal P R) (accept ∘ Prod.fst)
        (by rw [enrichedProposal_probability]; exact hp) := by
  apply PMF.ext
  intro t
  obtain ⟨z,rfl⟩ := (markedTapeEquiv (α := α) (β := β)).surjective t
  rw [pmf_map_equiv_apply,Equiv.symm_apply_apply,markedDistribution_apply,distribution_apply,
    CountableRejection.distribution_apply]
  rcases z with ⟨⟨k,a,p⟩,b,q⟩
  change ENNReal.ofReal (prefixWeight P accept k a * (if accept p then P.weight p else 0)) *
      prefixMarks R k a b * R p q =
    CountableRejection.prefixMass (enrichedProposal P R) (accept ∘ Prod.fst) k (zipTapes k a b) *
      (if accept p then enrichedProposal P R (p,q) else 0)
  rw [enriched_prefixMass]
  cases h : accept p
  · simp [h]
  · simp only [h,if_true,enrichedProposal_apply,toPMF_apply]
    rw [ENNReal.ofReal_mul (prefixWeight_nonneg P accept k a)]
    ring

end

end CircuitCompiler.Sampling.Unbounded

namespace CircuitCompiler.Rectangular.Taped

open Refresh MatrixRefresh Sampling Sampling.Unbounded

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n t : ℕ}

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u ∈ U(F, (n + t)); k ∈ ℕ; a ∈ Tape(Attempt(n = n, u), k); b ∈ Tape(Mark(F, n, (n + t)), k), we have

rawPrefix(u, k, a, b) = CountableRejection.mapTape(((pm ↦ rawAttempt(u, (pm)₁, (pm)₂))), k, zipTapes(k, a, b)).
-/
theorem rawPrefix_eq_map_zip (u : U F (n+t)) (k : ℕ)
    (a : Tape (Attempt (n := n) u) k) (b : Tape (Mark F n (n+t)) k) :
    rawPrefix u k a b = CountableRejection.mapTape (fun pm => rawAttempt u pm.1 pm.2)
      k (zipTapes k a b) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rawPrefix,zipTapes,CountableRejection.mapTape,ih] <;> rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u ∈ U(F, (n + t)), we have

rawTrace(u) = CountableRejection.mapStopped(((pm ↦ rawAttempt(u, (pm)₁, (pm)₂)))) ∘ markedTapeEquiv .
-/
theorem rawTrace_eq_map_flatten (u : U F (n+t)) :
    rawTrace u = CountableRejection.mapStopped (fun pm => rawAttempt u pm.1 pm.2) ∘ markedTapeEquiv := by
  funext z
  rcases z with ⟨⟨k,a,p⟩,b,q⟩
  simp only [rawTrace,CountableRejection.mapStopped,markedTapeEquiv,Equiv.coe_fn_mk,
    Function.comp_def,rawPrefix_eq_map_zip]

/-- The analytic marked model is exactly the direct uncapped implementation on complete raw sampler records. This is equality of whole trace distributions, so it holds simultaneously for every possible finite leakage observation. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For u, v ∈ U(F, (n + t)), assume 2 ≤ n. Then

(rawTrace(u)_*fullTapeDistribution(u, v)) = rawRetryDistribution(u, v).
-/
theorem fullTapeDistribution_rawTrace (hn : 2 ≤ n) (u v : U F (n+t)) :
    (fullTapeDistribution hn u v).map (rawTrace u) = rawRetryDistribution hn u v := by
  rw [rawTrace_eq_map_flatten,← PMF.map_comp]
  unfold fullTapeDistribution
  rw [markedDistribution_eq_countable]
  have he : rawAccept u v ∘ (fun pm : Attempt (n := n) u × Mark F n (n+t) =>
      rawAttempt u pm.1 pm.2) = (fun p => decide (rightOutput v p ≠ 0)) ∘ Prod.fst := by
    funext pm
    exact rawAccept_rawAttempt u v pm.1 pm.2
  have hp : 0 < CountableRejection.probability
      (enrichedProposal (attemptDistribution hn u) (fun p => markDistribution hn u p.val.1))
      (rawAccept u v ∘ (fun pm => rawAttempt u pm.1 pm.2)) := by
    rw [he,enrichedProposal_probability]
    exact attempt_acceptance_pos hn u v
  have hlaw : CountableRejection.distribution
      (enrichedProposal (attemptDistribution hn u) (fun p => markDistribution hn u p.val.1))
      ((fun p => decide (rightOutput v p ≠ 0)) ∘ Prod.fst)
      (by rw [enrichedProposal_probability]; exact attempt_acceptance_pos hn u v) =
    CountableRejection.distribution
      (enrichedProposal (attemptDistribution hn u) (fun p => markDistribution hn u p.val.1))
      (rawAccept u v ∘ (fun pm => rawAttempt u pm.1 pm.2)) hp := by
    apply PMF.ext
    intro z
    simp only [CountableRejection.distribution_apply,he]
  rw [hlaw,CountableRejection.distribution_map]
  apply PMF.ext
  intro z
  simp only [CountableRejection.distribution_apply,rawRetryDistribution,raw_proposal_distribution]

end

end CircuitCompiler.Rectangular.Taped
