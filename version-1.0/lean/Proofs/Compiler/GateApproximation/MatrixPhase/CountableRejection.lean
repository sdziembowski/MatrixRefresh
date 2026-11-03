import Proofs.Compiler.GateApproximation.MatrixPhase.MarkedRejection
import Proofs.Compiler.GateApproximation.Shortening.RectangularPhysicalStochastic
import Proofs.Compiler.Construction.Parameters



/-!
# Direct rejection sampling from a countable proposal distribution

The mass of a stopped trace is the product of its actual proposal masses, with all earlier proposals rejected and the terminal one accepted. The normalization proof is geometric and does not require a finite proposal carrier. Acceptance-preserving maps commute with this entire retry distribution.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal Classical

namespace CircuitCompiler.Sampling.CountableRejection

open Refresh Unbounded

noncomputable section

variable {α β : Type*}

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ PMF(α); accept ∈ α → Bool, we have

0 ≤ probability(P, accept).
-/
theorem probability_nonneg (P : PMF α) (accept : α → Bool) : 0 ≤ probability P accept :=
  (toFinite (P.map accept)).nonneg true

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ PMF(α); accept ∈ α → Bool; t ∈ StoppedTape(α), assume 0 < probability(P, accept). Then

distribution(P, accept, t) = traceMass(P, accept, t).
-/
@[simp] theorem distribution_apply (P : PMF α) (accept : α → Bool) (hp : 0 < probability P accept)
    (t : StoppedTape α) : distribution P accept hp t = traceMass P accept t :=
  rfl

/- Mathematical definition (normal notation): Apply f coordinatewise to every proposal in a fixed-length tape, preserving the tape's order and length. -/
def mapTape (f : α → β) : (k : ℕ) → Tape α k → Tape β k
  | 0,_ => PUnit.unit
  | k+1,t => (f t.1,mapTape f k t.2)

/-
Mathematical definition (normal notation): For f ∈ α → β; t ∈ StoppedTape(α), define

mapStopped(f, t) := ((t)₁, (mapTape(f, (t)₁, ((t)₂)₁), f(((t)₂)₂))).
-/
def mapStopped (f : α → β) (t : StoppedTape α) : StoppedTape β :=
  ⟨t.1,(mapTape f t.1 t.2.1,f t.2.2)⟩

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ PMF(α); f ∈ α → β; accept ∈ β → Bool; y ∈ β, we have

(∑ₓ ({ rejectedMass(P, (accept ∘ f), x) if y = f(x),; 0 otherwise })) = rejectedMass((f_*P), accept, y).
-/
theorem rejectedMass_map (P : PMF α) (f : α → β) (accept : β → Bool) (y : β) :
    (∑' x, if y=f x then rejectedMass P (accept ∘ f) x else 0) =
      rejectedMass (P.map f) accept y := by
  rw [rejectedMass,PMF.map_apply]
  by_cases hy : accept y=true
  · simp only [hy,ite_true]
    apply ENNReal.tsum_eq_zero.mpr
    intro x
    by_cases hx : y=f x
    · simp [rejectedMass,Function.comp_def,← hx,hy]
    · simp [hx]
  · simp only [hy,ite_false]
    apply tsum_congr
    intro x
    by_cases hx : y=f x
    · simp [rejectedMass,Function.comp_def,← hx,hy]
    · simp [hx]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ PMF(α); f ∈ α → β; accept ∈ β → Bool; y ∈ β, we have

(∑ₓ ({ acceptedMass(P, (accept ∘ f), x) if y = f(x),; 0 otherwise })) = acceptedMass((f_*P), accept, y).
-/
theorem acceptedMass_map (P : PMF α) (f : α → β) (accept : β → Bool) (y : β) :
    (∑' x, if y=f x then acceptedMass P (accept ∘ f) x else 0) =
      acceptedMass (P.map f) accept y := by
  rw [acceptedMass,PMF.map_apply]
  by_cases hy : accept y=true
  · simp only [hy,ite_true]
    apply tsum_congr
    intro x
    by_cases hx : y=f x
    · simp [acceptedMass,Function.comp_def,← hx,hy]
    · simp [hx]
  · simp only [hy,ite_false]
    apply ENNReal.tsum_eq_zero.mpr
    intro x
    by_cases hx : y=f x
    · simp [acceptedMass,Function.comp_def,← hx,hy]
    · simp [hx]

/-- Pushforward of the unnormalized rejected-prefix distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ PMF(α); f ∈ α → β; accept ∈ β → Bool; k ∈ ℕ; y ∈ Tape(β, k), we have

(∑_(x ∈ Tape(α, k)) ({ prefixMass(P, (accept ∘ f), k, x) if y = mapTape(f, k, x),; 0 otherwise })) = prefixMass((f_*P), accept, k, y).
-/
theorem prefixMass_map (P : PMF α) (f : α → β) (accept : β → Bool)
    (k : ℕ) (y : Tape β k) :
    (∑' x : Tape α k, if y=mapTape f k x then prefixMass P (accept ∘ f) k x else 0) =
      prefixMass (P.map f) accept k y := by
  induction k with
  | zero => cases y; simp [Tape,mapTape,prefixMass]
  | succ k ih =>
      rcases y with ⟨y,ys⟩
      simp only [Tape,mapTape,prefixMass]
      rw [ENNReal.tsum_prod']
      have h (x : α) (xs : Tape α k) :
          (if (y,ys)=(f x,mapTape f k xs) then
            rejectedMass P (accept ∘ f) x * prefixMass P (accept ∘ f) k xs else 0) =
          (if y=f x then rejectedMass P (accept ∘ f) x else 0) *
            (if ys=mapTape f k xs then prefixMass P (accept ∘ f) k xs else 0) := by
        by_cases hx : y=f x <;> by_cases hs : ys=mapTape f k xs <;> simp [hx,hs]
      simp_rw [h,ENNReal.tsum_mul_left,ih,ENNReal.tsum_mul_right,rejectedMass_map]

/-- Pushforward of the complete fixed-length, unnormalized stopped distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ PMF(α); f ∈ α → β; accept ∈ β → Bool; k ∈ ℕ; y ∈ Tape(β, k) × β, we have

(∑_(x ∈ Tape(α, k) × α) ({ traceMass(P, (accept ∘ f), (k, x)) if y = (mapTape(f, k, (x)₁), f((x)₂)),; 0 otherwise })) = traceMass((f_*P), accept, (k, y)).
-/
theorem traceMass_map (P : PMF α) (f : α → β) (accept : β → Bool)
    (k : ℕ) (y : Tape β k × β) :
    (∑' x : Tape α k × α, if y=(mapTape f k x.1,f x.2) then
      traceMass P (accept ∘ f) ⟨k,x⟩ else 0) = traceMass (P.map f) accept ⟨k,y⟩ := by
  rcases y with ⟨ys,y⟩
  rw [ENNReal.tsum_prod']
  have h (xs : Tape α k) (x : α) :
      (if (ys,y)=(mapTape f k xs,f x) then traceMass P (accept ∘ f) ⟨k,(xs,x)⟩ else 0) =
      (if ys=mapTape f k xs then prefixMass P (accept ∘ f) k xs else 0) *
        (if y=f x then acceptedMass P (accept ∘ f) x else 0) := by
    by_cases hs : ys=mapTape f k xs <;> by_cases hx : y=f x <;> simp [traceMass,hx,hs]
  simp_rw [h,ENNReal.tsum_mul_left,acceptedMass_map,ENNReal.tsum_mul_right,prefixMass_map]
  rfl

/-- A deterministic proposal map preserving the acceptance test commutes with full unbounded rejection, including every failed proposal. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ PMF(α); f ∈ α → β; accept ∈ β → Bool, assume 0 < probability(P, (accept ∘ f)). Then

(mapStopped(f)_*distribution(P, (accept ∘ f))) = distribution((f_*P), accept).
-/
theorem distribution_map (P : PMF α) (f : α → β) (accept : β → Bool)
    (hp : 0 < probability P (accept ∘ f)) :
    (distribution P (accept ∘ f) hp).map (mapStopped f) =
      distribution (P.map f) accept (by rwa [probability_map]) := by
  classical
  apply PMF.ext
  rintro ⟨k,y⟩
  rw [PMF.map_apply,ENNReal.tsum_sigma']
  let mass : (j : ℕ) → Tape α j × α → ℝ≥0∞ := fun j x =>
    @ite ℝ≥0∞ ((⟨k,y⟩ : StoppedTape β)=mapStopped f ⟨j,x⟩)
      (Classical.propDecidable _) (distribution P (accept ∘ f) hp ⟨j,x⟩) 0
  change (∑' j, ∑' x, mass j x) = _
  have hoff (j : ℕ) (hj : j ≠ k) : (∑' x, mass j x) = 0 := by
    apply ENNReal.tsum_eq_zero.mpr
    intro x
    apply if_neg
    intro h
    have he := congrArg Sigma.fst h
    exact hj he.symm
  rw [tsum_eq_single k hoff]
  dsimp only [mass]
  simp only [distribution_apply,mapStopped,Sigma.mk.inj_iff,heq_eq_eq,true_and]
  exact traceMass_map P f accept k y

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool; k ∈ ℕ; t ∈ Tape(α, k), assume α is finite. Then

prefixMass(toPMF(P), accept, k, t) = ENNReal.ofReal(Unbounded.prefixWeight(P, accept, k, t)).
-/
theorem prefixMass_toPMF [Fintype α] (P : FiniteDistribution α) (accept : α → Bool)
    (k : ℕ) (t : Tape α k) :
    prefixMass (toPMF P) accept k t = ENNReal.ofReal (Unbounded.prefixWeight P accept k t) := by
  induction k with
  | zero => simp [prefixMass,Unbounded.prefixWeight]
  | succ k ih =>
      simp only [prefixMass,Unbounded.prefixWeight,ih,rejectedMass]
      cases hx : accept t.1
      · simp only [hx,Bool.false_eq_true,ite_false,toPMF_apply]
        exact (ENNReal.ofReal_mul (P.nonneg _)).symm
      · simp [hx]

/-- The generic distribution extends the previously checked finite-proposal distribution exactly. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For P ∈ 𝒟(α); accept ∈ α → Bool, assume α is finite; 0 < Sampling.acceptance(P, accept). Then

distribution(toPMF(P), accept) = Unbounded.distribution(P, accept).
-/
theorem distribution_toPMF [Fintype α] (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < Sampling.acceptance P accept) :
    distribution (toPMF P) accept (by rwa [probability_toPMF]) = Unbounded.distribution P accept hp := by
  apply PMF.ext
  intro t
  simp only [distribution_apply,Unbounded.distribution_apply,traceMass,Unbounded.traceWeight,prefixMass_toPMF,acceptedMass]
  cases hx : accept t.2.2
  · simp [hx]
  · simp only [hx,ite_true,toPMF_apply]
    exact (ENNReal.ofReal_mul (Unbounded.prefixWeight_nonneg P accept _ _)).symm

end

end CircuitCompiler.Sampling.CountableRejection
