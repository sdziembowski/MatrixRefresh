import Proofs.Compiler.GateApproximation.Shortening.RectangularCounts
import Proofs.Compiler.GateApproximation.Shortening.ShorteningTransport
import Proofs.Compiler.Construction.Parameters



/-!
# Reverse fibers and marginal preservation for rectangular shortening

The reverse operation draws a full-row-rank matrix and averages over a fiber of its right action. The identities here use finite uniform distributions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace CircuitCompiler.Rectangular

open Refresh MatrixRefresh

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Right multiplication permutes full-row-rank matrices. -/
/-
Mathematical definition (normal notation): Right multiplication by an invertible matrix M permutes the full-row-rank n × m matrices:

H↔ H · M.

The inverse multiplies by M⁻¹.
-/
def fullRankRightEquiv {n m : ℕ} (M : Refresh.«GL» F m) :
    FullRank F n m ≃ FullRank F n m where
  toFun H := ⟨H.val * M.val, fullRowRank_right H M⟩
  invFun H := ⟨H.val * (M⁻¹).val, fullRowRank_right H M⁻¹⟩
  left_inv H := by apply Subtype.ext; simp [Matrix.mul_assoc]
  right_inv H := by apply Subtype.ext; simp [Matrix.mul_assoc]

/-- Averaging the reverse left pullback preserves the uniform nonzero marginal. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ, assume U(F, n) ≠ ∅; FullRank(F, n, m) ≠ ∅; U(F, m) ≠ ∅. Then

(((p ↦ leftShare((p)₂, (p)₁)))_*𝒰_(U(F, n) × FullRank(F, n, m))) = 𝒰_(U(F, m)).
-/
theorem leftShare_uniform {n m : ℕ} [Nonempty (U F n)] [Nonempty (FullRank F n m)]
    [Nonempty (U F m)] :
    (FiniteDistribution.uniform : FiniteDistribution (U F n × FullRank F n m)).map
      (fun p => leftShare p.2 p.1) = (FiniteDistribution.uniform : FiniteDistribution (U F m)) := by
  classical
  let u₀ := Classical.choice (inferInstance : Nonempty (U F m))
  apply FiniteDistribution.uniform_map_of_fiber_card _
    (Fintype.card {p : U F n × FullRank F n m // leftShare p.2 p.1 = u₀})
  intro u
  obtain ⟨M,hM⟩ := exists_rowRefresh_eq u u₀
  let e : (U F n × FullRank F n m) ≃ (U F n × FullRank F n m) :=
    Equiv.prodCongr (Equiv.refl _) (fullRankRightEquiv M)
  apply Fintype.card_congr
  apply e.subtypeEquiv
  intro p
  have he : leftShare (e p).2 (e p).1 = rowRefresh (leftShare p.2 p.1) M := by
    apply Subtype.ext
    simp [e,fullRankRightEquiv,leftShare,rowRefresh,Matrix.vecMul_vecMul]
  rw [he, ← hM]
  constructor
  · intro h; rw [h]
  · intro h
    have hh := congrArg (fun x => rowRefresh x M⁻¹) h
    simpa [rowRefresh,Matrix.vecMul_vecMul] using hh

instance preimageFintype {n m : ℕ} (H : FullRank F n m) (r : U F n) :
    Fintype (Preimage H r) := Fintype.ofFinite _

instance preimageNonempty {n m : ℕ} (H : FullRank F n m) (r : U F n) :
    Nonempty (Preimage H r) :=
  ⟨(preimageEquivKernel H r).symm ⟨0,by simp⟩⟩

/-- Every nonzero right fiber has the same cardinality. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; H ∈ FullRank(F, n, (n + t)); r ∈ U(F, n), we have

|Preimage(H, r)| = (|F|)ᵗ.
-/
theorem preimage_card {n t : ℕ} (H : FullRank F n (n+t)) (r : U F n) :
    Fintype.card (Preimage H r) = fieldCard F ^ t :=
  (Fintype.card_congr (preimageEquivKernel H r)).trans (kernel_card H)

/-- Draw the full-row-rank matrix, the nonzero short right share, and a uniform long right share in its preimage. -/
/-
Mathematical definition (normal notation): For n, t ∈ ℕ, assume FullRank(F, n, (n + t)) ≠ ∅; U(F, n) ≠ ∅. define

rightReverseDistribution := bind(𝒰_(FullRank(F, n, (n + t))), (H ↦ bind(𝒰_(U(F, n)), (r ↦ (Subtype_*𝒰_(Preimage(H, r))))))).
-/
def rightReverseDistribution {n t : ℕ} [Nonempty (FullRank F n (n+t))] [Nonempty (U F n)] :
    FiniteDistribution (U F (n+t)) :=
  (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).bind fun H =>
    (FiniteDistribution.uniform : FiniteDistribution (U F n)).bind fun r =>
      (FiniteDistribution.uniform : FiniteDistribution (Preimage H r)).map Subtype.val

/-
Mathematical definition (normal notation): For F a set; n, m ∈ ℕ, assume F is a field. define

RightSample(n, m) := {p ∈ FullRank(F, n, m) × U(F, n) × U(F, m) | p.1.val.mulVec(((p)₂)₂) = ((p)₂)₁}.
-/
abbrev RightSample (F : Type*) [Field F] (n m : ℕ) :=
  {p : FullRank F n m × U F n × U F m // p.1.val.mulVec p.2.2.val = p.2.1.val}

instance rightSampleFintype (n m : ℕ) : Fintype (RightSample F n m) := Fintype.ofFinite _

/-- Simultaneous change of long coordinates preserves the reverse experiment. -/
/-
Mathematical definition (normal notation): For n, m ∈ ℕ; M ∈ GLₘ(F); p ∈ RightSample(F, n, m), define

rightSampleAction(M, p) := (fullRankRightEquiv(M, (p)₁), ((p)₂)₁, columnRefresh(((p)₂)₂, M)).
-/
def rightSampleAction {n m : ℕ} (M : Refresh.«GL» F m) (p : RightSample F n m) :
    RightSample F n m :=
  ⟨(fullRankRightEquiv M p.val.1,p.val.2.1,columnRefresh p.val.2.2 M), by
    change (p.val.1.val * M.val).mulVec ((M⁻¹).val.mulVec p.val.2.2.val) = p.val.2.1.val
    simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc] using p.property⟩

/- Mathematical definition (normal notation): For invertible M, simultaneously replacing H by H · M and its long preimage v by M⁻¹ · v permutes right-sampling records (H,r,v), preserving H · v = r. -/
def rightSampleEquiv {n m : ℕ} (M : Refresh.«GL» F m) :
    RightSample F n m ≃ RightSample F n m where
  toFun := rightSampleAction M
  invFun := rightSampleAction M⁻¹
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext; simp [rightSampleAction,fullRankRightEquiv,Matrix.mul_assoc]
    · apply Prod.ext
      · rfl
      · apply Subtype.ext; simp [rightSampleAction,columnRefresh,Matrix.mulVec_mulVec]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext; simp [rightSampleAction,fullRankRightEquiv,Matrix.mul_assoc]
    · apply Prod.ext
      · rfl
      · apply Subtype.ext; simp [rightSampleAction,columnRefresh,Matrix.mulVec_mulVec]

/- Mathematical definition (normal notation): Regard a right-sampling record as first a full-row-rank matrix H, then a nonzero short right share r, and then an element of the affine fiber H · v = r. This regrouping is a bijection. -/
def rightSampleSigmaEquiv (n m : ℕ) :
    RightSample F n m ≃ ((H : FullRank F n m) × (r : U F n) × Preimage H r) where
  toFun p := ⟨p.val.1,p.val.2.1,⟨p.val.2.2,p.property⟩⟩
  invFun p := ⟨(p.1,p.2.1,p.2.2.val),p.2.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance rightSampleNonempty {n m : ℕ} [Nonempty (U F n)] [Nonempty (FullRank F n m)] :
    Nonempty (RightSample F n m) := by
  let H := Classical.choice (inferInstance : Nonempty (FullRank F n m))
  let r := Classical.choice (inferInstance : Nonempty (U F n))
  let v := Classical.choice (inferInstance : Nonempty (Preimage H r))
  exact ⟨⟨(H,r,v.val),v.property⟩⟩

/-- Transitivity on right shares, obtained from transitivity on label-one pairs. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; v, w ∈ U(F, m), we have

∃ M ∈ GLₘ(F), columnRefresh(v, M) = w .
-/
theorem exists_columnRefresh_eq {m : ℕ} (v w : U F m) :
    ∃ M : Refresh.«GL» F m, columnRefresh v M = w := by
  obtain ⟨a,ha⟩ := exists_dot_one v
  obtain ⟨b,hb⟩ := exists_dot_one w
  let a' : U F m := ⟨a,by intro h; simp [h,dot] at ha⟩
  let b' : U F m := ⟨b,by intro h; simp [h,dot] at hb⟩
  obtain ⟨M,hM⟩ := refresh_transitive (⟨a',v⟩ : State F m) (⟨b',w⟩ : State F m)
    (by change dot a v.val = dot b w.val; rw [dot_comm a, dot_comm b,ha,hb])
  exact ⟨M,congrArg State.R hM⟩

/-- Uniform valid reverse triples have uniform long right marginal. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ, assume U(F, n) ≠ ∅; FullRank(F, n, m) ≠ ∅; U(F, m) ≠ ∅. Then

(((p ↦ ((p)₂)₂))_*𝒰_(RightSample(F, n, m))) = 𝒰_(U(F, m)).
-/
theorem rightSample_uniform {n m : ℕ} [Nonempty (U F n)] [Nonempty (FullRank F n m)]
    [Nonempty (U F m)] :
    (FiniteDistribution.uniform : FiniteDistribution (RightSample F n m)).map (fun p => p.val.2.2) =
      (FiniteDistribution.uniform : FiniteDistribution (U F m)) := by
  classical
  let v₀ := Classical.choice (inferInstance : Nonempty (U F m))
  apply FiniteDistribution.uniform_map_of_fiber_card _
    (Fintype.card {p : RightSample F n m // p.val.2.2 = v₀})
  intro v
  obtain ⟨M,hM⟩ := exists_columnRefresh_eq v v₀
  apply Fintype.card_congr
  apply (rightSampleEquiv M).subtypeEquiv
  intro p
  change p.val.2.2 = v ↔ columnRefresh p.val.2.2 M = v₀
  rw [← hM]
  constructor
  · intro h; rw [h]
  · intro h
    have hh := congrArg (fun x => columnRefresh x M⁻¹) h
    simpa [columnRefresh,Matrix.mulVec_mulVec] using hh

/-- The actual sequential reverse sampler has exactly the uniform long right marginal; averaging over matrices removes the individual fiber bias. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ, assume FullRank(F, n, (n + t)) ≠ ∅; U(F, n) ≠ ∅; U(F, (n + t)) ≠ ∅. Then

rightReverseDistribution(F = F, n = n, t = t) = 𝒰_(U(F, (n + t))).
-/
theorem rightReverseDistribution_uniform {n t : ℕ} [Nonempty (FullRank F n (n+t))]
    [Nonempty (U F n)] [Nonempty (U F (n+t))] :
    rightReverseDistribution (F := F) (n := n) (t := t) =
      (FiniteDistribution.uniform : FiniteDistribution (U F (n+t))) := by
  classical
  let H₀ := Classical.choice (inferInstance : Nonempty (FullRank F n (n+t)))
  let r₀ := Classical.choice (inferInstance : Nonempty (U F n))
  let J := fun H : FullRank F n (n+t) => (r : U F n) × Preimage H r
  letI : ∀ H, Nonempty (J H) := fun H =>
    ⟨⟨r₀,Classical.choice (inferInstance : Nonempty (Preimage H r₀))⟩⟩
  letI : Nonempty ((H : FullRank F n (n+t)) × J H) :=
    ⟨⟨H₀,Classical.choice (inferInstance : Nonempty (J H₀))⟩⟩
  have hc (H : FullRank F n (n+t)) : Fintype.card (J H) = Fintype.card (J H₀) := by
    simp [J,Fintype.card_sigma,preimage_card]
  have hout := uniform_sigma_bind (J := J) H₀ hc
  have hin (H : FullRank F n (n+t)) := uniform_sigma_bind
    (J := fun r => Preimage H r) r₀ (fun r => by simp [preimage_card])
  have hu := rightSample_uniform (F := F) (n := n) (m := n+t)
  rw [← uniform_equiv (rightSampleSigmaEquiv (F := F) n (n+t)).symm,
    FiniteDistribution.map_map, ← hout, FiniteDistribution.map_bind] at hu
  simp only [FiniteDistribution.map_map] at hu
  simp_rw [← hin, FiniteDistribution.map_bind, FiniteDistribution.map_map] at hu
  exact hu

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; H ∈ FullRank(F, n, m); r ∈ U(F, n), we have

(rightLift(H, r)_*𝒰_(Kernel(H))) = (Subtype_*𝒰_(Preimage(H, r))).
-/
theorem rightLift_uniform {n m : ℕ} (H : FullRank F n m) (r : U F n) :
    (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).map (rightLift H r) =
      (FiniteDistribution.uniform : FiniteDistribution (Preimage H r)).map Subtype.val := by
  rw [← uniform_equiv (preimageEquivKernel H r).symm, FiniteDistribution.map_map]
  rfl

/-- Left energy is preserved after averaging over the matrix. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; f ∈ U(F, m) → ℝ, assume U(F, n) ≠ ∅; FullRank(F, n, m) ≠ ∅; U(F, m) ≠ ∅. Then

𝔼_(H ← 𝒰_(FullRank(F, n, m))) [𝔼_(a ← 𝒰_(U(F, n))) [f(leftShare(H, a))]] = 𝔼_(x ← 𝒰_(U(F, m))) [f(x)].
-/
theorem left_pullback_expect {n m : ℕ} [Nonempty (U F n)] [Nonempty (FullRank F n m)]
    [Nonempty (U F m)] (f : U F m → ℝ) :
    (FiniteDistribution.uniform : FiniteDistribution (FullRank F n m)).expect (fun H =>
      (FiniteDistribution.uniform : FiniteDistribution (U F n)).expect (fun a => f (leftShare H a))) =
      (FiniteDistribution.uniform : FiniteDistribution (U F m)).expect f := by
  have h := congrArg (fun P : FiniteDistribution (U F m) => P.expect f)
    (leftShare_uniform (F := F) (n := n) (m := m))
  try dsimp only at h
  rw [expect_map, Shortening.uniform_prod, expect_prod] at h
  rw [expect_comm]
  exact h

/-- Right energy is preserved after averaging over the matrix and its fibers. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; f ∈ U(F, (n + t)) → ℝ, assume FullRank(F, n, (n + t)) ≠ ∅; U(F, n) ≠ ∅; U(F, (n + t)) ≠ ∅. Then

𝔼_(H ← 𝒰_(FullRank(F, n, (n + t)))) [𝔼_(r ← 𝒰_(U(F, n))) [𝔼_(k ← 𝒰_(Kernel(H))) [f(rightLift(H, r, k))]]] = 𝔼_(ξ ← 𝒰_(U(F, (n + t)))) [f(ξ)].
-/
theorem right_pullback_expect {n t : ℕ} [Nonempty (FullRank F n (n+t))]
    [Nonempty (U F n)] [Nonempty (U F (n+t))] (f : U F (n+t) → ℝ) :
    (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
      (FiniteDistribution.uniform : FiniteDistribution (U F n)).expect (fun r =>
        (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect (fun k => f (rightLift H r k)))) =
      (FiniteDistribution.uniform : FiniteDistribution (U F (n+t))).expect f := by
  have h := congrArg (fun P : FiniteDistribution (U F (n+t)) => P.expect f)
    (rightReverseDistribution_uniform (F := F) (n := n) (t := t))
  simp only [rightReverseDistribution,expect_bind,expect_map] at h
  have he (H : FullRank F n (n+t)) (r : U F n) :=
    congrArg (fun P : FiniteDistribution (U F (n+t)) => P.expect f) (rightLift_uniform H r)
  simp only [expect_map] at he
  simp_rw [he]
  exact h

end

end CircuitCompiler.Rectangular
