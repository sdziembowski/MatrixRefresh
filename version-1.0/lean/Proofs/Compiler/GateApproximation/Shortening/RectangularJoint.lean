import Proofs.Compiler.GateApproximation.Shortening.RectangularReverse
import Proofs.Compiler.Construction.Parameters



/-!
# Joint reverse distribution on an inner-product fiber
-/
set_option autoImplicit false

set_option maxHeartbeats 1500000

open scoped BigOperators

namespace CircuitCompiler.Rectangular

open Refresh MatrixRefresh

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

instance backwardFintype (n m : ℕ) (s : F) : Fintype (Backward F n m s) := Fintype.ofFinite _

/-
Mathematical definition (normal notation): For n, m ∈ ℕ; s ∈ F; M ∈ GLₘ(F); p ∈ Backward(F, n, m, s), define

backwardAction(M, p) := ((p)₁, fullRankRightEquiv(M, ((p)₂)₁), columnRefresh(((p)₂)₂, M)).
-/
def backwardAction {n m : ℕ} {s : F} (M : Refresh.«GL» F m) (p : Backward F n m s) :
    Backward F n m s :=
  ⟨(p.val.1, fullRankRightEquiv M p.val.2.1, columnRefresh p.val.2.2 M), by
    change (p.val.2.1.val * M.val).mulVec ((M⁻¹).val.mulVec p.val.2.2.val) = p.val.1.val.R.val
    simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc] using p.property⟩

/-
Mathematical definition (normal notation): For any invertible long matrix M, the action

((a,r),H,v) ↦ ((a,r),H · M,M⁻¹ · v)

permutes reverse records of a fixed secret. It preserves the short output because (H · M) · (M⁻¹ · v) = H · v.
-/
def backwardEquiv {n m : ℕ} {s : F} (M : Refresh.«GL» F m) :
    Backward F n m s ≃ Backward F n m s where
  toFun := backwardAction M
  invFun := backwardAction M⁻¹
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext; simp [backwardAction,fullRankRightEquiv,Matrix.mul_assoc]
      · apply Subtype.ext; simp [backwardAction,columnRefresh,Matrix.mulVec_mulVec]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext; simp [backwardAction,fullRankRightEquiv,Matrix.mul_assoc]
      · apply Subtype.ext; simp [backwardAction,columnRefresh,Matrix.mulVec_mulVec]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; s ∈ F; M ∈ GLₘ(F); p ∈ Backward(F, n, m, s), we have

backwardSource(backwardAction(M, p)) = refreshInFiber(backwardSource(p), M).
-/
theorem backwardSource_action {n m : ℕ} {s : F} (M : Refresh.«GL» F m)
    (p : Backward F n m s) :
    backwardSource (backwardAction M p) = refreshInFiber (backwardSource p) M := by
  apply Subtype.ext
  apply State.ext
  · apply Subtype.ext
    simp [backwardSource,backwardAction,leftShare,fullRankRightEquiv,
      refreshInFiber,refresh,rowRefresh,Matrix.vecMul_vecMul]
  · rfl

/- Mathematical definition (normal notation): A reverse record is equivalently a triple consisting of a short encoding (a,r) of s, a full-row-rank matrix H, and a long nonzero vector v in the affine fiber H · v = r. The bijection changes only the grouping of these data. -/
def backwardSigmaEquiv {n m : ℕ} (s : F) :
    Backward F n m s ≃
      ((p : Fiber F n s) × (H : FullRank F n m) × Preimage H p.val.R) where
  toFun p := ⟨p.val.1,p.val.2.1,⟨p.val.2.2,p.property⟩⟩
  invFun p := ⟨(p.1,p.2.1,p.2.2.val),p.2.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance backwardNonempty {n m : ℕ} {s : F} [Nonempty (Fiber F n s)]
    [Nonempty (FullRank F n m)] : Nonempty (Backward F n m s) := by
  let p := Classical.choice (inferInstance : Nonempty (Fiber F n s))
  let H := Classical.choice (inferInstance : Nonempty (FullRank F n m))
  let v := Classical.choice (inferInstance : Nonempty (Preimage H p.val.R))
  exact ⟨⟨(p,H,v.val),v.property⟩⟩

/-- Uniform reverse triples have the uniform long encoding as their source. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; s ∈ F, assume Fiber(F, n, s) ≠ ∅; FullRank(F, n, m) ≠ ∅; Fiber(F, m, s) ≠ ∅. Then

(backwardSource_*𝒰_(Backward(F, n, m, s))) = 𝒰_(Fiber(F, m, s)).
-/
theorem backwardSource_uniform {n m : ℕ} (s : F) [Nonempty (Fiber F n s)]
    [Nonempty (FullRank F n m)] [Nonempty (Fiber F m s)] :
    (FiniteDistribution.uniform : FiniteDistribution (Backward F n m s)).map backwardSource =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F m s)) := by
  classical
  let x₀ := Classical.choice (inferInstance : Nonempty (Fiber F m s))
  apply FiniteDistribution.uniform_map_of_fiber_card _
    (Fintype.card {p : Backward F n m s // backwardSource p = x₀})
  intro x
  obtain ⟨M,hM⟩ := refresh_transitive x.val x₀.val (x.property.trans x₀.property.symm)
  have hMx : refreshInFiber x M = x₀ := Subtype.ext hM
  apply Fintype.card_congr
  apply (backwardEquiv M).subtypeEquiv
  intro p
  change backwardSource p = x ↔ backwardSource (backwardAction M p) = x₀
  rw [backwardSource_action, ← hMx]
  constructor
  · intro h; rw [h]
  · intro h
    have hh := congrArg (fun y => refreshInFiber y M⁻¹) h
    simpa [refreshInFiber,refresh_mul] using hh

/-- Joint reverse averaging preserves the exact inner-product fiber distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; s ∈ F; f ∈ Fiber(F, (n + t), s) → ℝ, assume Fiber(F, n, s) ≠ ∅; FullRank(F, n, (n + t)) ≠ ∅; Fiber(F, (n + t), s) ≠ ∅. Then

𝔼_(p ← 𝒰_(Fiber(F, n, s))) [𝔼_(H ← 𝒰_(FullRank(F, n, (n + t)))) [𝔼_(v ← 𝒰_(Preimage(H, p.val.R))) [f(backwardSource(((p, H, v), v.property)))]]] = 𝔼_(ω ← 𝒰_(Fiber(F, (n + t), s))) [f(ω)].
-/
theorem backward_expect {n t : ℕ} (s : F) [Nonempty (Fiber F n s)]
    [Nonempty (FullRank F n (n+t))] [Nonempty (Fiber F (n+t) s)]
    (f : Fiber F (n+t) s → ℝ) :
    (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s)).expect (fun p =>
      (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
        (FiniteDistribution.uniform : FiniteDistribution (Preimage H p.val.R)).expect (fun v =>
          f (backwardSource ⟨(p,H,v.val),v.property⟩)))) =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) s)).expect f := by
  classical
  let p₀ := Classical.choice (inferInstance : Nonempty (Fiber F n s))
  let H₀ := Classical.choice (inferInstance : Nonempty (FullRank F n (n+t)))
  let J := fun p : Fiber F n s => (H : FullRank F n (n+t)) × Preimage H p.val.R
  letI : ∀ p, Nonempty (J p) := fun p => ⟨⟨H₀,Classical.choice inferInstance⟩⟩
  letI : Nonempty ((p : Fiber F n s) × J p) := ⟨⟨p₀,Classical.choice inferInstance⟩⟩
  have hc (p : Fiber F n s) : Fintype.card (J p) = Fintype.card (J p₀) := by
    simp [J,Fintype.card_sigma,preimage_card]
  have hout := uniform_sigma_bind (J := J) p₀ hc
  have hin (p : Fiber F n s) := uniform_sigma_bind
    (J := fun H : FullRank F n (n+t) => Preimage H p.val.R) H₀
      (fun H => by simp [preimage_card])
  have hu := backwardSource_uniform (F := F) (n := n) (m := n+t) s
  rw [← uniform_equiv (backwardSigmaEquiv (F := F) (n := n) (m := n+t) s).symm,
    FiniteDistribution.map_map, ← hout, FiniteDistribution.map_bind] at hu
  simp only [FiniteDistribution.map_map] at hu
  simp_rw [← hin, FiniteDistribution.map_bind, FiniteDistribution.map_map] at hu
  have h := congrArg (fun P : FiniteDistribution (Fiber F (n+t) s) => P.expect f) hu
  simpa! only [expect_bind,expect_map,Function.comp_def,backwardSigmaEquiv,
    Equiv.coe_fn_symm_mk] using h

/-- Reverse source parameterized by a uniform kernel vector. -/
/-
Mathematical definition (normal notation): For n, m ∈ ℕ; s ∈ F; p ∈ Fiber(F, n, s); H ∈ FullRank(F, n, m); k ∈ Kernel(H), define

liftedSource(p, H, k) := backwardSource((p, H, (preimageEquivKernel(H, p.val.R))⁻¹(k))).
-/
def liftedSource {n m : ℕ} {s : F} (p : Fiber F n s) (H : FullRank F n m)
    (k : Kernel H) : Fiber F m s :=
  backwardSource ⟨(p,H,((preimageEquivKernel H p.val.R).symm k).val),
    ((preimageEquivKernel H p.val.R).symm k).property⟩

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; s ∈ F; f ∈ Fiber(F, (n + t), s) → ℝ, assume Fiber(F, n, s) ≠ ∅; FullRank(F, n, (n + t)) ≠ ∅; Fiber(F, (n + t), s) ≠ ∅. Then

𝔼_(p ← 𝒰_(Fiber(F, n, s))) [𝔼_(H ← 𝒰_(FullRank(F, n, (n + t)))) [𝔼_(k ← 𝒰_(Kernel(H))) [f(liftedSource(p, H, k))]]] = 𝔼_(ω ← 𝒰_(Fiber(F, (n + t), s))) [f(ω)].
-/
theorem backward_expect_kernel {n t : ℕ} (s : F) [Nonempty (Fiber F n s)]
    [Nonempty (FullRank F n (n+t))] [Nonempty (Fiber F (n+t) s)]
    (f : Fiber F (n+t) s → ℝ) :
    (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s)).expect (fun p =>
      (FiniteDistribution.uniform : FiniteDistribution (FullRank F n (n+t))).expect (fun H =>
        (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect (fun k => f (liftedSource p H k)))) =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) s)).expect f := by
  have h := backward_expect s f
  have he (p : Fiber F n s) (H : FullRank F n (n+t)) :=
    congrArg (fun P : FiniteDistribution (Preimage H p.val.R) =>
      P.expect (fun v => f (backwardSource ⟨(p,H,v.val),v.property⟩)))
      (uniform_equiv (preimageEquivKernel H p.val.R).symm)
  simp only [expect_map] at he
  change ∀ p H, (FiniteDistribution.uniform : FiniteDistribution (Kernel H)).expect
    (fun k => f (liftedSource p H k)) = _ at he
  simp_rw [he]
  exact h

end

end CircuitCompiler.Rectangular
