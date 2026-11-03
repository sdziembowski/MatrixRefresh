import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.InitialDistribution
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Transitivity
import Proofs.Compiler.Construction.Parameters



set_option autoImplicit false

namespace Refresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Matrices giving a specified fiber-valued refresh output are exactly the matrices in the corresponding transporter set. -/
/- Mathematical definition (normal notation): Identify the matrices sending the fiber element x to y with the transporter set between their underlying encoding states. This map leaves the matrix unchanged and only forgets or restores the fiber membership certificates. -/
def outputFiberEquivTransporter {n : ℕ} {s : F} (x y : Fiber F n s) :
    {M : Refresh.«GL» F n // refreshInFiber x M = y} ≃ Transporter x.val y.val where
  toFun M := ⟨M.val, congrArg Subtype.val M.property⟩
  invFun M := ⟨M.val, Subtype.ext M.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- All output points in the same secret fiber have equally many realizing matrices. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F; x, y ∈ Fiber(F, n, s), we have

|Transporter(x, y)| = |Transporter(x, x)|.
-/
theorem transporter_card_eq {n : ℕ} {s : F} (x y : Fiber F n s) :
    Fintype.card (Transporter x.val y.val) = Fintype.card (Transporter x.val x.val) :=
  transporter_card_eq_of_secret_eq x.val y.val x.val (y.property.trans x.property.symm)

/-- L2.19, fixed-input freshness: uniform independent matrix sampling completely refreshes a fixed input. -/

/- Mathematical statement (normal notation): Fix any encoding in a nonempty fiber {(ℓ,r):ℓ · r = s}. Applying a uniformly random invertible refresh matrix produces the uniform distribution on that entire fiber. -/
theorem refresh_uniform_fiber {n : ℕ} {s : F} [Nonempty (Fiber F n s)] (x : Fiber F n s) :
    (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F n)).map (refreshInFiber x) =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s)) := by
  apply FiniteDistribution.uniform_map_of_fiber_card _ (Fintype.card (Transporter x.val x.val))
  intro y
  rw [Fintype.card_congr (outputFiberEquivTransporter x y)]
  exact transporter_card_eq x y

/-- Exact freshness on the shared ambient state carrier, with no transitivity hypothesis. -/

/-
Mathematical statement (normal notation): Let n ≥ 2 and fix nonzero shares (ℓ,r) with ℓ · r = s. For a uniformly sampled invertible matrix M, the refreshed pair

(ℓ · M,M⁻¹ · r)

is distributed exactly as μₛ, the uniform distribution on all nonzero-share encodings of s.
-/
theorem refresh_uniform {n : ℕ} (hn : 2 ≤ n) (s : F) (x : State F n) (hx : secret x = s) :
    (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F n)).map (refresh x) = mu F n hn s := by
  letI := fiber_nonempty F n hn s
  have h := congrArg (fun P : FiniteDistribution (Fiber F n s) => P.map Subtype.val)
    (refresh_uniform_fiber (⟨x, hx⟩ : Fiber F n s))
  try dsimp only at h
  rw [FiniteDistribution.map_map] at h
  exact h

end Refresh
