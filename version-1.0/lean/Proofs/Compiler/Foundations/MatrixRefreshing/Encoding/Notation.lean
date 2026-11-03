import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Units
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Proofs.Compiler.Construction.Parameters



/-!
# Shared finite-field model

Vectors have `n` coordinates in a field `F`. `fieldCard F` is the field size, `vectorCard F n` counts all vectors, and `shareCard F n` counts nonzero vectors. For the binary field used in the paper, these last two quantities are `N = 2^n` and `q = N - 1`, respectively. The refresh state retains two nonzero shares. Row and column roles are encoded by their matrix actions, while both use the same underlying vector type. The manuscript labels these roles `U_L` and `U_R`; both are represented by `U F n` in Lean.

There are two ways to group the four shares of a transition: `State × State` groups them by time, whereas `Endpoint × Endpoint` groups them by party. `regroup` is the exact equivalence used to move between these descriptions.

Leakage is always measured in bits, independently of `F`. Thus a complete round answer has `K ℓ = 2^(2ℓ)` possibilities even over an extension field. The alias `F2` denotes the binary field in binary specializations.
-/

set_option autoImplicit false

namespace Refresh

/-- Projecting a state constructed from two shares recovers the left party's share. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For F a set; n ∈ ℕ; l, r ∈ U(F, n), assume F is a field. Then

L(State.mk(l, r)) = l.
-/
@[simp] theorem stateLeftShare_mk {F : Type*} [Field F] {n : ℕ} (l r : U F n) :
    stateLeftShare (State.mk l r) = l :=
  rfl

/-- Projecting a state constructed from two shares recovers the right party's share. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For F a set; n ∈ ℕ; l, r ∈ U(F, n), assume F is a field. Then

R(State.mk(l, r)) = r.
-/
@[simp] theorem stateRightShare_mk {F : Type*} [Field F] {n : ℕ} (l r : U F n) :
    stateRightShare (State.mk l r) = r :=
  rfl

/-- The old and new shares of one party, used as one table index. This represents `U_L²` for the left party or `U_R²` for the right party, with named coordinates; `endpointEquivProd` gives the exact identification. -/
/- Mathematical definition (normal notation): A party's local endpoint is the ordered pair of its old and new nonzero shares: (L,L') on the left or (R,R') on the right. -/
@[ext] structure Endpoint (F : Type*) [Field F] (n : ℕ) where
  oldShare : U F n
  newShare : U F n

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Enumerate local endpoints by enumerating their old and new nonzero shares. -/
instance endpointFintype (n : ℕ) : Fintype (Endpoint F n) :=
  Fintype.ofEquiv (U F n × U F n)
    ⟨fun p => ⟨p.1, p.2⟩, fun x => (x.oldShare, x.newShare), fun _ => rfl, fun _ => rfl⟩

/-- An answer block of exactly `ℓ` Boolean coordinates. -/
/- Mathematical definition (normal notation): A λ-bit answer belongs to {0,1}^λ. -/
abbrev Bits (ℓ : ℕ) := Fin ℓ → Bool

/-- Both parties' answers, labeled by party even when the query order changes. -/
/- Mathematical definition (normal notation): A complete round answer is an ordered pair (z_L,z_R) ∈ {0,1}^λ × {0,1}^λ, retaining the party labels. -/
abbrev Leaf (ℓ : ℕ) := Bits ℓ × Bits ℓ

/-- The complete answers from the first `i` rounds, in chronological order. -/
/- Mathematical definition (normal notation): A history of i rounds is the ordered list (z₁,…,zᵢ) of complete round answers. -/
abbrev History (ℓ i : ℕ) := Fin i → Leaf ℓ

/-- The size of a complete-round alphabet: each party contributes an `ℓ`-bit answer. -/
/- Mathematical definition (normal notation): The number of possible complete answers in one round is K := 2^(2λ) when each party leaks λ bits. -/
def K (ℓ : ℕ) : ℕ := 2 ^ (2 * ℓ)

/-- Regroup the four explicit coordinates from time-grouped states `((ell,r),(ell',r'))` into party-grouped pairs `((ell,ell'),(r,r'))`. The manuscript displays these coordinates directly; the formal equivalence uses the named state projections. No information or randomness changes. -/
/- Mathematical definition (normal notation): The coordinate bijection ((ℓ,r),(ℓ',r')) ↦ ((ℓ,ℓ'),(r,r')) groups endpoints by party instead of by time. -/
def regroup (F : Type*) [Field F] (n : ℕ) :
    State F n × State F n ≃ Endpoint F n × Endpoint F n where
  toFun p := (⟨(stateLeftShare p.1), (stateLeftShare p.2)⟩, ⟨(stateRightShare p.1), (stateRightShare p.2)⟩)
  invFun p := (⟨p.1.oldShare, p.2.oldShare⟩, ⟨p.1.newShare, p.2.newShare⟩)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Endpoint compatibility: the old and new states encode the same secret. -/
/- Mathematical definition (normal notation): The endpoint tuple is consistent precisely when ℓ · r = ℓ' · r'. -/
def D {n : ℕ} (x y : Endpoint F n) : Prop :=
  dot x.oldShare.val y.oldShare.val = dot x.newShare.val y.newShare.val

/-- Compatibility within a specified secret fiber, used for its restricted distribution. -/
/- Mathematical definition (normal notation): The endpoint tuple belongs to the s-fiber precisely when ℓ · r = s and ℓ' · r' = s. -/
def DSecret {n : ℕ} (s : F) (x y : Endpoint F n) : Prop :=
  dot x.oldShare.val y.oldShare.val = s ∧ dot x.newShare.val y.newShare.val = s

end Refresh
