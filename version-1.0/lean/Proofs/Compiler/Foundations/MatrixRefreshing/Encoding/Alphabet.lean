import Mathlib.Tactic.Ring
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Notation



set_option autoImplicit false

namespace Refresh

/-- Both complete answer blocks count toward the per-round alphabet. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ℓ ∈ ℕ, we have

|Leaf(ℓ)| = K(ℓ).
-/
@[simp] theorem card_leaf (ℓ : ℕ) : Fintype.card (Leaf ℓ) = K ℓ := by
  simp [Leaf, K, pow_mul, pow_two, Nat.mul_comm]

end Refresh
