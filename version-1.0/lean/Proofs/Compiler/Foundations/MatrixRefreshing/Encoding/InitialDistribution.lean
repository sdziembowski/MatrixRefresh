import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Counts
import Proofs.Compiler.Foundations.MatrixRefreshing.Probability.FiniteProbability
import Proofs.Compiler.Construction.Parameters



set_option autoImplicit false

namespace Refresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The initial encoding distribution assigns nonzero mass only to states encoding the prescribed secret. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, assume 2 ≤ n. Then

Supports(μₛ)(((x ↦ secret(x) = s))).
-/
theorem mu_supports (n : ℕ) (hn : 2 ≤ n) (s : F) :
    (mu F n hn s).Supports (fun x => secret x = s) := by
  letI := fiber_nonempty F n hn s
  exact FiniteDistribution.map_supports (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s)) Subtype.val
    (fun _ => True) (fun x => secret x = s) (FiniteDistribution.supports_true _)
    (fun x _ => x.property)

/-- The uniform probability distribution on nonzero vectors; dimension at least two ensures this carrier is inhabited. -/
/- Mathematical definition (normal notation): The uniform distribution on U = 𝔽ⁿ ∖ {0} assigns mass 1/(|𝔽|ⁿ-1) to every share. -/
noncomputable def uniformShare (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) (hn : 2 ≤ n) : FiniteDistribution (U F n) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  exact FiniteDistribution.uniform

/-- The initial left share is exactly uniform on the nonzero vectors. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, assume 2 ≤ n. Then

(stateLeftShare_*μₛ) = uniformShare(F, n).
-/
theorem mu_left_marginal (n : ℕ) (hn : 2 ≤ n) (s : F) :
    (mu F n hn s).map stateLeftShare = uniformShare F n hn := by
  letI := fiber_nonempty F n hn s
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  unfold mu
  rw [FiniteDistribution.map_map]
  apply FiniteDistribution.uniform_map_of_fiber_card _ (if s = 0 then fieldCard F ^ (n - 1) - 1 else fieldCard F ^ (n - 1))
  intro l
  change Fintype.card {x : Fiber F n s // (stateLeftShare x.val) = l} = _
  rw [left_marginal_card, partner_card_eq]

/-- The initial right share is exactly uniform on the same nonzero carrier. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, assume 2 ≤ n. Then

(stateRightShare_*μₛ) = uniformShare(F, n) .
-/
theorem mu_right_marginal (n : ℕ) (hn : 2 ≤ n) (s : F) :
    (mu F n hn s).map stateRightShare = uniformShare F n hn := by
  letI := fiber_nonempty F n hn s
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  unfold mu
  rw [FiniteDistribution.map_map]
  apply FiniteDistribution.uniform_map_of_fiber_card _ (if s = 0 then fieldCard F ^ (n - 1) - 1 else fieldCard F ^ (n - 1))
  intro r
  change Fintype.card {x : Fiber F n s // (stateRightShare x.val) = r} = _
  rw [right_marginal_card, partner_card_eq]

end Refresh
