import Mathlib.Tactic
import Proofs.Compiler.Construction.Parameters
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Counts
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.MatrixAction



set_option autoImplicit false

namespace Refresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Every pair of outputs with the same secret has equally many realizing matrices. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; x, y, z ∈ State(F, n), assume secret(y) = secret(z). Then

|Transporter(x, y)| = |Transporter(x, z)|.
-/
theorem transporter_card_eq_of_secret_eq {n : ℕ} (x y z : State F n) (hs : secret y = secret z) :
    Fintype.card (Transporter x y) = Fintype.card (Transporter x z) := by
  obtain ⟨A, hA⟩ := refresh_transitive y z hs
  simpa only [hA] using transporter_card_refresh x y A

end Refresh
