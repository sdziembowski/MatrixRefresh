import Proofs.Compiler.Construction.Parameters
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Notation



set_option autoImplicit false

namespace Refresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The underlying refreshed column is the inverse sampled matrix multiplied by the original column. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; r ∈ U(F, n); M ∈ GLₙ(F), we have

columnRefresh(r, M) = Matrix.mulVec((M)⁻¹, r).
-/
@[simp] theorem columnRefresh_val {n : ℕ} (r : U F n) (M : «GL» F n) :
    (columnRefresh r M).val = Matrix.mulVec (↑M⁻¹) r.val :=
  rfl

/-- The identity matrix leaves the row share unchanged. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; l ∈ U(F, n), we have

rowRefresh(l, 1) = l.
-/
@[simp] theorem rowRefresh_one {n : ℕ} (l : U F n) : rowRefresh l 1 = l := by
  apply Subtype.ext
  simp

/-- The identity matrix leaves the column share unchanged. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; r ∈ U(F, n), we have

columnRefresh(r, 1) = r.
-/
@[simp] theorem columnRefresh_one {n : ℕ} (r : U F n) : columnRefresh r 1 = r := by
  apply Subtype.ext
  simp

/-- Refreshing a state with the identity matrix leaves both shares unchanged. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; x ∈ State(F, n), we have

refresh(x, 1) = x.
-/
@[simp] theorem refresh_one {n : ℕ} (x : State F n) : refresh x 1 = x := by
  cases x
  simp [refresh]

/-- The matrices realizing one specified input/output transition. -/
/- Mathematical definition (normal notation): For fixed encoding states x,y, the transporter set is {M ∈ GLₙ(𝔽):refresh_M(x) = y}. -/
abbrev Transporter {n : ℕ} (x y : State F n) := {M : «GL» F n // refresh x M = y}

/-- Right multiplication identifies transporter sets with different attainable outputs. -/
/- Mathematical definition (normal notation): Right multiplication M ↦ M · A bijects the matrices sending x to y with those sending x to the refresh of y by A. The inverse is M ↦ M · A⁻¹. -/
def transporterEquiv {n : ℕ} (x y : State F n) (A : «GL» F n) :
    Transporter x y ≃ Transporter x (refresh y A) where
  toFun M := ⟨M.val * A, by rw [← refresh_mul, M.property]⟩
  invFun M := ⟨M.val * A⁻¹, by
    rw [← refresh_mul, M.property, refresh_mul, mul_inv_cancel, refresh_one]⟩
  left_inv M := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv M := by
    apply Subtype.ext
    simp [mul_assoc]

/-- Refreshing a prescribed output does not change the number of matrices that realize a transition from a fixed input. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; x, y ∈ State(F, n); A ∈ GLₙ(F), we have

|Transporter(x, y)| = |Transporter(x, refresh(y, A))|.
-/
theorem transporter_card_refresh {n : ℕ} (x y : State F n) (A : «GL» F n) :
    Fintype.card (Transporter x y) =
      Fintype.card (Transporter x (refresh y A)) :=
  Fintype.card_congr (transporterEquiv x y A)

end Refresh
