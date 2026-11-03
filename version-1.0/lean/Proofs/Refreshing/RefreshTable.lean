import Proofs.Refreshing.Unrestricted
import Proofs.Refreshing.LocalTables

/-! The unrestricted refreshing table used in the four-cycle argument. -/

noncomputable section
open scoped Matrix

namespace RefreshingProof
open Refreshing

/-- An old nonzero share paired with an unrestricted new binary vector. -/
abbrev ExtendedSharePair (n : ℕ) := Share n × Refreshing.Vector n

/-- The paper's unrestricted refreshing table T_A, with the new right share kept as part of the column index instead of applying an inverse to a singular A. -/
def unrestrictedRefreshTable {n : ℕ}
    (F : Local.Table (ExtendedSharePair n) (ExtendedSharePair n)) (A : BinaryMatrix n) :
    Local.Table (Share n) (ExtendedSharePair n) :=
  fun l rr => if A *ᵥ rr.2 = rr.1.val then
    Real.sqrt ((2 : ℝ) ^ n) * F (l, l.val ᵥ* A) rr else 0


end RefreshingProof
