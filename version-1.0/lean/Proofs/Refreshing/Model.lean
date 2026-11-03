import Proofs.Refreshing.PublicModel

/-!
# Nonempty encoding fibers

The public refreshing model uses a private witness to construct its distributions.
This module proves the separately audited `encoding_nonempty` theorem.
-/

noncomputable section
open scoped BigOperators Matrix ENNReal
open MeasureTheory

namespace Refreshing

/-- Every secret has a nonzero-share encoding when the dimension is at least two. -/
theorem encoding_nonempty {n : ℕ} (hn : 2 ≤ n) (s : Bit) :
    Nonempty (Encoding n s) := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  let l : Vector n := Pi.single i 1
  let r : Vector n := Pi.single i s + Pi.single j 1
  have hl : l ≠ 0 := by
    intro h
    have := congrFun h i
    simp [l] at this
  have hr : r ≠ 0 := by
    intro h
    have := congrFun h j
    simp [r, Ne.symm hij] at this
  refine ⟨⟨(⟨l, hl⟩, ⟨r, hr⟩), ?_⟩⟩
  simp [secret, l, r, dotProduct, Pi.single_apply, hij]

end Refreshing
