import Proofs.Compiler.GateApproximation.MatrixPhase.Operator
import Proofs.Compiler.Construction.Parameters



/-!
# Augmented tensor features for multiplication and NAND

The final coordinate carries the public offset before the matrix refresh. The dimension is `n*n+1`, and both long shares are nonzero. Over the binary field the feature maps are injective, as required by the local matrix lemma.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace CircuitCompiler.Rectangular

open Refresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The offset is already encoded in the long input to the matrix phase. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For nonzero u₁,u₂,v₁,v₂ and any offset c,

(u₁ ⊗ u₂,c) · (v₁ ⊗ v₂,1) = (u₁ · v₁) · (u₂ · v₂)+c.
-/
theorem augmentedShare_dot {n : ℕ} (c : F) (x y : U F n × U F n) :
    dot (augmentedShare c x).val (augmentedShare 1 y).val =
      dot x.1.val y.1.val * dot x.2.val y.2.val + c := by
  change (∑ i : Fin (n*n+1),
    Fin.append (tensorVector x.1.val x.2.val) (fun _ : Fin 1 => c) i *
    Fin.append (tensorVector y.1.val y.2.val) (fun _ : Fin 1 => (1:F)) i) = _
  rw [Fin.sum_univ_add]
  simpa [dot, dotProduct] using congrArg (fun z : F => z+c)
    (tensorVector_dot x.1.val x.2.val y.1.val y.2.val)


/-
Mathematical statement (normal notation): Over the binary field, for any fixed offset c, the augmented tensor map

(u,v) ↦ (u ⊗ v,c)

is injective on pairs of nonzero length-n vectors.
-/
theorem augmentedShare_injective_binary {n : ℕ} (hq : fieldCard F = 2) (c : F) :
    Function.Injective (augmentedShare (n := n) c) := by
  intro x y h
  apply RefreshAnalysis.inputTensor_injective_binary hq
  apply Subtype.ext
  funext i
  have hi := congrArg (fun z : U F (n*n+1) => z.val (Fin.castAdd 1 i)) h
  simpa [augmentedShare,inputTensor] using hi

/-
Mathematical definition (normal notation): From two encoding states (L₁,R₁), (L₂,R₂), form the long state

((L₁ ⊗ L₂,c), (R₁ ⊗ R₂,1)).

Its inner product is the product of the two encoded values plus c.
-/
def augmentedTensor {n : ℕ} (c : F) (x y : State F n) : State F (n*n+1) :=
  ⟨augmentedShare c (x.L,y.L),augmentedShare 1 (x.R,y.R)⟩

-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): If the input states encode s₁ and s₂, their augmented tensor state with offset c encodes exactly s₁ · s₂+c. -/
theorem augmentedTensor_secret {n : ℕ} (c : F) (x y : State F n) :
    secret (augmentedTensor c x y) = secret x * secret y + c :=
  augmentedShare_dot c (x.L,y.L) (x.R,y.R)

/-- The long dimension can be supplied to the rectangular sampler as `n+t`. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, assume 1 ≤ n. Then

n + (n · n + 1 - n) = n · n + 1.
-/
theorem augmented_dimension {n : ℕ} (hn : 1 ≤ n) : n + (n*n+1-n) = n*n+1 := by
  have h : n ≤ n*n+1 := by nlinarith
  omega

end CircuitCompiler.Rectangular
