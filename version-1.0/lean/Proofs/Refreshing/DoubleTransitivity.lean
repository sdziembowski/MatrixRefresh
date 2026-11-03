import Proofs.Refreshing.Freshness
import Proofs.Refreshing.BinaryCharacters

/-!
# Two distinct nonzero binary vectors under a fresh matrix

Binary-specific pair transitivity is the distributional ingredient of the Gram-variance calculation. It is proved from linear independence, rather than assumed as a property of random matrices.
-/

noncomputable section
open scoped Matrix

namespace RefreshingProof

/-- Binary vectors on the index set whose coordinate function is nonzero. -/
abbrev NonzeroBinary (I : Type*) := {v : I → ZMod 2 // v ≠ 0}
/-- Ordered pairs of distinct nonzero binary vectors. -/
abbrev DistinctBinaryPair (I : Type*) :=
  {p : NonzeroBinary I × NonzeroBinary I // p.1 ≠ p.2}

/-- Over F₂, two distinct nonzero vectors are linearly independent. -/
theorem distinct_binary_pair_independent {I : Type*} (x : DistinctBinaryPair I) :
    LinearIndependent (ZMod 2) ![x.val.1.val, x.val.2.val] := by
  rw [linearIndependent_fin2]
  refine ⟨x.val.2.property, ?_⟩
  intro c hc
  rcases Binary.bit_cases c with rfl | rfl
  · have h : x.val.1.val = 0 := by simpa using hc.symm
    exact x.val.1.property h
  · have h : x.val.1.val = x.val.2.val := by simpa using hc.symm
    exact x.property (Subtype.ext h)

/-- The action of a matrix unit on ordered distinct nonzero columns. -/
def distinctBinaryPairEquiv {I : Type*} [Fintype I] [DecidableEq I]
    (M : (Matrix I I (ZMod 2))ˣ) : DistinctBinaryPair I ≃ DistinctBinaryPair I := by
  let e := matrixUnitNonzeroEquiv M
  exact {
    toFun := fun x => ⟨(e x.val.1, e x.val.2), fun h => x.property (e.injective h)⟩
    invFun := fun x => ⟨(e.symm x.val.1, e.symm x.val.2),
      fun h => x.property (e.symm.injective h)⟩
    left_inv := by intro x; apply Subtype.ext; simp
    right_inv := by intro x; apply Subtype.ext; simp }

/-- Every two ordered distinct nonzero binary pairs are connected by GL. -/
theorem exists_distinctBinaryPairEquiv_eq {I : Type*} [Fintype I] [DecidableEq I]
    (x y : DistinctBinaryPair I) :
    ∃ M : (Matrix I I (ZMod 2))ˣ, distinctBinaryPairEquiv M x = y := by
  obtain ⟨M, hM⟩ := exists_matrixUnit_mulVec_family
    ![x.val.1.val, x.val.2.val] ![y.val.1.val, y.val.2.val]
    (distinct_binary_pair_independent x) (distinct_binary_pair_independent y)
  refine ⟨M, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    simpa [distinctBinaryPairEquiv, matrixUnitNonzeroEquiv, matrixUnitNonzeroApply]
      using hM 0
  · apply Subtype.ext
    simpa [distinctBinaryPairEquiv, matrixUnitNonzeroEquiv, matrixUnitNonzeroApply]
      using hM 1

/-- A fresh uniform matrix gives exactly uniform distinct images to any two fixed distinct nonzero binary vectors. -/
theorem uniform_distinct_binary_pair {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype ((Matrix I I (ZMod 2))ˣ)] (x : DistinctBinaryPair I) :
    (Refreshing.uniformPMF ((Matrix I I (ZMod 2))ˣ)).map
        (fun M => distinctBinaryPairEquiv M x) =
      @Refreshing.uniformPMF (DistinctBinaryPair I) _ ⟨x⟩ := by
  letI : Nonempty (DistinctBinaryPair I) := ⟨x⟩
  apply pmf_eq_uniform_of_constant
  intro y' y
  obtain ⟨N, hN⟩ := exists_distinctBinaryPairEquiv_eq y y'
  apply uniformPMF_map_apply_eq_of_fiber_matching _ y y' (Equiv.mulLeft N)
  intro M
  have hmul : distinctBinaryPairEquiv N (distinctBinaryPairEquiv M x) =
      distinctBinaryPairEquiv (N * M) x := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [distinctBinaryPairEquiv, matrixUnitNonzeroEquiv, matrixUnitNonzeroApply]
  change y' = distinctBinaryPairEquiv (N * M) x ↔ y = distinctBinaryPairEquiv M x
  rw [← hmul, ← hN]
  exact (distinctBinaryPairEquiv N).injective.eq_iff

end RefreshingProof
