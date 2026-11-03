import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic
import Proofs.Refreshing.ModelFacts

/-!
# Transitivity ingredients for uniform matrix refreshing

The results below construct actual invertible linear maps, with no orbit or transitivity hypothesis. They are preliminary ingredients for the paper's freshness lemma. Joint transitivity on pairs of shares with fixed inner product and the corresponding uniform probability distribution are separate statements.
-/

noncomputable section
open scoped Matrix BigOperators ENNReal

namespace RefreshingProof

/-- Any two linearly independent finite families in the same vector space can be matched by an invertible linear map of the ambient space. -/
theorem exists_linearEquiv_map_family {K V ι : Type*}
    [DivisionRing K] [AddCommGroup V] [Module K V] [Finite ι]
    (v w : ι → V) (hv : LinearIndependent K v) (hw : LinearIndependent K w) :
    ∃ e : V ≃ₗ[K] V, ∀ i, e (v i) = w i := by
  classical
  let f := hv.linearCombinationEquiv.symm ≪≫ₗ hw.linearCombinationEquiv
  let : FiniteDimensional K (Submodule.span K (Set.range v)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range _)
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨e, fun i => ?_⟩
  have h := he (hv.linearCombinationEquiv (Finsupp.single i 1))
  have h' := congrArg (fun x : Submodule.span K (Set.range w) => (x : V))
    (show f (hv.linearCombinationEquiv (Finsupp.single i 1)) =
      hw.linearCombinationEquiv (Finsupp.single i 1) by simp [f])
  have hv' : (hv.linearCombinationEquiv (Finsupp.single i 1) : V) = v i := by simp
  have hw' : (hw.linearCombinationEquiv (Finsupp.single i 1) : V) = w i := by simp
  rw [hv'] at h
  exact h.symm.trans (h'.trans hw')

/-- In particular, the general linear group is transitive on nonzero vectors. -/
theorem exists_linearEquiv_map_nonzero {K V : Type*}
    [DivisionRing K] [AddCommGroup V] [Module K V]
    (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ e : V ≃ₗ[K] V, e v = w := by
  have hv' : LinearIndependent K (fun _ : Unit => v) :=
    linearIndependent_unique_iff.mpr hv
  have hw' : LinearIndependent K (fun _ : Unit => w) :=
    linearIndependent_unique_iff.mpr hw
  obtain ⟨e, he⟩ := exists_linearEquiv_map_family _ _ hv' hw'
  exact ⟨e, he ()⟩

/-- Actual matrix form: an invertible square matrix sends any prescribed nonzero column vector to any other. This applies in particular to binary shares. -/
theorem exists_matrixUnit_mulVec_eq {K I : Type*}
    [Field K] [Fintype I] [DecidableEq I]
    (v w : I → K) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ M : (Matrix I I K)ˣ, (M : Matrix I I K) *ᵥ v = w := by
  obtain ⟨e, he⟩ := exists_linearEquiv_map_nonzero (K := K) v w hv hw
  let M : (Matrix I I K)ˣ := Units.map
    (LinearMap.toMatrixAlgEquiv' : Module.End K (I → K) ≃ₐ[K] Matrix I I K).toMonoidHom
    (LinearMap.GeneralLinearGroup.ofLinearEquiv e)
  refine ⟨M, ?_⟩
  change LinearMap.toMatrix' (e : (I → K) →ₗ[K] I → K) *ᵥ v = w
  rw [LinearMap.toMatrix'_mulVec]
  exact he

/-- The matrix version also matches any finite independent family at once. -/
theorem exists_matrixUnit_mulVec_family {K I J : Type*}
    [Field K] [Fintype I] [DecidableEq I] [Finite J]
    (v w : J → I → K) (hv : LinearIndependent K v) (hw : LinearIndependent K w) :
    ∃ M : (Matrix I I K)ˣ, ∀ j, (M : Matrix I I K) *ᵥ v j = w j := by
  obtain ⟨e, he⟩ := exists_linearEquiv_map_family v w hv hw
  let M : (Matrix I I K)ˣ := Units.map
    (LinearMap.toMatrixAlgEquiv' : Module.End K (I → K) ≃ₐ[K] Matrix I I K).toMonoidHom
    (LinearMap.GeneralLinearGroup.ofLinearEquiv e)
  refine ⟨M, fun j => ?_⟩
  change LinearMap.toMatrix' (e : (I → K) →ₗ[K] I → K) *ᵥ v j = w j
  rw [LinearMap.toMatrix'_mulVec]
  exact he j

/-- Transposing both a matrix and its inverse produces another matrix unit. -/
def transposeMatrixUnit {K I : Type*} [CommRing K] [Fintype I] [DecidableEq I]
    (M : (Matrix I I K)ˣ) : (Matrix I I K)ˣ :=
  ⟨(M : Matrix I I K)ᵀ, (↑(M⁻¹) : Matrix I I K)ᵀ,
    by rw [← Matrix.transpose_mul]; simp,
    by rw [← Matrix.transpose_mul]; simp⟩

/-- Actual row-multiplication form, as used for the left share in refreshing. -/
theorem exists_matrixUnit_vecMul_eq {K I : Type*}
    [Field K] [Fintype I] [DecidableEq I]
    (v w : I → K) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ M : (Matrix I I K)ˣ, v ᵥ* (M : Matrix I I K) = w := by
  obtain ⟨M, hM⟩ := exists_matrixUnit_mulVec_eq v w hv hw
  refine ⟨transposeMatrixUnit M, ?_⟩
  change v ᵥ* (M : Matrix I I K)ᵀ = w
  rw [Matrix.vecMul_transpose]
  exact hM

/-- Left multiplication by a transition matrix bijects the corresponding fibers of the map M ↦ Mv. This is the counting mechanism behind uniformity. -/
def mulVecFiberEquiv {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (v w w' : I → K) (N : (Matrix I I K)ˣ)
    (hN : (N : Matrix I I K) *ᵥ w = w') :
    {M : (Matrix I I K)ˣ // (M : Matrix I I K) *ᵥ v = w} ≃
      {M : (Matrix I I K)ˣ // (M : Matrix I I K) *ᵥ v = w'} where
  toFun M := ⟨N * M.val, by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, M.property]
    exact hN⟩
  invFun M := ⟨N⁻¹ * M.val, by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, M.property, ← hN]
    simp⟩
  left_inv M := by apply Subtype.ext; simp
  right_inv M := by apply Subtype.ext; simp

/-- For fixed input v, every two nonzero output columns have exactly the same number of invertible-matrix preimages. In the finite-field case this gives equal probabilities under a fresh uniform invertible matrix. -/
theorem card_mulVec_fiber_eq {K I : Type*}
    [Field K] [Fintype I] [DecidableEq I]
    (v w w' : I → K) (hw : w ≠ 0) (hw' : w' ≠ 0) :
    Nat.card {M : (Matrix I I K)ˣ // (M : Matrix I I K) *ᵥ v = w} =
      Nat.card {M : (Matrix I I K)ˣ // (M : Matrix I I K) *ᵥ v = w'} := by
  obtain ⟨N, hN⟩ := exists_matrixUnit_mulVec_eq w w' hw hw'
  exact Nat.card_congr (mulVecFiberEquiv v w w' N hN)

/-- Any finite PMF with equal point masses is the uniform PMF. -/
theorem pmf_eq_uniform_of_constant {α : Type*} [Fintype α] [Nonempty α]
    (p : PMF α) (hp : ∀ a b, p a = p b) : p = Refreshing.uniformPMF α := by
  apply PMF.ext
  intro a
  have hsum : (Fintype.card α : ℝ≥0∞) * p a = 1 := by
    have h := p.tsum_coe
    rw [tsum_fintype] at h
    have hc : ∀ b, p b = p a := fun b => hp b a
    simp_rw [hc] at h
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h
  exact ENNReal.eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hsum)

/-- Reindexing uniform input coins by an equivalence preserves output masses whenever that equivalence matches the two specified output fibers. -/
theorem uniformPMF_map_apply_eq_of_fiber_matching {α β : Type*}
    [Fintype α] [Nonempty α] (f : α → β) (b b' : β) (e : α ≃ α)
    (he : ∀ a, b' = f (e a) ↔ b = f a) :
    ((Refreshing.uniformPMF α).map f) b' = ((Refreshing.uniformPMF α).map f) b := by
  classical
  simp only [PMF.map_apply, tsum_fintype, Refreshing.uniformPMF_apply]
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  rw [he a]

/-- Uniform coins are invariant under any permutation of their finite space. -/
theorem uniformPMF_map_equiv {α : Type*} [Fintype α] [Nonempty α] (e : α ≃ α) :
    (Refreshing.uniformPMF α).map e = Refreshing.uniformPMF α := by
  classical
  apply PMF.ext
  intro a
  simp only [PMF.map_apply, tsum_fintype, Refreshing.uniformPMF_apply]
  rw [← e.symm.sum_comp]
  simp

/-- An invertible matrix acts on the nonzero vectors. -/
def matrixUnitNonzeroApply {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (M : (Matrix I I K)ˣ) (v : {x : I → K // x ≠ 0}) : {x : I → K // x ≠ 0} :=
  ⟨(M : Matrix I I K) *ᵥ v.val, by
    intro h
    have h' := congrArg (fun x => (↑(M⁻¹) : Matrix I I K) *ᵥ x) h
    exact v.property (by simpa using h')⟩

/-- This action is a permutation, with inverse given by the inverse matrix. -/
def matrixUnitNonzeroEquiv {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (M : (Matrix I I K)ˣ) : {x : I → K // x ≠ 0} ≃ {x : I → K // x ≠ 0} where
  toFun := matrixUnitNonzeroApply M
  invFun := matrixUnitNonzeroApply M⁻¹
  left_inv v := by apply Subtype.ext; simp [matrixUnitNonzeroApply]
  right_inv v := by apply Subtype.ext; simp [matrixUnitNonzeroApply]

/-- Single-share freshness: a uniform invertible matrix sends any fixed nonzero column to a uniform nonzero column, over every finite field. -/
theorem uniform_matrixUnit_nonzero {K I : Type*}
    [Field K] [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    [Fintype ((Matrix I I K)ˣ)] [Nonempty {x : I → K // x ≠ 0}]
    (v : {x : I → K // x ≠ 0}) :
    (Refreshing.uniformPMF ((Matrix I I K)ˣ)).map (fun M => matrixUnitNonzeroApply M v) =
      Refreshing.uniformPMF {x : I → K // x ≠ 0} := by
  apply pmf_eq_uniform_of_constant
  intro w' w
  obtain ⟨N, hN⟩ := exists_matrixUnit_mulVec_eq w.val w'.val w.property w'.property
  apply uniformPMF_map_apply_eq_of_fiber_matching _ w w' (Equiv.mulLeft N)
  intro M
  have hw : matrixUnitNonzeroEquiv N w = w' := Subtype.ext hN
  have hM : matrixUnitNonzeroEquiv N (matrixUnitNonzeroApply M v) =
      matrixUnitNonzeroApply (N * M) v := by
    apply Subtype.ext
    simp [matrixUnitNonzeroEquiv, matrixUnitNonzeroApply]
  change w' = matrixUnitNonzeroApply (N * M) v ↔ w = matrixUnitNonzeroApply M v
  rw [← hw, ← hM]
  exact (matrixUnitNonzeroEquiv N).injective.eq_iff

/-- The inverse matrix is uniform as well, giving the exact single-share distribution for the right-party update M⁻¹R. -/
theorem uniform_inverse_matrixUnit_nonzero {K I : Type*}
    [Field K] [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    [Fintype ((Matrix I I K)ˣ)] [Nonempty {x : I → K // x ≠ 0}]
    (v : {x : I → K // x ≠ 0}) :
    (Refreshing.uniformPMF ((Matrix I I K)ˣ)).map
        (fun M => matrixUnitNonzeroApply M⁻¹ v) =
      Refreshing.uniformPMF {x : I → K // x ≠ 0} := by
  calc
    _ = ((Refreshing.uniformPMF ((Matrix I I K)ˣ)).map (Equiv.inv _)).map
        (fun M => matrixUnitNonzeroApply M v) :=
      (PMF.map_comp _ _ _).symm
    _ = (Refreshing.uniformPMF ((Matrix I I K)ˣ)).map
        (fun M => matrixUnitNonzeroApply M v) := by rw [uniformPMF_map_equiv]
    _ = _ := uniform_matrixUnit_nonzero v

end RefreshingProof
