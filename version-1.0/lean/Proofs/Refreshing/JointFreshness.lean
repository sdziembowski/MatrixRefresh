import Proofs.Refreshing.Freshness
import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Joint fixed-inner-product transitivity

These algebraic lemmas are prerequisites of the paper's joint freshness lemma.
-/

noncomputable section
open scoped Matrix
namespace RefreshingProof

/-- The stabilizer of a linear functional acts transitively on its nonzero vectors of any fixed functional value, including value zero. -/
theorem exists_functional_stabilizer_map {K V : Type*}
    [Field K] [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] K) (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (heq : f v = f w) :
    ∃ e : V ≃ₗ[K] V, e v = w ∧ ∀ x, f (e x) = f x := by
  classical
  by_cases hfv : f v = 0
  · have hfw : f w = 0 := heq.symm.trans hfv
    let v' : LinearMap.ker f := ⟨v, hfv⟩
    let w' : LinearMap.ker f := ⟨w, hfw⟩
    have hv' : v' ≠ 0 := fun h => hv (congrArg Subtype.val h)
    have hw' : w' ≠ 0 := fun h => hw (congrArg Subtype.val h)
    obtain ⟨g, hg⟩ := exists_linearEquiv_map_nonzero (K := K) v' w' hv' hw'
    obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (LinearMap.ker f)
    let a := (LinearMap.ker f).prodEquivOfIsCompl Q hQ
    let e := a.symm ≪≫ₗ LinearEquiv.prodCongr g (LinearEquiv.refl K Q) ≪≫ₗ a
    refine ⟨e, ?_, ?_⟩
    · have hav : a.symm v = (v', 0) :=
        (LinearMap.ker f).prodEquivOfIsCompl_symm_apply_left Q hQ v'
      simp [e, hav, hg, a, w']
    · intro x
      obtain ⟨⟨k, q⟩, rfl⟩ := a.surjective x
      have hk : f k.val = 0 := k.property
      have hgk : f (g k).val = 0 := (g k).property
      simp [e, a, map_add, hk, hgk]
  · let u : V := (f v)⁻¹ • (w - v)
    have hfu : f u = 0 := by simp [u, map_sub, ← heq]
    refine ⟨LinearEquiv.transvection hfu, ?_, ?_⟩
    · change v + f v • u = w
      simp [u, smul_smul, hfv]
    · intro x
      change f (x + f x • u) = f x
      simp [hfu]

/-- Any two nonzero-share states with the same inner product are connected by an actual matrix refresh. No restriction to a nonzero stored secret is needed. -/
theorem exists_matrixUnit_refresh_eq {K I : Type*}
    [Field K] [Fintype I] [DecidableEq I]
    (l r l' r' : I → K) (hl : l ≠ 0) (hr : r ≠ 0)
    (hl' : l' ≠ 0) (hr' : r' ≠ 0) (hs : l ⬝ᵥ r = l' ⬝ᵥ r') :
    ∃ M : (Matrix I I K)ˣ,
      l ᵥ* (M : Matrix I I K) = l' ∧ (↑(M⁻¹) : Matrix I I K) *ᵥ r = r' := by
  classical
  obtain ⟨N, hN⟩ := exists_matrixUnit_vecMul_eq l l' hl hl'
  let t : I → K := (N : Matrix I I K) *ᵥ r'
  have ht : t ≠ 0 := (matrixUnitNonzeroApply N ⟨r', hr'⟩).property
  let f : (I → K) →ₗ[K] K := dotProductBilin K K l
  have hft : f t = f r := by
    change l ⬝ᵥ ((N : Matrix I I K) *ᵥ r') = l ⬝ᵥ r
    rw [Matrix.dotProduct_mulVec, hN]
    exact hs.symm
  obtain ⟨e, he, hef⟩ := exists_functional_stabilizer_map f t r ht hr hft
  let H : (Matrix I I K)ˣ := Units.map
    (LinearMap.toMatrixAlgEquiv' : Module.End K (I → K) ≃ₐ[K] Matrix I I K).toMonoidHom
    (LinearMap.GeneralLinearGroup.ofLinearEquiv e)
  have hH (x : I → K) : (H : Matrix I I K) *ᵥ x = e x := by
    change LinearMap.toMatrix' (e : (I → K) →ₗ[K] I → K) *ᵥ x = e x
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  have hlH : l ᵥ* (H : Matrix I I K) = l := by
    ext i
    have h := hef (Pi.single i 1)
    change l ⬝ᵥ e (Pi.single i 1) = l ⬝ᵥ Pi.single i 1 at h
    rw [← hH, Matrix.dotProduct_mulVec] at h
    simpa using h
  let M := H * N
  refine ⟨M, ?_, ?_⟩
  · change l ᵥ* ((H : Matrix I I K) * (N : Matrix I I K)) = l'
    rw [← Matrix.vecMul_vecMul, hlH, hN]
  · have hMr : (M : Matrix I I K) *ᵥ r' = r := by
      change ((H : Matrix I I K) * (N : Matrix I I K)) *ᵥ r' = r
      rw [← Matrix.mulVec_mulVec, hH]
      exact he
    have h := congrArg (fun x => (↑(M⁻¹) : Matrix I I K) *ᵥ x) hMr
    simpa using h.symm

/-- The same fixed-inner-product fiber as in the specification, generalized from the binary field to any field. -/
abbrev PairEncoding (K I : Type*) [Field K] [Fintype I] (s : K) :=
  {x : {v : I → K // v ≠ 0} × {v : I → K // v ≠ 0} // x.1.val ⬝ᵥ x.2.val = s}

/-- An actual refresh on a fixed-inner-product fiber. -/
def pairRefresh {K I : Type*} [Field K] [Fintype I] [DecidableEq I] {s : K}
    (x : PairEncoding K I s) (M : (Matrix I I K)ˣ) : PairEncoding K I s := by
  let l : {v : I → K // v ≠ 0} := ⟨x.val.1.val ᵥ* (M : Matrix I I K), by
    intro h
    have h' := congrArg (fun v => v ᵥ* (↑(M⁻¹) : Matrix I I K)) h
    exact x.val.1.property (by simpa using h')⟩
  let r := matrixUnitNonzeroApply M⁻¹ x.val.2
  refine ⟨(l, r), ?_⟩
  change (x.val.1.val ᵥ* (M : Matrix I I K)) ⬝ᵥ
    ((↑(M⁻¹) : Matrix I I K) *ᵥ x.val.2.val) = s
  rw [← Matrix.dotProduct_mulVec]
  simpa using x.property

/-- Refreshing an encoding by the identity matrix leaves it unchanged. -/
@[simp] theorem pairRefresh_one {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    {s : K} (x : PairEncoding K I s) : pairRefresh x 1 = x := by
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext <;> simp [pairRefresh, matrixUnitNonzeroApply]

/-- Refresh composition is right multiplication of its matrix coins. -/
theorem pairRefresh_mul {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    {s : K} (x : PairEncoding K I s) (M N : (Matrix I I K)ˣ) :
    pairRefresh x (M * N) = pairRefresh (pairRefresh x M) N := by
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext <;> simp [pairRefresh, matrixUnitNonzeroApply]

/-- Each fixed matrix permutes the encoding fiber. -/
def pairRefreshEquiv {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (s : K) (M : (Matrix I I K)ˣ) : PairEncoding K I s ≃ PairEncoding K I s where
  toFun x := pairRefresh x M
  invFun x := pairRefresh x M⁻¹
  left_inv x := by
    change pairRefresh (pairRefresh x M) M⁻¹ = x
    rw [← pairRefresh_mul]
    simp
  right_inv x := by
    change pairRefresh (pairRefresh x M⁻¹) M = x
    rw [← pairRefresh_mul]
    simp

/-- Every two points of the fiber are connected by a matrix refresh. -/
theorem exists_pairRefresh_eq {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    {s : K} (x y : PairEncoding K I s) :
    ∃ M : (Matrix I I K)ˣ, pairRefresh x M = y := by
  obtain ⟨M, hM₁, hM₂⟩ := exists_matrixUnit_refresh_eq
    x.val.1.val x.val.2.val y.val.1.val y.val.2.val
    x.val.1.property x.val.2.property y.val.1.property y.val.2.property
    (x.property.trans y.property.symm)
  refine ⟨M, ?_⟩
  apply Subtype.ext
  exact Prod.ext (Subtype.ext hM₁) (Subtype.ext hM₂)

/-- Joint freshness: a fresh uniform invertible matrix sends any fixed encoding to the uniform distribution on its entire fixed-inner-product fiber. -/
theorem uniform_pairRefresh {K I : Type*}
    [Field K] [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    [Fintype ((Matrix I I K)ˣ)] (s : K) [Nonempty (PairEncoding K I s)]
    (x : PairEncoding K I s) :
    (Refreshing.uniformPMF ((Matrix I I K)ˣ)).map (pairRefresh x) =
      Refreshing.uniformPMF (PairEncoding K I s) := by
  apply pmf_eq_uniform_of_constant
  intro y' y
  obtain ⟨N, hN⟩ := exists_pairRefresh_eq y y'
  apply uniformPMF_map_apply_eq_of_fiber_matching _ y y' (Equiv.mulRight N)
  intro M
  have hNy : pairRefreshEquiv s N y = y' := hN
  have hNM : pairRefreshEquiv s N (pairRefresh x M) = pairRefresh x (M * N) :=
    (pairRefresh_mul x M N).symm
  change y' = pairRefresh x (M * N) ↔ y = pairRefresh x M
  rw [← hNy, ← hNM]
  exact (pairRefreshEquiv s N).injective.eq_iff

end RefreshingProof
