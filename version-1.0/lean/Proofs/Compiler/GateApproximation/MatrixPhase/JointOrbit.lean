import Proofs.Compiler.GateApproximation.MatrixPhase.JointCompletion



/-!
# The simultaneous two-row/two-column orbit

The compatible independent quadruples form one orbit under the shared matrix and inverse-matrix action. Translation in the finite group therefore makes the output uniform on the entire compatible carrier.
-/
set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators Classical

namespace CircuitCompiler

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Matrix representation of a linear equivalence acting on columns. -/
/- Mathematical definition (normal notation): Represent a linear automorphism of Fᵐ by its matrix in the coordinate basis. Its inverse matrix is the matrix of the inverse automorphism. -/
def columnMatrixUnit {m : ℕ} (e : V F m ≃ₗ[F] V F m) : Refresh.«GL» F m where
  val := LinearMap.toMatrix' e.toLinearMap
  inv := LinearMap.toMatrix' e.symm.toLinearMap
  val_inv := by
    rw [← LinearMap.toMatrix'_comp]
    have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by ext v; simp
    rw [h, LinearMap.toMatrix'_id]
  inv_val := by
    rw [← LinearMap.toMatrix'_comp]
    have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext v; simp
    rw [h, LinearMap.toMatrix'_id]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; e ∈ V(F, m) —linear over F→ V(F, m); v ∈ V(F, m), we have

Matrix.mulVec(columnMatrixUnit(e), v) = e(v).
-/
@[simp] theorem columnMatrixUnit_mulVec {m : ℕ} (e : V F m ≃ₗ[F] V F m) (v : V F m) :
    Matrix.mulVec (columnMatrixUnit e).val v = e v :=
  LinearMap.toMatrix'_mulVec _ _

/-- Compatible independent row and column prescriptions admit an invertible matrix realizing all four vector constraints simultaneously. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; l, rho, lout, rout ∈ {0,…,2-1} → V(F, m), assume 3 ≤ m; LinearIndependent(F, l); LinearIndependent(F, rho); LinearIndependent(F, lout); LinearIndependent(F, rout); ExtensionCompatible(l, rho, lout, rout). Then

∃ M ∈ GLₘ(F), (∀ i, Matrix.vecMul(l(i), M) = lout(i)) ∧ (∀ j, Matrix.mulVec(M, rho(j)) = rout(j)).
-/
theorem exists_GL_completion {m : ℕ} (hm : 3 ≤ m)
    (l rho lout rout : Fin 2 → V F m)
    (hl : LinearIndependent F l) (hrho : LinearIndependent F rho)
    (hlout : LinearIndependent F lout) (hrout : LinearIndependent F rout)
    (hc : ExtensionCompatible l rho lout rout) :
    ∃ M : Refresh.«GL» F m, (∀ i, Matrix.vecMul (l i) M.val = lout i) ∧
      (∀ j, Matrix.mulVec M.val (rho j) = rout j) := by
  obtain ⟨f, hf⟩ := exists_injective_completion hm l rho lout rout hl hrho hlout hrout hc
  let e := LinearEquiv.ofBijective f.val ⟨hf, Finite.surjective_of_injective hf⟩
  refine ⟨columnMatrixUnit e, ?_, ?_⟩
  · apply (matrix_row_constraints_iff l lout _).2
    change (dotMap l).comp (Matrix.toLin' (LinearMap.toMatrix' e.toLinearMap)) = _
    rw [Matrix.toLin'_toMatrix']
    exact f.property.1
  · intro j
    rw [columnMatrixUnit_mulVec]
    exact f.property.2 j

/-- Inverse column action preserves independence of an ordered vector pair. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; v, w ∈ V(F, m); M ∈ GLₘ(F), assume LinearIndependent(F, (v, w)). Then

LinearIndependent(F, (Matrix.mulVec((M)⁻¹, v), Matrix.mulVec((M)⁻¹, w))).
-/
theorem column_pair_independent {m : ℕ} (v w : V F m)
    (hv : LinearIndependent F ![v, w]) (M : Refresh.«GL» F m) :
    LinearIndependent F ![Matrix.mulVec (M⁻¹).val v, Matrix.mulVec (M⁻¹).val w] := by
  let f : V F m →ₗ[F] V F m := Matrix.toLin' (M⁻¹).val
  have hf : Function.Injective f := by
    intro a b h
    have h' := congrArg (fun x : V F m => Matrix.mulVec M.val x) h
    simpa [f] using h'
  have he : f ∘ ![v, w] = ![Matrix.mulVec (M⁻¹).val v, Matrix.mulVec (M⁻¹).val w] := by
    funext i
    fin_cases i <;> rfl
  rw [← he]
  exact hv.map' f (LinearMap.ker_eq_bot.mpr hf)

/-- Every scalar pairing is preserved by the common matrix and its inverse. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; u, v ∈ V(F, m); M ∈ GLₘ(F), we have

(Matrix.vecMul(u, M) · Matrix.mulVec((M)⁻¹, v)) = (u · v).
-/
theorem shared_pairing {m : ℕ} (u v : V F m) (M : Refresh.«GL» F m) :
    dot (Matrix.vecMul u M.val) (Matrix.mulVec (M⁻¹).val v) = dot u v := by
  unfold dot
  rw [← Matrix.dotProduct_mulVec]
  simp

/-- The actual shared-matrix action on the counted compatible orbit. -/
/- Mathematical definition (normal notation): Apply the same invertible matrix M to both row vectors on the right and M⁻¹ to both column vectors on the left. The row and column pairs remain independent, and all four cross inner products are preserved. -/
def quadrupleRefresh {m : ℕ} {S : Matrix (Fin 2) (Fin 2) F}
    (p : CompatibleQuadruples (m := m) S) (M : Refresh.«GL» F m) :
    CompatibleQuadruples (m := m) S :=
  ⟨independentPairRefresh p.1 M,
    ⟨(Matrix.mulVec (M⁻¹).val p.2.val.1, Matrix.mulVec (M⁻¹).val p.2.val.2), by
      refine ⟨?_, ?_, column_pair_independent _ _ p.2.property.2.2 M⟩
      · funext i
        fin_cases i
        · exact (shared_pairing _ _ M).trans (congrFun p.2.property.1 0)
        · exact (shared_pairing _ _ M).trans (congrFun p.2.property.1 1)
      · funext i
        fin_cases i
        · exact (shared_pairing _ _ M).trans (congrFun p.2.property.2.1 0)
        · exact (shared_pairing _ _ M).trans (congrFun p.2.property.2.1 1)⟩⟩

/-- Equality of the four underlying vectors determines a compatible orbit point, independently of its dependent proof fields. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; S ∈ F^({0,…,2−1} × {0,…,2−1}); p, q ∈ CompatibleQuadruples(m = m, S), assume (p)₁ = (q)₁; (p)₂ = (q)₂. Then

p = q.
-/
theorem compatibleQuadruples_ext {m : ℕ} {S : Matrix (Fin 2) (Fin 2) F}
    {p q : CompatibleQuadruples (m := m) S}
    (hl : p.1.val = q.1.val) (hr : p.2.val = q.2.val) : p = q := by
  have hpq : p.1 = q.1 := Subtype.ext hl
  cases p with
  | mk p₁ p₂ =>
    cases q with
    | mk q₁ q₂ =>
      dsimp only at hpq
      subst q₁
      congr 1
      exact Subtype.ext hr

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; S ∈ F^({0,…,2−1} × {0,…,2−1}); p ∈ CompatibleQuadruples(m = m, S), we have

quadrupleRefresh(p, 1) = p.
-/
@[simp] theorem quadrupleRefresh_one {m : ℕ} {S : Matrix (Fin 2) (Fin 2) F}
    (p : CompatibleQuadruples (m := m) S) : quadrupleRefresh p 1 = p := by
  apply compatibleQuadruples_ext
  · simp [quadrupleRefresh, independentPairRefresh]
  · simp [quadrupleRefresh]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; S ∈ F^({0,…,2−1} × {0,…,2−1}); p ∈ CompatibleQuadruples(m = m, S); M, A ∈ GLₘ(F), we have

quadrupleRefresh(quadrupleRefresh(p, M), A) = quadrupleRefresh(p, (M · A)).
-/
theorem quadrupleRefresh_mul {m : ℕ} {S : Matrix (Fin 2) (Fin 2) F}
    (p : CompatibleQuadruples (m := m) S) (M A : Refresh.«GL» F m) :
    quadrupleRefresh (quadrupleRefresh p M) A = quadrupleRefresh p (M * A) := by
  apply compatibleQuadruples_ext
  · simp [quadrupleRefresh, independentPairRefresh, rowRefresh_mul]
  · simp [quadrupleRefresh, mul_inv_rev]

/-- Any two compatible independent quadruples are related by a shared invertible matrix. All four cross pairings are retained. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; S ∈ F^({0,…,2−1} × {0,…,2−1}); p, q ∈ CompatibleQuadruples(m = m, S), assume 3 ≤ m. Then

∃ M ∈ GLₘ(F), quadrupleRefresh(p, M) = q.
-/
theorem quadrupleRefresh_transitive {m : ℕ} (hm : 3 ≤ m)
    {S : Matrix (Fin 2) (Fin 2) F} (p q : CompatibleQuadruples (m := m) S) :
    ∃ M : Refresh.«GL» F m, quadrupleRefresh p M = q := by
  let l := ![p.1.val.1.val, p.1.val.2.val]
  let lout := ![q.1.val.1.val, q.1.val.2.val]
  let rho := ![q.2.val.1, q.2.val.2]
  let rout := ![p.2.val.1, p.2.val.2]
  have hc : ExtensionCompatible l rho lout rout := by
    intro i j
    fin_cases j
    · exact (congrFun p.2.property.1 i).trans (congrFun q.2.property.1 i).symm
    · exact (congrFun p.2.property.2.1 i).trans (congrFun q.2.property.2.1 i).symm
  obtain ⟨M, hrow, hcol⟩ := exists_GL_completion hm l rho lout rout
    p.1.property q.2.property.2.2 q.1.property p.2.property.2.2 hc
  refine ⟨M, compatibleQuadruples_ext ?_ ?_⟩
  · apply Prod.ext <;> apply Subtype.ext
    · exact hrow 0
    · exact hrow 1
  · apply Prod.ext
    · have h := congrArg (fun x : V F m => Matrix.mulVec (M⁻¹).val x) (hcol 0)
      simpa only [quadrupleRefresh, rho, rout, Matrix.cons_val_zero, Matrix.mulVec_mulVec,
        Units.inv_mul, Matrix.one_mulVec] using h.symm
    · have h := congrArg (fun x : V F m => Matrix.mulVec (M⁻¹).val x) (hcol 1)
      simpa only [quadrupleRefresh, rho, rout, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.mulVec_mulVec,
        Units.inv_mul, Matrix.one_mulVec] using h.symm

/-- Right translation gives an explicit bijection of transporter fibers. -/
/- Mathematical definition (normal notation): If matrices carrying quadruple p to q are called transporters, right multiplication M ↦ M A bijects them with transporters carrying p to the refresh of q by A. The inverse multiplies by A⁻¹. -/
def quadrupleTransporterEquiv {m : ℕ} {S : Matrix (Fin 2) (Fin 2) F}
    (p q : CompatibleQuadruples (m := m) S) (A : Refresh.«GL» F m) :
    {M : Refresh.«GL» F m // quadrupleRefresh p M = q} ≃
      {M : Refresh.«GL» F m // quadrupleRefresh p M = quadrupleRefresh q A} where
  toFun M := ⟨M.val * A, by rw [← quadrupleRefresh_mul, M.property]⟩
  invFun M := ⟨M.val * A⁻¹, by
    rw [← quadrupleRefresh_mul, M.property, quadrupleRefresh_mul,
      mul_inv_cancel, quadrupleRefresh_one]⟩
  left_inv M := by apply Subtype.ext; simp [mul_assoc]
  right_inv M := by apply Subtype.ext; simp [mul_assoc]

/-- Every point in the compatible orbit has the same number of realizing matrices. No invertibility-density approximation enters this exact statement. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; S ∈ F^({0,…,2−1} × {0,…,2−1}); p, q, r ∈ CompatibleQuadruples(m = m, S), assume 3 ≤ m. Then

|{M ∈ GLₘ(F) | quadrupleRefresh(p, M) = q}| = |{M ∈ GLₘ(F) | quadrupleRefresh(p, M) = r}|.
-/
theorem quadrupleTransporter_card_eq {m : ℕ} (hm : 3 ≤ m)
    {S : Matrix (Fin 2) (Fin 2) F} (p q r : CompatibleQuadruples (m := m) S) :
    Fintype.card {M : Refresh.«GL» F m // quadrupleRefresh p M = q} =
      Fintype.card {M : Refresh.«GL» F m // quadrupleRefresh p M = r} := by
  obtain ⟨A, hA⟩ := quadrupleRefresh_transitive hm q r
  rw [← hA]
  exact Fintype.card_congr (quadrupleTransporterEquiv p q A)

/-- Exact simultaneous orbit distribution for the shared matrix and its inverse. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; S ∈ F^({0,…,2−1} × {0,…,2−1}); p ∈ CompatibleQuadruples(m = m, S), assume 3 ≤ m; CompatibleQuadruples(m = m, S) ≠ ∅. Then

(quadrupleRefresh(p)_*𝒰_(GLₘ(F))) = 𝒰_(CompatibleQuadruples(m = m, S)).
-/
theorem quadrupleRefresh_uniform {m : ℕ} (hm : 3 ≤ m)
    {S : Matrix (Fin 2) (Fin 2) F} [Nonempty (CompatibleQuadruples (m := m) S)]
    (p : CompatibleQuadruples (m := m) S) :
    (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F m)).map (quadrupleRefresh p) =
      (FiniteDistribution.uniform : FiniteDistribution (CompatibleQuadruples (m := m) S)) := by
  apply FiniteDistribution.uniform_map_of_fiber_card _
    (Fintype.card {M : Refresh.«GL» F m // quadrupleRefresh p M = p})
  intro r
  exact quadrupleTransporter_card_eq hm p r p

/-- Real expectation form of the exact two-row/two-column orbit distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; S ∈ F^({0,…,2−1} × {0,…,2−1}); p ∈ CompatibleQuadruples(m = m, S); f ∈ CompatibleQuadruples(m = m, S) → ℝ, assume 3 ≤ m. Then

𝔼_(M ∈ GLₘ(F)) [f(quadrupleRefresh(p, M))] = 𝔼ᵤ [f(u)].
-/
theorem uavg_quadrupleRefresh {m : ℕ} (hm : 3 ≤ m)
    {S : Matrix (Fin 2) (Fin 2) F} (p : CompatibleQuadruples (m := m) S)
    (f : CompatibleQuadruples (m := m) S → ℝ) :
    uavg (fun M : Refresh.«GL» F m => f (quadrupleRefresh p M)) = uavg f := by
  letI : Nonempty (CompatibleQuadruples (m := m) S) := ⟨p⟩
  rw [uavg_eq_expect_uniform, uavg_eq_expect_uniform, ← expect_map, quadrupleRefresh_uniform hm]

end

end CircuitCompiler
