import Proofs.Compiler.GateApproximation.MatrixPhase.JointOrbitDensity



/-!
# Exact orbit change of measure

The compatible independent quadruple carrier is embedded into four nonzero vectors. Its uniform average is exactly the ambient masked average multiplied by the proved orbit density.
-/
set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators Classical

namespace CircuitCompiler

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-
Mathematical definition (normal notation): For F a set; m ∈ ℕ, assume F is a field. define

AmbientQuadruple(m) := (U(F, m) × U(F, m)) × (U(F, m) × U(F, m)).
-/
abbrev AmbientQuadruple (F : Type*) [Field F] (m : ℕ) :=
  (U F m × U F m) × (U F m × U F m)

/-
Mathematical definition (normal notation): For m ∈ ℕ; p ∈ AmbientQuadruple(F, m), define

quadruplePairings(p) := (i, j ↦ ((((p)₁)₁, ((p)₁)₂)(i) · (((p)₂)₁, ((p)₂)₂)(j))).
-/
def quadruplePairings {m : ℕ} (p : AmbientQuadruple F m) : Matrix (Fin 2) (Fin 2) F :=
  fun i j => dot (![p.1.1.val, p.1.2.val] i) (![p.2.1.val, p.2.2.val] j)

/-
Mathematical definition (normal notation): For m ∈ ℕ; p ∈ AmbientQuadruple(F, m), define

quadrupleIndependent(p) := LinearIndependent(F, (((p)₁)₁, ((p)₁)₂)) ∧ LinearIndependent(F, (((p)₂)₁, ((p)₂)₂)).
-/
def quadrupleIndependent {m : ℕ} (p : AmbientQuadruple F m) : Prop :=
  LinearIndependent F ![p.1.1.val, p.1.2.val] ∧
    LinearIndependent F ![p.2.1.val, p.2.2.val]

/-
Mathematical definition (normal notation): For m ∈ ℕ; S ∈ F^({0,…,2−1} × {0,…,2−1}); p ∈ AmbientQuadruple(F, m), define

quadrupleAdmissible(S, p) := quadrupleIndependent(p) ∧ quadruplePairings(p) = S.
-/
def quadrupleAdmissible {m : ℕ} (S : Matrix (Fin 2) (Fin 2) F)
    (p : AmbientQuadruple F m) : Prop :=
  quadrupleIndependent p ∧ quadruplePairings p = S

/-- Forget the constraints of the counted compatible carrier. -/
/- Mathematical definition (normal notation): Forget the independence and prescribed-pairing certificates of a compatible quadruple, retaining its four nonzero vectors. This forgetful map is injective. -/
def quadrupleEmbedding {m : ℕ} (S : Matrix (Fin 2) (Fin 2) F) :
    CompatibleQuadruples (m := m) S ↪ AmbientQuadruple F m where
  toFun p := (p.1.val,
    (⟨p.2.val.1, p.2.property.2.2.ne_zero 0⟩, ⟨p.2.val.2, p.2.property.2.2.ne_zero 1⟩))
  inj' := by
    intro p q h
    apply compatibleQuadruples_ext (congrArg Prod.fst h)
    exact Prod.ext (congrArg (fun a => a.2.1.val) h) (congrArg (fun a => a.2.2.val) h)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; S ∈ F^({0,…,2−1} × {0,…,2−1}); p ∈ CompatibleQuadruples(m = m, S), we have

quadrupleAdmissible(S, quadrupleEmbedding(S, p)) .
-/
theorem quadrupleEmbedding_admissible {m : ℕ} (S : Matrix (Fin 2) (Fin 2) F)
    (p : CompatibleQuadruples (m := m) S) : quadrupleAdmissible S (quadrupleEmbedding S p) := by
  refine ⟨⟨p.1.property, p.2.property.2.2⟩, ?_⟩
  funext i j
  fin_cases j
  · exact congrFun p.2.property.1 i
  · exact congrFun p.2.property.2.1 i

/-- The embedding contains exactly the independent quadruples with the four prescribed cross pairings. -/
/- Mathematical definition (normal notation): Compatible quadruples with pairing matrix S are exactly ambient quadruples whose row pair and column pair are each independent and whose four cross pairings equal the entries of S. -/
def quadrupleSubtypeEquiv {m : ℕ} (S : Matrix (Fin 2) (Fin 2) F) :
    CompatibleQuadruples (m := m) S ≃ {p : AmbientQuadruple F m // quadrupleAdmissible S p} where
  toFun p := ⟨quadrupleEmbedding S p, quadrupleEmbedding_admissible S p⟩
  invFun p := ⟨⟨p.val.1, p.property.1.1⟩, ⟨(p.val.2.1.val, p.val.2.2.val), by
    refine ⟨?_, ?_, p.property.1.2⟩
    · funext i
      exact congrFun (congrFun p.property.2 i) 0
    · funext i
      exact congrFun (congrFun p.property.2 i) 1⟩⟩
  left_inv p := by apply compatibleQuadruples_ext <;> rfl
  right_inv p := by apply Subtype.ext; rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; S ∈ F^({0,…,2−1} × {0,…,2−1}); f ∈ AmbientQuadruple(F, m) → ℝ, we have

(∑_(p ∈ CompatibleQuadruples(m = m, S)) (f(quadrupleEmbedding(S, p)))) = ∑_(p ∈ AmbientQuadruple(F, m)) ({ f(p) if quadrupleAdmissible(S, p),; 0 otherwise }).
-/
theorem quadruple_sum {m : ℕ} (S : Matrix (Fin 2) (Fin 2) F)
    (f : AmbientQuadruple F m → ℝ) :
    (∑ p : CompatibleQuadruples (m := m) S, f (quadrupleEmbedding S p)) =
      ∑ p : AmbientQuadruple F m, if quadrupleAdmissible S p then f p else 0 := by
  have h := Equiv.sum_comp (quadrupleSubtypeEquiv (m := m) S) (fun p => f p.val)
  change (∑ p : CompatibleQuadruples (m := m) S, f (quadrupleEmbedding S p)) =
    ∑ p : {p : AmbientQuadruple F m // quadrupleAdmissible S p}, f p.val at h
  have hs := Fintype.sum_subtype_add_sum_subtype (quadrupleAdmissible S)
    (fun p => if quadrupleAdmissible S p then f p else 0)
  have hp (p : {p : AmbientQuadruple F m // quadrupleAdmissible S p}) :
      (if quadrupleAdmissible S p.val then f p.val else 0) = f p.val := if_pos p.property
  have hn (p : {p : AmbientQuadruple F m // ¬quadrupleAdmissible S p}) :
      (if quadrupleAdmissible S p.val then f p.val else 0) = 0 := if_neg p.property
  exact h.trans (by simpa only [hp, hn, Finset.sum_const_zero, add_zero] using hs)

/-- Exact density identity, including both output rank restrictions. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; S ∈ F^({0,…,2−1} × {0,…,2−1}); f ∈ AmbientQuadruple(F, m) → ℝ, assume U(F, m) ≠ ∅. Then

𝔼_(p ∈ CompatibleQuadruples(m = m, S)) [f(quadrupleEmbedding(S, p))] = jointOrbitDensity(m, S) · 𝔼ₚ [{ f(p) if quadrupleAdmissible(S, p),; 0 otherwise }].
-/
theorem uavg_compatibleQuadruples {m : ℕ} [Nonempty (U F m)]
    (S : Matrix (Fin 2) (Fin 2) F) (f : AmbientQuadruple F m → ℝ) :
    uavg (fun p : CompatibleQuadruples (m := m) S => f (quadrupleEmbedding S p)) =
      jointOrbitDensity m S * uavg (fun p => if quadrupleAdmissible S p then f p else 0) := by
  rw [uavg, quadruple_sum]
  unfold jointOrbitDensity uavg
  simp only [Fintype.card_prod, Nat.cast_mul]
  have hcard : (Fintype.card (U F m) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The shared matrix average equals the ambient density formula exactly. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; S ∈ F^({0,…,2−1} × {0,…,2−1}); p ∈ CompatibleQuadruples(m = m, S); f ∈ AmbientQuadruple(F, m) → ℝ, assume 3 ≤ m; U(F, m) ≠ ∅. Then

𝔼_(M ∈ GLₘ(F)) [f(quadrupleEmbedding(S, quadrupleRefresh(p, M)))] = jointOrbitDensity(m, S) · 𝔼ₚ [{ f(p) if quadrupleAdmissible(S, p),; 0 otherwise }].
-/
theorem uavg_shared_quadruple {m : ℕ} (hm : 3 ≤ m) [Nonempty (U F m)]
    {S : Matrix (Fin 2) (Fin 2) F} (p : CompatibleQuadruples (m := m) S)
    (f : AmbientQuadruple F m → ℝ) :
    uavg (fun M : Refresh.«GL» F m => f (quadrupleEmbedding S (quadrupleRefresh p M))) =
      jointOrbitDensity m S * uavg (fun p => if quadrupleAdmissible S p then f p else 0) := by
  exact (uavg_quadrupleRefresh hm p (fun q => f (quadrupleEmbedding S q))).trans
    (uavg_compatibleQuadruples S f)

end

end CircuitCompiler
