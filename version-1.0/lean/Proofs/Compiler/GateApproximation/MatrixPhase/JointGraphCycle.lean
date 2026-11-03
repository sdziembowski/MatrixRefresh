import Proofs.Compiler.GateApproximation.MatrixPhase.JointCycleFourier
import Proofs.Compiler.GateApproximation.MatrixPhase.JointOrbitComparison



/-!
# The actual joint-port graph four-cycle

This file connects the signed orbit comparison to the complex four-cycle of the actual shared-matrix graph restriction. Every uniform normalization is kept explicit.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical

namespace CircuitCompiler

open Refresh MatrixRefresh TableAnalysis

noncomputable section

/-
Mathematical definition (normal notation): For I a set, define

CycleQuad := (I × I) × (I × I).
-/
abbrev CycleQuad (I : Type*) := (I × I) × (I × I)

/-
Mathematical definition (normal notation): For I a set; E ∈ ℂ^(I × I); p ∈ CycleQuad(I), define

cycleEntry(E, p) := re((E(((p)₁)₁, ((p)₂)₁) · star(E(((p)₁)₂, ((p)₂)₁)) · E(((p)₁)₂, ((p)₂)₂) · star(E(((p)₁)₁, ((p)₂)₂)))).
-/
def cycleEntry {I : Type*} (E : Matrix I I ℂ) (p : CycleQuad I) : ℝ :=
  (E p.1.1 p.2.1 * star (E p.1.2 p.2.1) * E p.1.2 p.2.2 * star (E p.1.1 p.2.2)).re

/-
Mathematical definition (normal notation): For F,I a set; Φ ∈ F^(I × I); p ∈ CycleQuad(I), assume Zero(F). define

cycleConstraint(Φ, p) := Φ(((p)₁)₁, ((p)₂)₁) = 0 ∧ Φ(((p)₁)₂, ((p)₂)₁) = 0 ∧ Φ(((p)₁)₂, ((p)₂)₂) = 0 ∧ Φ(((p)₁)₁, ((p)₂)₂) = 0.
-/
def cycleConstraint {F I : Type*} [Zero F] (Φ : Matrix I I F) (p : CycleQuad I) : Prop :=
  Φ p.1.1 p.2.1 = 0 ∧ Φ p.1.2 p.2.1 = 0 ∧ Φ p.1.2 p.2.2 = 0 ∧ Φ p.1.1 p.2.2 = 0

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For I a set; E ∈ ℂ^(I × I); B ∈ ℝ; p ∈ CycleQuad(I), assume 0 ≤ B; ∀ i, j, ‖ E(i, j)‖ ≤ B. Then

|cycleEntry(E, p)| ≤ B⁴.
-/
theorem cycleEntry_abs_le {I : Type*} (E : Matrix I I ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ i j, ‖E i j‖ ≤ B) (p : CycleQuad I) : |cycleEntry E p| ≤ B ^ 4 := by
  refine (Complex.abs_re_le_norm _).trans ?_
  simp only [norm_mul, norm_star]
  have h₁ := mul_le_mul (hE p.1.1 p.2.1) (hE p.1.2 p.2.1) (norm_nonneg _) hB
  have h₂ := mul_le_mul h₁ (hE p.1.2 p.2.2) (norm_nonneg _) (mul_nonneg hB hB)
  have h₃ := mul_le_mul h₂ (hE p.1.1 p.2.2) (norm_nonneg _) (mul_nonneg (mul_nonneg hB hB) hB)
  convert h₃ using 1 <;> ring

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For I a set; E ∈ ℂ^(I × I), assume I is finite. Then

𝔼ᵤ [cycleEntry(E, u)] = re(complexMixedFourCycle(E, E, E, E)) / (|I|)⁴.
-/
theorem uavg_cycleEntry {I : Type*} [Fintype I] (E : Matrix I I ℂ) :
    uavg (cycleEntry E) = (complexMixedFourCycle E E E E).re / (Fintype.card I : ℝ) ^ 4 := by
  have hs : (∑ p : CycleQuad I, cycleEntry E p) = (complexMixedFourCycle E E E E).re := by
    simp only [Fintype.sum_prod_type, cycleEntry, complexMixedFourCycle, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  rw [uavg, hs]
  simp only [Fintype.card_prod, Nat.cast_mul]
  ring

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For F,I a set; Φ ∈ F^(I × I); E ∈ ℂ^(I × I), assume F is a field; F is finite; I is finite. Then

𝔼ₚ [{ cycleEntry(E, p) if cycleConstraint(Φ, p),; 0 otherwise }] = re(constrainedFourCycle(Φ, E)) / (|I|)⁴.
-/
theorem uavg_cycleConstraint {F I : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [DecidableEq I] (Φ : Matrix I I F) (E : Matrix I I ℂ) :
    uavg (fun p => if cycleConstraint Φ p then cycleEntry E p else 0) =
      (constrainedFourCycle Φ E).re / (Fintype.card I : ℝ) ^ 4 := by
  have hs : (∑ p : CycleQuad I, if cycleConstraint Φ p then cycleEntry E p else 0) =
      (constrainedFourCycle Φ E).re := by
    simp only [Fintype.sum_prod_type, cycleConstraint, cycleEntry, constrainedFourCycle,
      Complex.re_sum, apply_ite, Complex.zero_re]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  rw [uavg, hs]
  simp only [Fintype.card_prod, Nat.cast_mul]
  ring

/- Mathematical definition (normal notation): Separate each coordinate pair in a four-cycle quadruple: a quadruple over X × Y is identified bijectively with its X-quadruple and Y-quadruple, with their positions unchanged. -/
def cycleRegroup (X Y : Type*) : CycleQuad (X × Y) ≃ CycleQuad X × CycleQuad Y where
  toFun p := (((p.1.1.1, p.1.2.1), (p.2.1.1, p.2.2.1)),
    ((p.1.1.2, p.1.2.2), (p.2.1.2, p.2.2.2)))
  invFun p := (((p.1.1.1, p.2.1.1), (p.1.1.2, p.2.1.2)),
    ((p.1.2.1, p.2.2.1), (p.1.2.2, p.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X,Y a set; f ∈ CycleQuad((X × Y)) → ℝ, assume X is finite; Y is finite. Then

𝔼ᵤ [f(u)] = 𝔼_(x ∈ CycleQuad(X)) [𝔼_(y ∈ CycleQuad(Y)) [f((cycleRegroup(X, Y))⁻¹((x, y)))]].
-/
theorem uavg_cycleRegroup {X Y : Type*} [Fintype X] [Fintype Y]
    (f : CycleQuad (X × Y) → ℝ) :
    uavg f = uavg (fun x : CycleQuad X => uavg (fun y : CycleQuad Y =>
      f ((cycleRegroup X Y).symm (x, y)))) := by
  rw [← uavg_equiv (cycleRegroup X Y).symm f, uavg_prod]

variable {F X : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype X] [DecidableEq X]

/-
Mathematical definition (normal notation): For m ∈ ℕ; a, b ∈ X → U(F, m); E ∈ ℂ^((X × U(F, m)) × (X × U(F, m))); M ∈ GLₘ(F), define

graphRestriction(a, b, E, M) := (x, y ↦ E((x, rowRefresh(a(x), M)), (y, columnRefresh(b(y), M)))).
-/
def graphRestriction {m : ℕ} (a b : X → U F m)
    (E : Matrix (X × U F m) (X × U F m) ℂ) (M : Refresh.«GL» F m) : Matrix X X ℂ :=
  fun x y => E (x, rowRefresh (a x) M) (y, columnRefresh (b y) M)

/-
Mathematical definition (normal notation): For m ∈ ℕ; a, b ∈ X → U(F, m), define

graphConstraint(a, b) := (x, y ↦ (a((x)₁) · b((y)₁)) - ((x)₂ · (y)₂)).
-/
def graphConstraint {m : ℕ} (a b : X → U F m) : Matrix (X × U F m) (X × U F m) F :=
  fun x y => dot (a x.1).val (b y.1).val - dot x.2.val y.2.val

/-
Mathematical definition (normal notation): For m ∈ ℕ; a, b ∈ X → U(F, m); p ∈ CycleQuad(X), define

oldPairingMatrix(a, b, p) := (i, j ↦ ((a(((p)₁)₁), a(((p)₁)₂))(i) · (b(((p)₂)₁), b(((p)₂)₂))(j))).
-/
def oldPairingMatrix {m : ℕ} (a b : X → U F m) (p : CycleQuad X) : Matrix (Fin 2) (Fin 2) F :=
  fun i j => dot (![a p.1.1, a p.1.2] i).val (![b p.2.1, b p.2.2] j).val

/-
Mathematical definition (normal notation): For m ∈ ℕ; a, b ∈ X → U(F, m); p ∈ CycleQuad(X), define

oldQuadrupleBad(a, b, p) := projectiveRel(a(((p)₁)₁), a(((p)₁)₂)) ∨ projectiveRel(b(((p)₂)₁), b(((p)₂)₂)).
-/
def oldQuadrupleBad {m : ℕ} (a b : X → U F m) (p : CycleQuad X) : Prop :=
  projectiveRel (a p.1.1) (a p.1.2) ∨ projectiveRel (b p.2.1) (b p.2.2)

/- Mathematical definition (normal notation): For a quadruple (x₁,x₂,y₁,y₂) outside the bad event, the two row encoding vectors a(x₁),a(x₂) and the two column vectors b(y₁),b(y₂) are each linearly independent. Package them as a compatible quadruple with pairing matrix Cᵢⱼ = a(xᵢ) · b(yⱼ). -/
def oldQuadruple {m : ℕ} (a b : X → U F m) (p : CycleQuad X)
    (hp : ¬oldQuadrupleBad a b p) : CompatibleQuadruples (m := m) (oldPairingMatrix a b p) := by
  have h := not_or.mp hp
  refine ⟨⟨(a p.1.1, a p.1.2), pair_independent_of_not_projectiveRel _ _ h.1⟩,
    ⟨((b p.2.1).val, (b p.2.2).val), ?_, ?_, pair_independent_of_not_projectiveRel _ _ h.2⟩⟩ <;>
    funext i <;> fin_cases i <;> rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; a, b ∈ X → U(F, m); p ∈ CycleQuad(X); u ∈ AmbientQuadruple(F, m), we have

cycleConstraint(graphConstraint(a, b), (cycleRegroup(X, U(F, m)))⁻¹((p, u))) ⇔ quadruplePairings(u) = oldPairingMatrix(a, b, p).
-/
theorem graph_constraint_iff {m : ℕ} (a b : X → U F m) (p : CycleQuad X)
    (u : AmbientQuadruple F m) :
    cycleConstraint (graphConstraint a b) ((cycleRegroup X (U F m)).symm (p, u)) ↔
      quadruplePairings u = oldPairingMatrix a b p := by
  simp only [cycleConstraint, graphConstraint, cycleRegroup, Equiv.coe_fn_symm_mk, sub_eq_zero]
  constructor
  · rintro ⟨h00, h10, h11, h01⟩
    funext i j
    fin_cases i <;> fin_cases j <;> simp [quadruplePairings, oldPairingMatrix, h00, h10, h11, h01]
  · intro h
    exact ⟨(congrFun (congrFun h 0) 0).symm, (congrFun (congrFun h 1) 0).symm,
      (congrFun (congrFun h 1) 1).symm, (congrFun (congrFun h 0) 1).symm⟩

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; a, b ∈ X → U(F, m); E ∈ ℂ^((X × U(F, m)) × (X × U(F, m))); B ∈ ℝ; p ∈ CycleQuad(X), assume 4 ≤ m; 0 ≤ B; ∀ i, j, ‖ E(i, j)‖ ≤ B; ¬ (oldQuadrupleBad(a, b, p)). Then

|𝔼_(M ∈ GLₘ(F)) [cycleEntry(graphRestriction(a, b, E, M), p)] - (|F|)⁴ · 𝔼_(u ∈ AmbientQuadruple(F, m)) [{ cycleEntry(E, (cycleRegroup(X, U(F, m)))⁻¹((p, u))) if cycleConstraint(graphConstraint(a, b), (cycleRegroup(X, U(F, m)))⁻¹((p, u))),; 0 otherwise }]| ≤ (jointOrbitComparisonConstant(F) / (|F|)ᵐ) · B⁴.
-/
theorem graph_cycle_good_quadruple {m : ℕ} (hm : 4 ≤ m) (a b : X → U F m)
    (E : Matrix (X × U F m) (X × U F m) ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ i j, ‖E i j‖ ≤ B) (p : CycleQuad X) (hp : ¬oldQuadrupleBad a b p) :
    |uavg (fun M : Refresh.«GL» F m => cycleEntry (graphRestriction a b E M) p) -
      (fieldCard F : ℝ) ^ 4 * uavg (fun u : AmbientQuadruple F m =>
        if cycleConstraint (graphConstraint a b) ((cycleRegroup X (U F m)).symm (p, u))
        then cycleEntry E ((cycleRegroup X (U F m)).symm (p, u)) else 0)| ≤
      (jointOrbitComparisonConstant F / (fieldCard F : ℝ) ^ m) * B ^ 4 := by
  have h := shared_quadruple_approximation hm (oldQuadruple a b p hp)
    (fun u => cycleEntry E ((cycleRegroup X (U F m)).symm (p, u))) (B ^ 4)
    (by positivity) (fun u => cycleEntry_abs_le E B hB hE _)
  simp_rw [graph_constraint_iff]
  exact h

/-- The full graph-cycle comparison combines the compatible orbit and both old-input rank exceptions. The collision probabilities may be specialized to the exact tensor degree or supplied for another concrete input map. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; a, b ∈ X → U(F, m); r, s ∈ ℝ; E ∈ ℂ^((X × U(F, m)) × (X × U(F, m))); B ∈ ℝ, assume X ≠ ∅; 4 ≤ m; ∀ x, 𝔼_y [{ 1 if projectiveRel(a(x), a(y)),; 0 otherwise }] = r; ∀ x, 𝔼_y [{ 1 if projectiveRel(b(x), b(y)),; 0 otherwise }] = s; 0 ≤ B; ∀ i, j, ‖ E(i, j)‖ ≤ B. Then

|𝔼_(M ∈ GLₘ(F)) [𝔼_w [cycleEntry(graphRestriction(a, b, E, M), w)]] - (|F|)⁴ · 𝔼ₚ [{ cycleEntry(E, p) if cycleConstraint(graphConstraint(a, b), p),; 0 otherwise }]| ≤ (jointOrbitComparisonConstant(F) / (|F|)ᵐ + (r + s) · (1 + (|F|)⁴)) · B⁴.
-/
theorem graph_cycle_approximation [Nonempty X] {m : ℕ} (hm : 4 ≤ m)
    (a b : X → U F m) (r s : ℝ)
    (ha : ∀ x, uavg (fun y => if projectiveRel (a x) (a y) then (1 : ℝ) else 0) = r)
    (hb : ∀ x, uavg (fun y => if projectiveRel (b x) (b y) then (1 : ℝ) else 0) = s)
    (E : Matrix (X × U F m) (X × U F m) ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ i j, ‖E i j‖ ≤ B) :
    |uavg (fun M : Refresh.«GL» F m => uavg (cycleEntry (graphRestriction a b E M))) -
      (fieldCard F : ℝ) ^ 4 * uavg (fun p =>
        if cycleConstraint (graphConstraint a b) p then cycleEntry E p else 0)| ≤
      (jointOrbitComparisonConstant F / (fieldCard F : ℝ) ^ m +
        (r + s) * (1 + (fieldCard F : ℝ) ^ 4)) * B ^ 4 := by
  letI : Nonempty (U F m) := ⟨a (Classical.choice inferInstance)⟩
  let G := fun p : CycleQuad X => uavg (fun M : Refresh.«GL» F m =>
    cycleEntry (graphRestriction a b E M) p)
  let H := fun p : CycleQuad X => (fieldCard F : ℝ) ^ 4 * uavg (fun u : AmbientQuadruple F m =>
    if cycleConstraint (graphConstraint a b) ((cycleRegroup X (U F m)).symm (p, u)) then
      cycleEntry E ((cycleRegroup X (U F m)).symm (p, u)) else 0)
  let L := jointOrbitComparisonConstant F / (fieldCard F : ℝ) ^ m * B ^ 4
  let K := (1 + (fieldCard F : ℝ) ^ 4) * B ^ 4
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL : 0 ≤ L := by
    have hq : (2 : ℝ) ≤ fieldCard F := by exact_mod_cast fieldCard_ge_two (F := F)
    have hq1 : 0 ≤ (fieldCard F : ℝ) - 1 := by linarith
    dsimp [L, jointOrbitComparisonConstant, jointOrbitDensityConstant]
    positivity
  have hpoint (p : CycleQuad X) : |G p - H p| ≤ L + (if oldQuadrupleBad a b p then K else 0) := by
    by_cases hp : oldQuadrupleBad a b p
    · rw [if_pos hp]
      have hG : |G p| ≤ B ^ 4 := abs_uavg_le_bound _ _ (fun M =>
        cycleEntry_abs_le _ B hB (fun x y => hE _ _) p)
      have hH : |H p| ≤ (fieldCard F : ℝ) ^ 4 * B ^ 4 := by
        dsimp [H]
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (fieldCard F : ℝ) ^ 4)]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply abs_uavg_le_bound
        intro u
        split_ifs
        · exact cycleEntry_abs_le E B hB hE _
        · simp; positivity
      have ht := (abs_sub _ _).trans (add_le_add hG hH)
      dsimp [K]
      nlinarith
    · rw [if_neg hp, add_zero]
      exact graph_cycle_good_quadruple hm a b E B hB hE p hp
  have hbad : uavg (fun p : CycleQuad X => if oldQuadrupleBad a b p then K else 0) ≤ (r + s) * K := by
    have h := two_relation_exception_le (fun x y => projectiveRel (a x) (a y))
      (fun x y => projectiveRel (b x) (b y)) r s K hK ha hb (fun _ _ _ _ => K)
      (fun _ _ _ _ => (abs_of_nonneg hK).le)
    simp only [uavg_prod]
    convert h using 1
    apply uavg_congr
    intro x
    apply uavg_congr
    intro x'
    apply uavg_congr
    intro y
    apply uavg_congr
    intro y'
    by_cases hp : projectiveRel (a x) (a x') ∨ projectiveRel (b y) (b y') <;>
      simp [oldQuadrupleBad, hp, abs_of_nonneg hK]
  have hfinal : |uavg G - uavg H| ≤ L + (r + s) * K := by
    rw [← uavg_sub]
    refine (abs_uavg_le_uavg_abs _).trans ((uavg_mono hpoint).trans ?_)
    rw [uavg_add, uavg_const]
    exact add_le_add (le_refl _) hbad
  have hG : uavg G = uavg (fun M : Refresh.«GL» F m => uavg (cycleEntry (graphRestriction a b E M))) :=
    uavg_comm _
  have hH : uavg H = (fieldCard F : ℝ) ^ 4 * uavg (fun p =>
      if cycleConstraint (graphConstraint a b) p then cycleEntry E p else 0) := by
    rw [uavg_cycleRegroup]
    exact uavg_const_mul _ _
  rw [hG, hH] at hfinal
  convert hfinal using 1
  dsimp [L, K]
  ring

/-- The operator fourth moment on the actual graph is bounded by its exact normalized four-cycle. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; a, b ∈ X → U(F, m); E ∈ ℂ^((X × U(F, m)) × (X × U(F, m))); M ∈ GLₘ(F), assume X ≠ ∅. Then

(‖ graphRestriction(a, b, E, M)‖ / |X|)⁴ ≤ 𝔼ᵤ [cycleEntry(graphRestriction(a, b, E, M), u)].
-/
theorem graph_norm_four_le_cycle [Nonempty X] {m : ℕ} (a b : X → U F m)
    (E : Matrix (X × U F m) (X × U F m) ℂ) (M : Refresh.«GL» F m) :
    (‖graphRestriction a b E M‖ / Fintype.card X) ^ 4 ≤
      uavg (cycleEntry (graphRestriction a b E M)) := by
  rw [uavg_cycleEntry, div_pow]
  exact div_le_div_of_nonneg_right (complexMatrix_norm_four_le_fourCycle _) (by positivity)

/-- Fourier expansion controls the full averaged graph operator fourth moment, with the actual orbit and collision errors made explicit. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; a, b ∈ X → U(F, m); r, s ∈ ℝ; ψ ∈ AddChar(F, ℂ); E ∈ ℂ^((X × U(F, m)) × (X × U(F, m))); B, β ∈ ℝ, assume X ≠ ∅; 4 ≤ m; ∀ x, 𝔼_y [{ 1 if projectiveRel(a(x), a(y)),; 0 otherwise }] = r; ∀ x, 𝔼_y [{ 1 if projectiveRel(b(x), b(y)),; 0 otherwise }] = s; ψ.IsPrimitive; 0 ≤ B; 0 ≤ β; ∀ i, j, ‖ E(i, j)‖ ≤ B; ∀ c, ‖ constraintTwist(ψ, graphConstraint(a, b), E, c)‖ / |(X × U(F, m))| ≤ β. Then

𝔼_(M ∈ GLₘ(F)) [(‖ graphRestriction(a, b, E, M)‖ / |X|)⁴] ≤ (|F|)⁴ · β² · (complexMatrixL2Sq(E) / (|(X × U(F, m))|)²) + (jointOrbitComparisonConstant(F) / (|F|)ᵐ + (r + s) · (1 + (|F|)⁴)) · B⁴.
-/
theorem graph_norm_four_moment [Nonempty X] {m : ℕ} (hm : 4 ≤ m)
    (a b : X → U F m) (r s : ℝ)
    (ha : ∀ x, uavg (fun y => if projectiveRel (a x) (a y) then (1 : ℝ) else 0) = r)
    (hb : ∀ x, uavg (fun y => if projectiveRel (b x) (b y) then (1 : ℝ) else 0) = s)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (E : Matrix (X × U F m) (X × U F m) ℂ) (B β : ℝ) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    (hE : ∀ i j, ‖E i j‖ ≤ B)
    (hTwist : ∀ c, ‖constraintTwist ψ (graphConstraint a b) E c‖ /
      Fintype.card (X × U F m) ≤ β) :
    uavg (fun M : Refresh.«GL» F m => (‖graphRestriction a b E M‖ / Fintype.card X) ^ 4) ≤
      (fieldCard F : ℝ) ^ 4 * β ^ 2 *
        (complexMatrixL2Sq E / (Fintype.card (X × U F m) : ℝ) ^ 2) +
      (jointOrbitComparisonConstant F / (fieldCard F : ℝ) ^ m +
        (r + s) * (1 + (fieldCard F : ℝ) ^ 4)) * B ^ 4 := by
  letI : Nonempty (U F m) := ⟨a (Classical.choice inferInstance)⟩
  have hcycle := graph_cycle_approximation hm a b r s ha hb E B hB hE
  have hfourier := constrainedFourCycle_uniform_re_le ψ hψ (graphConstraint a b) E β hβ hTwist
  have hre : ((fieldCard F : ℂ) ^ 4 * constrainedFourCycle (graphConstraint a b) E).re =
      (fieldCard F : ℝ) ^ 4 * (constrainedFourCycle (graphConstraint a b) E).re := by
    simp [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.mul_re]
  rw [hre] at hfourier
  rw [uavg_cycleConstraint] at hcycle
  have hupper := (le_abs_self _).trans hcycle
  have hnorm := uavg_mono (fun M => graph_norm_four_le_cycle a b E M)
  have hreorder : (fieldCard F : ℝ) ^ 4 * ((constrainedFourCycle (graphConstraint a b) E).re /
      (Fintype.card (X × U F m) : ℝ) ^ 4) =
      ((fieldCard F : ℝ) ^ 4 * (constrainedFourCycle (graphConstraint a b) E).re) /
        (Fintype.card (X × U F m) : ℝ) ^ 4 := by ring
  rw [hreorder] at hupper
  linarith

/-
Mathematical definition (normal notation): For F a set, assume F is a field; F is finite. define

tensorCycleErrorConstant := jointOrbitComparisonConstant(F) + 8 · (|F| - 1)² · (1 + (|F|)⁴).
-/
def tensorCycleErrorConstant (F : Type*) [Field F] [Fintype F] : ℝ :=
  jointOrbitComparisonConstant F +
    8 * ((fieldCard F : ℝ) - 1) ^ 2 * (1 + (fieldCard F : ℝ) ^ 4)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, assume 2 ≤ n. Then

jointOrbitComparisonConstant(F) / (|F|)^(n · n) + (2 · ((|F| - 1)²) / (|U(F, n)|)²) · (1 + (|F|)⁴) ≤ tensorCycleErrorConstant(F) / (|F|ⁿ)².
-/
theorem tensor_cycle_error_coefficient {n : ℕ} (hn : 2 ≤ n) :
    jointOrbitComparisonConstant F / (fieldCard F : ℝ) ^ (n * n) +
      (2 * (((fieldCard F - 1 : ℕ) : ℝ) ^ 2) / (Fintype.card (U F n) : ℝ) ^ 2) *
        (1 + (fieldCard F : ℝ) ^ 4) ≤
      tensorCycleErrorConstant F / (vectorCard F n : ℝ) ^ 2 := by
  have hq : (2 : ℝ) ≤ fieldCard F := by exact_mod_cast fieldCard_ge_two (F := F)
  have hN := vectorCard_real_ge_four (F := F) hn
  have hNsq : 0 < (vectorCard F n : ℝ) ^ 2 := by positivity
  have hNm : 0 < ((vectorCard F n : ℝ) - 1) ^ 2 := by nlinarith
  have hQ : (vectorCard F n : ℝ) ^ 2 ≤ (fieldCard F : ℝ) ^ (n * n) := by
    have hp : (fieldCard F ^ n) ^ 2 ≤ fieldCard F ^ (n * n) := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (show 1 ≤ fieldCard F by have := fieldCard_ge_two (F := F); omega) (by nlinarith)
    exact_mod_cast hp
  have hC : 0 ≤ jointOrbitComparisonConstant F := by
    have hq1 : 0 ≤ (fieldCard F : ℝ) - 1 := by linarith
    unfold jointOrbitComparisonConstant jointOrbitDensityConstant
    positivity
  have hfirst := div_le_div_of_nonneg_left hC hNsq hQ
  have hratio : 2 * ((fieldCard F : ℝ) - 1) ^ 2 / ((vectorCard F n : ℝ) - 1) ^ 2 ≤
      8 * ((fieldCard F : ℝ) - 1) ^ 2 / (vectorCard F n : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ hNm hNsq).2
    have hd : (vectorCard F n : ℝ) ^ 2 ≤ 4 * ((vectorCard F n : ℝ) - 1) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hd (sq_nonneg ((fieldCard F : ℝ) - 1))]
  rw [card_U_real, Nat.cast_sub (show 1 ≤ fieldCard F by have := fieldCard_ge_two (F := F); omega), Nat.cast_one]
  refine (add_le_add hfirst (mul_le_mul_of_nonneg_right hratio (by positivity))).trans_eq ?_
  unfold tensorCycleErrorConstant
  ring

/-- The concrete tensor ports satisfy the residual fourth-moment bound with a field-only error constant times `N⁻²`. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; ψ ∈ AddChar(F, ℂ); E ∈ ℂ^(((U(F, n) × U(F, n)) × U(F, (n · n))) × ((U(F, n) × U(F, n)) × U(F, (n · n)))); B, β ∈ ℝ, assume 2 ≤ n; ψ.IsPrimitive; 0 ≤ B; 0 ≤ β; ∀ i, j, ‖ E(i, j)‖ ≤ B; ∀ c, ‖ constraintTwist(ψ, graphConstraint(inputTensor, inputTensor), E, c)‖ / |((U(F, n) × U(F, n)) × U(F, (n · n)))| ≤ β. Then

𝔼_(M ∈ GL_(n · n)(F)) [(‖ graphRestriction(inputTensor, inputTensor, E, M)‖ / |(U(F, n) × U(F, n))|)⁴] ≤ (|F|)⁴ · β² · (complexMatrixL2Sq(E) / (|((U(F, n) × U(F, n)) × U(F, (n · n)))|)²) + (tensorCycleErrorConstant(F) / (|F|ⁿ)²) · B⁴.
-/
theorem tensor_graph_norm_four_moment {n : ℕ} (hn : 2 ≤ n)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (E : Matrix ((U F n × U F n) × U F (n * n)) ((U F n × U F n) × U F (n * n)) ℂ)
    (B β : ℝ) (hB : 0 ≤ B) (hβ : 0 ≤ β) (hE : ∀ i j, ‖E i j‖ ≤ B)
    (hTwist : ∀ c, ‖constraintTwist ψ (graphConstraint inputTensor inputTensor) E c‖ /
      Fintype.card ((U F n × U F n) × U F (n * n)) ≤ β) :
    uavg (fun M : Refresh.«GL» F (n * n) =>
      (‖graphRestriction inputTensor inputTensor E M‖ / Fintype.card (U F n × U F n)) ^ 4) ≤
      (fieldCard F : ℝ) ^ 4 * β ^ 2 *
        (complexMatrixL2Sq E / (Fintype.card ((U F n × U F n) × U F (n * n)) : ℝ) ^ 2) +
      (tensorCycleErrorConstant F / (vectorCard F n : ℝ) ^ 2) * B ^ 4 := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  have h := graph_norm_four_moment (m := n * n) (by nlinarith) inputTensor inputTensor
    _ _ tensor_projective_probability tensor_projective_probability ψ hψ E B β hB hβ hE hTwist
  have hcoeff := tensor_cycle_error_coefficient (F := F) hn
  have he : (((fieldCard F - 1 : ℕ) : ℝ) ^ 2 / (Fintype.card (U F n) : ℝ) ^ 2 +
      ((fieldCard F - 1 : ℕ) : ℝ) ^ 2 / (Fintype.card (U F n) : ℝ) ^ 2) =
      2 * (((fieldCard F - 1 : ℕ) : ℝ) ^ 2) / (Fintype.card (U F n) : ℝ) ^ 2 := by ring
  rw [he] at h
  exact h.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcoeff (by positivity)))

/-- Taking fourth roots gives the manuscript's actual residual graph bound: the main term is `q sqrt(β) sqrt(L₂(E))`, and the error is a field-only constant times `N^(-1/2)` times the entry cap. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; ψ ∈ AddChar(F, ℂ); E ∈ ℂ^(((U(F, n) × U(F, n)) × U(F, (n · n))) × ((U(F, n) × U(F, n)) × U(F, (n · n)))); B, β ∈ ℝ, assume 2 ≤ n; ψ.IsPrimitive; 0 ≤ B; 0 ≤ β; ∀ i, j, ‖ E(i, j)‖ ≤ B; ∀ c, ‖ constraintTwist(ψ, graphConstraint(inputTensor, inputTensor), E, c)‖ / |((U(F, n) × U(F, n)) × U(F, (n · n)))| ≤ β. Then

𝔼_(M ∈ GL_(n · n)(F)) [‖ graphRestriction(inputTensor, inputTensor, E, M)‖ / |(U(F, n) × U(F, n))|] ≤ |F| · √β · fourthRoot((complexMatrixL2Sq(E) / (|((U(F, n) × U(F, n)) × U(F, (n · n)))|)²)) + (fourthRoot(tensorCycleErrorConstant(F)) / √(|F|ⁿ)) · B.
-/
theorem tensor_graph_norm_mean {n : ℕ} (hn : 2 ≤ n)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (E : Matrix ((U F n × U F n) × U F (n * n)) ((U F n × U F n) × U F (n * n)) ℂ)
    (B β : ℝ) (hB : 0 ≤ B) (hβ : 0 ≤ β) (hE : ∀ i j, ‖E i j‖ ≤ B)
    (hTwist : ∀ c, ‖constraintTwist ψ (graphConstraint inputTensor inputTensor) E c‖ /
      Fintype.card ((U F n × U F n) × U F (n * n)) ≤ β) :
    uavg (fun M : Refresh.«GL» F (n * n) =>
      ‖graphRestriction inputTensor inputTensor E M‖ / Fintype.card (U F n × U F n)) ≤
      (fieldCard F : ℝ) * Real.sqrt β * fourthRoot
        (complexMatrixL2Sq E / (Fintype.card ((U F n × U F n) × U F (n * n)) : ℝ) ^ 2) +
      (fourthRoot (tensorCycleErrorConstant F) / Real.sqrt (vectorCard F n : ℝ)) * B := by
  have hmoment := tensor_graph_norm_four_moment hn ψ hψ E B β hB hβ hE hTwist
  let f := fun M : Refresh.«GL» F (n * n) =>
    ‖graphRestriction inputTensor inputTensor E M‖ / Fintype.card (U F n × U F n)
  have hf (M : Refresh.«GL» F (n * n)) : 0 ≤ f M := by dsimp [f]; positivity
  have hJ := expect_fourthRoot_le (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n * n)))
    (fun M => f M ^ 4) (fun _ => by positivity)
  simp only [fourthRoot_pow_four_of_nonneg (hf _), ← uavg_eq_expect_uniform] at hJ
  refine hJ.trans ((fourthRoot_mono hmoment).trans ?_)
  have hq0 : 0 ≤ (fieldCard F : ℝ) := Nat.cast_nonneg _
  have hN0 : 0 ≤ (vectorCard F n : ℝ) := Nat.cast_nonneg _
  have hH : 0 ≤ complexMatrixL2Sq E /
      (Fintype.card ((U F n × U F n) × U F (n * n)) : ℝ) ^ 2 :=
    div_nonneg (complexMatrixL2Sq_nonneg E) (sq_nonneg _)
  have hC : 0 ≤ tensorCycleErrorConstant F := by
    have hq : (2 : ℝ) ≤ fieldCard F := by exact_mod_cast fieldCard_ge_two (F := F)
    have hq1 : 0 ≤ (fieldCard F : ℝ) - 1 := by linarith
    unfold tensorCycleErrorConstant jointOrbitComparisonConstant jointOrbitDensityConstant
    positivity
  refine (fourthRoot_add_le (by positivity) (by positivity)).trans_eq ?_
  rw [fourthRoot_mul (mul_nonneg (pow_nonneg hq0 _) (sq_nonneg β)),
    fourthRoot_mul (pow_nonneg hq0 _), fourthRoot_pow_four_of_nonneg hq0,
    fourthRoot_mul (div_nonneg hC (sq_nonneg _)), fourthRoot_pow_four_of_nonneg hB]
  have hβroot : fourthRoot (β ^ 2) = Real.sqrt β := by
    simp only [fourthRoot, Real.sqrt_sq hβ]
  have hCroot : fourthRoot (tensorCycleErrorConstant F / (vectorCard F n : ℝ) ^ 2) =
      fourthRoot (tensorCycleErrorConstant F) / Real.sqrt (vectorCard F n : ℝ) := by
    unfold fourthRoot
    rw [Real.sqrt_div hC, Real.sqrt_div (Real.sqrt_nonneg _), Real.sqrt_sq hN0]
  rw [hβroot, hCroot]

end

end CircuitCompiler
