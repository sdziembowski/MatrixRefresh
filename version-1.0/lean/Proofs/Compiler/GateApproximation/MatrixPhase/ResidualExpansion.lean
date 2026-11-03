import Proofs.Compiler.GateApproximation.MatrixPhase.RankCases
import Proofs.Compiler.GateApproximation.MatrixPhase.ResidualGeometry



/-!
# Expanding the actual residual matrix moment into completion probabilities

This is a signed identity: independent row-image variables are inserted by finite fiber summation. No absolute value is taken before the four-cycle.
-/
set_option autoImplicit false

set_option maxHeartbeats 1500000

open scoped BigOperators Classical

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A a set; p ∈ A → Prop, assume A is finite; DecidablePred(p). Then

𝔼ₐ [{ 1 if p(a),; 0 otherwise }] = |{a | p(a)}| / |A|.
-/
theorem uavg_indicator_eq_card {A : Type*} [Fintype A]
    (p : A → Prop) [DecidablePred p] :
    uavg (fun a => if p a then (1 : ℝ) else 0) =
      (Fintype.card {a // p a} : ℝ) / Fintype.card A := by
  simp [uavg, Fintype.card_subtype, Finset.sum_boole, div_eq_mul_inv, mul_comm]

/-- Insert a uniform candidate for a finite deterministic output. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A,B a set; g ∈ A → B; f ∈ A → ℝ, assume A is finite; B is finite; B ≠ ∅. Then

𝔼ᵤ [f(u)] = |B| · 𝔼_b [𝔼ₐ [{ f(a) if g(a) = b,; 0 otherwise }]].
-/
theorem uavg_insert_output {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (g : A → B) (f : A → ℝ) :
    uavg f = (Fintype.card B : ℝ) *
      uavg (fun b => uavg (fun a => if g a = b then f a else 0)) := by
  rw [uavg_comm, ← uavg_const_mul]
  apply uavg_congr
  intro a
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [uavg, hB]

/-- Exact finite fiber formula with an additional deterministic event. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A,B a set; g ∈ A → B; p ∈ A → Prop; f ∈ B → ℝ, assume A is finite; B is finite; B ≠ ∅. Then

𝔼ₐ [{ f(g(a)) if p(a),; 0 otherwise }] = |B| · 𝔼_b [(|{a | g(a) = b ∧ p(a)}| / |A|) · f(b)].
-/
theorem uavg_output_event {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (g : A → B) (p : A → Prop) (f : B → ℝ) :
    uavg (fun a => if p a then f (g a) else 0) =
      (Fintype.card B : ℝ) * uavg (fun b =>
        ((Fintype.card {a // g a = b ∧ p a} : ℝ) / Fintype.card A) * f b) := by
  rw [uavg_insert_output g]
  congr 1
  apply uavg_congr
  intro b
  have hp (a : A) :
      (if g a = b then (if p a then f (g a) else 0) else 0) =
        (if g a = b ∧ p a then (1 : ℝ) else 0) * f b := by
    split_ifs <;> simp_all
  simp_rw [hp]
  rw [uavg_mul_const]
  exact congrArg (fun x : ℝ => x * f b)
    (uavg_indicator_eq_card (fun a => g a = b ∧ p a))

variable {F X Y : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype X] [Fintype Y] {m : ℕ}

/-
Mathematical definition (normal notation): For E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ; x₀, x₁ ∈ X; u₀, u₁ ∈ V(F, m); y₀, y₁ ∈ Y; v₀, v₁ ∈ V(F, m), define

fullFeatureCorner(E, x₀, x₁, u₀, u₁, y₀, y₁, v₀, v₁) := featureZeroExtend(E, x₀, u₀, y₀, v₀) · featureZeroExtend(E, x₁, u₁, y₀, v₀) · featureZeroExtend(E, x₁, u₁, y₁, v₁) · featureZeroExtend(E, x₀, u₀, y₁, v₁).
-/
def fullFeatureCorner (E : (X × U F m) → (Y × U F m) → ℝ)
    (x₀ x₁ : X) (u₀ u₁ : V F m) (y₀ y₁ : Y) (v₀ v₁ : V F m) : ℝ :=
  featureZeroExtend E x₀ u₀ y₀ v₀ * featureZeroExtend E x₁ u₁ y₀ v₀ *
    featureZeroExtend E x₁ u₁ y₁ v₁ * featureZeroExtend E x₀ u₀ y₁ v₁

omit [Fintype X] [Fintype Y] in
/-- For fixed old rows and new columns, insert independent prescribed row images. The remaining weight is the exact four-constraint matrix probability. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m); b ∈ Y → U(F, m); E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ; x₀, x₁ ∈ X; y₀, y₁ ∈ Y; v₀, v₁ ∈ V(F, m), we have

𝔼_(A ∈ F^({0,…,m−1} × {0,…,m−1})) [{ fullFeatureCorner(E, x₀, x₁, Matrix.vecMul(a(x₀), A), Matrix.vecMul(a(x₁), A), y₀, y₁, v₀, v₁) if Matrix.mulVec(A, v₀) = b(y₀) ∧ Matrix.mulVec(A, v₁) = b(y₁),; 0 otherwise }] = (|F|ᵐ)² · 𝔼_(u ∈ V(F, m) × V(F, m)) [(|MatrixCompletion((a(x₀), a(x₁)), (v₀, v₁), ((u)₁, (u)₂), (b(y₀), b(y₁)))| / |F^({0,…,m−1} × {0,…,m−1})|) · fullFeatureCorner(E, x₀, x₁, (u)₁, (u)₂, y₀, y₁, v₀, v₁)].
-/
theorem fullFeatureCorner_average (a : X → U F m) (b : Y → U F m)
    (E : (X × U F m) → (Y × U F m) → ℝ)
    (x₀ x₁ : X) (y₀ y₁ : Y) (v₀ v₁ : V F m) :
    uavg (fun A : Matrix (Fin m) (Fin m) F =>
      if Matrix.mulVec A v₀ = (b y₀).val ∧ Matrix.mulVec A v₁ = (b y₁).val then
        fullFeatureCorner E x₀ x₁ (Matrix.vecMul (a x₀).val A)
          (Matrix.vecMul (a x₁).val A) y₀ y₁ v₀ v₁ else 0) =
      (vectorCard F m : ℝ)^2 * uavg (fun u : V F m × V F m =>
        ((Fintype.card (MatrixCompletion ![(a x₀).val,(a x₁).val] ![v₀,v₁]
          ![u.1,u.2] ![(b y₀).val,(b y₁).val]) : ℝ) /
            Fintype.card (Matrix (Fin m) (Fin m) F)) *
          fullFeatureCorner E x₀ x₁ u.1 u.2 y₀ y₁ v₀ v₁) := by
  have h := uavg_output_event
    (fun A : Matrix (Fin m) (Fin m) F =>
      (Matrix.vecMul (a x₀).val A, Matrix.vecMul (a x₁).val A))
    (fun A => Matrix.mulVec A v₀ = (b y₀).val ∧ Matrix.mulVec A v₁ = (b y₁).val)
    (fun u : V F m × V F m => fullFeatureCorner E x₀ x₁ u.1 u.2 y₀ y₁ v₀ v₁)
  have hcard (u : V F m × V F m) :
      Fintype.card {A : Matrix (Fin m) (Fin m) F //
        (Matrix.vecMul (a x₀).val A, Matrix.vecMul (a x₁).val A) = u ∧
        (Matrix.mulVec A v₀ = (b y₀).val ∧ Matrix.mulVec A v₁ = (b y₁).val)} =
      Fintype.card (MatrixCompletion ![(a x₀).val,(a x₁).val] ![v₀,v₁]
        ![u.1,u.2] ![(b y₀).val,(b y₁).val]) := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro A
    simp [Prod.ext_iff, Fin.forall_fin_two]
  simp only [← Nat.card_eq_fintype_card] at hcard h
  simp_rw [hcard] at h
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, V, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_pow, vectorCard, fieldCard, ← pow_two] using h

omit [Fintype X] [Fintype Y] in
/-- The square-root column weight appears four times around a cycle. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m); b ∈ Y → U(F, m); E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ; A ∈ F^({0,…,m−1} × {0,…,m−1}); x₀, x₁ ∈ X; y₀, y₁ ∈ Y; v₀, v₁ ∈ V(F, m), we have

cornerProduct(enlargedRestriction(a, b, E, A), ((x₀, x₁), ((y₀, v₀), (y₁, v₁)))) = (|F|ᵐ)² · ({ fullFeatureCorner(E, x₀, x₁, Matrix.vecMul(a(x₀), A), Matrix.vecMul(a(x₁), A), y₀, y₁, v₀, v₁) if Matrix.mulVec(A, v₀) = b(y₀) ∧ Matrix.mulVec(A, v₁) = b(y₁),; 0 otherwise }).
-/
theorem enlarged_corner (a : X → U F m) (b : Y → U F m)
    (E : (X × U F m) → (Y × U F m) → ℝ)
    (A : Matrix (Fin m) (Fin m) F) (x₀ x₁ : X) (y₀ y₁ : Y) (v₀ v₁ : V F m) :
    cornerProduct (enlargedRestriction a b E A) ((x₀,x₁),((y₀,v₀),(y₁,v₁))) =
      (vectorCard F m : ℝ)^2 *
        (if Matrix.mulVec A v₀ = (b y₀).val ∧ Matrix.mulVec A v₁ = (b y₁).val then
          fullFeatureCorner E x₀ x₁ (Matrix.vecMul (a x₀).val A)
            (Matrix.vecMul (a x₁).val A) y₀ y₁ v₀ v₁ else 0) := by
  have hs : Real.sqrt (Fintype.card (V F m) : ℝ)^4 = (vectorCard F m : ℝ)^2 := by
    rw [show (4 : ℕ) = 2*2 by norm_num, pow_mul, Real.sq_sqrt (by positivity)]
    simp [V, vectorCard, fieldCard]
  by_cases h₀ : Matrix.mulVec A v₀ = (b y₀).val <;>
    by_cases h₁ : Matrix.mulVec A v₁ = (b y₁).val
  · simp only [cornerProduct, enlargedRestriction, h₀, h₁, if_true, and_self]
    convert congrArg (fun z : ℝ => z *
      fullFeatureCorner E x₀ x₁ (Matrix.vecMul (a x₀).val A)
        (Matrix.vecMul (a x₁).val A) y₀ y₁ v₀ v₁) hs using 1 <;>
      simp only [fullFeatureCorner] <;> ring
  all_goals simp [cornerProduct, enlargedRestriction, h₀, h₁]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m); b ∈ Y → U(F, m); E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ; x₀, x₁ ∈ X; y₀, y₁ ∈ Y; v₀, v₁ ∈ V(F, m), we have

𝔼_(A ∈ F^({0,…,m−1} × {0,…,m−1})) [cornerProduct(enlargedRestriction(a, b, E, A), ((x₀, x₁), ((y₀, v₀), (y₁, v₁))))] = (|F|ᵐ)⁴ · 𝔼_(u ∈ V(F, m) × V(F, m)) [(|MatrixCompletion((a(x₀), a(x₁)), (v₀, v₁), ((u)₁, (u)₂), (b(y₀), b(y₁)))| / |F^({0,…,m−1} × {0,…,m−1})|) · fullFeatureCorner(E, x₀, x₁, (u)₁, (u)₂, y₀, y₁, v₀, v₁)].
-/
theorem enlarged_corner_average (a : X → U F m) (b : Y → U F m)
    (E : (X × U F m) → (Y × U F m) → ℝ)
    (x₀ x₁ : X) (y₀ y₁ : Y) (v₀ v₁ : V F m) :
    uavg (fun A : Matrix (Fin m) (Fin m) F =>
      cornerProduct (enlargedRestriction a b E A) ((x₀,x₁),((y₀,v₀),(y₁,v₁)))) =
      (vectorCard F m : ℝ)^4 * uavg (fun u : V F m × V F m =>
        ((Fintype.card (MatrixCompletion ![(a x₀).val,(a x₁).val] ![v₀,v₁]
          ![u.1,u.2] ![(b y₀).val,(b y₁).val]) : ℝ) /
            Fintype.card (Matrix (Fin m) (Fin m) F)) *
          fullFeatureCorner E x₀ x₁ u.1 u.2 y₀ y₁ v₀ v₁) := by
  simp_rw [enlarged_corner]
  rw [uavg_const_mul, fullFeatureCorner_average]
  ring

/-- The full-output zero extension as a rectangular table. -/
/-
Mathematical definition (normal notation): For E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ, define

fullFeatureTable(E) := (x, y ↦ featureZeroExtend(E, (x)₁, (x)₂, (y)₁, (y)₂)).
-/
def fullFeatureTable (E : (X × U F m) → (Y × U F m) → ℝ) :
    (X × V F m) → (Y × V F m) → ℝ :=
  fun x y => featureZeroExtend E x.1 x.2 y.1 y.2

/-
Mathematical definition (normal notation): For four endpoint corners ((x₁,u₁),(x₂,u₂),(y₁,v₁),(y₂,v₂)), define the probability that a uniformly random, unrestricted matrix A meets all four linear constraints:

a(x₁) · A = u₁, a(x₂) · A = u₂, A · v₁ = b(y₁), A · v₂ = b(y₂).

It equals the number of such matrix completions divided by |𝔽|^(m²).
-/
def cornerCompletionProbability (a : X → U F m) (b : Y → U F m)
    (p : ((X × V F m) × (X × V F m)) × ((Y × V F m) × (Y × V F m))) : ℝ :=
  (Fintype.card (MatrixCompletion ![(a p.1.1.1).val,(a p.1.2.1).val]
    ![p.2.1.2,p.2.2.2] ![p.1.1.2,p.1.2.2] ![(b p.2.1.1).val,(b p.2.2.1).val]) : ℝ) /
    Fintype.card (Matrix (Fin m) (Fin m) F)

/-
Mathematical definition (normal notation): Regroup the independently listed old left inputs and new left vectors into left endpoint pairs:

(((x₁,x₂),((y₁,v₁),(y₂,v₂))),(u₁,u₂)) ↔(((x₁,u₁),(x₂,u₂)),((y₁,v₁),(y₂,v₂))).
-/
def residualQuadRegroup :
    (((X × X) × ((Y × V F m) × (Y × V F m))) × (V F m × V F m)) ≃
      (((X × V F m) × (X × V F m)) × ((Y × V F m) × (Y × V F m))) where
  toFun p := (((p.1.1.1,p.2.1),(p.1.1.2,p.2.2)),p.1.2)
  invFun p := (((p.1.1.1,p.1.2.1),p.2),(p.1.1.2,p.1.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A,B a set; K ∈ A → B → ℝ, assume A is finite; B is finite. Then

fourCycle(K) = 𝔼ᵤ [cornerProduct(K, u)].
-/
theorem fourCycle_eq_uavg_cornerProduct {A B : Type*} [Fintype A] [Fintype B]
    (K : A → B → ℝ) : fourCycle K = uavg (cornerProduct K) := by
  simp only [fourCycle_expansion, cornerProduct, uavg_prod]

/-- The actual unrestricted enlarged-table four-cycle is exactly the eight-variable signed reference average weighted by completion probabilities. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m); b ∈ Y → U(F, m); E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ, we have

𝔼_(A ∈ F^({0,…,m−1} × {0,…,m−1})) [fourCycle(enlargedRestriction(a, b, E, A))] = (|F|ᵐ)⁴ · 𝔼ₚ [cornerCompletionProbability(a, b, p) · cornerProduct(fullFeatureTable(E), p)].
-/
theorem enlarged_fourCycle_expansion (a : X → U F m) (b : Y → U F m)
    (E : (X × U F m) → (Y × U F m) → ℝ) :
    uavg (fun A : Matrix (Fin m) (Fin m) F => fourCycle (enlargedRestriction a b E A)) =
      (vectorCard F m : ℝ)^4 * uavg (fun p =>
        cornerCompletionProbability a b p * cornerProduct (fullFeatureTable E) p) := by
  simp_rw [fourCycle_eq_uavg_cornerProduct]
  rw [uavg_comm]
  simp_rw [enlarged_corner_average]
  rw [uavg_const_mul]
  congr 1
  let f := fun p => cornerCompletionProbability a b p * cornerProduct (fullFeatureTable E) p
  change uavg (fun p => uavg (fun u => f (residualQuadRegroup (p,u)))) = uavg f
  exact (uavg_prod (fun p => f (residualQuadRegroup p))).symm.trans
    (uavg_equiv residualQuadRegroup f)

omit [Fintype X] [Fintype Y] in
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m); b ∈ Y → U(F, m); E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ; x ∈ X; u ∈ V(F, m); y ∈ Y; v ∈ V(F, m), assume ∀ x, y, ((a((x)₁) · b((y)₁)) ≠ ((x)₂ · (y)₂)) ⇒ E(x, y) = 0; (a(x) · b(y)) ≠ (u · v). Then

featureZeroExtend(E, x, u, y, v) = 0.
-/
theorem featureZeroExtend_incompatible (a : X → U F m) (b : Y → U F m)
    (E : (X × U F m) → (Y × U F m) → ℝ)
    (hE : ∀ x y, dot (a x.1).val (b y.1).val ≠ dot x.2.val y.2.val → E x y = 0)
    (x : X) (u : V F m) (y : Y) (v : V F m)
    (h : dot (a x).val (b y).val ≠ dot u v) :
    featureZeroExtend E x u y v = 0 := by
  unfold featureZeroExtend
  split_ifs
  · exact hE _ _ h
  · rfl

/-- Support on all four pairing equations is inherited by the full corner. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m); b ∈ Y → U(F, m); E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ; p ∈ ((X × V(F, m)) × (X × V(F, m))) × ((Y × V(F, m)) × (Y × V(F, m))), assume ∀ x, y, ((a((x)₁) · b((y)₁)) ≠ ((x)₂ · (y)₂)) ⇒ E(x, y) = 0; ¬ (ExtensionCompatible((a((((p)₁)₁)₁), a((((p)₁)₂)₁)), ((((p)₂)₁)₂, (((p)₂)₂)₂), ((((p)₁)₁)₂, (((p)₁)₂)₂), (b((((p)₂)₁)₁), b((((p)₂)₂)₁)))). Then

cornerProduct(fullFeatureTable(E), p) = 0.
-/
theorem fullFeatureCorner_incompatible (a : X → U F m) (b : Y → U F m)
    (E : (X × U F m) → (Y × U F m) → ℝ)
    (hE : ∀ x y, dot (a x.1).val (b y.1).val ≠ dot x.2.val y.2.val → E x y = 0)
    (p : ((X × V F m) × (X × V F m)) × ((Y × V F m) × (Y × V F m)))
    (hp : ¬ExtensionCompatible ![(a p.1.1.1).val,(a p.1.2.1).val]
      ![p.2.1.2,p.2.2.2] ![p.1.1.2,p.1.2.2] ![(b p.2.1.1).val,(b p.2.2.1).val]) :
    cornerProduct (fullFeatureTable E) p = 0 := by
  have hh : ∃ i j, dot (![(a p.1.1.1).val,(a p.1.2.1).val] i)
      (![(b p.2.1.1).val,(b p.2.2.1).val] j) ≠
        dot (![p.1.1.2,p.1.2.2] i) (![p.2.1.2,p.2.2.2] j) := by
    simpa only [ExtensionCompatible, not_forall] using hp
  obtain ⟨i,j,hij⟩ := hh
  fin_cases i <;> fin_cases j <;> dsimp at hij
  all_goals
    have hz := featureZeroExtend_incompatible a b E hE _ _ _ _ hij
    simp [cornerProduct, fullFeatureTable, hz]

/-- The exact rank probabilities give a pointwise signed comparison. The three lower-rank corrections are full-row, full-column, and both collisions; the removed main-term restrictions are only old-row/new-column collisions. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m); b ∈ Y → U(F, m); E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ; p ∈ ((X × V(F, m)) × (X × V(F, m))) × ((Y × V(F, m)) × (Y × V(F, m))), assume |F| = 2; 2 ≤ m; a is injective; b is injective; ∀ x, y, ((a((x)₁) · b((y)₁)) ≠ ((x)₂ · (y)₂)) ⇒ E(x, y) = 0. Then

(|F|ᵐ)⁴ · cornerCompletionProbability(a, b, p) · cornerProduct(fullFeatureTable(E), p) ≤ 16 · cornerProduct(fullFeatureTable(E), p) + 16 · ({ |cornerProduct(fullFeatureTable(E), p)| if (((p)₁)₁)₁ = (((p)₁)₂)₁ ∨ (((p)₂)₁)₂ = (((p)₂)₂)₂,; 0 otherwise }) + 4 · |F|ᵐ · ({ |cornerProduct(fullFeatureTable(E), p)| if ((p)₁)₁ = ((p)₁)₂,; 0 otherwise }) + 4 · |F|ᵐ · ({ |cornerProduct(fullFeatureTable(E), p)| if ((p)₂)₁ = ((p)₂)₂,; 0 otherwise }) + 2 · (|F|ᵐ)² · ({ |cornerProduct(fullFeatureTable(E), p)| if ((p)₁)₁ = ((p)₁)₂ ∧ ((p)₂)₁ = ((p)₂)₂,; 0 otherwise }).
-/
theorem weighted_corner_le_rank_errors (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a : X → U F m) (b : Y → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (E : (X × U F m) → (Y × U F m) → ℝ)
    (hE : ∀ x y, dot (a x.1).val (b y.1).val ≠ dot x.2.val y.2.val → E x y = 0)
    (p : ((X × V F m) × (X × V F m)) × ((Y × V F m) × (Y × V F m))) :
    (vectorCard F m : ℝ)^4 * cornerCompletionProbability a b p * cornerProduct (fullFeatureTable E) p ≤
      16 * cornerProduct (fullFeatureTable E) p +
      16 * (if p.1.1.1 = p.1.2.1 ∨ p.2.1.2 = p.2.2.2 then |cornerProduct (fullFeatureTable E) p| else 0) +
      4*(vectorCard F m : ℝ)*(if p.1.1 = p.1.2 then |cornerProduct (fullFeatureTable E) p| else 0) +
      4*(vectorCard F m : ℝ)*(if p.2.1 = p.2.2 then |cornerProduct (fullFeatureTable E) p| else 0) +
      2*(vectorCard F m : ℝ)^2*(if p.1.1 = p.1.2 ∧ p.2.1 = p.2.2 then |cornerProduct (fullFeatureTable E) p| else 0) := by
  by_cases hz : cornerProduct (fullFeatureTable E) p = 0
  · simp [hz]
  have hv₀ : p.2.1.2 ≠ 0 := by
    intro hv
    apply hz
    simp [cornerProduct, fullFeatureTable, featureZeroExtend, hv]
  have hv₁ : p.2.2.2 ≠ 0 := by
    intro hv
    apply hz
    simp [cornerProduct, fullFeatureTable, featureZeroExtend, hv]
  have hc : ExtensionCompatible ![(a p.1.1.1).val,(a p.1.2.1).val]
      ![p.2.1.2,p.2.2.2] ![p.1.1.2,p.1.2.2] ![(b p.2.1.1).val,(b p.2.2.1).val] := by
    by_contra hh
    exact hz (fullFeatureCorner_incompatible a b E hE p hh)
  have hw := scaled_completion_probability hq hm (a p.1.1.1) (a p.1.2.1)
    ⟨p.2.1.2,hv₀⟩ ⟨p.2.2.2,hv₁⟩ p.1.1.2 p.1.2.2 (b p.2.1.1).val (b p.2.2.1).val hc
  have he := rank_coefficient_error (vectorCard F m : ℝ) (cornerProduct (fullFeatureTable E) p)
    (by positivity) (a p.1.1.1 = a p.1.2.1) (p.1.1.2 = p.1.2.2)
      (p.2.1.2 = p.2.2.2) ((b p.2.1.1).val = (b p.2.2.1).val)
  simp only [Subtype.mk.injEq] at hw
  apply (congrArg (fun w : ℝ => w * cornerProduct (fullFeatureTable E) p) hw).le.trans
  convert he using 1 <;>
    simp only [ha.eq_iff, Subtype.val_inj, hb.eq_iff, Prod.ext_iff,
      and_comm, and_left_comm, and_assoc]

end

end CircuitCompiler.RefreshAnalysis
