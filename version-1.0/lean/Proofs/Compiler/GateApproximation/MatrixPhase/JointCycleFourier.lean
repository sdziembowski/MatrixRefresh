import Proofs.Compiler.GateApproximation.MatrixPhase.JointFourCycle
import Proofs.Compiler.GateApproximation.MatrixPhase.JointFourier



/-!
# Character expansion of the four joint-port constraints

The two conjugated edges use the negative character indices. Consequently every summand is exactly a mixed four-cycle of four allowed twists.
-/

set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler

open Refresh

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Scalar character orthogonality in the coefficient variable. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ψ ∈ AddChar(F, ℂ); s ∈ F, assume ψ.IsPrimitive. Then

(∑_(c ∈ F) (ψ((c · s)))) = { |F| if s = 0,; 0 otherwise }.
-/
lemma sum_character_mul (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (s : F) :
    (∑ c : F, ψ (c * s)) = if s = 0 then (fieldCard F : ℂ) else 0 := by
  by_cases hs : s = 0
  · simp [hs, fieldCard]
  · rw [if_neg hs]
    have h := AddChar.sum_eq_zero_of_ne_one (hψ hs)
    simpa only [AddChar.mulShift_apply, mul_comm] using h

/-- Conjugating the negative character recovers the positive character. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ψ ∈ AddChar(F, ℂ); c, s ∈ F, we have

star(ψ((-(c) · s))) = ψ((c · s)).
-/
lemma star_character_neg_mul (ψ : AddChar F ℂ) (c s : F) :
    star (ψ ((-c) * s)) = ψ (c * s) := by
  rw [neg_mul, ψ.map_neg_eq_inv, star_inv₀]
  have h : star (ψ (c * s)) = (ψ (c * s))⁻¹ := by
    simpa only [Complex.star_def] using (Complex.inv_eq_conj (ψ.norm_apply (c * s))).symm
  rw [h, inv_inv]

/-- The exact four-equation character identity before any output rank restriction. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ψ ∈ AddChar(F, ℂ); s₀₀, s₁₀, s₁₁, s₀₁ ∈ F, assume ψ.IsPrimitive. Then

(∑_(a ∈ F) (∑_(b ∈ F) (∑_(c ∈ F) (∑_(d ∈ F) (ψ((a · s₀₀)) · star(ψ((-(b) · s₁₀))) · ψ((c · s₁₁)) · star(ψ((-(d) · s₀₁)))))))) = { (|F|)⁴ if s₀₀ = 0 ∧ s₁₀ = 0 ∧ s₁₁ = 0 ∧ s₀₁ = 0,; 0 otherwise }.
-/
theorem four_character_indicator (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (s₀₀ s₁₀ s₁₁ s₀₁ : F) :
    (∑ a : F, ∑ b : F, ∑ c : F, ∑ d : F,
      ψ (a * s₀₀) * star (ψ ((-b) * s₁₀)) * ψ (c * s₁₁) * star (ψ ((-d) * s₀₁))) =
      if s₀₀ = 0 ∧ s₁₀ = 0 ∧ s₁₁ = 0 ∧ s₀₁ = 0 then (fieldCard F : ℂ) ^ 4 else 0 := by
  simp_rw [star_character_neg_mul]
  have he : (∑ a : F, ∑ b : F, ∑ c : F, ∑ d : F,
      ψ (a * s₀₀) * ψ (b * s₁₀) * ψ (c * s₁₁) * ψ (d * s₀₁)) =
      (∑ a : F, ψ (a * s₀₀)) * (∑ b : F, ψ (b * s₁₀)) *
        (∑ c : F, ψ (c * s₁₁)) * (∑ d : F, ψ (d * s₀₁)) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    let rev : (F × F × F × F) ≃ (F × F × F × F) :=
      { toFun := fun x => (x.2.2.2, x.2.2.1, x.2.1, x.1)
        invFun := fun x => (x.2.2.2, x.2.2.1, x.2.1, x.1)
        left_inv := by intro ⟨a, b, c, d⟩; rfl
        right_inv := by intro ⟨a, b, c, d⟩; rfl }
    have hr := Fintype.sum_equiv rev
      (fun x => ψ (x.1 * s₀₀) * ψ (x.2.1 * s₁₀) * ψ (x.2.2.1 * s₁₁) * ψ (x.2.2.2 * s₀₁))
      (fun x => ψ (x.2.2.2 * s₀₀) * ψ (x.2.2.1 * s₁₀) * ψ (x.2.1 * s₁₁) * ψ (x.1 * s₀₁))
      (by intro ⟨a, b, c, d⟩; rfl)
    simpa only [Fintype.sum_prod_type] using hr
  rw [he]
  simp_rw [sum_character_mul ψ hψ]
  split_ifs <;> simp_all [fieldCard] <;> ring

/-- A general field-valued constraint matrix twists any complex table. -/
/-
Mathematical definition (normal notation): For I a set; ψ ∈ AddChar(F, ℂ); Φ ∈ F^(I × I); E ∈ ℂ^(I × I); c ∈ F, define

constraintTwist(ψ, Φ, E, c) := (i, j ↦ ψ((c · Φ(i, j))) · E(i, j)).
-/
def constraintTwist {I : Type*} (ψ : AddChar F ℂ) (Φ : Matrix I I F)
    (E : Matrix I I ℂ) (c : F) : Matrix I I ℂ := fun i j => ψ (c * Φ i j) * E i j

/-- Pointwise form with all four table factors and alternating conjugations. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ψ ∈ AddChar(F, ℂ); I a set; Φ ∈ F^(I × I); E ∈ ℂ^(I × I); i, j, k, l ∈ I, assume ψ.IsPrimitive. Then

(∑_(a ∈ F) (∑_(b ∈ F) (∑_(c ∈ F) (∑_(d ∈ F) (constraintTwist(ψ, Φ, E, a, i, j) · star(constraintTwist(ψ, Φ, E, -(b), k, j)) · constraintTwist(ψ, Φ, E, c, k, l) · star(constraintTwist(ψ, Φ, E, -(d), i, l))))))) = ({ (|F|)⁴ if Φ(i, j) = 0 ∧ Φ(k, j) = 0 ∧ Φ(k, l) = 0 ∧ Φ(i, l) = 0,; 0 otherwise }) · (E(i, j) · star(E(k, j)) · E(k, l) · star(E(i, l))).
-/
theorem four_twisted_entries (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    {I : Type*} (Φ : Matrix I I F) (E : Matrix I I ℂ) (i j k l : I) :
    (∑ a : F, ∑ b : F, ∑ c : F, ∑ d : F,
      constraintTwist ψ Φ E a i j * star (constraintTwist ψ Φ E (-b) k j) *
      constraintTwist ψ Φ E c k l * star (constraintTwist ψ Φ E (-d) i l)) =
      (if Φ i j = 0 ∧ Φ k j = 0 ∧ Φ k l = 0 ∧ Φ i l = 0 then (fieldCard F : ℂ) ^ 4 else 0) *
        (E i j * star (E k j) * E k l * star (E i l)) := by
  have h := four_character_indicator ψ hψ (Φ i j) (Φ k j) (Φ k l) (Φ i l)
  rw [← h, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  simp only [constraintTwist, star_mul]
  ring

variable {I : Type*} [Fintype I] [DecidableEq I]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ψ ∈ AddChar(F, ℂ); Φ ∈ F^(I × I); E ∈ ℂ^(I × I); c ∈ F, we have

complexMatrixL2Sq(constraintTwist(ψ, Φ, E, c)) = complexMatrixL2Sq(E).
-/
lemma constraintTwist_energy (ψ : AddChar F ℂ) (Φ : Matrix I I F)
    (E : Matrix I I ℂ) (c : F) : complexMatrixL2Sq (constraintTwist ψ Φ E c) = complexMatrixL2Sq E := by
  simp [complexMatrixL2Sq, constraintTwist, norm_mul, ψ.norm_apply]

/-- Each character term in the four-constraint expansion obeys the same bound. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ψ ∈ AddChar(F, ℂ); Φ ∈ F^(I × I); E ∈ ℂ^(I × I); β ∈ ℝ; a, b, c, d ∈ F, assume 0 ≤ β; ∀ c, ‖ constraintTwist(ψ, Φ, E, c)‖ ≤ β. Then

‖ complexMixedFourCycle(constraintTwist(ψ, Φ, E, a), constraintTwist(ψ, Φ, E, -(b)), constraintTwist(ψ, Φ, E, c), constraintTwist(ψ, Φ, E, -(d)))‖ ≤ β² · complexMatrixL2Sq(E).
-/
theorem character_mixed_cycle_le (ψ : AddChar F ℂ) (Φ : Matrix I I F)
    (E : Matrix I I ℂ) (β : ℝ) (hβ : 0 ≤ β)
    (hE : ∀ c, ‖constraintTwist ψ Φ E c‖ ≤ β) (a b c d : F) :
    ‖complexMixedFourCycle (constraintTwist ψ Φ E a) (constraintTwist ψ Φ E (-b))
      (constraintTwist ψ Φ E c) (constraintTwist ψ Φ E (-d))‖ ≤ β ^ 2 * complexMatrixL2Sq E :=
  complexMixedFourCycle_le _ _ _ _ β (complexMatrixL2Sq E) hβ (complexMatrixL2Sq_nonneg E)
    (hE a) (hE c) (le_of_eq (constraintTwist_energy ψ Φ E (-b)))
    (le_of_eq (constraintTwist_energy ψ Φ E (-d)))

/-- The four-cycle restricted by all four compatibility equations. -/
/-
Mathematical definition (normal notation): For Φ ∈ F^(I × I); E ∈ ℂ^(I × I), define

constrainedFourCycle(Φ, E) := ∑ᵢ (∑ⱼ (∑ₖ (∑ₗ ({ E(i, j) · star(E(k, j)) · E(k, l) · star(E(i, l)) if Φ(i, j) = 0 ∧ Φ(k, j) = 0 ∧ Φ(k, l) = 0 ∧ Φ(i, l) = 0,; 0 otherwise })))).
-/
def constrainedFourCycle (Φ : Matrix I I F) (E : Matrix I I ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    if Φ i j = 0 ∧ Φ k j = 0 ∧ Φ k l = 0 ∧ Φ i l = 0
    then E i j * star (E k j) * E k l * star (E i l) else 0

/-- Summing the pointwise character expansion gives exactly `q⁴` times the compatibility-restricted four-cycle, with no rank restrictions or error term. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ψ ∈ AddChar(F, ℂ); Φ ∈ F^(I × I); E ∈ ℂ^(I × I), assume ψ.IsPrimitive. Then

(|F|)⁴ · constrainedFourCycle(Φ, E) = ∑_(a ∈ F) (∑_(b ∈ F) (∑_(c ∈ F) (∑_(d ∈ F) (complexMixedFourCycle(constraintTwist(ψ, Φ, E, a), constraintTwist(ψ, Φ, E, -(b)), constraintTwist(ψ, Φ, E, c), constraintTwist(ψ, Φ, E, -(d))))))).
-/
theorem constrainedFourCycle_character_expansion (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (Φ : Matrix I I F) (E : Matrix I I ℂ) :
    (fieldCard F : ℂ) ^ 4 * constrainedFourCycle Φ E =
      ∑ a : F, ∑ b : F, ∑ c : F, ∑ d : F,
        complexMixedFourCycle (constraintTwist ψ Φ E a) (constraintTwist ψ Φ E (-b))
          (constraintTwist ψ Φ E c) (constraintTwist ψ Φ E (-d)) := by
  let t := fun (c : F × F × F × F) (x : I × I × I × I) =>
    constraintTwist ψ Φ E c.1 x.1 x.2.1 * star (constraintTwist ψ Φ E (-c.2.1) x.2.2.1 x.2.1) *
      constraintTwist ψ Φ E c.2.2.1 x.2.2.1 x.2.2.2 *
      star (constraintTwist ψ Φ E (-c.2.2.2) x.1 x.2.2.2)
  have hswap : (∑ c : F × F × F × F, ∑ x : I × I × I × I, t c x) =
      ∑ x : I × I × I × I, ∑ c : F × F × F × F, t c x := Finset.sum_comm
  have he : (∑ a : F, ∑ b : F, ∑ c : F, ∑ d : F,
        complexMixedFourCycle (constraintTwist ψ Φ E a) (constraintTwist ψ Φ E (-b))
          (constraintTwist ψ Φ E c) (constraintTwist ψ Φ E (-d))) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (∑ a : F, ∑ b : F, ∑ c : F, ∑ d : F,
          constraintTwist ψ Φ E a i j * star (constraintTwist ψ Φ E (-b) k j) *
            constraintTwist ψ Φ E c k l * star (constraintTwist ψ Φ E (-d) i l)) := by
    simpa only [t, Fintype.sum_prod_type, complexMixedFourCycle] using hswap
  rw [he]
  simp_rw [four_twisted_entries ψ hψ]
  simp only [constrainedFourCycle, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp

/-- Summing all `q⁴` mixed-cycle estimates bounds the main orbit-density term. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ψ ∈ AddChar(F, ℂ); Φ ∈ F^(I × I); E ∈ ℂ^(I × I); β ∈ ℝ, assume ψ.IsPrimitive; 0 ≤ β; ∀ c, ‖ constraintTwist(ψ, Φ, E, c)‖ ≤ β. Then

‖ (|F|)⁴ · constrainedFourCycle(Φ, E)‖ ≤ (|F|)⁴ · β² · complexMatrixL2Sq(E).
-/
theorem constrainedFourCycle_norm_le (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (Φ : Matrix I I F) (E : Matrix I I ℂ) (β : ℝ) (hβ : 0 ≤ β)
    (hE : ∀ c, ‖constraintTwist ψ Φ E c‖ ≤ β) :
    ‖(fieldCard F : ℂ) ^ 4 * constrainedFourCycle Φ E‖ ≤
      (fieldCard F : ℝ) ^ 4 * β ^ 2 * complexMatrixL2Sq E := by
  rw [constrainedFourCycle_character_expansion ψ hψ]
  calc
    _ ≤ ∑ a : F, ∑ b : F, ∑ c : F, ∑ d : F,
        ‖complexMixedFourCycle (constraintTwist ψ Φ E a) (constraintTwist ψ Φ E (-b))
          (constraintTwist ψ Φ E c) (constraintTwist ψ Φ E (-d))‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro c _
      exact norm_sum_le _ _
    _ ≤ ∑ _a : F, ∑ _b : F, ∑ _c : F, ∑ _d : F, β ^ 2 * complexMatrixL2Sq E :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ =>
        Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun d _ =>
          character_mixed_cycle_le ψ Φ E β hβ hE a b c d))))
    _ = _ := by simp [fieldCard]; ring

/-- The real pairing used by the orbit calculation is bounded by the same main term. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ψ ∈ AddChar(F, ℂ); Φ ∈ F^(I × I); E ∈ ℂ^(I × I); β ∈ ℝ, assume ψ.IsPrimitive; 0 ≤ β; ∀ c, ‖ constraintTwist(ψ, Φ, E, c)‖ ≤ β. Then

re(((|F|)⁴ · constrainedFourCycle(Φ, E))) ≤ (|F|)⁴ · β² · complexMatrixL2Sq(E).
-/
theorem constrainedFourCycle_re_le (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (Φ : Matrix I I F) (E : Matrix I I ℂ) (β : ℝ) (hβ : 0 ≤ β)
    (hE : ∀ c, ‖constraintTwist ψ Φ E c‖ ≤ β) :
    ((fieldCard F : ℂ) ^ 4 * constrainedFourCycle Φ E).re ≤
      (fieldCard F : ℝ) ^ 4 * β ^ 2 * complexMatrixL2Sq E :=
  (Complex.re_le_norm _).trans (constrainedFourCycle_norm_le ψ hψ Φ E β hβ hE)

/-- Uniform normalization of the main four-cycle estimate. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For ψ ∈ AddChar(F, ℂ); Φ ∈ F^(I × I); E ∈ ℂ^(I × I); β ∈ ℝ, assume I ≠ ∅; ψ.IsPrimitive; 0 ≤ β; ∀ c, ‖ constraintTwist(ψ, Φ, E, c)‖ / |I| ≤ β. Then

re(((|F|)⁴ · constrainedFourCycle(Φ, E))) / (|I|)⁴ ≤ (|F|)⁴ · β² · (complexMatrixL2Sq(E) / (|I|)²).
-/
theorem constrainedFourCycle_uniform_re_le [Nonempty I]
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (Φ : Matrix I I F) (E : Matrix I I ℂ)
    (β : ℝ) (hβ : 0 ≤ β) (hE : ∀ c, ‖constraintTwist ψ Φ E c‖ / Fintype.card I ≤ β) :
    ((fieldCard F : ℂ) ^ 4 * constrainedFourCycle Φ E).re / (Fintype.card I : ℝ) ^ 4 ≤
      (fieldCard F : ℝ) ^ 4 * β ^ 2 * (complexMatrixL2Sq E / (Fintype.card I : ℝ) ^ 2) := by
  have hd : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have he (c : F) : ‖constraintTwist ψ Φ E c‖ ≤ β * Fintype.card I :=
    (div_le_iff₀ hd).1 (hE c)
  have h := constrainedFourCycle_re_le ψ hψ Φ E (β * Fintype.card I)
    (mul_nonneg hβ hd.le) he
  apply (div_le_iff₀ (pow_pos hd 4)).2
  convert h using 1 <;> field_simp <;> ring

end

end CircuitCompiler
