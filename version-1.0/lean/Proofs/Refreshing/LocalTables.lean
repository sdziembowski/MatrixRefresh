import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite-table identities used in the local refreshing approximation

These are the probability-normalized table conventions of the paper.  The projection identities below implement the exact residual identity in the local-approximation proof, using the projected-norm and residual formulas. No refreshing or security conclusion is assumed.
-/

noncomputable section
open scoped BigOperators

namespace RefreshingProof.Local

/-- Uniform average, including the usual empty-domain value zero. -/
def average {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ a, f a

/-- The uniform finite average preserves addition. -/
@[simp] theorem average_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    average (fun a => f a + g a) = average f + average g := by
  simp [average, Finset.sum_add_distrib, mul_add]

/-- The uniform finite average preserves subtraction. -/
@[simp] theorem average_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    average (fun a => f a - g a) = average f - average g := by
  simp [average, Finset.sum_sub_distrib, mul_sub]

/-- A real scalar factors out of the uniform finite average. -/
@[simp] theorem average_smul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    average (fun a => c * f a) = c * average f := by
  simp [average, ← Finset.mul_sum, mul_left_comm]

/-- The uniform finite average of a nonnegative function is nonnegative. -/
theorem average_nonneg {α : Type*} [Fintype α] {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    0 ≤ average f :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun a _ => hf a)

/-- Pointwise equal functions have equal uniform finite averages. -/
theorem average_congr {α : Type*} [Fintype α] {f g : α → ℝ} (h : ∀ a, f a = g a) :
    average f = average g := by
  exact congrArg average (funext h)

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- A real-valued table indexed by one left coordinate and one right coordinate. -/
abbrev Table (X Y : Type*) := X → Y → ℝ

/-- Probability-normalized pairing of two real tables. -/
def pairing (F G : Table X Y) : ℝ := average fun x => average fun y => F x y * G x y

/-- Squared probability-normalized L₂ norm. -/
def normSq (F : Table X Y) : ℝ := pairing F F

/-- Coordinate projection onto the consistent entries. -/
def projection (consistent : X → Y → Prop) [DecidableRel consistent]
    (F : Table X Y) : Table X Y := fun x y => if consistent x y then F x y else 0

/-- The centered consistency sign J, so that ΠF = F/2 + JF. -/
def consistencySign (consistent : X → Y → Prop) [DecidableRel consistent] : Table X Y :=
  fun x y => if consistent x y then 1 / 2 else -(1 / 2)

omit [Fintype X] [Fintype Y] in
/-- Restricting a table twice to the same consistency relation equals restricting it once. -/
@[simp] theorem projection_idempotent (consistent : X → Y → Prop)
    [DecidableRel consistent] (F : Table X Y) :
    projection consistent (projection consistent F) = projection consistent F := by
  funext x y
  by_cases h : consistent x y <;> simp [projection, h]

omit [Fintype X] [Fintype Y] in
/-- Restriction to consistent entries equals half the table plus its consistency-sign multiple. -/
theorem projection_sign (consistent : X → Y → Prop) [DecidableRel consistent]
    (F : Table X Y) (x : X) (y : Y) :
    projection consistent F x y = (1 / 2 : ℝ) * F x y +
      consistencySign consistent x y * F x y := by
  by_cases h : consistent x y
  · simp [projection, consistencySign, h]
    ring
  · simp [projection, consistencySign, h]

/-- The support condition lets a pairing ignore the consistency projection. -/
theorem pairing_projection (consistent : X → Y → Prop) [DecidableRel consistent]
    (F G : Table X Y) (hF : ∀ x y, ¬ consistent x y → F x y = 0) :
    pairing F (projection consistent G) = pairing F G := by
  apply average_congr
  intro x
  apply average_congr
  intro y
  by_cases h : consistent x y
  · simp [projection, h]
  · simp [projection, h, hF x y h]

/-- The projected-norm identity: projection keeps exactly half the square plus its correlation with the centered consistency sign. -/
theorem projection_normSq (consistent : X → Y → Prop) [DecidableRel consistent]
    (P : Table X Y) :
    normSq (projection consistent P) = (1 / 2 : ℝ) * normSq P +
      pairing P (fun x y => consistencySign consistent x y * P x y) := by
  unfold normSq pairing
  rw [← average_smul, ← average_add]
  apply average_congr
  intro x
  rw [← average_smul, ← average_add]
  apply average_congr
  intro y
  by_cases h : consistent x y
  · simp [projection, consistencySign, h]
    ring
  · simp [projection, consistencySign, h]
    ring

/-- The exact algebraic residual identity from the paper. The hypothesis is orthogonality of the spectral truncation: ⟨F,P⟩ = ‖P‖₂². -/
theorem residual_identity (consistent : X → Y → Prop) [DecidableRel consistent]
    (F P : Table X Y) (hF : ∀ x y, ¬ consistent x y → F x y = 0)
    (horth : pairing F P = normSq P) :
    normSq (fun x y => F x y - 2 * projection consistent P x y) =
      pairing F (fun x y => F x y - 2 * projection consistent P x y) +
      4 * pairing P (fun x y => consistencySign consistent x y * P x y) := by
  have pointwise (x : X) (y : Y) :
      (F x y - 2 * projection consistent P x y) ^ 2 =
        F x y * (F x y - 2 * projection consistent P x y) +
        4 * (P x y * (consistencySign consistent x y * P x y)) +
        2 * (P x y * P x y - F x y * P x y) := by
    by_cases h : consistent x y
    · simp [projection, consistencySign, h]
      ring
    · simp [projection, consistencySign, h, hF x y h]
      ring
  have hzero : average (fun x => average fun y =>
      2 * (P x y * P x y - F x y * P x y)) = 0 := by
    simp only [average_smul, average_sub]
    change 2 * (normSq P - pairing F P) = 0
    rw [horth, sub_self, mul_zero]
  unfold normSq pairing
  calc
    _ = average (fun x => average fun y =>
        F x y * (F x y - 2 * projection consistent P x y) +
        4 * (P x y * (consistencySign consistent x y * P x y)) +
        2 * (P x y * P x y - F x y * P x y)) := by
      apply average_congr
      intro x
      apply average_congr
      intro y
      simpa [pow_two] using pointwise x y
    _ = _ := by
      simp only [average_add, average_smul]
      rw [show 2 * average (fun x => average fun y =>
          P x y * P x y - F x y * P x y) = 0 by simpa only [average_smul] using hzero]
      ring

/-- Multiplication of independent uniform averages. -/
theorem average_mul_average {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℝ) (g : β → ℝ) :
    average f * average g = average (fun a => average (fun b => f a * g b)) := by
  simp only [average, ← Finset.mul_sum, ← Finset.sum_mul]
  ring


/-- Interchange independent uniform averages. -/
theorem average_comm {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    average (fun a => average (fun b => f a b)) =
      average (fun b => average (fun a => f a b)) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

/-- A uniform average over a finite product is an iterated uniform average. -/
theorem average_product {α β : Type*} [Fintype α] [Fintype β]
    (f : α × β → ℝ) :
    average f = average (fun a => average (fun b => f (a, b))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

/-- Interchange two pairs of independent uniform coordinates. -/
theorem average_pair_comm {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    average (fun a => average (fun b => average (fun c => average (fun d => f a b c d)))) =
      average (fun c => average (fun d => average (fun a => average (fun b => f a b c d)))) := by
  calc
    _ = average (fun ab : α × β => average (fun cd : γ × δ =>
      f ab.1 ab.2 cd.1 cd.2)) := by simp only [average_product]
    _ = average (fun cd : γ × δ => average (fun ab : α × β =>
      f ab.1 ab.2 cd.1 cd.2)) := average_comm _
    _ = _ := by simp only [average_product]

/-- Cauchy--Schwarz in the paper's probability normalization. -/
theorem average_cauchy_schwarz {α : Type*} [Fintype α] (f g : α → ℝ) :
    (average (fun a => f a * g a)) ^ 2 ≤
      average (fun a => f a ^ 2) * average (fun a => g a ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have h' := mul_le_mul_of_nonneg_left h (sq_nonneg (Fintype.card α : ℝ)⁻¹)
  simpa only [average, mul_pow, pow_two, mul_assoc, mul_left_comm, mul_comm] using h'

/-- Complete four-cycle average of a signed real table. -/
def fourCycle (F : Table X Y) : ℝ := average fun x₁ => average fun x₂ =>
  average fun y₁ => average fun y₂ =>
    F x₁ y₁ * F x₁ y₂ * F x₂ y₁ * F x₂ y₂

/-- Four cycles are the mean square of the row Gram matrix. -/
theorem fourCycle_gram (F : Table X Y) :
    fourCycle F = average (fun x₁ => average (fun x₂ =>
      (average (fun y => F x₁ y * F x₂ y)) ^ 2)) := by
  apply average_congr
  intro x₁
  apply average_congr
  intro x₂
  rw [pow_two, average_mul_average]
  apply average_congr
  intro y₁
  apply average_congr
  intro y₂
  ring


/-- Row and column formulations of the four-cycle average coincide. -/
theorem fourCycle_transpose (F : Table X Y) :
    fourCycle (fun y x => F x y) = fourCycle F := by
  unfold fourCycle
  rw [average_pair_comm]
  apply average_congr
  intro x₁
  apply average_congr
  intro x₂
  apply average_congr
  intro y₁
  apply average_congr
  intro y₂
  ring

/-- Four cycles are also the mean square of the column Gram matrix. -/
theorem fourCycle_column_gram (F : Table X Y) :
    fourCycle F = average (fun y₁ => average (fun y₂ =>
      (average (fun x => F x y₁ * F x y₂)) ^ 2)) := by
  rw [← fourCycle_transpose F]
  exact fourCycle_gram _

/-- The complete four-cycle average is nonnegative, even for signed tables. This is why conditioning on invertibility may be applied to a complete cycle. -/
theorem fourCycle_nonneg (F : Table X Y) : 0 ≤ fourCycle F := by
  rw [fourCycle_gram]
  exact average_nonneg fun _ => average_nonneg fun _ => sq_nonneg _


/-- The four-cycle testing inequality, raised to the fourth power to avoid choosing roots. This is the polynomial form of the paper's four-cycle testing bound. -/
theorem fourCycle_test_fourth (F : Table X Y) (f : X → ℝ) (g : Y → ℝ) :
    (average (fun x => f x * average (fun y => F x y * g y))) ^ 4 ≤
      (average (fun x => f x ^ 2)) ^ 2 *
        (average (fun y => g y ^ 2)) ^ 2 * fourCycle F := by
  let A := average (fun x => (average (fun y => F x y * g y)) ^ 2)
  have hA0 : 0 ≤ A := average_nonneg fun _ => sq_nonneg _
  have hf0 : 0 ≤ average (fun x => f x ^ 2) := average_nonneg fun _ => sq_nonneg _
  have hA : A = average (fun y₁ => average (fun y₂ =>
      (g y₁ * g y₂) * average (fun x => F x y₁ * F x y₂))) := by
    calc
      A = average (fun x => average (fun y₁ => average (fun y₂ =>
          (g y₁ * g y₂) * (F x y₁ * F x y₂)))) := by
        apply average_congr
        intro x
        rw [pow_two, average_mul_average]
        apply average_congr
        intro y₁
        apply average_congr
        intro y₂
        ring
      _ = _ := by
        rw [average_comm]
        apply average_congr
        intro y₁
        rw [average_comm]
        apply average_congr
        intro y₂
        exact average_smul _ _
  have hG : average (fun y₁ => average (fun y₂ => (g y₁ * g y₂) ^ 2)) =
      (average (fun y => g y ^ 2)) ^ 2 := by
    rw [pow_two, average_mul_average]
    apply average_congr
    intro y₁
    apply average_congr
    intro y₂
    ring
  have h₂ := average_cauchy_schwarz
    (fun yy : Y × Y => g yy.1 * g yy.2)
    (fun yy : Y × Y => average (fun x => F x yy.1 * F x yy.2))
  simp only [average_product] at h₂
  rw [← hA, hG, ← fourCycle_column_gram] at h₂
  have h₁ := average_cauchy_schwarz f (fun x => average (fun y => F x y * g y))
  change _ ≤ average (fun x => f x ^ 2) * A at h₁
  have h₁sq := (sq_le_sq₀ (sq_nonneg _) (mul_nonneg hf0 hA0)).mpr h₁
  have h₂mul := mul_le_mul_of_nonneg_left h₂ (sq_nonneg (average (fun x => f x ^ 2)))
  calc
    _ = ((average (fun x => f x * average (fun y => F x y * g y))) ^ 2) ^ 2 := by ring
    _ ≤ (average (fun x => f x ^ 2) * A) ^ 2 := h₁sq
    _ = (average (fun x => f x ^ 2)) ^ 2 * A ^ 2 := mul_pow _ _ _
    _ ≤ _ := by simpa only [mul_assoc] using h₂mul


/-- The root form of the four-cycle testing inequality. Nested square roots are the nonnegative real fourth root used in the four-cycle testing bound. -/
theorem fourCycle_test (F : Table X Y) (f : X → ℝ) (g : Y → ℝ) :
    |average (fun x => f x * average (fun y => F x y * g y))| ≤
      Real.sqrt (average (fun x => f x ^ 2)) *
        Real.sqrt (average (fun y => g y ^ 2)) * Real.sqrt (Real.sqrt (fourCycle F)) := by
  have hf0 : 0 ≤ average (fun x => f x ^ 2) := average_nonneg fun _ => sq_nonneg _
  have hg0 : 0 ≤ average (fun y => g y ^ 2) := average_nonneg fun _ => sq_nonneg _
  have hc0 := fourCycle_nonneg F
  have fourth_sqrt (a : ℝ) (ha : 0 ≤ a) : (Real.sqrt a) ^ 4 = a ^ 2 := by
    calc
      _ = ((Real.sqrt a) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt ha]
  have fourth_fourthroot : (Real.sqrt (Real.sqrt (fourCycle F))) ^ 4 = fourCycle F := by
    rw [fourth_sqrt _ (Real.sqrt_nonneg _), Real.sq_sqrt hc0]
  apply le_of_pow_le_pow_left₀ (by norm_num : 4 ≠ 0) (by positivity)
  rw [mul_pow, mul_pow, fourth_sqrt _ hf0, fourth_sqrt _ hg0, fourth_fourthroot]
  simpa only [show 4 = 2 * 2 by norm_num, pow_mul, sq_abs] using
    fourCycle_test_fourth F f g

/-- Pointwise balanced-factor energy bound from the row's Bessel bound. The statement is the arithmetic step in the paper's projection-energy estimate. -/
theorem retained_weighted_energy {ι : Type*} (I : Finset ι) (σ u : ι → ℝ)
    {β : ℝ} (hβ : 0 < β) (hσ : ∀ j ∈ I, β ≤ σ j)
    (hrow : ∑ j ∈ I, σ j ^ 2 * u j ^ 2 ≤ 1) :
    ∑ j ∈ I, σ j * u j ^ 2 ≤ 1 / β := by
  have hterm : ∀ j ∈ I, β * (σ j * u j ^ 2) ≤ σ j ^ 2 * u j ^ 2 := by
    intro j hj
    have hs := hσ j hj
    have hs0 : 0 ≤ σ j := le_trans (le_of_lt hβ) hs
    have hm := mul_nonneg (sub_nonneg.mpr hs) (mul_nonneg hs0 (sq_nonneg (u j)))
    nlinarith
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  apply (le_div_iff₀ hβ).mpr
  nlinarith

/-- Unweighted row energy of the retained singular functions. -/
theorem retained_unweighted_energy {ι : Type*} (I : Finset ι) (σ u : ι → ℝ)
    {β : ℝ} (hβ : 0 < β) (hσ : ∀ j ∈ I, β ≤ σ j)
    (hrow : ∑ j ∈ I, σ j ^ 2 * u j ^ 2 ≤ 1) :
    ∑ j ∈ I, u j ^ 2 ≤ 1 / β ^ 2 := by
  have hterm : ∀ j ∈ I, β ^ 2 * u j ^ 2 ≤ σ j ^ 2 * u j ^ 2 := by
    intro j hj
    have hs := hσ j hj
    have hs0 : 0 ≤ σ j := le_trans (le_of_lt hβ) hs
    have hsq : β ^ 2 ≤ σ j ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  apply (le_div_iff₀ (sq_pos_of_pos hβ)).mpr
  nlinarith

/-- The nuclear bootstrap inequality forces an absolute nuclear norm at most two. -/
theorem nuclear_bootstrap {L : ℝ} (hL : 0 ≤ L)
    (h : 2 * L ≤ 2 + Real.sqrt (2 * L)) : L ≤ 2 := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * L)
  have hp := Real.sqrt_nonneg (2 * L)
  nlinarith

end RefreshingProof.Local
