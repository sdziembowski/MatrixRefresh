import Proofs.Compiler.GateApproximation.MatrixPhase.JointMixing
import Proofs.Compiler.GateApproximation.MatrixPhase.JointOrbitDensity



/-!
# Exceptional dependent pairs in the joint four-cycle

The old tensors have exact projective degree `(q-1)^2`. Ordinary nonzero output vectors have projective degree `q-1`. The union bound below retains arbitrary bounded four-corner functions rather than assuming their sign.
-/
set_option autoImplicit false

open scoped BigOperators Classical

namespace CircuitCompiler

open Refresh MatrixRefresh TableAnalysis

noncomputable section

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X,Y a set; P ∈ X → X → Prop; Q ∈ Y → Y → Prop; r, s, B ∈ ℝ; f ∈ X → X → Y → Y → ℝ, assume X is finite; Y is finite; X ≠ ∅; Y ≠ ∅; 0 ≤ B; ∀ x, 𝔼_(x') [{ 1 if P(x, x'),; 0 otherwise }] = r; ∀ y, 𝔼_(y') [{ 1 if Q(y, y'),; 0 otherwise }] = s; ∀ x, x', y, y', |f(x, x', y, y')| ≤ B. Then

𝔼ₓ [𝔼_(x') [𝔼_y [𝔼_(y') [{ |f(x, x', y, y')| if P(x, x') ∨ Q(y, y'),; 0 otherwise }]]]] ≤ (r + s) · B.
-/
theorem two_relation_exception_le {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (P : X → X → Prop) (Q : Y → Y → Prop)
    (r s B : ℝ) (hB : 0 ≤ B)
    (hP : ∀ x, uavg (fun x' => if P x x' then (1 : ℝ) else 0) = r)
    (hQ : ∀ y, uavg (fun y' => if Q y y' then (1 : ℝ) else 0) = s)
    (f : X → X → Y → Y → ℝ) (hf : ∀ x x' y y', |f x x' y y'| ≤ B) :
    uavg (fun x => uavg (fun x' => uavg (fun y => uavg (fun y' =>
      if P x x' ∨ Q y y' then |f x x' y y'| else 0)))) ≤ (r + s) * B := by
  calc
    _ ≤ uavg (fun x => uavg (fun x' => uavg (fun y => uavg (fun y' =>
        ((if P x x' then (1 : ℝ) else 0) + (if Q y y' then 1 else 0)) * B)))) := by
      apply uavg_mono
      intro x
      apply uavg_mono
      intro x'
      apply uavg_mono
      intro y
      apply uavg_mono
      intro y'
      by_cases hp : P x x' <;> by_cases hq : Q y y' <;>
        simp only [hp, hq, or_self, or_true, true_or, if_true, if_false, add_zero,
          zero_add, zero_mul, one_mul] <;> linarith [hf x x' y y']
    _ = _ := by
      simp_rw [uavg_mul_const, uavg_add, uavg_const, hQ, hP]
      simp only [uavg_const]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Tensor proportionality has exactly the counted exceptional probability for each fixed old input. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; x ∈ U(F, n) × U(F, n), we have

𝔼_(y ∈ U(F, n) × U(F, n)) [{ 1 if projectiveRel(inputTensor(x), inputTensor(y)),; 0 otherwise }] = ((|F| - 1)²) / (|U(F, n)|)².
-/
theorem tensor_projective_probability {n : ℕ} (x : U F n × U F n) :
    uavg (fun y : U F n × U F n =>
      if projectiveRel (inputTensor x) (inputTensor y) then (1 : ℝ) else 0) =
      (((fieldCard F - 1 : ℕ) : ℝ) ^ 2) / (Fintype.card (U F n) : ℝ) ^ 2 := by
  change uavg (fun y => projectiveIndicator (inputTensor x) (inputTensor y)) = _
  rw [uavg, inputTensor_projective_row_sum, Fintype.card_prod, Nat.cast_mul]
  ring

/-- Either dependent old tensor pair costs at most twice its exact collision fraction, with no assumption on the signed corner contribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; B ∈ ℝ; f ∈ (U(F, n) × U(F, n)) → (U(F, n) × U(F, n)) → (U(F, n) × U(F, n)) → (U(F, n) × U(F, n)) → ℝ, assume 2 ≤ n; 0 ≤ B; ∀ x, x', y, y', |f(x, x', y, y')| ≤ B. Then

𝔼ₓ [𝔼_(x') [𝔼_y [𝔼_(y') [{ |f(x, x', y, y')| if projectiveRel(inputTensor(x), inputTensor(x')) ∨ projectiveRel(inputTensor(y), inputTensor(y')),; 0 otherwise }]]]] ≤ (2 · ((|F| - 1)²) / (|U(F, n)|)²) · B.
-/
theorem tensor_rank_exception_le {n : ℕ} (hn : 2 ≤ n) (B : ℝ) (hB : 0 ≤ B)
    (f : (U F n × U F n) → (U F n × U F n) →
      (U F n × U F n) → (U F n × U F n) → ℝ)
    (hf : ∀ x x' y y', |f x x' y y'| ≤ B) :
    uavg (fun x => uavg (fun x' => uavg (fun y => uavg (fun y' =>
      if projectiveRel (inputTensor x) (inputTensor x') ∨
        projectiveRel (inputTensor y) (inputTensor y') then |f x x' y y'| else 0)))) ≤
      (2 * (((fieldCard F - 1 : ℕ) : ℝ) ^ 2) / (Fintype.card (U F n) : ℝ) ^ 2) * B := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0, by omega⟩⟩
  convert two_relation_exception_le (fun x x' => projectiveRel (inputTensor x) (inputTensor x'))
    (fun y y' => projectiveRel (inputTensor y) (inputTensor y')) _ _ B hB
    tensor_projective_probability tensor_projective_probability f hf using 1 <;> ring

/-- The projective collision probability of uniform nonzero output vectors. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; x ∈ U(F, m), we have

𝔼_(y ∈ U(F, m)) [{ 1 if projectiveRel(x, y),; 0 otherwise }] = (|F| - 1) / |U(F, m)|.
-/
theorem output_projective_probability {m : ℕ} (x : U F m) :
    uavg (fun y : U F m => if projectiveRel x y then (1 : ℝ) else 0) =
      ((fieldCard F : ℝ) - 1) / Fintype.card (U F m) := by
  change uavg (fun y => projectiveIndicator x y) = _
  rw [uavg, projectiveIndicator_row_sum]
  ring

/-- Removing either output rank restriction has an explicit `Oq(Q⁻¹)` cost under the independent nonzero output distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; B ∈ ℝ; f ∈ U(F, m) → U(F, m) → U(F, m) → U(F, m) → ℝ, assume U(F, m) ≠ ∅; 0 ≤ B; ∀ u, u', v, v', |f(u, u', v, v')| ≤ B. Then

𝔼ᵤ [𝔼_(u') [𝔼ᵥ [𝔼_(v') [{ |f(u, u', v, v')| if projectiveRel(u, u') ∨ projectiveRel(v, v'),; 0 otherwise }]]]] ≤ (2 · (|F| - 1) / |U(F, m)|) · B.
-/
theorem output_rank_exception_le {m : ℕ} [Nonempty (U F m)] (B : ℝ) (hB : 0 ≤ B)
    (f : U F m → U F m → U F m → U F m → ℝ)
    (hf : ∀ u u' v v', |f u u' v v'| ≤ B) :
    uavg (fun u => uavg (fun u' => uavg (fun v => uavg (fun v' =>
      if projectiveRel u u' ∨ projectiveRel v v' then |f u u' v v'| else 0)))) ≤
      (2 * ((fieldCard F : ℝ) - 1) / Fintype.card (U F m)) * B := by
  convert two_relation_exception_le projectiveRel projectiveRel _ _ B hB
    output_projective_probability output_projective_probability f hf using 1 <;> ring

end

end CircuitCompiler
