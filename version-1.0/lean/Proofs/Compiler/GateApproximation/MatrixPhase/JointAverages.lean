import Proofs.Compiler.GateApproximation.MatrixPhase.JointGramPerturbation
import Proofs.Compiler.Foundations.LinearAlgebra.Mixing



/-!
# Averaging the Gram perturbation costs

Two finite Cauchy--Schwarz steps provide the fourth-root moment bound. These estimates apply to the correlated row and column errors under the same refresh matrix; independence is never required.
-/

set_option autoImplicit false

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace CircuitCompiler

open MatrixRefresh TableAnalysis

noncomputable section

variable {G : Type*} [Fintype G] [Nonempty G]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ G → ℝ, we have

(𝔼ᵤ [f(u)])² ≤ 𝔼_g [(f(g))²].
-/
lemma joint_average_sq_le (f : G → ℝ) : uavg f ^ 2 ≤ uavg (fun g => f g ^ 2) := by
  simpa only [mul_one, one_pow, uavg_const] using uavg_mul_sq_le f (fun _ => 1)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ G → ℝ, we have

𝔼ᵤ [f(u)] ≤ √(𝔼_g [(f(g))²]).
-/
lemma joint_average_le_root_mean_sq (f : G → ℝ) :
    uavg f ≤ Real.sqrt (uavg (fun g => f g ^ 2)) := by
  have h := Real.sqrt_le_sqrt (joint_average_sq_le f)
  rw [Real.sqrt_sq_eq_abs] at h
  exact (le_abs_self _).trans h

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ G → ℝ, assume ∀ g, 0 ≤ f(g). Then

𝔼_g [√(f(g))] ≤ √(𝔼ᵤ [f(u)]).
-/
lemma joint_average_sqrt_le (f : G → ℝ) (hf : ∀ g, 0 ≤ f g) :
    uavg (fun g => Real.sqrt (f g)) ≤ Real.sqrt (uavg f) := by
  have h := joint_average_le_root_mean_sq (fun g => Real.sqrt (f g))
  simpa only [Real.sq_sqrt (hf _)] using h

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f ∈ G → ℝ; V ∈ ℝ, assume ∀ g, 0 ≤ f(g); 𝔼_g [(f(g))²] ≤ V. Then

𝔼_g [√(f(g))] ≤ √(√V).
-/
lemma joint_average_sqrt_le_fourthRoot (f : G → ℝ) (hf : ∀ g, 0 ≤ f g)
    (V : ℝ) (hV : uavg (fun g => f g ^ 2) ≤ V) :
    uavg (fun g => Real.sqrt (f g)) ≤ Real.sqrt (Real.sqrt V) := by
  apply (joint_average_sqrt_le f hf).trans
  apply Real.sqrt_le_sqrt
  exact (joint_average_le_root_mean_sq f).trans (Real.sqrt_le_sqrt hV)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f, h ∈ G → ℝ; V ∈ ℝ, assume ∀ g, 0 ≤ f(g); ∀ g, 0 ≤ h(g); 𝔼_g [(f(g))²] ≤ V; 𝔼_g [(h(g))²] ≤ V. Then

𝔼_g [√(f(g)) · √(h(g))] ≤ √V.
-/
lemma joint_average_sqrt_product_le (f h : G → ℝ)
    (hf : ∀ g, 0 ≤ f g) (hh : ∀ g, 0 ≤ h g)
    (V : ℝ) (hVf : uavg (fun g => f g ^ 2) ≤ V) (hVh : uavg (fun g => h g ^ 2) ≤ V) :
    uavg (fun g => Real.sqrt (f g) * Real.sqrt (h g)) ≤ Real.sqrt V := by
  have havf := (joint_average_le_root_mean_sq f).trans (Real.sqrt_le_sqrt hVf)
  have havh := (joint_average_le_root_mean_sq h).trans (Real.sqrt_le_sqrt hVh)
  calc
    _ ≤ uavg (fun g => (f g + h g) / 2) := by
      apply uavg_mono
      intro g
      nlinarith [sq_nonneg (Real.sqrt (f g) - Real.sqrt (h g)),
        Real.sq_sqrt (hf g), Real.sq_sqrt (hh g)]
    _ = (uavg f + uavg h) / 2 := by simp only [div_eq_mul_inv, uavg_mul_const, uavg_add]
    _ ≤ _ := by linarith

/-- The averaged four-block estimate, using only second moments of both errors. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For k, f, h ∈ G → ℝ; d, a, b, V ∈ ℝ, assume 0 ≤ a; 0 ≤ b; ∀ g, 0 ≤ f(g); ∀ g, 0 ≤ h(g); 𝔼_g [(f(g))²] ≤ V; 𝔼_g [(h(g))²] ≤ V; ∀ g, k(g) ≤ d + a · √(h(g)) + b · √(f(g)) + √(f(g)) · √(h(g)). Then

𝔼ᵤ [k(u)] ≤ d + (a + b) · √(√V) + √V.
-/
theorem joint_average_perturbation_bound (k f h : G → ℝ) (d a b V : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf : ∀ g, 0 ≤ f g) (hh : ∀ g, 0 ≤ h g)
    (hVf : uavg (fun g => f g ^ 2) ≤ V) (hVh : uavg (fun g => h g ^ 2) ≤ V)
    (hk : ∀ g, k g ≤ d + a * Real.sqrt (h g) + b * Real.sqrt (f g) +
      Real.sqrt (f g) * Real.sqrt (h g)) :
    uavg k ≤ d + (a + b) * Real.sqrt (Real.sqrt V) + Real.sqrt V := by
  have hf' := joint_average_sqrt_le_fourthRoot f hf V hVf
  have hh' := joint_average_sqrt_le_fourthRoot h hh V hVh
  have hprod := joint_average_sqrt_product_le f h hf hh V hVf hVh
  have h := uavg_mono hk
  simp only [uavg_add, uavg_const_mul, uavg_const] at h
  nlinarith [mul_le_mul_of_nonneg_left hf' hb, mul_le_mul_of_nonneg_left hh' ha]

end

end CircuitCompiler
