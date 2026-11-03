import Proofs.Compiler.Foundations.MatrixRefreshing.Analysis.FourthRoot
import Proofs.Compiler.Foundations.MatrixRefreshing.Analysis.Tables



/-! The signed table product estimate, proved with two finite Cauchy--Schwarz steps. -/

set_option autoImplicit false

namespace MatrixRefresh

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]

/-- Finite Cauchy--Schwarz bounds the square of the uniform mean of a product by the product of the two uniform mean squares. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For f, g ∈ α → ℝ, we have

(𝔼ₐ [f(a) · g(a)])² ≤ 𝔼ₐ [(f(a))²] · 𝔼ₐ [(g(a))²].
-/
theorem uavg_mul_sq_le (f g : α → ℝ) :
    uavg (fun a => f a * g a) ^ 2 ≤
      uavg (fun a => f a ^ 2) * uavg (fun a => g a ^ 2) := by
  simpa only [uavg_eq_expect_uniform] using
    expect_mul_sq_le (Refresh.FiniteDistribution.uniform : Refresh.FiniteDistribution α) f g

/-- Expand the mean square of a weighted column average as a double row average involving the table's row Gram product. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Φ ∈ α → β → ℝ; f ∈ α → ℝ, we have

𝔼_y [(𝔼ₓ [f(x) · Φ(x, y)])²] = 𝔼ₓ [𝔼_(x') [f(x) · f(x') · rowProduct(Φ, x, x')]].
-/
theorem table_weighted_square_expansion (Φ : α → β → ℝ) (f : α → ℝ) :
    uavg (fun y => (uavg (fun x => f x * Φ x y)) ^ 2) =
      uavg (fun x => uavg (fun x' => f x * f x' * rowProduct Φ x x')) := by
  simp only [pow_two, uavg_mul_uavg]
  calc
    uavg (fun y => uavg (fun x => uavg (fun x' =>
        (f x * Φ x y) * (f x' * Φ x' y)))) =
      uavg (fun x => uavg (fun y => uavg (fun x' =>
        (f x * Φ x y) * (f x' * Φ x' y)))) := uavg_comm _
    _ = uavg (fun x => uavg (fun x' => uavg (fun y =>
        (f x * Φ x y) * (f x' * Φ x' y)))) := by
      apply uavg_congr
      intro x
      rw [uavg_comm]
    _ = _ := by
      apply uavg_congr
      intro x
      apply uavg_congr
      intro x'
      unfold rowProduct
      rw [← uavg_const_mul]
      apply uavg_congr
      intro y
      ring

end

end MatrixRefresh
