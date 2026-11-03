import Proofs.Compiler.GateApproximation.MatrixPhase.PhysicalShares
import Proofs.Compiler.LocalComparisons.FactorEnergies
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Tensor discrepancy for independent signed encoding differences

A bound for one signed left/right kernel tensorizes by applying its linear operator one coordinate at a time. Squared counting L₂ norms keep this argument elementary; uniform normalization is applied only after tensorization. No positivity of a signed kernel is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.DirectComposition

variable {X : Type*} [Fintype X]

/-- Apply a finite signed matrix to a real column using counting measure. -/
def sumTransform (D : X → X → ℝ) (g : X → ℝ) (x : X) : ℝ :=
  ∑ y, D x y * g y

/-- A counting L₂ operator estimate, stated without square roots. -/
def CountingSquaredBound (D : X → X → ℝ) (c : ℝ) : Prop :=
  ∀ g : X → ℝ, (∑ x, sumTransform D g x ^ 2) ≤ c ^ 2 * ∑ y, g y ^ 2

/-- Testing a bilinear bound on the image vector gives the corresponding squared operator estimate. -/
theorem countingSquaredBound_of_pairing (D : X → X → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hD : ∀ f g : X → ℝ,
      |∑ x, ∑ y, D x y * f x * g y| ≤
        c * Real.sqrt (∑ x, f x ^ 2) * Real.sqrt (∑ y, g y ^ 2)) :
    CountingSquaredBound D c := by
  intro g
  let t := sumTransform D g
  have hs : 0 ≤ ∑ x, t x ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hg : 0 ≤ ∑ y, g y ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp : (∑ x, ∑ y, D x y * t x * g y) = ∑ x, t x ^ 2 := by
    apply Finset.sum_congr rfl
    intro x _
    calc
      (∑ y, D x y * t x * g y) = t x * ∑ y, D x y * g y := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = t x ^ 2 := by change t x * t x = t x ^ 2; ring
  have h := hD t g
  rw [hp,abs_of_nonneg hs] at h
  have hroot : Real.sqrt (∑ x, t x ^ 2) ≤ c * Real.sqrt (∑ y, g y ^ 2) := by
    by_contra hn
    have hlt : c * Real.sqrt (∑ y, g y ^ 2) < Real.sqrt (∑ x, t x ^ 2) := lt_of_not_ge hn
    have hpos : 0 < Real.sqrt (∑ x, t x ^ 2) :=
      lt_of_le_of_lt (mul_nonneg hc (Real.sqrt_nonneg _)) hlt
    nlinarith [Real.sq_sqrt hs]
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hc (Real.sqrt_nonneg _))).2 hroot
  simpa only [mul_pow,Real.sq_sqrt hs,Real.sq_sqrt hg] using hsq

/-- A product of signed coordinate kernels on tuples of length k. -/
def tensorKernel {k : ℕ} (D : Fin k → X → X → ℝ)
    (left right : Fin k → X) : ℝ := ∏ i, D i (left i) (right i)

/-- Separate the first coordinate in a counting sum over finite tuples. -/
theorem sum_tuple_succ {k : ℕ} (f : (Fin (k+1) → X) → ℝ) :
    (∑ x, f x) = ∑ a : X, ∑ rest : Fin k → X, f (Fin.cons a rest) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k+1) => X))]
  simp only [Fintype.sum_prod_type]
  rfl

/-- Applying a tensor kernel separates into a coordinate operator and the operator on the remaining tuple. -/
theorem tensorTransform_cons {k : ℕ} (D : Fin (k+1) → X → X → ℝ)
    (g : (Fin (k+1) → X) → ℝ) (a : X) (left : Fin k → X) :
    sumTransform (tensorKernel D) g (Fin.cons a left) =
      ∑ b : X, D 0 a b * sumTransform (tensorKernel (fun i => D i.succ))
        (fun right => g (Fin.cons b right)) left := by
  unfold sumTransform
  rw [sum_tuple_succ]
  simp only [tensorKernel,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right _
  ring

/-- Counting L₂ operator bounds multiply under tensor products, including the empty tensor. -/
theorem tensorKernel_squaredBound : ∀ (k : ℕ) (D : Fin k → X → X → ℝ) (c : Fin k → ℝ),
    (∀ i, CountingSquaredBound (D i) (c i)) →
    CountingSquaredBound (tensorKernel D) (∏ i, c i) := by
  intro k
  induction k with
  | zero =>
      intro D c hD g
      simp [CountingSquaredBound,sumTransform,tensorKernel]
  | succ k ih =>
      intro D c hD g
      let H (b : X) (left : Fin k → X) :=
        sumTransform (tensorKernel (fun i => D i.succ))
          (fun right => g (Fin.cons b right)) left
      have hrest := ih (fun i => D i.succ) (fun i => c i.succ) (fun i => hD i.succ)
      have hpoint (left : Fin k → X) :
          (∑ a : X, sumTransform (tensorKernel D) g (Fin.cons a left) ^ 2) ≤
            c 0 ^ 2 * ∑ b : X, H b left ^ 2 := by
        simp_rw [tensorTransform_cons]
        exact hD 0 (fun b => H b left)
      calc
        (∑ left, sumTransform (tensorKernel D) g left ^ 2)
            = ∑ tail : Fin k → X, ∑ a : X,
                sumTransform (tensorKernel D) g (Fin.cons a tail) ^ 2 := by
                  rw [sum_tuple_succ,Finset.sum_comm]
        _ ≤ ∑ tail : Fin k → X, c 0 ^ 2 * ∑ b : X, H b tail ^ 2 :=
              Finset.sum_le_sum (fun tail _ => hpoint tail)
        _ = c 0 ^ 2 * ∑ b : X, ∑ tail : Fin k → X, H b tail ^ 2 := by
              rw [← Finset.mul_sum,Finset.sum_comm]
        _ ≤ c 0 ^ 2 * ∑ b : X, (∏ i : Fin k, c i.succ) ^ 2 *
              ∑ right : Fin k → X, g (Fin.cons b right) ^ 2 := by
                apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
                exact Finset.sum_le_sum (fun b _ => hrest (fun right => g (Fin.cons b right)))
        _ = (∏ i : Fin (k+1), c i) ^ 2 * ∑ right, g right ^ 2 := by
              rw [← Finset.mul_sum,
                ← sum_tuple_succ (fun right : Fin (k+1) → X => g right ^ 2),
                Fin.prod_univ_succ,mul_pow]
              ring

/-- A squared operator estimate controls every signed bilinear pairing by Cauchy–Schwarz. -/
theorem counting_pairing_of_squaredBound (D : X → X → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hD : CountingSquaredBound D c) (f g : X → ℝ) :
    |∑ x, ∑ y, D x y * f x * g y| ≤
      c * Real.sqrt (∑ x, f x ^ 2) * Real.sqrt (∑ y, g y ^ 2) := by
  have hp : (∑ x, ∑ y, D x y * f x * g y) = ∑ x, f x * sumTransform D g x := by
    apply Finset.sum_congr rfl
    intro x _
    rw [sumTransform,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hp]
  calc
    _ ≤ Real.sqrt (∑ x, f x ^ 2) * Real.sqrt (∑ x, sumTransform D g x ^ 2) :=
      Refresh.abs_sum_mul_le f (sumTransform D g)
    _ ≤ Real.sqrt (∑ x, f x ^ 2) * Real.sqrt (c ^ 2 * ∑ y, g y ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hD g)) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc];ring

/-- Rename tuple coordinates along an equivalence without changing any value. -/
def tupleReindex {W : Type*} {k : ℕ} (e : Fin k ≃ W) : (Fin k → X) ≃ (W → X) where
  toFun x w := x (e.symm w)
  invFun x i := x (e i)
  left_inv x := by funext i; simp
  right_inv x := by funext w; simp

/-- Coordinate renaming preserves a counting sum over tuples. -/
theorem sum_tuple_reindex {W : Type*} [Fintype W] {k : ℕ} (e : Fin k ≃ W)
    (f : (W → X) → ℝ) :
    (∑ x, f x) = ∑ x : Fin k → X, f (tupleReindex e x) := by
  exact (Equiv.sum_comp (tupleReindex e) f).symm

/-- Coordinate renaming preserves the product of the signed coordinate kernels. -/
theorem prod_kernel_reindex {W : Type*} [Fintype W] {k : ℕ} (e : Fin k ≃ W)
    (D : W → X → X → ℝ) (left right : Fin k → X) :
    (∏ w, D w (tupleReindex e left w) (tupleReindex e right w)) =
      tensorKernel (fun i => D (e i)) left right := by
  rw [← Equiv.prod_comp e]
  simp [tensorKernel,tupleReindex]

/-- One-coordinate counting bilinear bounds tensorize on every finite coordinate set. -/
theorem tensor_counting_pairing {W : Type*} [Fintype W]
    (D : W → X → X → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hD : ∀ w (f g : X → ℝ),
      |∑ x, ∑ y, D w x y * f x * g y| ≤
        c * Real.sqrt (∑ x, f x ^ 2) * Real.sqrt (∑ y, g y ^ 2))
    (f g : (W → X) → ℝ) :
    |∑ left, ∑ right, (∏ w, D w (left w) (right w)) * f left * g right| ≤
      c ^ Fintype.card W * Real.sqrt (∑ left, f left ^ 2) *
        Real.sqrt (∑ right, g right ^ 2) := by
  let e := (Fintype.equivFin W).symm
  have hsq := tensorKernel_squaredBound (Fintype.card W) (fun i => D (e i))
    (fun _ => c) (fun i => countingSquaredBound_of_pairing (D (e i)) c hc (hD (e i)))
  have h := counting_pairing_of_squaredBound
    (tensorKernel (fun i => D (e i))) (∏ _ : Fin (Fintype.card W), c)
    (Finset.prod_nonneg (fun _ _ => hc)) hsq
    (fun left => f (tupleReindex e left)) (fun right => g (tupleReindex e right))
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at h
  simpa only [sum_tuple_reindex e,prod_kernel_reindex] using h

/-- Uniform RMS products equal the corresponding counting square-root product divided by the carrier cardinality. -/
theorem uniform_rms_product [Nonempty X] (f g : X → ℝ) :
    Real.sqrt ((Refresh.FiniteDistribution.uniform : Refresh.FiniteDistribution X).expect
        (fun x => f x ^ 2)) *
      Real.sqrt ((Refresh.FiniteDistribution.uniform : Refresh.FiniteDistribution X).expect
        (fun x => g x ^ 2)) =
    (Fintype.card X : ℝ)⁻¹ * Real.sqrt (∑ x, f x ^ 2) * Real.sqrt (∑ x, g x ^ 2) := by
  have hcard : 0 ≤ (Fintype.card X : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  simp only [Refresh.FiniteDistribution.expect,Refresh.FiniteDistribution.uniform,← Finset.mul_sum]
  rw [Real.sqrt_mul hcard,Real.sqrt_mul hcard]
  calc
    _ = Real.sqrt ((Fintype.card X : ℝ)⁻¹) ^ 2 *
        Real.sqrt (∑ x, f x ^ 2) * Real.sqrt (∑ x, g x ^ 2) := by ring
    _ = _ := by rw [Real.sq_sqrt hcard]

/-- Uniform one-wire discrepancy tensorizes with one factor of δ for each independent wire. -/
theorem tensor_uniform_pairing [Nonempty X] {W : Type*} [Fintype W]
    (D : W → X → X → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hD : ∀ w (f g : X → ℝ),
      |∑ x, ∑ y, D w x y * f x * g y| ≤
        δ * Real.sqrt ((Refresh.FiniteDistribution.uniform : Refresh.FiniteDistribution X).expect
          (fun x => f x ^ 2)) *
          Real.sqrt ((Refresh.FiniteDistribution.uniform : Refresh.FiniteDistribution X).expect
            (fun x => g x ^ 2)))
    (f g : (W → X) → ℝ) :
    |∑ left, ∑ right, (∏ w, D w (left w) (right w)) * f left * g right| ≤
      δ ^ Fintype.card W *
        Real.sqrt ((Refresh.FiniteDistribution.uniform : Refresh.FiniteDistribution (W → X)).expect
          (fun left => f left ^ 2)) *
        Real.sqrt ((Refresh.FiniteDistribution.uniform : Refresh.FiniteDistribution (W → X)).expect
          (fun right => g right ^ 2)) := by
  have hc : 0 ≤ δ * (Fintype.card X : ℝ)⁻¹ :=
    mul_nonneg hδ (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hsingle (w : W) (a b : X → ℝ) :
      |∑ x, ∑ y, D w x y * a x * b y| ≤
        (δ * (Fintype.card X : ℝ)⁻¹) * Real.sqrt (∑ x, a x ^ 2) *
          Real.sqrt (∑ y, b y ^ 2) := by
    have h := hD w a b
    calc
      _ ≤ δ * (Real.sqrt (Refresh.FiniteDistribution.uniform.expect (fun x => a x ^ 2)) *
            Real.sqrt (Refresh.FiniteDistribution.uniform.expect (fun x => b x ^ 2))) := by
              simpa only [mul_assoc] using h
      _ = _ := by rw [uniform_rms_product];ring
  have h := tensor_counting_pairing D (δ * (Fintype.card X : ℝ)⁻¹) hc hsingle f g
  convert h using 1
  rw [mul_assoc (δ ^ Fintype.card W),uniform_rms_product]
  simp only [mul_pow,inv_pow,Fintype.card_fun,Nat.cast_pow]
  ring

/-- A signed tensor pairing is linear in a finite sum of tables. -/
theorem tensor_pairing_sum {W J : Type*} [Fintype W] [Fintype J]
    (D : W → X → X → ℝ) (f : J → (W → X) → (W → X) → ℝ) :
    (∑ left, ∑ right, (∏ w, D w (left w) (right w)) * ∑ j, f j left right) =
      ∑ j, ∑ left, ∑ right, (∏ w, D w (left w) (right w)) * f j left right := by
  simp_rw [Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.sum_comm]

/-- Tensor discrepancy controls a table by the separate mean energies of any chosen product representation. -/
theorem tensor_factors_pairing [Nonempty X] {W : Type*} [Fintype W]
    (D : W → X → X → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hD : ∀ w (f g : X → ℝ),
      |∑ x, ∑ y, D w x y * f x * g y| ≤
        δ * Real.sqrt ((Refresh.FiniteDistribution.uniform : Refresh.FiniteDistribution X).expect
          (fun x => f x ^ 2)) *
          Real.sqrt ((Refresh.FiniteDistribution.uniform : Refresh.FiniteDistribution X).expect
            (fun x => g x ^ 2)))
    (f : (W → X) → (W → X) → ℝ)
    (a : CircuitCompiler.AveragedEnergyComparison.Factors f) :
    |∑ left, ∑ right, (∏ w, D w (left w) (right w)) * f left right| ≤
      δ ^ Fintype.card W *
        (Real.sqrt ((Refresh.FiniteDistribution.uniform :
          Refresh.FiniteDistribution (W → X)).expect a.leftEnergy) *
         Real.sqrt ((Refresh.FiniteDistribution.uniform :
          Refresh.FiniteDistribution (W → X)).expect a.rightEnergy)) := by
  simp_rw [a.reconstruct]
  rw [tensor_pairing_sum]
  calc
    _ ≤ ∑ j, |∑ left, ∑ right,
          (∏ w, D w (left w) (right w)) * (a.left left j * a.right right j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, δ ^ Fintype.card W *
        MatrixRefresh.rms Refresh.FiniteDistribution.uniform (fun left => a.left left j) *
        MatrixRefresh.rms Refresh.FiniteDistribution.uniform (fun right => a.right right j) := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [MatrixRefresh.rms,mul_assoc] using
        tensor_uniform_pairing D δ hδ hD (fun left => a.left left j) (fun right => a.right right j)
    _ = δ ^ Fintype.card W * ∑ j,
        MatrixRefresh.rms Refresh.FiniteDistribution.uniform (fun left => a.left left j) *
        MatrixRefresh.rms Refresh.FiniteDistribution.uniform (fun right => a.right right j) := by
      simp only [Finset.mul_sum,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (a.cost_le Refresh.FiniteDistribution.uniform Refresh.FiniteDistribution.uniform)
      (pow_nonneg hδ _)

/-- Pointwise factor-energy bounds remain sufficient after summing over all marked-wire coordinates with their signed weights. -/
theorem tensor_factors_pairing_le [Nonempty X] {W : Type*} [Fintype W]
    (D : W → X → X → ℝ) (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hD : ∀ w (f g : X → ℝ),
      |∑ x, ∑ y, D w x y * f x * g y| ≤
        δ * Real.sqrt ((Refresh.FiniteDistribution.uniform : Refresh.FiniteDistribution X).expect
          (fun x => f x ^ 2)) *
          Real.sqrt ((Refresh.FiniteDistribution.uniform : Refresh.FiniteDistribution X).expect
            (fun x => g x ^ 2)))
    (f : (W → X) → (W → X) → ℝ)
    (a : CircuitCompiler.AveragedEnergyComparison.Factors f)
    (hleft : ∀ left, a.leftEnergy left ≤ B) (hright : ∀ right, a.rightEnergy right ≤ B) :
    |∑ left, ∑ right, (∏ w, D w (left w) (right w)) * f left right| ≤
      δ ^ Fintype.card W * B := by
  have hL : (Refresh.FiniteDistribution.uniform :
      Refresh.FiniteDistribution (W → X)).expect a.leftEnergy ≤ B := by
    calc
      _ ≤ Refresh.FiniteDistribution.uniform.expect (fun _ : W → X => B) :=
        Refresh.FiniteDistribution.expect_mono _ hleft
      _ = B := Refresh.FiniteDistribution.expect_const _ _
  have hR : (Refresh.FiniteDistribution.uniform :
      Refresh.FiniteDistribution (W → X)).expect a.rightEnergy ≤ B := by
    calc
      _ ≤ Refresh.FiniteDistribution.uniform.expect (fun _ : W → X => B) :=
        Refresh.FiniteDistribution.expect_mono _ hright
      _ = B := Refresh.FiniteDistribution.expect_const _ _
  apply (tensor_factors_pairing D δ hδ hD f a).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hδ _)
  calc
    _ ≤ Real.sqrt B * Real.sqrt B := mul_le_mul (Real.sqrt_le_sqrt hL)
      (Real.sqrt_le_sqrt hR) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = B := Real.mul_self_sqrt hB

end CompilerProof.DirectComposition
