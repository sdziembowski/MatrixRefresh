import Proofs.Compiler.Construction.Parameters
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Freshness



/-!
# The tensor and matrix phases of a compiled gate

These definitions use the actual finite-field shares and invertible-matrix refresh already formalized by `MatrixRefresh`. The tensor has `n * n` coordinates, indexed using `finProdFinEquiv`. Both parties use the same matrix; no independence of their matrix randomness is assumed.
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler

open Refresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Tensoring two inner-product encodings multiplies their represented values. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; a, b, c, d ∈ V(F, n), we have

(tensorVector(a, b) · tensorVector(c, d)) = (a · c) · (b · d).
-/
theorem tensorVector_dot {n : ℕ} (a b c d : V F n) :
    dot (tensorVector a b) (tensorVector c d) = dot a c * dot b d := by
  unfold dot dotProduct
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [tensorVector_pair, Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The two nonzero tensor shares before the matrix phase. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; a, b ∈ State(F, n), define

tensorState(a, b) := (tensorVector(a.L, b.L), tensorVector(a.R, b.R)).
-/
def tensorState {n : ℕ} (a b : State F n) : State F (n * n) :=
  ⟨⟨tensorVector a.L.val b.L.val, tensorVector_ne_zero a.L b.L⟩,
   ⟨tensorVector a.R.val b.R.val, tensorVector_ne_zero a.R b.R⟩⟩

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; a, b ∈ State(F, n), we have

secret(tensorState(a, b)) = secret(a) · secret(b).
-/
@[simp] theorem tensorState_secret {n : ℕ} (a b : State F n) :
    secret (tensorState a b) = secret a * secret b := by
  exact tensorVector_dot a.L.val b.L.val a.R.val b.R.val

/-- The actual long encoding produced by the tensor and matrix phases. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; a, b ∈ State(F, n); M ∈ GL_(n · n)(F), define

refreshedTensor(a, b, M) := refresh(tensorState(a, b), M).
-/
def refreshedTensor {n : ℕ} (a b : State F n) (M : Refresh.«GL» F (n * n)) :
    State F (n * n) := refresh (tensorState a b) M

/-- Pointwise correctness holds for every sampled invertible matrix. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; a, b ∈ State(F, n); M ∈ GL_(n · n)(F), we have

secret(refreshedTensor(a, b, M)) = secret(a) · secret(b).
-/
@[simp] theorem refreshedTensor_secret {n : ℕ} (a b : State F n)
    (M : Refresh.«GL» F (n * n)) :
    secret (refreshedTensor a b M) = secret a * secret b := by
  simp [refreshedTensor]

/-- The initial tensor as an element of the product-value fiber. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; a, b ∈ State(F, n), define

tensorFiber(a, b) := tensorState(a, b).
-/
def tensorFiber {n : ℕ} (a b : State F n) :
    Fiber F (n * n) (secret a * secret b) :=
  ⟨tensorState a b, tensorState_secret a b⟩

/-- Uniform matrix refresh is exactly uniform on the product fiber for every fixed pair of input encodings. This includes a zero represented product. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): For every fixed pair of operand encodings with secrets s₁,s₂, refreshing their tensor encoding by a uniform invertible matrix produces exactly the uniform encoding distribution of s₁s₂ in dimension n². This includes the case s₁s₂ = 0. -/
theorem refreshedTensor_uniform_fiber {n : ℕ} (a b : State F n) :
    letI : Nonempty (Fiber F (n * n) (secret a * secret b)) := ⟨tensorFiber a b⟩
    (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n * n))).map
        (refreshInFiber (tensorFiber a b)) =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n * n) (secret a * secret b))) := by
  letI : Nonempty (Fiber F (n * n) (secret a * secret b)) := ⟨tensorFiber a b⟩
  exact refresh_uniform_fiber (tensorFiber a b)

/-- The same exact freshness statement on the ambient nonzero-share carrier. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; a, b ∈ State(F, n), assume 2 ≤ n · n. Then

(refreshedTensor(a, b)_*𝒰_(GL_(n · n)(F))) = μ_(secret(a) · secret(b)).
-/
theorem refreshedTensor_uniform {n : ℕ} (hn : 2 ≤ n * n) (a b : State F n) :
    (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n * n))).map (refreshedTensor a b) =
      mu F (n * n) hn (secret a * secret b) := by
  exact refresh_uniform hn _ (tensorState a b) (tensorState_secret a b)

/-- Before observing leakage answers, the refreshed long encoding is independent of both old input encodings, for any distribution of those encodings with fixed represented values. Independence of the two old inputs is not needed. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s₁, s₂ ∈ F; P ∈ 𝒟((Fiber(F, n, s₁) × Fiber(F, n, s₂))), assume 2 ≤ n · n. Then

P.joint(((ab ↦ (refreshedTensor((ab)₁, (ab)₂)_*𝒰_(GL_(n · n)(F)))))) = (P ⊗ μ_(s₁ · s₂)).
-/
theorem refreshedTensor_joint_independent {n : ℕ} (hn : 2 ≤ n * n) (s₁ s₂ : F)
    (P : FiniteDistribution (Fiber F n s₁ × Fiber F n s₂)) :
    P.joint (fun ab => (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n * n))).map
      (refreshedTensor ab.1.val ab.2.val)) =
      P.prod (mu F (n * n) hn (s₁ * s₂)) := by
  have h (ab : Fiber F n s₁ × Fiber F n s₂) :
      (FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F (n * n))).map
        (refreshedTensor ab.1.val ab.2.val) = mu F (n * n) hn (s₁ * s₂) := by
    simpa only [ab.1.property, ab.2.property] using
      refreshedTensor_uniform hn ab.1.val ab.2.val
  simp only [h, FiniteDistribution.prod]

end CircuitCompiler
