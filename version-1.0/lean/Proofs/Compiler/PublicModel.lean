import Proofs.Refreshing.PublicModel

/-!
# Compiler foundations

Definitions needed by the compiler model and its privacy views.
-/

section Encodings

set_option backward.isDefEq.respectTransparency false
section
section
set_option autoImplicit false
namespace Refresh
/-- The space of field-valued vectors with `n` coordinates. -/

abbrev V (F : Type*) (n : ℕ) := Fin n → F
/-- The subtype of vectors whose coordinates are not all zero. It represents both labelled share spaces `U_L` and `U_R` in the manuscript. -/

abbrev U (F : Type*) [Zero F] (n : ℕ) := {v : V F n // v ≠ 0}
/-- Invertible matrices over `F`, packaged with their inverse identities. For `F2`, this is the paper's `InvMatr_2^n`. -/

abbrev «GL» (F : Type*) [Field F] (n : ℕ) := (Matrix (Fin n) (Fin n) F)ˣ
/-- A retained encoding state: a nonzero row and a nonzero column. It represents the manuscript's joint-state space `U_L × U_R`. The manuscript displays the coordinates as `(ell,r)` when they are needed, and uses whole-state variables in local comparisons and probabilistic arguments. Lean retains the named projections `stateLeftShare` and `stateRightShare` to read those coordinates. -/

@[ext] structure State (F : Type*) [Field F] (n : ℕ) where
  /-- The stored left coordinate; `stateLeftShare` exposes it as an explicit projection. -/
  L : U F n
  /-- The stored right coordinate; `stateRightShare` exposes it as an explicit projection. -/
  R : U F n
/-- The left party's coordinate projection from a joint state to its nonzero row share. It reads only the left coordinate and requires no finiteness assumption. -/

def stateLeftShare {F : Type*} [Field F] {n : ℕ} : State F n → U F n
  | ⟨l, _⟩ => l
/-- The right party's coordinate projection from a joint state to its nonzero column share. It reads only the right coordinate and requires no finiteness assumption. -/

def stateRightShare {F : Type*} [Field F] {n : ℕ} : State F n → U F n
  | ⟨_, r⟩ => r
/-- The inverse laws for the state and share-pair correspondence. -/
def stateEquivProd_laws (F : Type*) [Field F] (n : ℕ) :
    (∀ x : State F n, (⟨stateLeftShare x, stateRightShare x⟩ : State F n) = x) ∧
    (∀ p : U F n × U F n,
      (stateLeftShare (⟨p.1, p.2⟩ : State F n),
       stateRightShare (⟨p.1, p.2⟩ : State F n)) = p) := by
  constructor
  · intro x
    rfl
  · intro p
    rfl
/-- An encoding state is equivalent to its ordered pair of nonzero shares. -/
def stateEquivProd (F : Type*) [Field F] (n : ℕ) : State F n ≃ U F n × U F n where
  toFun x := (stateLeftShare x, stateRightShare x)
  invFun p := ⟨p.1, p.2⟩
  left_inv := (stateEquivProd_laws F n).1
  right_inv := (stateEquivProd_laws F n).2
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Enumerate encoding states by enumerating both nonzero shares independently. -/
instance stateFintype (n : ℕ) : Fintype (State F n) :=
  Fintype.ofEquiv (U F n × U F n) (stateEquivProd F n).symm
/-- The coordinatewise inner product over the field. -/

def dot {n : ℕ} (l r : V F n) : F := dotProduct l r
/-- The field element encoded by a state is the inner product of its two shares. -/

def secret {n : ℕ} (x : State F n) : F := dot (stateLeftShare x).val (stateRightShare x).val
/-- Legal nonzero-share encodings of a specified field element. -/

abbrev Fiber (F : Type*) [Field F] (n : ℕ) (s : F) :=
  {x : State F n // secret x = s}
end Refresh
end
section
set_option autoImplicit false
namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- The left party multiplies its nonzero row by the sampled invertible matrix. -/
abbrev rowRefresh_ne_zero {n : ℕ} (l : U F n) (M : «GL» F n) :
    Matrix.vecMul l.val M.val ≠ 0 := by
  intro h
  apply l.property
  have h' := congrArg (fun v : V F n => Matrix.vecMul v (M⁻¹).val) h
  simpa using h'

def rowRefresh {n : ℕ} (l : U F n) (M : «GL» F n) : U F n :=
  ⟨Matrix.vecMul l.val M.val, rowRefresh_ne_zero l M⟩
/-- The right party multiplies its nonzero column by the inverse sampled matrix. -/
abbrev columnRefresh_ne_zero {n : ℕ} (r : U F n) (M : «GL» F n) :
    Matrix.mulVec (M⁻¹).val r.val ≠ 0 := by
  intro h
  apply r.property
  have h' := congrArg (fun v : V F n => Matrix.mulVec M.val v) h
  simpa using h'

def columnRefresh {n : ℕ} (r : U F n) (M : «GL» F n) : U F n :=
  ⟨Matrix.mulVec (M⁻¹).val r.val, columnRefresh_ne_zero r M⟩
/-- The actual state update uses the same matrix on both sides. -/

def refresh {n : ℕ} (x : State F n) (M : «GL» F n) : State F n :=
  ⟨rowRefresh (stateLeftShare x) M, columnRefresh (stateRightShare x) M⟩
end Refresh
end
end
section
set_option autoImplicit false
namespace Refresh
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- The inner product is symmetric because multiplication in the field is commutative. -/
lemma dot_comm {n : ℕ} (l r : V F n) : dot l r = dot r l := by
  simp [dot, dotProduct, mul_comm]
/-- Pairing with a fixed row distributes over addition of the column vectors. -/
lemma dot_add_right {n : ℕ} (l a b : V F n) : dot l (a + b) = dot l a + dot l b := by
  simp [dot, dotProduct_add]
/-- Pairing with a fixed row distributes over subtraction of the column vectors. -/
lemma dot_sub_right {n : ℕ} (l a b : V F n) : dot l (a - b) = dot l a - dot l b := by
  simp [dot, dotProduct_sub]
/-- Scaling the column vector scales its inner product by the same field element. -/
lemma dot_smul_right {n : ℕ} (l a : V F n) (c : F) : dot l (c • a) = c * dot l a := by
  simp [dot, dotProduct_smul, smul_eq_mul, mul_comm]
/-- A nonzero vector has at least one nonzero coordinate. -/
lemma exists_coord_ne_zero {n : ℕ} {l : V F n} (hl : l ≠ 0) : ∃ i, l i ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hl
  exact ⟨i, by simpa using hi⟩
/-- Normalize a nonzero coordinate to obtain a vector of pairing one. -/
theorem exists_dot_one {n : ℕ} (l : U F n) : ∃ v : V F n, dot l.val v = 1 := by
  obtain ⟨i, hi⟩ := exists_coord_ne_zero l.property
  refine ⟨Pi.single i (l.val i)⁻¹, ?_⟩
  simpa [dot] using mul_inv_cancel₀ hi
end Refresh
end
section
set_option autoImplicit false
namespace Refresh
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Every field element can be encoded by two nonzero shares when the dimension is at least two. -/
theorem encoding_fiber_nonempty {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (hn : 2 ≤ n) (s : F) : Nonempty (Fiber F n s) := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  let l : V F n := Pi.single i 1
  let r : V F n := Pi.single i s + Pi.single j 1
  have hl : l ≠ 0 := by
    intro h
    have := congrFun h i
    simp [l] at this
  have hr : r ≠ 0 := by
    intro h
    have := congrFun h j
    simp [r, Ne.symm hij] at this
  refine ⟨⟨⟨⟨l, hl⟩, ⟨r, hr⟩⟩, ?_⟩⟩
  change dot l r = s
  simp [dot, l, r, dotProduct, Pi.single_apply, hij]
end Refresh
end
end Encodings

section FiniteProbability

set_option backward.isDefEq.respectTransparency false
section
section
set_option autoImplicit false
open scoped BigOperators
namespace Refresh
/-- A probability mass function on a finite carrier, with nonnegative real weights summing to one. -/

@[ext] structure FiniteDistribution (α : Type*) [Fintype α] where
  weight : α → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  total : ∑ a, weight a = 1
/-- A real weight on each point; unlike a probability distribution, it may be negative and need not have total mass one. -/

abbrev SignedWeight (α : Type*) := α → ℝ
/-- The total absolute mass of a signed weight on a finite set. -/

def variationNorm {α : Type*} [Fintype α] (ν : SignedWeight α) : ℝ :=
  ∑ a, |ν a|
/-- Half the total absolute difference of two probability mass functions; this normalization is the usual finite total variation distance. -/

noncomputable def statisticalDistance {α : Type*} [Fintype α] (P Q : FiniteDistribution α) : ℝ :=
  (1 / 2 : ℝ) * variationNorm (fun a => P.weight a - Q.weight a)
namespace FiniteDistribution
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
/-- The point-mass distribution that assigns probability one to `a` and zero elsewhere. -/
def pure_valid [DecidableEq α] (a : α) :
    (∀ b, 0 ≤ (if b = a then (1 : ℝ) else 0)) ∧
    (∑ b, (if b = a then (1 : ℝ) else 0)) = 1 := by
  constructor
  · intro b
    split_ifs <;> norm_num
  · simp
noncomputable def pure (a : α) : FiniteDistribution α :=
  letI : DecidableEq α := Classical.decEq α
  ⟨(fun b => if b = a then 1 else 0), (pure_valid a).1, (pure_valid a).2⟩
/-- The probability distribution giving every point equal mass `1 / card α`; the finite carrier must be nonempty. -/
def uniform_valid [Nonempty α] :
    (∀ _ : α, 0 ≤ (Fintype.card α : ℝ)⁻¹) ∧
    (∑ _ : α, (Fintype.card α : ℝ)⁻¹) = 1 := by
  constructor
  · intro _
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [hc]
noncomputable def uniform [Nonempty α] : FiniteDistribution α where
  weight _ := (Fintype.card α : ℝ)⁻¹
  nonneg := uniform_valid.1
  total := uniform_valid.2
/-- Sample from `P`, then from the distribution selected by the first sample. -/
def bind_valid (P : FiniteDistribution α) (Q : α → FiniteDistribution β) :
    (∀ b, 0 ≤ ∑ a, P.weight a * (Q a).weight b) ∧
    (∑ b, ∑ a, P.weight a * (Q a).weight b) = 1 := by
  constructor
  · intro b
    exact Finset.sum_nonneg fun a _ => mul_nonneg (P.nonneg a) ((Q a).nonneg b)
  · rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (Q _).total, mul_one]
    exact P.total
noncomputable def bind (P : FiniteDistribution α) (Q : α → FiniteDistribution β) : FiniteDistribution β where
  weight b := ∑ a, P.weight a * (Q a).weight b
  nonneg := (bind_valid P Q).1
  total := (bind_valid P Q).2
/-- Push a probability distribution forward through a deterministic function, summing the masses of all inputs with the same output. -/

noncomputable def map (P : FiniteDistribution α) (f : α → β) : FiniteDistribution β :=
  P.bind (fun a => pure (f a))
/-- Sample from `P` and then from `Q a`, retaining both the first sample and the conditional second sample. Exposed random tapes use this joint distribution. -/
def joint_valid (P : FiniteDistribution α) (Q : α → FiniteDistribution β) :
    (∀ ab : α × β, 0 ≤ P.weight ab.1 * (Q ab.1).weight ab.2) ∧
    (∑ ab : α × β, P.weight ab.1 * (Q ab.1).weight ab.2) = 1 := by
  constructor
  · intro ab
    exact mul_nonneg (P.nonneg _) ((Q _).nonneg _)
  · simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, (Q _).total, mul_one]
    exact P.total
noncomputable def joint (P : FiniteDistribution α) (Q : α → FiniteDistribution β) : FiniteDistribution (α × β) where
  weight ab := P.weight ab.1 * (Q ab.1).weight ab.2
  nonneg := (joint_valid P Q).1
  total := (joint_valid P Q).2
end FiniteDistribution
end Refresh
end
end
section
set_option autoImplicit false
namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Every secret fiber is inhabited in dimensions at least two. -/
def fiber_nonempty (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) (hn : 2 ≤ n) (s : F) : Nonempty (Fiber F n s) :=
  encoding_fiber_nonempty hn s
end Refresh
end
end FiniteProbability

section FiniteExpectations

set_option autoImplicit false
open scoped BigOperators
namespace Refresh
namespace FiniteDistribution
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
/-- The finite probability-weighted sum of a real-valued function. -/
/- Mathematical definition (normal notation): The expectation of f:X → ℝ under P is 𝔼_(x ← P) [f(x)] := ∑ₓ P(x) · f(x). -/
def expect (P : FiniteDistribution α) (f : α → ℝ) : ℝ := ∑ a, P.weight a * f a
end FiniteDistribution
end Refresh
end FiniteExpectations

section FiniteRms

set_option autoImplicit false
open scoped BigOperators
namespace MatrixRefresh
open Refresh
variable {α β J : Type*} [Fintype α] [Fintype β] [Fintype J]
/-- Root mean square with respect to a normalized finite real-weight distribution. This is `sqrt(E[f²])`, not the unnormalized Euclidean norm of the value table. -/
/- Mathematical definition (normal notation): The L₂ norm under a finite distribution P is ‖f‖_(2,P) := √(𝔼_(x ← P) [f(x)²]). This is a probability-weighted norm, possibly a seminorm when P has zero-mass points. -/
noncomputable def rms (P : FiniteDistribution α) (f : α → ℝ) : ℝ :=
  Real.sqrt (P.expect (fun a => f a ^ 2))
end MatrixRefresh
end FiniteRms

/-!
## Counted arithmetic and matrix sampling

Explicit algorithms and field-operation counters for matrices and tensors.
-/

section GaussianArithmetic

set_option backward.isDefEq.respectTransparency false
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular.Gaussian
variable {F : Type*} [Field F] [DecidableEq F]
/-- A computation annotated by an explicit work counter. The arithmetic routines below charge scalar arithmetic and zero tests. Routine vector indexing and allocation are left to conventional implementation analysis. -/

structure Counted (α : Type*) where
  value : α
  operations : ℕ
/-- An actual linear scan: no search oracle or decidable rank proposition. -/

def pivotScan {m : ℕ} (row : Vector F m) : List (Fin m) → Counted (Option (Fin m))
  | [] => ⟨none,0⟩
  | j::js => if row.get j = 0 then
      let tail := pivotScan row js
      ⟨tail.value,1+tail.operations⟩
    else ⟨some j,1⟩
end CircuitCompiler.Rectangular.Gaussian
end
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular.Gaussian
variable {F : Type*} [Field F] [DecidableEq F]
theorem pivotScan_some {m : ℕ} (row : Vector F m) (js : List (Fin m))
    (j : Fin m) (h : (pivotScan row js).value = some j) : row.get j ≠ 0 := by
  induction js with
  | nil => simp [pivotScan] at h
  | cons k ks ih =>
    by_cases hk : row.get k = 0
    · exact ih (by simpa [pivotScan,hk] using h)
    · have hj : k = j := by simpa [pivotScan,hk] using h
      simpa [← hj] using hk
theorem pivotScan_none {m : ℕ} (row : Vector F m) (js : List (Fin m))
    (h : (pivotScan row js).value = none) : ∀ j ∈ js, row.get j = 0 := by
  induction js with
  | nil => simp
  | cons k ks ih =>
    have hk : row.get k = 0 := by
      by_contra hk
      simp [pivotScan,hk] at h
    have ht : (pivotScan row ks).value = none := by simpa [pivotScan,hk] using h
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hk
    · exact ih ht j hj
end CircuitCompiler.Rectangular.Gaussian
end
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular.Gaussian
variable {F : Type*} [Field F] [DecidableEq F]
/-- Scan a row in coordinate order for its first nonzero entry. -/
def findPivot {m : ℕ} (row : Vector F m) : Counted (Option (Fin m)) :=
  pivotScan row (List.finRange m)
end CircuitCompiler.Rectangular.Gaussian
end
end GaussianArithmetic

section MatrixRefreshing

set_option backward.isDefEq.respectTransparency false
section
set_option autoImplicit false
namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- The underlying refreshed row is the original row multiplied by the sampled matrix. -/
@[simp] theorem rowRefresh_val {n : ℕ} (l : U F n) (M : «GL» F n) :
    (rowRefresh l M).val = Matrix.vecMul l.val M.val :=
  rfl
/-- Consecutive refreshes multiply matrices in the paper's right-action order. -/
theorem rowRefresh_mul {n : ℕ} (l : U F n) (M M' : «GL» F n) :
    rowRefresh (rowRefresh l M) M' = rowRefresh l (M * M') := by
  apply Subtype.ext
  simp
/-- Two column refreshes compose in the same matrix-product order as row refreshes, because their inverse actions reverse that order. -/
theorem columnRefresh_mul {n : ℕ} (r : U F n) (M M' : «GL» F n) :
    columnRefresh (columnRefresh r M) M' = columnRefresh r (M * M') := by
  apply Subtype.ext
  simp [columnRefresh, mul_inv_rev]
/-- Refreshing first with `M` and then with `M′` equals one refresh with their product `M * M′`. -/
theorem refresh_mul {n : ℕ} (x : State F n) (M M' : «GL» F n) :
    refresh (refresh x M) M' = refresh x (M * M') := by
  cases x
  simp [refresh, stateLeftShare, stateRightShare, rowRefresh_mul, columnRefresh_mul]
/-- The pairing is exactly preserved, with no probabilistic assumption. -/
@[simp] def refresh_secret {n : ℕ} (x : State F n) (M : «GL» F n) :
    secret (refresh x M) = secret x := by
  change dotProduct (Matrix.vecMul (stateLeftShare x).val M.val)
    (Matrix.mulVec (↑M⁻¹) (stateRightShare x).val) = dotProduct (stateLeftShare x).val (stateRightShare x).val
  rw [← Matrix.dotProduct_mulVec]
  simp
end Refresh
end
section
set_option autoImplicit false
namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Two nonzero vectors admit a functional nonzero on both, even if proportional. -/
theorem exists_common_dot_ne_zero {n : ℕ} (l k : U F n) :
    ∃ v : V F n, dot l.val v ≠ 0 ∧ dot k.val v ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_dot_one l
  obtain ⟨b, hb⟩ := exists_dot_one k
  by_cases hka : dot k.val a ≠ 0
  · exact ⟨a, by simpa [ha] using (one_ne_zero : (1 : F) ≠ 0), hka⟩
  by_cases hlb : dot l.val b ≠ 0
  · exact ⟨b, hlb, by simpa [hb] using (one_ne_zero : (1 : F) ≠ 0)⟩
  have hka0 : dot k.val a = 0 := not_ne_iff.mp hka
  have hlb0 : dot l.val b = 0 := not_ne_iff.mp hlb
  refine ⟨a + b, ?_, ?_⟩
  · simp [dot_add_right, ha, hlb0]
  · simp [dot_add_right, hka0, hb]
/-- Squaring the outer-product matrix gives the same matrix scaled by the inner product of its two defining vectors. -/
theorem rankOne_square {n : ℕ} (a b : V F n) :
    Matrix.vecMulVec a b * Matrix.vecMulVec a b = dot b a • Matrix.vecMulVec a b := by
  rw [Matrix.vecMulVec_mul_vecMulVec]
  ext i j
  simp [Matrix.vecMulVec, dot, smul_eq_mul]
  ring
/-- When `1 + dot b a` is nonzero, the explicit Sherman–Morrison matrix is a right inverse of the rank-one update. -/
theorem rankOne_inverse_right {n : ℕ} (a b : V F n) (h : 1 + dot b a ≠ 0) :
    (1 + Matrix.vecMulVec a b) *
      (1 - (1 + dot b a)⁻¹ • Matrix.vecMulVec a b) = 1 := by
  have hc : (1 + dot b a)⁻¹ + (1 + dot b a)⁻¹ * dot b a = 1 := by
    field_simp
  simp only [mul_sub, add_mul, mul_one, Matrix.mul_smul, one_mul, rankOne_square,
    smul_smul]
  rw [← add_smul, hc, one_smul]
  abel
end Refresh
end
section
set_option autoImplicit false
namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- The Sherman-Morrison rank-one update, with its inverse checked algebraically. -/

def rankOneUnit {n : ℕ} (a b : V F n) (h : 1 + dot b a ≠ 0) : Refresh.«GL» F n where
  val := 1 + Matrix.vecMulVec a b
  inv := 1 - (1 + dot b a)⁻¹ • Matrix.vecMulVec a b
  val_inv := rankOne_inverse_right a b h
  -- A one-sided inverse of a finite square matrix is also a left inverse.
  inv_val := mul_eq_one_comm.mp (rankOne_inverse_right a b h)
end Refresh
end
section
set_option autoImplicit false
namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Multiplication of a row by the rank-one update adds a multiple of `b`, with coefficient given by its pairing with `a`. -/
theorem rankOne_row {n : ℕ} (l a b : V F n) (h : 1 + dot b a ≠ 0) :
    Matrix.vecMul l (rankOneUnit a b h).val = l + dot l a • b := by
  change Matrix.vecMul l (1 + Matrix.vecMulVec a b) = _
  rw [Matrix.vecMul_add, Matrix.vecMul_one, Matrix.vecMul_vecMulVec]
  rfl
/-- Multiplication of a column by the rank-one update adds a multiple of `a`, with coefficient given by its pairing with `b`. -/
/- Mathematical statement (normal notation): If 1+b · a ≠ 0, then the rank-one matrix M := I+a · bᵀ acts on every column r by M · r = r+(b · r) · a. -/
theorem rankOne_column {n : ℕ} (r a b : V F n) (h : 1 + dot b a ≠ 0) :
    Matrix.mulVec (rankOneUnit a b h).val r = r + dot b r • a := by
  change Matrix.mulVec (1 + Matrix.vecMulVec a b) r = _
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
  ext i
  simp [dot, mul_comm]
/-- One invertible rank-one update carries any nonzero row to any other. -/
theorem exists_rowRefresh_eq {n : ℕ} (l k : U F n) :
    ∃ M : Refresh.«GL» F n, rowRefresh l M = k := by
  obtain ⟨a, hla, hka⟩ := exists_common_dot_ne_zero l k
  let a' : V F n := (dot l.val a)⁻¹ • a
  have hla' : dot l.val a' = 1 := by
    rw [dot_smul_right, inv_mul_cancel₀ hla]
  have hka' : dot k.val a' ≠ 0 := by
    rw [dot_smul_right]
    exact mul_ne_zero (inv_ne_zero hla) hka
  have hscalar : 1 + dot (k.val - l.val) a' = dot k.val a' := by
    change 1 + dotProduct (k.val - l.val) a' = _
    rw [sub_dotProduct]
    change 1 + (dot k.val a' - dot l.val a') = _
    rw [hla']
    ring
  refine ⟨rankOneUnit a' (k.val - l.val) (by rw [hscalar]; exact hka'), ?_⟩
  apply Subtype.ext
  rw [rowRefresh_val, rankOne_row, hla', one_smul]
  abel
/-- Inside a pairing fiber, an invertible rank-one update fixes the row and moves the column. -/
theorem exists_refresh_fix_row {n : ℕ} (l r r' : U F n)
    (hs : dot l.val r.val = dot l.val r'.val) :
    ∃ M : Refresh.«GL» F n, rowRefresh l M = l ∧ columnRefresh r M = r' := by
  obtain ⟨b, hr'b, hrb⟩ := exists_common_dot_ne_zero r' r
  let b' : V F n := (dot r'.val b)⁻¹ • b
  have hnew : dot b' r'.val = 1 := by
    rw [dot_comm, dot_smul_right, inv_mul_cancel₀ hr'b]
  have hold : dot b' r.val ≠ 0 := by
    rw [dot_comm, dot_smul_right]
    exact mul_ne_zero (inv_ne_zero hr'b) hrb
  have hscalar : 1 + dot b' (r.val - r'.val) = dot b' r.val := by
    rw [dot_sub_right, hnew]
    ring
  have hlegal : dot l.val (r.val - r'.val) = 0 := by rw [dot_sub_right, hs, sub_self]
  let M := rankOneUnit (r.val - r'.val) b' (by rw [hscalar]; exact hold)
  have hforward : Matrix.mulVec M.val r'.val = r.val := by
    rw [rankOne_column, hnew, one_smul]
    abel
  refine ⟨M, ?_, ?_⟩
  · apply Subtype.ext
    rw [rowRefresh_val, rankOne_row, hlegal, zero_smul, add_zero]
  · apply Subtype.ext
    have hback := congrArg (fun v : V F n => Matrix.mulVec (M⁻¹).val v) hforward
    simpa [columnRefresh] using hback.symm
/-- GL acts transitively on each nonzero-share fiber, in every dimension where it exists. The proof uses two explicit invertible rank-one updates, avoiding a choice of basis extension. -/
theorem refresh_transitive {n : ℕ} (x y : State F n) (hs : secret x = secret y) :
    ∃ M : Refresh.«GL» F n, refresh x M = y := by
  obtain ⟨A, hA⟩ := exists_rowRefresh_eq (stateLeftShare x) (stateLeftShare y)
  have hpair : dot (stateLeftShare y).val (columnRefresh (stateRightShare x) A).val = dot (stateLeftShare y).val (stateRightShare y).val := by
    have hp := refresh_secret x A
    change dot (rowRefresh (stateLeftShare x) A).val (columnRefresh (stateRightShare x) A).val = secret x at hp
    rw [hA, hs] at hp
    exact hp
  obtain ⟨B, hBL, hBR⟩ := exists_refresh_fix_row (stateLeftShare y) (columnRefresh (stateRightShare x) A) (stateRightShare y) hpair
  refine ⟨A * B, ?_⟩
  rw [← refresh_mul]
  apply State.ext
  · change rowRefresh (rowRefresh (stateLeftShare x) A) B = (stateLeftShare y)
    rw [hA, hBL]
  · exact hBR
end Refresh
end
section
section
set_option autoImplicit false
namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end Refresh
end
section
set_option autoImplicit false
namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Certificate that a refreshed state remains in its encoding fiber. -/
abbrev refreshInFiber_mem {n : ℕ} {s : F} (x : Fiber F n s) (M : Refresh.«GL» F n) :
    secret (refresh x.val M) = s := by
  simpa using x.property

/-- Refresh an encoding while retaining its proof that the encoded secret remains in the same fiber. -/
def refreshInFiber {n : ℕ} {s : F} (x : Fiber F n s) (M : Refresh.«GL» F n) : Fiber F n s :=
  ⟨refresh x.val M, refreshInFiber_mem x M⟩
end Refresh
end
end
end MatrixRefreshing

section MatrixSampling

set_option backward.isDefEq.respectTransparency false
section
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler
open Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Tensor of two share vectors, with a concrete finite coordinate ordering. -/

def tensorVector {n : ℕ} (a b : V F n) : V F (n * n) :=
  fun k => a (finProdFinEquiv.symm k).1 * b (finProdFinEquiv.symm k).2
end CircuitCompiler
end
section
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler
open Refresh
variable {F : Type*} [Field F]
@[simp] theorem tensorVector_pair {n : ℕ} (a b : V F n) (i j : Fin n) :
    tensorVector a b (finProdFinEquiv (i, j)) = a i * b j := by
  simp [tensorVector]
/-- A tensor of two nonzero field-valued vectors is nonzero. -/
def tensorVector_ne_zero {n : ℕ} (a b : U F n) :
    tensorVector a.val b.val ≠ 0 := by
  classical
  intro h
  obtain ⟨i, hi⟩ : ∃ i, a.val i ≠ 0 := by
    by_contra he
    apply a.property
    funext i
    simpa using not_exists.mp he i
  obtain ⟨j, hj⟩ : ∃ j, b.val j ≠ 0 := by
    by_contra he
    apply b.property
    funext j
    simpa using not_exists.mp he j
  have hz := congrFun h (finProdFinEquiv (i, j))
  exact mul_ne_zero hi hj (by simpa using hz)
end CircuitCompiler
end
section
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Sampling
open Refresh
variable {α β : Type*} [Fintype α] [Fintype β]
/-- The probability that one proposal passes the specified acceptance test. -/
def acceptance (P : FiniteDistribution α) (accept : α → Bool) : ℝ :=
  ∑ a, if accept a then P.weight a else 0
end CircuitCompiler.Sampling
end
section
section
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Sampling
open Refresh
variable {α β : Type*} [Fintype α] [Fintype β]
def acceptance_le_one (P : FiniteDistribution α) (accept : α → Bool) :
    acceptance P accept ≤ 1 := by
  rw [← P.total]
  apply Finset.sum_le_sum
  intro a _
  split_ifs
  · rfl
  · exact P.nonneg a
end CircuitCompiler.Sampling
end
section
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Sampling
open Refresh
variable {α β : Type*} [Fintype α] [Fintype β]
universe u
/-- A finite sequence of proposals, represented without any probabilistic oracle. -/

def Tape (α : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => α × Tape α n
instance tapeFintype : (n : ℕ) → Fintype (Tape α n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => @instFintypeProd α (Tape α n) _ (tapeFintype n)
end CircuitCompiler.Sampling
end
section
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
variable {F : Type*} [Field F]
/-- Append one constant coordinate to the tensor product of two nonzero shares. -/
abbrev augmentedShare_ne_zero {n : ℕ} (c : F) (x : U F n × U F n) :
    Fin.append (tensorVector x.1.val x.2.val) (fun _ : Fin 1 => c) ≠ 0 := by
  intro h
  apply tensorVector_ne_zero x.1 x.2
  funext i
  simpa using congrFun h (Fin.castAdd 1 i)

def augmentedShare {n : ℕ} (c : F) (x : U F n × U F n) : U F (n*n+1) :=
  ⟨Fin.append (tensorVector x.1.val x.2.val) (fun _ : Fin 1 => c),
    augmentedShare_ne_zero c x⟩
end CircuitCompiler.Rectangular
end
end
section
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Sampling
open Refresh
variable {α : Type*} [Fintype α] [Nonempty α]
section Matrix
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- The acceptance test uses only the determinant of the proposed matrix. -/

def invertibleTest {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : Bool :=
  decide (M.det ≠ 0)
/-- Units and raw matrices with nonzero determinant are exactly the same choices. -/
def invertibleTest_unit {n : ℕ} (M : Refresh.«GL» F n) :
    invertibleTest M.val = true := by
  simp only [invertibleTest, decide_eq_true_eq]
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det M.val).mp M.isUnit)

def invertibleTest_isUnit {n : ℕ}
    (M : {M : Matrix (Fin n) (Fin n) F // invertibleTest M = true}) :
    IsUnit M.val := by
  apply (Matrix.isUnit_iff_isUnit_det M.val).mpr
  exact isUnit_iff_ne_zero.mpr (by simpa [invertibleTest] using M.property)

def invertibleEquiv_toFun {n : ℕ} (M : Refresh.«GL» F n) :
    {M : Matrix (Fin n) (Fin n) F // invertibleTest M = true} :=
  ⟨M.val, invertibleTest_unit M⟩

noncomputable def invertibleEquiv_invFun {n : ℕ}
    (M : {M : Matrix (Fin n) (Fin n) F // invertibleTest M = true}) :
    Refresh.«GL» F n :=
  (invertibleTest_isUnit M).unit

def invertibleEquiv_laws (n : ℕ) :
    (∀ M : Refresh.«GL» F n, invertibleEquiv_invFun (invertibleEquiv_toFun M) = M) ∧
    (∀ M : {M : Matrix (Fin n) (Fin n) F // invertibleTest M = true},
      invertibleEquiv_toFun (invertibleEquiv_invFun M) = M) := by
  constructor
  · intro M
    exact Units.ext (IsUnit.unit_spec _)
  · intro M
    apply Subtype.ext
    simp only [invertibleEquiv_toFun, invertibleEquiv_invFun, IsUnit.unit_spec]

noncomputable def invertibleEquiv (n : ℕ) :
    Refresh.«GL» F n ≃ {M : Matrix (Fin n) (Fin n) F // invertibleTest M = true} where
  toFun := invertibleEquiv_toFun
  invFun := invertibleEquiv_invFun
  left_inv := (invertibleEquiv_laws n).1
  right_inv := (invertibleEquiv_laws n).2
end Matrix
end CircuitCompiler.Sampling
end
end MatrixSampling

/-!
## Execution and local comparison interfaces

Answer histories, causal runners, scoped networks, and local estimates.
-/

section ChronologicalPrograms

set_option backward.isDefEq.respectTransparency false
section
section
set_option autoImplicit false
open scoped BigOperators
universe u
namespace CircuitCompiler.Composition
open Refresh
/-- A fixed-length answer history, represented recursively for summation. -/

def Answers (A : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => A × Answers A n
/-- The finite enumeration used when summing over answer histories. -/
instance answersFintype (A : Type*) [Fintype A] : (n : ℕ) → Fintype (Answers A n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => @instFintypeProd A (Answers A n) _ (answersFintype A n)
end CircuitCompiler.Composition
end
section
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Composition
open Refresh
universe u
/-- Recursive answers and a chronological finite vector carry the same data. -/
def answersToVector (A : Type u) : (n : ℕ) → Answers A n → Fin n → A
  | 0, _ => Fin.elim0
  | n + 1, h => Fin.cons h.1 (answersToVector A n h.2)

def vectorToAnswers (A : Type u) : (n : ℕ) → (Fin n → A) → Answers A n
  | 0, _ => PUnit.unit
  | n + 1, h => (h 0, vectorToAnswers A n (Fin.tail h))

def answersEquiv_laws (A : Type u) : (n : ℕ) →
    (∀ h : Answers A n, vectorToAnswers A n (answersToVector A n h) = h) ∧
    (∀ h : Fin n → A, answersToVector A n (vectorToAnswers A n h) = h)
  | 0 => by
      constructor
      · intro h
        cases h
        rfl
      · intro h
        funext i
        exact Fin.elim0 i
  | n + 1 => by
      obtain ⟨hleft, hright⟩ := answersEquiv_laws A n
      constructor
      · intro h
        rcases h with ⟨head, tail⟩
        simp [answersToVector, vectorToAnswers, hleft]
      · intro h
        funext i
        cases i using Fin.cases with
        | zero => simp [answersToVector, vectorToAnswers]
        | succ i => simpa [answersToVector, vectorToAnswers, Fin.tail] using congrFun (hright (Fin.tail h)) i

def answersEquiv (A : Type u) (n : ℕ) : Answers A n ≃ (Fin n → A) where
  toFun := answersToVector A n
  invFun := vectorToAnswers A n
  left_inv := (answersEquiv_laws A n).1
  right_inv := (answersEquiv_laws A n).2
end CircuitCompiler.Composition
end
section
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Composition.TopologicalExecution
open Refresh
universe u v
/-- The current encoded wire array together with its complete chronological answer history. -/
abbrev RunState (E : Type u) (A : Type v) (inputs gates : ℕ) :=
  (Fin (inputs + gates) → E) × (Fin gates → A)
variable {E : Type u} {A : Type v} [Fintype E] [Fintype A] {inputs T : ℕ}
/-- Freshly allocated outputs and new answers are appended to their respective vectors; no existing wire encoding is resampled. -/
def appendState (pair : RunState E A inputs T × (E × A)) : RunState E A inputs (T + 1) :=
  (Fin.snoc pair.1.1 pair.2.1, Fin.snoc pair.1.2 pair.2.2)

def splitState (state : RunState E A inputs (T + 1)) : RunState E A inputs T × (E × A) :=
  ((Fin.init state.1, Fin.init state.2),
    (state.1 (Fin.last (inputs + T)), state.2 (Fin.last T)))

def appendEquiv_laws :
    (∀ pair : RunState E A inputs T × (E × A), splitState (appendState pair) = pair) ∧
    (∀ state : RunState E A inputs (T + 1), appendState (splitState state) = state) := by
  constructor
  · rintro ⟨⟨encoding, history⟩, output, answer⟩
    simp [appendState, splitState]
  · rintro ⟨encoding, history⟩
    simp [appendState, splitState]

def appendEquiv : RunState E A inputs T × (E × A) ≃ RunState E A inputs (T + 1) where
  toFun := appendState
  invFun := splitState
  left_inv := appendEquiv_laws.1
  right_inv := appendEquiv_laws.2
/-- A genuine sequential runner over growing prefixes. Its gate answer table may adapt to the entire previous answer vector. -/

inductive Runner (E : Type u) (A : Type v) [Fintype E] [Fintype A] (inputs : ℕ) : ℕ → Type (max u v) where
  | nil : Runner E A inputs 0
  | snoc {T : ℕ} (prior : Runner E A inputs T)
      (gate : RunState E A inputs T → FiniteDistribution (E × A)) : Runner E A inputs (T + 1)
/-- Execute the chronological runner from an initial encoding distribution, retaining all allocated wires and answers. -/
noncomputable def Runner.execute (initial : FiniteDistribution (Fin inputs → E)) :
    {T : ℕ} → Runner E A inputs T → FiniteDistribution (RunState E A inputs T)
  | 0, .nil => initial.map (fun encoding => (encoding, Fin.elim0))
  | _ + 1, .snoc prior gate => ((prior.execute initial).joint gate).map appendState
end CircuitCompiler.Composition.TopologicalExecution
end
end
section
set_option autoImplicit false
namespace CircuitCompiler
/-- A source operation is either multiplication or a constant minus a product; over bits these are AND and NAND. -/
inductive GateKind (F : Type*) where
  | product
  | complement (constant : F)
/-- A binary gate names its operation and its two predecessor wire addresses. -/
structure Gate (F : Type*) (wires : ℕ) where
  kind : GateKind F
  left : Fin wires
  right : Fin wires
end CircuitCompiler
end
section
section
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler
open Refresh _root_.CircuitCompiler.Composition _root_.CircuitCompiler.Composition.TopologicalExecution
variable {F Alpha Beta : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype Alpha] [Fintype Beta] {n t inputs T : ℕ}
/-- The public affine postprocessing constants for the stated gate basis. -/

def GateKind.affineConstant : GateKind F → F
  | .product => 0
  | .complement c => c
end CircuitCompiler
end
end
end ChronologicalPrograms

section FactorEnergies

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace CircuitCompiler.AveragedEnergyComparison
open Refresh MatrixRefresh
/-- A finite real product representation, with its energies left explicit. -/
/-
Mathematical definition (normal notation): A product representation of F:X × Y → ℝ consists of a finite index set and real functions aⱼ,bⱼ such that

F(x,y) = ∑ⱼ aⱼ(x) · bⱼ(y) for every (x,y).

No orthogonality, positivity, or minimality is required.
-/
structure Factors {X Y : Type*} (f : X → Y → ℝ) where
  rank : ℕ
  left : X → Fin rank → ℝ
  right : Y → Fin rank → ℝ
  reconstruct : ∀ x y, f x y = ∑ j, left x j * right y j
namespace Factors
variable {X Y X' Y' : Type*} {f g : X → Y → ℝ}
def leftEnergy (a : Factors f) (x : X) : ℝ := ∑ j, a.left x j ^ 2
def rightEnergy (a : Factors f) (y : Y) : ℝ := ∑ j, a.right y j ^ 2
end Factors
end CircuitCompiler.AveragedEnergyComparison
end FactorEnergies

section ScopedNetwork

set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Composition
open Refresh
variable {W E A : Type*} [Fintype W] [DecidableEq W] [Fintype E] [Fintype A]
  {T : ℕ}
/-- A function inspects only the wire encodings in its declared scope. -/
/-
Mathematical definition (normal notation): For scope ∈ Finset(W); f ∈ (W → E) → ℝ, define

Scoped(scope, f) := ∀ first, second, (∀ w ∈ scope, first(w) = second(w)) → f(first) = f(second).
-/
def Scoped (scope : Finset W) (f : (W → E) → ℝ) : Prop :=
  ∀ first second, (∀ w ∈ scope, first w = second w) → f first = f second
end CircuitCompiler.Composition
end ScopedNetwork

section NetworkExecution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace CircuitCompiler.Composition
open Refresh
/-- Independently sample one encoding for every distinct wire. -/
/- Mathematical definition (normal notation): For one probability distribution μ_w per wire, define their product distribution on complete encoding assignments by Pr[X = x] = ∏_w μ_w(x_w). Thus all wire encodings are independent. -/
def independentDistribution_valid {W E : Type*} [Fintype W] [DecidableEq W] [Fintype E]
    (wireDistribution : W → FiniteDistribution E) :
    (∀ encoding : W → E, 0 ≤ ∏ w, (wireDistribution w).weight (encoding w)) ∧
    (∑ encoding : W → E, ∏ w, (wireDistribution w).weight (encoding w)) = 1 := by
  constructor
  · intro encoding
    exact Finset.prod_nonneg (fun w _ => (wireDistribution w).nonneg _)
  · classical
    rw [← Fintype.prod_sum]
    simp only [(wireDistribution _).total, Finset.prod_const_one]

noncomputable def independentDistribution {W E : Type*} [Fintype W] [DecidableEq W] [Fintype E]
    (wireDistribution : W → FiniteDistribution E) : FiniteDistribution (W → E) where
  weight encoding := ∏ w, (wireDistribution w).weight (encoding w)
  nonneg := (independentDistribution_valid wireDistribution).1
  total := (independentDistribution_valid wireDistribution).2
/-- Group left coordinates and right coordinates after independently sampling whole wire encodings. Their joint distribution retains each wire's correlation. -/
/-
Mathematical definition (normal notation): For W,E,D a set; wireDistribution ∈ W → 𝒟(E), assume W is finite; E is finite; D is finite; E → D. define

groupedDistribution(wireDistribution) := (((encoding ↦ ((w ↦ left(encoding(w))), (w ↦ right(encoding(w))))))_*independentDistribution(wireDistribution)) .
-/
noncomputable def groupedDistribution {W E D : Type*} [Fintype W] [DecidableEq W]
    [Fintype E] [Fintype D]
    (wireDistribution : W → FiniteDistribution E) (left right : E → D) :
    FiniteDistribution ((W → D) × (W → D)) :=
  (independentDistribution wireDistribution).map (fun encoding =>
    (fun w => left (encoding w), fun w => right (encoding w)))
end CircuitCompiler.Composition
end NetworkExecution

section ScopedSplit

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace CircuitCompiler.AveragedEnergyComparison
open Refresh MatrixRefresh _root_.CircuitCompiler.Composition
noncomputable section
variable {W E A : Type*} [Fintype W] [DecidableEq W] [Fintype E] [Fintype A]
  {T : ℕ}
structure ScopedProbabilities (scope : Fin T → Finset W) where
  prob : Fin T → List A → (W → E) → A → ℝ
  nonneg : ∀ i h e a, 0 ≤ prob i h e a
  total_le : ∀ i h e, (∑ a, prob i h e a) ≤ 1
  locality : ∀ i h a, Scoped (scope i) (fun e => prob i h e a)
end
end CircuitCompiler.AveragedEnergyComparison
end ScopedSplit

section CommonLocalEstimates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace CircuitCompiler.AveragedEnergyComparison
open Refresh MatrixRefresh
noncomputable section
structure GateLocalEstimates {X S : Type*} [Fintype X] [Nonempty X]
    (laws : S → FiniteDistribution (X × X)) (valid : S → Prop)
    (original : S → X → X → ℝ) (β ε : ℝ) where
  approximation : X → X → ℝ
  factors : Factors approximation
  left_max : ∀ x, factors.leftEnergy x ≤ 2 / β
  right_max : ∀ x, factors.rightEnergy x ≤ 2 / β
  left_mean : (FiniteDistribution.uniform : FiniteDistribution X).expect factors.leftEnergy ≤ 8
  right_mean : (FiniteDistribution.uniform : FiniteDistribution X).expect factors.rightEnergy ≤ 8
  all_labels_rms : ∀ s, rms (laws s) (fun xy => approximation xy.1 xy.2) ≤ 12
  valid_error_rms : ∀ s, valid s →
    rms (laws s) (fun xy => original s xy.1 xy.2 - approximation xy.1 xy.2) ≤ ε
end
end CircuitCompiler.AveragedEnergyComparison
end CommonLocalEstimates

/-!
## Physical sampling and gate execution

Acceptance tests, rectangular constructions, rejection tapes, and counted runs.
-/

section AcceptanceSupport

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical

namespace CircuitCompiler.Sampling.DefinitionSupport
open Refresh

/-- Positive mass at one accepted proposal implies positive acceptance. -/
def acceptance_positive_of_witness {α : Type*} [Fintype α]
    (P : FiniteDistribution α) (accept : α → Bool) (a : α)
    (hweight : 0 < P.weight a) (haccept : accept a = true) :
    0 < acceptance P accept := by
  unfold acceptance
  have ha : 0 < (if accept a then P.weight a else 0) := by simpa [haccept] using hweight
  exact ha.trans_le (Finset.single_le_sum (f := fun b => if accept b then P.weight b else 0) (fun b _ => by
    split_ifs
    · exact P.nonneg b
    · exact le_rfl) (Finset.mem_univ a))

/-- A finite nonempty uniform law assigns positive mass to every point. -/
def uniform_positive {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    0 < (FiniteDistribution.uniform : FiniteDistribution α).weight a := by
  exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
end CircuitCompiler.Sampling.DefinitionSupport
end
end AcceptanceSupport

section CompilerParameters

section CompilerPublicModel
set_option autoImplicit false
noncomputable section
namespace Compiler
/-- Compatibility names for proof modules that predate the shared definitions. -/
abbrev Bit := Refreshing.Bit
abbrev Share (n : ℕ) := Refreshing.Share n
abbrev LeakageOutput (leakage : ℕ) := Refreshing.LeakageOutput leakage
/-- A complete gate answer contains the two λᴹ-bit matrix-phase answers and the two λˢ-bit shortening answers. Its alphabet has 2^(2(λᴹ + λˢ)) elements. -/
abbrev Answer (matrixLeakage shorteningLeakage : ℕ) :=
  Refreshing.Answer matrixLeakage × Refreshing.Answer shorteningLeakage
/-- The rectangular sampler writes the long dimension m = n² + 1 as n + t, with t = n² + 1 − n. This is nonnegative for every natural n. -/
def shorteningExtra (n : ℕ) : ℕ := n * n + 1 - n
/-- The two descriptions of the long dimension coincide: n² + 1 = n + (n² + 1 − n). -/
def longDimension (n : ℕ) : n * n + 1 = n + shorteningExtra n := by
  have h := Nat.le_mul_self n
  unfold shorteningExtra
  omega
/-- Statistical distance is δ(P,Q) = ½ · ∑ᵥ |P(v) − Q(v)| on the finite complete-view space. The sum is not divided by its cardinality. -/
abbrev statisticalDistance {α : Type*} [Fintype α]
    (P Q : Refresh.FiniteDistribution α) : ℝ := Refresh.statisticalDistance P Q
/-- The number of nonzero length-n shares is q(n) = 2ⁿ − 1. -/
def q (n : ℕ) : ℕ := 2 ^ n - 1
/-- The complete-answer alphabet has size K(λ) = 2^(2λ), where λ = λᴹ + λˢ is each party's total leakage budget per ordinary gate. -/
def K (leakage : ℕ) : ℕ := 2 ^ (2 * leakage)
end Compiler
end
end CompilerPublicModel
end CompilerParameters

section RectangularAlgebra

set_option backward.isDefEq.respectTransparency false
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Full row rank, in the equivalent right-inverse formulation. -/

def FullRowRank {n m : ℕ} (H : Matrix (Fin n) (Fin m) F) : Prop :=
  ∃ J : Matrix (Fin m) (Fin n) F, H * J = 1
/-- The finite carrier of rectangular matrices with full row rank. -/
abbrev FullRank (F : Type*) [Field F] (n m : ℕ) :=
  {H : Matrix (Fin n) (Fin m) F // FullRowRank H}
end
end CircuitCompiler.Rectangular
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Right multiplication by an invertible square matrix preserves full row rank. -/
theorem fullRowRank_right {n m : ℕ} (H : FullRank F n m) (M : Refresh.«GL» F m) :
    FullRowRank (H.val * M.val) := by
  obtain ⟨J,hJ⟩ := H.property
  refine ⟨(M⁻¹).val * J, ?_⟩
  calc
    _ = H.val * (M.val * (M⁻¹).val) * J := by simp only [Matrix.mul_assoc]
    _ = 1 := by simpa using hJ
end
end CircuitCompiler.Rectangular
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- The sampler's finite choices after the left row has been selected. -/

abbrev Completion {n m : ℕ} (u : U F m) (A : U F n) :=
  {H : FullRank F n m // Matrix.vecMul A.val H.val = u.val}
/-- A complete first-attempt outcome, before testing the right output. -/

abbrev Attempt {n m : ℕ} (u : U F m) :=
  {p : U F n × FullRank F n m // Matrix.vecMul p.1.val p.2.val = u.val}
/-- The right output is allowed to be zero before the retry test. -/

def rightOutput {n m : ℕ} {u : U F m} (v : U F m) (p : Attempt (n := n) u) : V F n :=
  Matrix.mulVec p.val.2.val v.val
/-- A shortening attempt whose right output is nonzero. -/
abbrev Success {n m : ℕ} (u v : U F m) :=
  {p : Attempt (n := n) u // rightOutput v p ≠ 0}
/-- Coordinate projection onto the first `n` coordinates. -/

def projection (n t : ℕ) : Matrix (Fin n) (Fin (n+t)) F :=
  fun i j => if j = Fin.castAdd t i then 1 else 0
end
end CircuitCompiler.Rectangular
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
@[simp] theorem projection_mulVec {n t : ℕ} (v : V F (n+t)) (i : Fin n) :
    Matrix.mulVec (projection (F := F) n t) v i = v (Fin.castAdd t i) := by
  simp [projection, Matrix.mulVec, dotProduct]
@[simp] theorem projection_transpose_mulVec {n t : ℕ} (v : V F n) :
    Matrix.mulVec (projection (F := F) n t).transpose v = Fin.append v 0 := by
  ext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [projection, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  · have h (x : Fin n) : Fin.natAdd n i ≠ Fin.castAdd t x := by
      intro he
      have := congrArg Fin.val he
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    simp [projection, Matrix.mulVec, dotProduct, Matrix.transpose_apply, h]
@[simp] theorem projection_vecMul {n t : ℕ} (v : V F n) :
    Matrix.vecMul v (projection (F := F) n t) = Fin.append v 0 := by
  rw [← Matrix.mulVec_transpose]
  exact projection_transpose_mulVec v
/-- Projection has the coordinate inclusion as a right inverse. -/
theorem projection_fullRowRank (n t : ℕ) : FullRowRank (projection (F := F) n t) := by
  refine ⟨(projection n t).transpose, ?_⟩
  ext i j
  simp [projection, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, eq_comm]
end
end CircuitCompiler.Rectangular
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Append zero tail coordinates to a nonzero share. -/
def embed_ne_zero {n t : ℕ} (a : U F n) : (Fin.append a.val (0 : Fin t → F)) ≠ 0 := by
  intro h
  apply a.property
  ext i
  have := congrFun h (Fin.castAdd t i)
  simpa using this

def embed {n t : ℕ} (a : U F n) : U F (n+t) :=
  ⟨Fin.append a.val 0, embed_ne_zero a⟩
end
end CircuitCompiler.Rectangular
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
@[simp] theorem embed_dot {n t : ℕ} (a b : U F n) :
    dot (embed (t := t) a).val (embed (t := t) b).val = dot a.val b.val := by
  simp [embed, dot, dotProduct, Fin.sum_univ_add]
/-- Every chosen nonzero short row admits a full-rank completion. -/
abbrev completion_nonempty {n t : ℕ} (u : U F (n+t)) (a : U F n) :
    Nonempty (Completion u a) := by
  obtain ⟨M,hM⟩ := exists_rowRefresh_eq (embed (t := t) a) u
  let P : FullRank F n (n+t) := ⟨projection n t, projection_fullRowRank n t⟩
  refine ⟨⟨⟨P.val * M.val, fullRowRank_right P M⟩, ?_⟩⟩
  change Matrix.vecMul a.val (projection n t * M.val) = u.val
  rw [← Matrix.vecMul_vecMul, projection_vecMul]
  exact congrArg Subtype.val hM
end
end CircuitCompiler.Rectangular
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- A short state can be embedded into the long space without changing its bit. -/

def embedState {n t : ℕ} (x : State F n) : State F (n+t) :=
  ⟨embed x.L, embed x.R⟩
end
end CircuitCompiler.Rectangular
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
@[simp] theorem embedState_secret {n t : ℕ} (x : State F n) :
    secret (embedState (t := t) x) = secret x :=
  embed_dot x.L x.R
/-- There is an accepted attempt for every fixed nonzero long input pair. -/
theorem success_nonempty {n t : ℕ} (hn : 2 ≤ n) (u v : U F (n+t)) :
    Nonempty (Success (n := n) u v) := by
  letI := fiber_nonempty F n hn (dot u.val v.val)
  let y : Fiber F n (dot u.val v.val) := Classical.choice inferInstance
  have hy : secret (embedState (t := t) y.val) = secret (State.mk u v) := by
    rw [embedState_secret]
    exact y.property
  obtain ⟨M,hM⟩ := refresh_transitive (embedState (t := t) y.val) ⟨u,v⟩ hy
  let P : FullRank F n (n+t) := ⟨projection n t, projection_fullRowRank n t⟩
  have hrow : Matrix.vecMul (Fin.append y.val.L.val 0) M.val = u.val :=
    congrArg (fun x : State F (n+t) => x.L.val) hM
  have hcol : Matrix.mulVec M.val v.val = Fin.append y.val.R.val 0 := by
    have h := congrArg (fun x : State F (n+t) => Matrix.mulVec M.val x.R.val) hM
    simpa [refresh, columnRefresh, embedState, embed, Matrix.mulVec_mulVec, stateRightShare] using h.symm
  let p : Attempt (n := n) u := ⟨(y.val.L, ⟨P.val * M.val, fullRowRank_right P M⟩), by
    change Matrix.vecMul y.val.L.val (projection n t * M.val) = u.val
    rw [← Matrix.vecMul_vecMul, projection_vecMul]
    exact hrow⟩
  have hp : rightOutput v p = y.val.R.val := by
    change Matrix.mulVec (projection n t * M.val) v.val = y.val.R.val
    rw [← Matrix.mulVec_mulVec, hcol]
    ext i
    simp
  exact ⟨⟨p, by rw [hp]; exact y.val.R.property⟩⟩
end
end CircuitCompiler.Rectangular
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- The subtype and sequential-sampling descriptions of an attempt agree. -/
def attemptToSigma {n m : ℕ} (u : U F m) (p : Attempt (n := n) u) :
    ((a : U F n) × Completion u a) :=
  ⟨p.val.1, ⟨p.val.2, p.property⟩⟩

def sigmaToAttempt {n m : ℕ} (u : U F m)
    (p : ((a : U F n) × Completion u a)) : Attempt (n := n) u :=
  ⟨(p.1, p.2.val), p.2.property⟩

def attemptSigmaEquiv_laws {n m : ℕ} (u : U F m) :
    (∀ p : Attempt (n := n) u, sigmaToAttempt u (attemptToSigma u p) = p) ∧
    (∀ p : ((a : U F n) × Completion u a), attemptToSigma u (sigmaToAttempt u p) = p) := by
  constructor
  · intro p
    rfl
  · intro p
    rfl

def attemptSigmaEquiv {n m : ℕ} (u : U F m) :
    Attempt (n := n) u ≃ ((a : U F n) × Completion u a) where
  toFun := attemptToSigma u
  invFun := sigmaToAttempt u
  left_inv := (attemptSigmaEquiv_laws u).1
  right_inv := (attemptSigmaEquiv_laws u).2
end
end CircuitCompiler.Rectangular
end
end RectangularAlgebra

section StoppedSampling

set_option backward.isDefEq.respectTransparency false
section
namespace ProbabilityTheory
/-- The probability of exactly n rejections before success with probability p is (1 − p)ⁿp. -/
noncomputable def geometricPMFReal (p : ℝ) (n : ℕ) : ℝ := (1 - p) ^ n * p
/-- For 0 < p ≤ 1, the geometric rejection-count probabilities sum to one. -/
def geometricPMFRealSum {p : ℝ} (hp_pos : 0 < p) (hp_le_one : p ≤ 1) :
    HasSum (fun n ↦ geometricPMFReal p n) 1 := by
  unfold geometricPMFReal
  have h := hasSum_geometric_of_lt_one (sub_nonneg.mpr hp_le_one) (sub_lt_self 1 hp_pos)
  apply (hasSum_mul_right_iff hp_pos.ne').mpr at h
  simp only [sub_sub_cancel] at h
  rw [inv_mul_eq_div, div_self hp_pos.ne'] at h
  exact h
/-- Geometric rejection-count probabilities are nonnegative for 0 < p ≤ 1. -/
def geometricPMFReal_nonneg {p : ℝ} {n : ℕ} (hp_pos : 0 < p) (hp_le_one : p ≤ 1) :
    0 ≤ geometricPMFReal p n := by
  unfold geometricPMFReal
  exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hp_le_one) n) hp_pos.le
/-- The probability distribution of the number of failed independent proposals before success. -/
def geometricPMF_normalized {p : ℝ} (hp_pos : 0 < p) (hp_le_one : p ≤ 1) :
    HasSum (fun n : ℕ => ENNReal.ofReal (geometricPMFReal p n)) 1 := by
  apply ENNReal.hasSum_coe.mpr
  simpa only [Real.toNNReal_one] using
    (geometricPMFRealSum hp_pos hp_le_one).toNNReal
      (fun n ↦ geometricPMFReal_nonneg hp_pos hp_le_one)

noncomputable def geometricPMF {p : ℝ} (hp_pos : 0 < p) (hp_le_one : p ≤ 1) : PMF ℕ :=
  ⟨fun n ↦ ENNReal.ofReal (geometricPMFReal p n), geometricPMF_normalized hp_pos hp_le_one⟩
end ProbabilityTheory
end
section
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
/-- A finite observation of a countable experiment is an ordinary finite distribution. -/

def toFinite_total (P : PMF β) : (∑ b, (P b).toReal) = 1 := by
  rw [← ENNReal.toReal_sum (fun b _ => P.apply_ne_top b)]
  rw [← (tsum_fintype (L := SummationFilter.unconditional β) (fun b => P b)), P.tsum_coe]
  simp

def toFinite (P : PMF β) : FiniteDistribution β where
  weight b := (P b).toReal
  nonneg b := ENNReal.toReal_nonneg
  total := toFinite_total P
end
end CircuitCompiler.Sampling.Unbounded
end
section
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
/-- The rejected prefix is followed by one final proposal. The natural-number index is its unbounded length; it is not a public output of the protocol. -/

abbrev StoppedTape (α : Type*) := Σ k : ℕ, Tape α k × α
/-- The probability of a particular failed prefix under independent proposals. -/

def prefixWeight (P : FiniteDistribution α) (accept : α → Bool) :
    (k : ℕ) → Tape α k → ℝ
  | 0, _ => 1
  | k + 1, t => (if accept t.1 then 0 else P.weight t.1) * prefixWeight P accept k t.2
/-- Exact independent-proposal mass of a stopped tape. -/

def traceWeight (P : FiniteDistribution α) (accept : α → Bool) (t : StoppedTape α) : ℝ :=
  prefixWeight P accept t.1 t.2.1 * (if accept t.2.2 then P.weight t.2.2 else 0)
end
end CircuitCompiler.Sampling.Unbounded
end
section
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
theorem prefixWeight_nonneg (P : FiniteDistribution α) (accept : α → Bool)
    (k : ℕ) (t : Tape α k) : 0 ≤ prefixWeight P accept k t := by
  induction k with
  | zero => exact zero_le_one
  | succ k ih =>
    apply mul_nonneg _ (ih t.2)
    split_ifs
    · exact le_refl 0
    · exact P.nonneg _
def traceWeight_nonneg (P : FiniteDistribution α) (accept : α → Bool)
    (t : StoppedTape α) : 0 ≤ traceWeight P accept t := by
  apply mul_nonneg (prefixWeight_nonneg P accept _ _)
  split_ifs
  · exact P.nonneg _
  · exact le_refl 0
theorem rejection_sum (P : FiniteDistribution α) (accept : α → Bool) :
    (∑ a, if accept a then 0 else P.weight a) = 1 - acceptance P accept := by
  have h : ∀ a, (if accept a then 0 else P.weight a) =
      P.weight a - (if accept a then P.weight a else 0) := by
    intro a
    cases accept a <;> simp
  simp_rw [h]
  rw [Finset.sum_sub_distrib, P.total]
  rfl
theorem prefixWeight_sum (P : FiniteDistribution α) (accept : α → Bool) (k : ℕ) :
    (∑ t : Tape α k, prefixWeight P accept k t) = (1 - acceptance P accept) ^ k := by
  induction k with
  | zero =>
    change (∑ _ : PUnit, (1 : ℝ)) = 1
    simp
  | succ k ih =>
    change (∑ t : α × Tape α k,
      (if accept t.1 then 0 else P.weight t.1) * prefixWeight P accept k t.2) = _
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ih]
    rw [← Finset.sum_mul, rejection_sum, pow_succ]
    ring
def traceWeight_sum (P : FiniteDistribution α) (accept : α → Bool) (k : ℕ) :
    (∑ t : Tape α k × α, traceWeight P accept ⟨k, t⟩) =
      ProbabilityTheory.geometricPMFReal (acceptance P accept) k := by
  simp_rw [traceWeight, Fintype.sum_prod_type, ← Finset.mul_sum]
  rw [← Finset.sum_mul, prefixWeight_sum]
  rfl
end
end CircuitCompiler.Sampling.Unbounded
end
section
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
/-- The unbounded physical retry distribution. All its mass is on finite stopped tapes because the acceptance probability is strictly positive. -/

abbrev distribution_normalized (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) :
    HasSum (fun t : StoppedTape α => ENNReal.ofReal (traceWeight P accept t)) 1 := by
  apply ENNReal.summable.hasSum_iff.mpr
  change (∑' t : Σ k : ℕ, Tape α k × α, ENNReal.ofReal (traceWeight P accept t)) = 1
  rw [ENNReal.tsum_sigma']
  simp_rw [tsum_fintype,
    ← ENNReal.ofReal_sum_of_nonneg (fun t _ => traceWeight_nonneg P accept _),
    traceWeight_sum]
  exact (ProbabilityTheory.geometricPMF hp (acceptance_le_one P accept)).tsum_coe

def distribution (P : FiniteDistribution α) (accept : α → Bool) (hp : 0 < acceptance P accept) :
    PMF (StoppedTape α) :=
  ⟨fun t => ENNReal.ofReal (traceWeight P accept t), distribution_normalized P accept hp⟩
end
end CircuitCompiler.Sampling.Unbounded
end
section
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
/-- Arbitrary finite-valued leakage on the entire stopped tape. -/

def observe (P : FiniteDistribution α) (accept : α → Bool) (hp : 0 < acceptance P accept)
    (f : StoppedTape α → β) : FiniteDistribution β := toFinite ((distribution P accept hp).map f)
end
end CircuitCompiler.Sampling.Unbounded
end
section
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
/-- A finite rejected-proposal sequence together with its length. -/
abbrev FailedPrefix (α : Type*) := Σ k : ℕ, Tape α k
end
end CircuitCompiler.Sampling.Unbounded
end
section
set_option autoImplicit false
open scoped BigOperators ENNReal
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
/-- Append one accepted proposal to its complete rejected prefix. -/
def joinPrefix (t : FailedPrefix α) (a : α) : StoppedTape α := ⟨t.1,(t.2,a)⟩
end
end CircuitCompiler.Sampling.Unbounded
end
section
set_option autoImplicit false
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- All rejected proposals and the final successful proposal. -/

abbrev FullTape {n m : ℕ} (u : U F m) :=
  Unbounded.StoppedTape (Attempt (n := n) u)
end
end CircuitCompiler.Rectangular
end
section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CircuitCompiler.Sampling
open Refresh MatrixRefresh Unbounded
noncomputable section
variable {F X L R V : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype L] [Fintype R] [Fintype V] {m : ℕ}
/-- Uniform square-matrix rejection sampling has positive acceptance probability. -/
def matrixAcceptancePositive (m : ℕ) :
    0 < acceptance (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin m) (Fin m) F)) invertibleTest := by
  exact CircuitCompiler.Sampling.DefinitionSupport.acceptance_positive_of_witness FiniteDistribution.uniform invertibleTest
    (1 : Matrix (Fin m) (Fin m) F) (CircuitCompiler.Sampling.DefinitionSupport.uniform_positive _) (by simp [invertibleTest])
/-- Totalized sampler return; invalid terminal proposals have probability zero. -/

def matrixReturned (M : Matrix (Fin m) (Fin m) F) : Refresh.«GL» F m :=
  if h : invertibleTest M = true then (invertibleTest_isUnit ⟨M,h⟩).unit else 1
end
end CircuitCompiler.Sampling
end
section
set_option autoImplicit false
namespace CircuitCompiler.Sampling
open Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Test whether a vector is nonzero. -/
def nonzeroTest {n : ℕ} (v : V F n) : Bool := decide (v ≠ 0)
end CircuitCompiler.Sampling
end
end StoppedSampling

section CompletionSampling

set_option backward.isDefEq.respectTransparency false
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- All rows except the chosen pivot row of an affine matrix completion. -/
abbrev FreeRows (F : Type*) (n m : ℕ) (j : Fin n) := {i : Fin n // i ≠ j} → Fin m → F
/-- Matrices H satisfying the affine row equation a · H = u. -/
abbrev AffineCompletion {n m : ℕ} (u : U F m) (a : U F n) :=
  {H : Matrix (Fin n) (Fin m) F // Matrix.vecMul a.val H = u.val}
/-- A linear scan of the short row finds a nonzero coefficient. -/

def pivotSearch {n : ℕ} (a : U F n) := Gaussian.findPivot (Vector.ofFn a.val)
end
end CircuitCompiler.Rectangular.CompletionSampler
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
def pivotSearch_ne_none {n : ℕ} (a : U F n) :
    (pivotSearch a).value ≠ none := by
  intro h
  apply a.property
  ext j
  have hz := Gaussian.pivotScan_none (Vector.ofFn a.val) (List.finRange n) h
    j (List.mem_finRange j)
  simpa! [Vector.get, Fin.cast_mk] using hz
end
end CircuitCompiler.Rectangular.CompletionSampler
end
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- The pivot is computed by a finite linear scan, not by a choice operation. -/

def pivot {n : ℕ} (a : U F n) : Fin n :=
  (pivotSearch a).value.get (Option.ne_none_iff_isSome.mp (pivotSearch_ne_none a))
end
end CircuitCompiler.Rectangular.CompletionSampler
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
def pivot_ne_zero {n : ℕ} (a : U F n) : a.val (pivot a) ≠ 0 := by
  have h : (Gaussian.findPivot (Vector.ofFn a.val)).value = some (pivot a) :=
    (Option.some_get _).symm
  have hz := Gaussian.pivotScan_some (Vector.ofFn a.val) (List.finRange n) (pivot a) h
  simpa! [Vector.get] using hz
def sum_pivot {n : ℕ} (j : Fin n) (f : Fin n → F) :
    (∑ i, f i) = f j + ∑ i : {i : Fin n // i ≠ j}, f i.val := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => i = j) f
  haveI : Unique {i : Fin n // i = j} :=
    ⟨⟨j,rfl⟩, fun i => Subtype.ext i.property⟩
  have hd : (default : {i : Fin n // i = j}).val = j := (default : {i : Fin n // i = j}).property
  simpa only [Fintype.sum_unique, hd] using h.symm
end
end CircuitCompiler.Rectangular.CompletionSampler
end
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- The free entries determine the unique remaining row. -/

def fill {n m : ℕ} (u : U F m) (a : U F n)
    (w : FreeRows F n m (pivot a)) : Matrix (Fin n) (Fin m) F := fun i k =>
  if hi : i = pivot a then
    (u.val k - ∑ r : {i : Fin n // i ≠ pivot a}, a.val r.val * w r k) / a.val (pivot a)
  else w ⟨i,hi⟩ k
end
end CircuitCompiler.Rectangular.CompletionSampler
end
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
@[simp] def fill_free {n m : ℕ} (u : U F m) (a : U F n)
    (w : FreeRows F n m (pivot a)) (i : {i : Fin n // i ≠ pivot a}) (k : Fin m) :
    fill u a w i.val k = w i k := by
  simp [fill,i.property]
@[simp] def fill_pivot {n m : ℕ} (u : U F m) (a : U F n)
    (w : FreeRows F n m (pivot a)) (k : Fin m) :
    fill u a w (pivot a) k =
      (u.val k - ∑ r : {i : Fin n // i ≠ pivot a}, a.val r.val * w r k) / a.val (pivot a) := by
  simp [fill]
def fill_constraint {n m : ℕ} (u : U F m) (a : U F n)
    (w : FreeRows F n m (pivot a)) : Matrix.vecMul a.val (fill u a w) = u.val := by
  ext k
  change (∑ i, a.val i * fill u a w i k) = u.val k
  rw [sum_pivot (pivot a), fill_pivot]
  simp_rw [fill_free]
  field_simp [pivot_ne_zero a]
  ring
end
end CircuitCompiler.Rectangular.CompletionSampler
end
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- All affine completions are sampled uniformly by independent free entries. -/

def affineEquiv_left_inv {n m : ℕ} (u : U F m) (a : U F n)
    (w : FreeRows F n m (pivot a)) :
    (fun i k => (fill u a w) i.val k) = w := by
  ext i k
  exact fill_free u a w i k

def affineEquiv_right_inv {n m : ℕ} (u : U F m) (a : U F n)
    (H : AffineCompletion u a) :
    (⟨fill u a (fun i k => H.val i.val k),
      fill_constraint u a (fun i k => H.val i.val k)⟩ : AffineCompletion u a) = H := by
  apply Subtype.ext
  ext i k
  change fill u a (fun r k => H.val r.val k) i k = H.val i k
  by_cases hi : i = pivot a
  · subst i
    rw [fill_pivot]
    have h := congrFun H.property k
    change (∑ i, a.val i * H.val i k) = u.val k at h
    rw [sum_pivot (pivot a)] at h
    apply (div_eq_iff (pivot_ne_zero a)).2
    linear_combination -h
  · simp [fill,hi]

def affineEquiv {n m : ℕ} (u : U F m) (a : U F n) :
    FreeRows F n m (pivot a) ≃ AffineCompletion u a where
  toFun w := ⟨fill u a w,fill_constraint u a w⟩
  invFun H := fun i k => H.val i.val k
  left_inv w := affineEquiv_left_inv u a w
  right_inv H := affineEquiv_right_inv u a H
/-- The test sees only a locally generated candidate matrix. -/

def accept {n m : ℕ} (u : U F m) (a : U F n)
    (w : FreeRows F n m (pivot a)) : Bool := by
  classical
  exact decide (FullRowRank (fill u a w))
/-- The accepted proposals are exactly the full-row-rank completions. -/

def acceptedForward_fullrank {n m : ℕ} (u : U F m) (a : U F n)
    (w : {w : FreeRows F n m (pivot a) // accept u a w = true}) :
    FullRowRank (fill u a w.val) := by
  exact of_decide_eq_true w.property

def acceptedForward {n m : ℕ} (u : U F m) (a : U F n)
    (w : {w : FreeRows F n m (pivot a) // accept u a w = true}) : Completion u a :=
  ⟨⟨fill u a w.val, acceptedForward_fullrank u a w⟩, fill_constraint u a w.val⟩

abbrev acceptedBackward_mem {n m : ℕ} (u : U F m) (a : U F n)
    (H : Completion u a) :
    accept u a (fun i k => H.val.val i.val k) = true := by
  change decide (FullRowRank (fill u a ((affineEquiv u a).symm ⟨H.val.val,H.property⟩))) = true
  have h := congrArg (fun W : AffineCompletion u a => W.val) ((affineEquiv u a).apply_symm_apply ⟨H.val.val,H.property⟩)
  exact decide_eq_true ((congrArg FullRowRank h).mpr H.val.property)

def acceptedBackward {n m : ℕ} (u : U F m) (a : U F n)
    (H : Completion u a) : {w : FreeRows F n m (pivot a) // accept u a w = true} :=
  ⟨(fun i k => H.val.val i.val k), acceptedBackward_mem u a H⟩

def acceptedEquiv_left_inv {n m : ℕ} (u : U F m) (a : U F n) :
    Function.LeftInverse (acceptedBackward u a) (acceptedForward u a) := by
  intro w
  apply Subtype.ext
  exact (affineEquiv u a).left_inv w.val

def acceptedEquiv_right_inv {n m : ℕ} (u : U F m) (a : U F n) :
    Function.RightInverse (acceptedBackward u a) (acceptedForward u a) := by
  intro H
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun W : AffineCompletion u a => W.val) ((affineEquiv u a).apply_symm_apply ⟨H.val.val,H.property⟩)

def acceptedEquiv {n m : ℕ} (u : U F m) (a : U F n) :
    {w : FreeRows F n m (pivot a) // accept u a w = true} ≃ Completion u a where
  toFun := acceptedForward u a
  invFun := acceptedBackward u a
  left_inv := acceptedEquiv_left_inv u a
  right_inv := acceptedEquiv_right_inv u a
end
end CircuitCompiler.Rectangular.CompletionSampler
end
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
abbrev acceptance_pos {n t : ℕ} (u : U F (n+t)) (a : U F n) :
    0 < acceptance (FiniteDistribution.uniform : FiniteDistribution (FreeRows F n (n+t) (pivot a))) (accept u a) := by
  let H := Classical.choice (completion_nonempty u a)
  let w := (acceptedEquiv u a).symm H
  exact CircuitCompiler.Sampling.DefinitionSupport.acceptance_positive_of_witness
    _ _ w.val (CircuitCompiler.Sampling.DefinitionSupport.uniform_positive _) w.property
end
end CircuitCompiler.Rectangular.CompletionSampler
end
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Complete internal tape, consisting of all rejected free-entry arrays and the accepted final array. -/

abbrev InternalTape {n m : ℕ} (a : U F n) :=
  Unbounded.StoppedTape (FreeRows F n m (pivot a))
/-- The rejected free-row proposals retained by an affine-completion sampler. -/
abbrev Prefix {n m : ℕ} (a : U F n) :=
  Unbounded.FailedPrefix (FreeRows F n m (pivot a))
/-- The concrete field-entry rejection sampler, with every proposal retained. -/

def tapeDistribution {n t : ℕ} (u : U F (n+t)) (a : U F n) :
    PMF (InternalTape (m := n+t) a) :=
  Unbounded.distribution FiniteDistribution.uniform (accept u a) (acceptance_pos u a)
/-- Insert the free entries of the fixed accepted matrix after its rejected prefix. In particular, the distribution of the prefix is not assumed to be independent of `(U,A)`. -/

def reconstruct {n m : ℕ} (u : U F m) (a : U F n)
    (p : Prefix (m := m) a) (H : Completion u a) : InternalTape (m := m) a :=
  Unbounded.joinPrefix p (acceptedBackward u a H).val
/-- Total returned-value function. Its arbitrary unsuccessful branch has zero probability under the stopped-tape sampler. -/

def returned {n t : ℕ} (u : U F (n+t)) (a : U F n)
    (w : FreeRows F n (n+t) (pivot a)) : Completion u a :=
  if h : accept u a w = true then acceptedForward u a ⟨w,h⟩ else
    @Classical.choice _ (completion_nonempty u a)
end
end CircuitCompiler.Rectangular.CompletionSampler
end
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
@[simp] theorem returned_accepted {n t : ℕ} (u : U F (n+t)) (a : U F n)
    (w : {w : FreeRows F n (n+t) (pivot a) // accept u a w = true}) :
    returned u a w.val = acceptedEquiv u a w := by
  simp only [returned,dif_pos w.property,acceptedEquiv,Equiv.coe_fn_mk]
@[simp] theorem returned_reconstruct {n t : ℕ} (u : U F (n+t)) (a : U F n)
    (p : Prefix (m := n+t) a) (H : Completion u a) :
    returned u a (reconstruct u a p H).2.2 = H := by
  change returned u a ((acceptedEquiv u a).symm H).val = H
  rw [returned_accepted,Equiv.apply_symm_apply]
end
end CircuitCompiler.Rectangular.CompletionSampler
end
end CompletionSampling

section RectangularExecution

set_option backward.isDefEq.respectTransparency false
section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.AttemptSampler
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- All rejected vector proposals followed by the accepted nonzero row. -/
abbrev RowTape (F : Type*) (n : ℕ) := StoppedTape (V F n)
/-- The rejected vector proposals preceding the accepted nonzero row. -/
abbrev RowPrefix (F : Type*) (n : ℕ) := FailedPrefix (V F n)
/-- A fixed nonzero coordinate vector, used only to complete the sampler’s ambient return function. -/
def rowDefault_nonzero {n : ℕ} (hn : 1 ≤ n) :
    (Pi.single (⟨0, by omega⟩ : Fin n) 1 : V F n) ≠ 0 := by
  intro h
  have hc := congrFun h (⟨0, by omega⟩ : Fin n)
  simpa using hc

def rowDefault {n : ℕ} (hn : 1 ≤ n) : U F n :=
  ⟨Pi.single ⟨0, by omega⟩ 1, rowDefault_nonzero hn⟩
end
end CircuitCompiler.Rectangular.AttemptSampler
end
section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.AttemptSampler
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
abbrev row_acceptance_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < acceptance (FiniteDistribution.uniform : FiniteDistribution (V F n)) nonzeroTest := by
  let a := CircuitCompiler.Rectangular.AttemptSampler.rowDefault (F := F) hn
  exact CircuitCompiler.Sampling.DefinitionSupport.acceptance_positive_of_witness _ _ a.val (CircuitCompiler.Sampling.DefinitionSupport.uniform_positive _)
    (by simp [nonzeroTest, a.property])
end
end CircuitCompiler.Rectangular.AttemptSampler
end
section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.AttemptSampler
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- The actual raw-vector rejection distribution used to sample a nonzero short row. -/
def rowDistribution {n : ℕ} (hn : 1 ≤ n) : PMF (RowTape F n) :=
  distribution FiniteDistribution.uniform nonzeroTest (row_acceptance_pos hn)
/-- Return a nonzero accepted row, with a fixed nonzero completion on rejected ambient inputs. -/
def rowReturned {n : ℕ} (hn : 1 ≤ n) (v : V F n) : U F n :=
  if hv : v ≠ 0 then ⟨v,hv⟩ else rowDefault hn
end
end CircuitCompiler.Rectangular.AttemptSampler
end
section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.AttemptSampler
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Recover the complete vector-sampling tape from its rejected prefix and accepted nonzero row. -/
def reconstructRow {n : ℕ} (p : RowPrefix F n) (a : U F n) : RowTape F n :=
  joinPrefix p a.val
end
end CircuitCompiler.Rectangular.AttemptSampler
end
section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.AttemptSampler
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- A complete internal record stores the actual raw row tape and actual raw completion tape; the returned row indexes the latter's type. -/

abbrev Record {n m : ℕ} (u : U F m) :=
  (a : U F n) × (RowTape F n × CompletionSampler.InternalTape (m := m) a)
/-- Actual sequential execution: draw and reject raw row vectors, then draw and reject raw free-entry matrices. -/

def sequentialDistribution {n t : ℕ} (hn : 1 ≤ n) (u : U F (n+t)) : PMF (Record (n := n) u) :=
  (rowDistribution hn).bind fun r =>
    (CompletionSampler.tapeDistribution u (rowReturned hn r.2.2)).map
      (fun c => ⟨rowReturned hn r.2.2,(r,c)⟩)
/-- The actual returned `(A,H)` proposal. -/

def returned {n t : ℕ} (u : U F (n+t)) (r : Record (n := n) u) : Attempt (n := n) u :=
  sigmaToAttempt u ⟨r.1,CompletionSampler.returned u r.1 r.2.2.2.2⟩
/-- The conditional internal rejected randomness of a fixed primitive attempt. -/

abbrev Mark {n m : ℕ} (a : U F n) :=
  RowPrefix F n × CompletionSampler.Prefix (m := m) a
/-- Recover one complete physical shortening proposal from its abstract attempt and its private sampler marks. -/
def reconstruct {n t : ℕ} (u : U F (n+t)) (p : Attempt (n := n) u)
    (k : Mark (m := n+t) p.val.1) : Record (n := n) u :=
  ⟨p.val.1,(reconstructRow k.1 p.val.1,
    CompletionSampler.reconstruct u p.val.1 k.2 ⟨p.val.2,p.property⟩)⟩
end
end CircuitCompiler.Rectangular.AttemptSampler
end
section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Classical
namespace CircuitCompiler.Rectangular.AttemptSampler
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
@[simp] theorem returned_reconstruct {n t : ℕ} (u : U F (n+t))
    (p : Attempt (n := n) u) (k : Mark (m := n+t) p.val.1) :
    returned u (reconstruct u p k) = p := by
  simp only [returned,reconstruct,CompletionSampler.returned_reconstruct]
  exact (attemptSigmaEquiv u).symm_apply_apply p
end
end CircuitCompiler.Rectangular.AttemptSampler
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Choose a right inverse of a full-row-rank rectangular matrix. -/
def rightInverse {n m : ℕ} (H : FullRank F n m) : Matrix (Fin m) (Fin n) F :=
  Classical.choose H.property
end
end CircuitCompiler.Rectangular
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
@[simp] theorem mul_rightInverse {n m : ℕ} (H : FullRank F n m) :
    H.val * rightInverse H = 1 :=
  Classical.choose_spec H.property
end
end CircuitCompiler.Rectangular
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Pulling back a nonzero row through a full-row-rank matrix stays nonzero. -/
def leftShare_ne_zero {n m : ℕ} (H : FullRank F n m) (a : U F n) :
    Matrix.vecMul a.val H.val ≠ 0 := by
  intro hz
  have h := congrArg (fun r => Matrix.vecMul r (rightInverse H)) hz
  exact a.property (by simpa [Matrix.vecMul_vecMul] using h)

def leftShare {n m : ℕ} (H : FullRank F n m) (a : U F n) : U F m :=
  ⟨Matrix.vecMul a.val H.val, leftShare_ne_zero H a⟩
end
end CircuitCompiler.Rectangular
end
section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- A reverse-shortening record contains a short encoding, a full-row-rank matrix, and a compatible long right share. -/
abbrev Backward (F : Type*) [Field F] (n m : ℕ) (s : F) :=
  {p : Fiber F n s × FullRank F n m × U F m // p.2.1.val.mulVec p.2.2.val = p.1.val.R.val}
/-- The long pair reconstructed by the reverse experiment has the same label. -/

def backwardSource_secret {n m : ℕ} {s : F} (p : Backward F n m s) :
    secret (⟨leftShare p.val.2.1 p.val.1.val.L, p.val.2.2⟩ : State F m) = s := by
  change dotProduct (Matrix.vecMul p.val.1.val.L.val p.val.2.1.val) p.val.2.2.val = s
  rw [← Matrix.dotProduct_mulVec,p.property]
  exact p.val.1.property

def backwardSource {n m : ℕ} {s : F} (p : Backward F n m s) : Fiber F m s :=
  ⟨⟨leftShare p.val.2.1 p.val.1.val.L,p.val.2.2⟩, backwardSource_secret p⟩
end
end CircuitCompiler.Rectangular
end
section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- A successful forward-shortening record contains the long encoding, short left row, and compatible full-row-rank matrix. -/
abbrev ForwardRecord (F : Type*) [Field F] (n m : ℕ) (s : F) :=
  {p : State F m × U F n × FullRank F n m //
    secret p.1 = s ∧ Matrix.vecMul p.2.1.val p.2.2.val = p.1.L.val ∧
      p.2.2.val.mulVec p.1.R.val ≠ 0}
/-- A successful forward record and a reverse record contain exactly the same values, merely listed in a different order. -/

def forwardToBackward_secret {n m : ℕ} {s : F} (p : ForwardRecord F n m s) :
    secret (⟨p.val.2.1,
      ⟨p.val.2.2.val.mulVec p.val.1.R.val, p.property.2.2⟩⟩ : State F n) = s := by
  change dotProduct p.val.2.1.val (p.val.2.2.val.mulVec p.val.1.R.val) = s
  rw [Matrix.dotProduct_mulVec,p.property.2.1]
  exact p.property.1

def forwardToBackward {n m : ℕ} {s : F} (p : ForwardRecord F n m s) : Backward F n m s :=
  ⟨(⟨⟨p.val.2.1, ⟨p.val.2.2.val.mulVec p.val.1.R.val, p.property.2.2⟩⟩,
    forwardToBackward_secret p⟩, p.val.2.2, p.val.1.R), rfl⟩

def backwardToForward_nonzero {n m : ℕ} {s : F} (p : Backward F n m s) :
    p.val.2.1.val.mulVec (backwardSource p).val.R.val ≠ 0 := by
  change p.val.2.1.val.mulVec p.val.2.2.val ≠ 0
  rw [p.property]
  exact p.val.1.val.R.property

def backwardToForward {n m : ℕ} {s : F} (p : Backward F n m s) : ForwardRecord F n m s :=
  ⟨((backwardSource p).val, p.val.1.val.L, p.val.2.1),
    (backwardSource p).property, rfl, backwardToForward_nonzero p⟩

def forwardBackward_left_inv {n m : ℕ} (s : F) (p : ForwardRecord F n m s) :
    backwardToForward (forwardToBackward p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · apply State.ext
    · apply Subtype.ext; exact p.property.2.1
    · rfl
  · rfl

def forwardBackward_right_inv {n m : ℕ} (s : F) (p : Backward F n m s) :
    forwardToBackward (backwardToForward p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply State.ext
    · rfl
    · apply Subtype.ext; exact p.property
  · rfl

def forwardBackwardEquiv {n m : ℕ} (s : F) : ForwardRecord F n m s ≃ Backward F n m s where
  toFun := forwardToBackward
  invFun := backwardToForward
  left_inv := forwardBackward_left_inv s
  right_inv := forwardBackward_right_inv s
end
end CircuitCompiler.Rectangular
end
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Forward successful choices, retaining the original long encoding. -/

abbrev SuccessfulJoint (F : Type*) [Field F] (n m : ℕ) (s : F) :=
  (x : Fiber F m s) × Success (n := n) x.val.L x.val.R
/-- Rearranging a successful choice gives the reverse record. -/

def successfulJointForward {n m : ℕ} (s : F) (p : SuccessfulJoint F n m s) :
    Backward F n m s :=
  forwardToBackward ⟨(p.1.val, p.2.val.val.1, p.2.val.val.2),
    p.1.property, p.2.val.property, p.2.property⟩

def successfulJointBackward {n m : ℕ} (s : F) (p : Backward F n m s) :
    SuccessfulJoint F n m s :=
  ⟨backwardSource p, ⟨⟨(p.val.1.val.L, p.val.2.1), rfl⟩,
    backwardToForward_nonzero p⟩⟩

def successfulJointEquiv_left_inv {n m : ℕ} (s : F)
    (p : SuccessfulJoint F n m s) :
    successfulJointBackward s (successfulJointForward s p) = p := by
  rcases p with ⟨⟨⟨⟨u,hu⟩,v⟩,hs⟩,⟨⟨⟨a,H⟩,ha⟩,hacc⟩⟩
  dsimp at ha
  subst u
  rfl

def successfulJointEquiv_right_inv {n m : ℕ} (s : F)
    (p : Backward F n m s) :
    successfulJointForward s (successfulJointBackward s p) = p := by
  apply Subtype.ext; apply Prod.ext
  · apply Subtype.ext; apply State.ext
    · rfl
    · apply Subtype.ext; exact p.property
  · rfl

def successfulJointEquiv {n m : ℕ} (s : F) :
    SuccessfulJoint F n m s ≃ Backward F n m s where
  toFun := successfulJointForward s
  invFun := successfulJointBackward s
  left_inv := successfulJointEquiv_left_inv s
  right_inv := successfulJointEquiv_right_inv s
end
end CircuitCompiler.Rectangular
end
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh
noncomputable section
variable {F O A B : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [DecidableEq O] [Nonempty O] [Fintype A] [Fintype B]
variable {n t : ℕ}
/-- The long secret encoded by the two feature vectors. -/

def gateSecret (a b : O → U F (n+t)) (o : O × O) : F :=
  dot (a o.1).val (b o.2).val
/-- The initial long feature encoding, retaining its plaintext equation. -/

def gateInput (a b : O → U F (n+t)) (o : O × O) :
    Fiber F (n+t) (gateSecret a b o) := ⟨⟨a o.1,b o.2⟩,rfl⟩
/-- The sampler returns the first row and the matrix-times-column output. The fallback merely makes this total on probability-zero invalid tapes. -/

def returnedOutput {s : F} (fallback : Fiber F n s) (x : Fiber F (n+t) s)
    (a : Attempt (n := n) x.val.L) : Fiber F n s :=
  if h : rightOutput x.val.R a ≠ 0 then
    (successfulJointForward s ⟨x,⟨a,h⟩⟩).val.1 else fallback
end
end CircuitCompiler.Rectangular
end
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh
open _root_.CircuitCompiler.Composition _root_.CircuitCompiler.Composition.TopologicalExecution
noncomputable section
variable {F O A B : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [Fintype A] [Fintype B]
/-- Reindex a feature vector when only the ambient dimension's spelling changes. -/

def featureDimension {m k : ℕ} (h : m = k) (a : O → U F m) : O → U F k :=
  fun x => Equiv.cast (congrArg (U F) h) (a x)
variable {n t inputs T : ℕ}
/-- Embed the left tensor share and its affine constant into the common long-vector dimension. -/
def augmentedLeftFeature (hdim : n*n+1 = n+t) (c : F) : (U F n × U F n) → U F (n+t) :=
  featureDimension hdim (augmentedShare c)
/-- Embed the right tensor share and its final unit coordinate into the common long-vector dimension. -/
def augmentedRightFeature (hdim : n*n+1 = n+t) : (U F n × U F n) → U F (n+t) :=
  featureDimension hdim (augmentedShare (1 : F))
/-- Group two old encoding pairs into the left party’s two shares and the right party’s two shares. -/
def augmentedOldPorts (left right : State F n) :
    (U F n × U F n) × (U F n × U F n) := ((left.L,right.L),(left.R,right.R))
end
end CircuitCompiler.Rectangular
end
section
set_option autoImplicit false
open scoped BigOperators Matrix Matrix.Norms.L2Operator
namespace CircuitCompiler
open Refresh MatrixRefresh
noncomputable section
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype A]
/-- Rename a nonzero share along an equality of vector dimensions. -/
def shareDimensionEquiv {m k : ℕ} (h : m = k) : U F m ≃ U F k :=
  Equiv.cast (congrArg (U F) h)
end
end CircuitCompiler
end
section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators
namespace CircuitCompiler.Rectangular.Taped
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
/-- Apply a map to every proposal of a finite tape. -/

def mapTape {X Y : Type*} (f : X → Y) : (k : ℕ) → Tape X k → Tape Y k
  | 0, _ => PUnit.unit
  | k+1, t => (f t.1,mapTape f k t.2)
/-- Apply a map to both the rejected prefix and the terminal proposal. -/

def mapStopped {X Y : Type*} (f : X → Y) (t : StoppedTape X) : StoppedTape Y :=
  ⟨t.1,(mapTape f t.1 t.2.1,f t.2.2)⟩
variable {F O A BL BR M : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [Fintype A] [Fintype BL] [Fintype BR]
variable {n t : ℕ}
/-- The right shortening view contains every rejected and accepted full-row-rank matrix. -/
abbrev RightView (F : Type*) [Field F] (n m : ℕ) :=
  StoppedTape (FullRank F n m)
/-- The right party sees the matrices, without the left rows or private marks. -/

def rightView {u : U F (n+t)} (z : FullTape (n := n) u) : RightView F n (n+t) :=
  mapStopped (fun p => p.val.2) z
end
end CircuitCompiler.Rectangular.Taped
end
section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open scoped BigOperators ENNReal
namespace CircuitCompiler.Rectangular.Taped
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n t : ℕ}
/-- Empty prefixes make the decoding total off the sampler's support. -/

def emptyMark (a : U F n) : AttemptSampler.Mark (m := n+t) a :=
  (⟨0,PUnit.unit⟩,⟨0,PUnit.unit⟩)
end
end CircuitCompiler.Rectangular.Taped
end
section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh
open _root_.CircuitCompiler.Composition _root_.CircuitCompiler.Composition.TopologicalExecution Sampling Sampling.Unbounded
noncomputable section
variable {F A BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype A] [Fintype BL] [Fintype BR]
variable {n t inputs T : ℕ}
namespace TapedAugmentedStrategy
variable {hdim : n*n+1 = n+t}
/-- An arbitrary total-function completion used only on zero-mass invalid tapes. -/

def fallback (hn : 2 ≤ n) (gate : Gate F (inputs+T)) (left right : State F n) :
    Fiber F n (gateSecret (augmentedLeftFeature hdim gate.kind.affineConstant)
      (augmentedRightFeature hdim) (augmentedOldPorts left right)) :=
  Classical.choice (fiber_nonempty F n hn _)
end TapedAugmentedStrategy
end
end CircuitCompiler.Rectangular
end
section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh
open _root_.CircuitCompiler.Composition _root_.CircuitCompiler.Composition.TopologicalExecution Sampling Sampling.Unbounded
noncomputable section
variable {F ML MR BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
variable {n t inputs T : ℕ}
/-- Arbitrary bounded local leakage of the fully implemented gate. Matrix sampler tapes are erased before the shortening leakage functions are invoked. -/

structure FullyTapedStrategy (F ML MR BL BR : Type*) [Field F] [Fintype F] [DecidableEq F]
    [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
    (n t inputs : ℕ) (hdim : n*n+1 = n+t) where
  matrixLeft : (i : ℕ) → Gate F (inputs+i) → (Fin i → (ML × MR) × (BL × BR)) →
    (U F n × U F n) → StoppedTape (Matrix (Fin (n+t)) (Fin (n+t)) F) → ML
  matrixRight : (i : ℕ) → Gate F (inputs+i) → (Fin i → (ML × MR) × (BL × BR)) →
    (U F n × U F n) → StoppedTape (Matrix (Fin (n+t)) (Fin (n+t)) F) → MR
  left : (i : ℕ) → Gate F (inputs+i) → (Fin i → (ML × MR) × (BL × BR)) →
    (ML × MR) → (U F n × U F n) → (u : U F (n+t)) →
      StoppedTape (AttemptSampler.Record (n := n) u) → BL
  right : (i : ℕ) → Gate F (inputs+i) → (Fin i → (ML × MR) × (BL × BR)) →
    (ML × MR) → (U F n × U F n) → U F (n+t) → Taped.RightView F n (n+t) → BR
namespace FullyTapedStrategy
variable {hdim : n*n+1 = n+t}
/-- The actual complete matrix-sampler observation retains its returned invertible matrix jointly with both leakage answers. -/

def rawMatrixExecution (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim)
    (i : ℕ) (gate : Gate F (inputs+i)) (history : Fin i → (ML × MR) × (BL × BR))
    (left right : State F n) : FiniteDistribution (Refresh.«GL» F (n+t) × (ML × MR)) :=
  observe FiniteDistribution.uniform invertibleTest (matrixAcceptancePositive (F := F) (n+t))
    (fun tape => (matrixReturned tape.2.2,
      (strategy.matrixLeft i gate history (augmentedOldPorts left right).1 tape,
       strategy.matrixRight i gate history (augmentedOldPorts left right).2 tape)))
end FullyTapedStrategy
end
end CircuitCompiler.Rectangular
end
end RectangularExecution

section TraceSupport

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators ENNReal Classical

namespace CircuitCompiler.Sampling.DefinitionSupport
open Refresh

/-- The immediate successful trace has its proposal's positive mass. -/
theorem zeroRetry_mem_support {α : Type*} [Fintype α]
    (P : FiniteDistribution α) (accept : α → Bool) (hp : 0 < acceptance P accept)
    (a : α) (hweight : 0 < P.weight a) (haccept : accept a = true) :
    (⟨0, (PUnit.unit, a)⟩ : Unbounded.StoppedTape α) ∈
      (Unbounded.distribution P accept hp).support := by
  change ENNReal.ofReal _ ≠ 0
  simpa [Unbounded.traceWeight, Unbounded.prefixWeight, haccept] using
    (ENNReal.ofReal_pos.mpr hweight).ne'
end CircuitCompiler.Sampling.DefinitionSupport
end
end TraceSupport

section Initialization

set_option backward.isDefEq.respectTransparency false
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Sampling.RawEncoding
open Refresh MatrixRefresh Unbounded Rectangular.Gaussian
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- A raw encoding proposal consists of two vectors, which may initially be zero. -/
abbrev Raw (F : Type*) (n : ℕ) := V F n × V F n
/-- Accept a raw pair exactly when both vectors are nonzero and their inner product equals the prescribed secret. -/
def accept {n : ℕ} (s : F) (x : Raw F n) : Bool :=
  nonzeroTest x.1 && nonzeroTest x.2 && decide (dot x.1 x.2 = s)
end
end CircuitCompiler.Sampling.RawEncoding
end
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Sampling.RawEncoding
open Refresh MatrixRefresh Unbounded Rectangular.Gaussian
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
@[simp] def accept_iff {n : ℕ} (s : F) (x : Raw F n) :
    accept s x = true ↔ x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ dot x.1 x.2 = s := by
  simp only [accept,Bool.and_eq_true,nonzeroTest,decide_eq_true_eq,and_assoc]
end
end CircuitCompiler.Sampling.RawEncoding
end
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Sampling.RawEncoding
open Refresh MatrixRefresh Unbounded Rectangular.Gaussian
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Accepted raw pairs and valid encodings are the same finite set. -/

def acceptedToFiber {n : ℕ} (s : F)
    (x : {x : Raw F n // accept s x = true}) : Fiber F n s :=
  ⟨⟨⟨x.val.1, ((accept_iff s x.val).mp x.property).1⟩,
    ⟨x.val.2, ((accept_iff s x.val).mp x.property).2.1⟩⟩,
    ((accept_iff s x.val).mp x.property).2.2⟩

def fiberToAccepted {n : ℕ} (s : F) (x : Fiber F n s) :
    {x : Raw F n // accept s x = true} :=
  ⟨(x.val.L.val, x.val.R.val),
    (accept_iff s _).mpr ⟨x.val.L.property, x.val.R.property, x.property⟩⟩

def acceptedEquiv_left_inv {n : ℕ} (s : F)
    (x : {x : Raw F n // accept s x = true}) :
    fiberToAccepted s (acceptedToFiber s x) = x := by
  apply Subtype.ext
  rfl

def acceptedEquiv_right_inv {n : ℕ} (s : F) (x : Fiber F n s) :
    acceptedToFiber s (fiberToAccepted s x) = x := by
  apply Subtype.ext
  rfl

def acceptedEquiv {n : ℕ} (s : F) :
    {x : Raw F n // accept s x = true} ≃ Fiber F n s where
  toFun := acceptedToFiber s
  invFun := fiberToAccepted s
  left_inv := acceptedEquiv_left_inv s
  right_inv := acceptedEquiv_right_inv s
end
end CircuitCompiler.Sampling.RawEncoding
end
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Sampling.RawEncoding
open Refresh MatrixRefresh Unbounded Rectangular.Gaussian
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
abbrev acceptance_pos {n : ℕ} (hn : 2 ≤ n) (s : F) :
    0 < acceptance (FiniteDistribution.uniform : FiniteDistribution (Raw F n)) (accept s) := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  let l : V F n := Pi.single i 1
  let r : V F n := Pi.single i s + Pi.single j 1
  have hl : l ≠ 0 := by
    intro h
    have := congrFun h i
    simp [l] at this
  have hr : r ≠ 0 := by
    intro h
    have := congrFun h j
    simp [r, Ne.symm hij] at this
  have hs : dot l r = s := by simp [dot, l, r, dotProduct, Pi.single_apply, hij]
  exact CircuitCompiler.Sampling.DefinitionSupport.acceptance_positive_of_witness FiniteDistribution.uniform (accept s) (l, r)
    (CircuitCompiler.Sampling.DefinitionSupport.uniform_positive _) (by simp [accept, nonzeroTest, hl, hr, hs])
end
end CircuitCompiler.Sampling.RawEncoding
end
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Sampling.RawEncoding
open Refresh MatrixRefresh Unbounded Rectangular.Gaussian
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Complete raw proposal tape, including every rejected pair. -/

def tapeDistribution {n : ℕ} (hn : 2 ≤ n) (s : F) : PMF (StoppedTape (Raw F n)) :=
  distribution FiniteDistribution.uniform (accept s) (acceptance_pos hn s)
/-- Decode the final accepted raw pair; the default is unreachable under `tapeDistribution` and only makes the function total on arbitrary tape values. -/

def returned {n : ℕ} (hn : 2 ≤ n) (s : F) (x : Raw F n) : Fiber F n s :=
  if h : accept s x = true then acceptedToFiber s ⟨x,h⟩
  else Classical.choice (fiber_nonempty F n hn s)
end
end CircuitCompiler.Sampling.RawEncoding
end
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace CircuitCompiler.Sampling.RawEncoding
open Refresh MatrixRefresh Unbounded _root_.CircuitCompiler.Composition
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Real initialization performs an uncapped raw-entry sampler for each input wire. The final state is retained and each completed private tape is erased. -/

def initializeWires {n : ℕ} (hn : 2 ≤ n) :
    {inputs : ℕ} → (Fin inputs → F) → PMF (Fin inputs → State F n)
  | 0,_ => PMF.pure Fin.elim0
  | k+1,input => (initializeWires hn (Fin.init input)).bind (fun earlier =>
      (tapeDistribution hn (input (Fin.last k))).map (fun tape =>
        Fin.snoc (α := fun _ => State F n) earlier (returned hn (input (Fin.last k)) tape.2.2).val))
/-- The compiled runner stores the same encoding as an explicit share pair. -/

def initializeShares {n inputs : ℕ} (hn : 2 ≤ n) (input : Fin inputs → F) :
    PMF (Fin inputs → U F n × U F n) :=
  (initializeWires hn input).map (fun states i => stateEquivProd F n (states i))
end
end CircuitCompiler.Sampling.RawEncoding
end
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Sampling.CountableRejection
open Refresh Unbounded
noncomputable section
variable {α β : Type*}
/-- The probability that a countable proposal passes the acceptance test. -/
def probability (P : PMF α) (accept : α → Bool) : ℝ :=
  (toFinite (P.map accept)).weight true
end
end CircuitCompiler.Sampling.CountableRejection
end
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Sampling.CountableRejection
open Refresh Unbounded
noncomputable section
variable {α β : Type*}
theorem probability_add_rejection (P : PMF α) (accept : α → Bool) :
    probability P accept + (toFinite (P.map accept)).weight false = 1 := by
  have h := (toFinite (P.map accept)).total
  simpa [probability,Fintype.sum_bool,add_comm] using h
def probability_le_one (P : PMF α) (accept : α → Bool) : probability P accept ≤ 1 := by
  have h := probability_add_rejection P accept
  have hn := (toFinite (P.map accept)).nonneg false
  linarith
end
end CircuitCompiler.Sampling.CountableRejection
end
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Sampling.CountableRejection
open Refresh Unbounded
noncomputable section
variable {α β : Type*}
/-- The proposal mass restricted to rejected values. -/
def rejectedMass (P : PMF α) (accept : α → Bool) (x : α) : ℝ≥0∞ :=
  if accept x then 0 else P x
/-- The proposal mass restricted to accepted values. -/
def acceptedMass (P : PMF α) (accept : α → Bool) (x : α) : ℝ≥0∞ :=
  if accept x then P x else 0
end
end CircuitCompiler.Sampling.CountableRejection
end
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Sampling.CountableRejection
open Refresh Unbounded
noncomputable section
variable {α β : Type*}
theorem tsum_acceptedMass (P : PMF α) (accept : α → Bool) :
    (∑' x, acceptedMass P accept x) = ENNReal.ofReal (probability P accept) := by
  rw [probability,toFinite,ENNReal.ofReal_toReal (PMF.apply_ne_top _ _),PMF.map_apply]
  apply tsum_congr
  intro x
  cases hx : accept x <;> simp [acceptedMass,hx]
theorem tsum_rejectedMass (P : PMF α) (accept : α → Bool) :
    (∑' x, rejectedMass P accept x) = ENNReal.ofReal (1-probability P accept) := by
  have hr : (toFinite (P.map accept)).weight false = 1-probability P accept := by
    linarith [probability_add_rejection P accept]
  rw [← hr,toFinite,ENNReal.ofReal_toReal (PMF.apply_ne_top _ _),PMF.map_apply]
  apply tsum_congr
  intro x
  cases hx : accept x <;> simp [rejectedMass,hx]
end
end CircuitCompiler.Sampling.CountableRejection
end
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Sampling.CountableRejection
open Refresh Unbounded
noncomputable section
variable {α β : Type*}
/-- The product mass of a finite sequence of rejected proposals. -/
def prefixMass (P : PMF α) (accept : α → Bool) : (k : ℕ) → Tape α k → ℝ≥0∞
  | 0,_ => 1
  | k+1,t => rejectedMass P accept t.1 * prefixMass P accept k t.2
/-- The mass of a complete rejection tape is its rejected-prefix mass times its accepted-final-proposal mass. -/
def traceMass (P : PMF α) (accept : α → Bool) (t : StoppedTape α) : ℝ≥0∞ :=
  prefixMass P accept t.1 t.2.1 * acceptedMass P accept t.2.2
end
end CircuitCompiler.Sampling.CountableRejection
end
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Sampling.CountableRejection
open Refresh Unbounded
noncomputable section
variable {α β : Type*}
theorem tsum_prefixMass (P : PMF α) (accept : α → Bool) (k : ℕ) :
    (∑' t, prefixMass P accept k t) = (ENNReal.ofReal (1-probability P accept))^k := by
  induction k with
  | zero => simp [prefixMass,Tape]
  | succ k ih =>
      change (∑' t : α × Tape α k, rejectedMass P accept t.1 * prefixMass P accept k t.2) = _
      rw [ENNReal.tsum_prod']
      simp only [ENNReal.tsum_mul_left,ih,ENNReal.tsum_mul_right,tsum_rejectedMass,pow_succ']
def tsum_traceMass (P : PMF α) (accept : α → Bool) (k : ℕ) :
    (∑' t : Tape α k × α, traceMass P accept ⟨k,t⟩) =
      ENNReal.ofReal (ProbabilityTheory.geometricPMFReal (probability P accept) k) := by
  simp only [traceMass,ENNReal.tsum_prod',ENNReal.tsum_mul_left,tsum_acceptedMass,
    ENNReal.tsum_mul_right,tsum_prefixMass,ProbabilityTheory.geometricPMFReal]
  rw [ENNReal.ofReal_mul (pow_nonneg (sub_nonneg.mpr (probability_le_one P accept)) k),
    ENNReal.ofReal_pow (by linarith [probability_le_one P accept])]
end
end CircuitCompiler.Sampling.CountableRejection
end
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Sampling.CountableRejection
open Refresh Unbounded
noncomputable section
variable {α β : Type*}
/-- Direct iid rejection semantics. Every finite stopped raw trace is assigned its independent proposal-product mass, and these masses sum to one. -/
abbrev distribution_normalized (P : PMF α) (accept : α → Bool)
    (hp : 0 < probability P accept) : HasSum (traceMass P accept) 1 := by
  apply ENNReal.summable.hasSum_iff.mpr
  rw [ENNReal.tsum_sigma']
  simp_rw [tsum_traceMass]
  exact (ProbabilityTheory.geometricPMF hp (probability_le_one P accept)).tsum_coe

def distribution (P : PMF α) (accept : α → Bool) (hp : 0 < probability P accept) :
    PMF (StoppedTape α) :=
  ⟨traceMass P accept, distribution_normalized P accept hp⟩
end
end CircuitCompiler.Sampling.CountableRejection
end
section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Rectangular.Taped
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n t : ℕ}
/-- The ordinary outer acceptance test is computed from the actual raw record's returned rectangular matrix and the right party's long share. -/

abbrev rawAccept (u v : U F (n+t)) (record : AttemptSampler.Record (n := n) u) : Bool :=
  decide (rightOutput v (AttemptSampler.returned u record) ≠ 0)
end
end CircuitCompiler.Rectangular.Taped
end
section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Rectangular.Taped
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n t : ℕ}
/-- A supported accepted proposal gives positive countable acceptance probability. -/
theorem countableAcceptancePositive_of_witness {α : Type*}
    (P : PMF α) (accept : α → Bool) (a : α)
    (hweight : a ∈ P.support) (haccept : accept a = true) :
    0 < CountableRejection.probability P accept := by
  apply ENNReal.toReal_pos _ (PMF.apply_ne_top (P.map accept) true)
  exact ((PMF.mem_support_map_iff accept P true).mpr ⟨a, hweight, haccept⟩ : true ∈ (P.map accept).support)

/-- Every legal completion has a supported raw record with no rejected primitive proposals. -/
theorem zeroRetry_record_supported {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n t : ℕ} (hn : 1 ≤ n) (u : U F (n+t)) (p : Attempt (n := n) u) :
    AttemptSampler.reconstruct u p (emptyMark p.val.1) ∈
      (AttemptSampler.sequentialDistribution hn u).support := by
  let a := p.val.1
  let H : Completion u a := ⟨p.val.2,p.property⟩
  let w := ((CompletionSampler.acceptedEquiv u a).symm H).val
  let row : AttemptSampler.RowTape F n := ⟨0,(PUnit.unit,a.val)⟩
  let completion : CompletionSampler.InternalTape (m := n+t) a := ⟨0,(PUnit.unit,w)⟩
  have hw : CompletionSampler.accept u a w = true :=
    ((CompletionSampler.acceptedEquiv u a).symm H).property
  have hr : row ∈ (AttemptSampler.rowDistribution hn).support :=
    CircuitCompiler.Sampling.DefinitionSupport.zeroRetry_mem_support _ _ _ a.val (CircuitCompiler.Sampling.DefinitionSupport.uniform_positive _) (by simp [nonzeroTest,a.property])
  have hc : completion ∈ (CompletionSampler.tapeDistribution u a).support :=
    CircuitCompiler.Sampling.DefinitionSupport.zeroRetry_mem_support _ _ _ w (CircuitCompiler.Sampling.DefinitionSupport.uniform_positive _) hw
  have hrow : AttemptSampler.rowReturned hn row.2.2 = a := by
    simp [row, AttemptSampler.rowReturned, a.property]
  unfold AttemptSampler.sequentialDistribution
  apply (PMF.mem_support_bind_iff _ _ _).mpr
  refine ⟨row,hr,?_⟩
  rw [hrow]
  apply (PMF.mem_support_map_iff _ _ _).mpr
  exact ⟨completion,hc,rfl⟩

abbrev raw_acceptance_positive (hn : 2 ≤ n) (u v : U F (n+t)) :
    0 < CountableRejection.probability (AttemptSampler.sequentialDistribution (by omega) u)
      (rawAccept u v) := by
  let p := Classical.choice (success_nonempty hn u v)
  apply countableAcceptancePositive_of_witness _ _
    (AttemptSampler.reconstruct u p.val (emptyMark p.val.val.1))
    (zeroRetry_record_supported (by omega) u p.val)
  simpa [rawAccept, AttemptSampler.returned_reconstruct] using
    (decide_eq_true p.property)
end
end CircuitCompiler.Rectangular.Taped
end
section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open scoped BigOperators ENNReal Classical
namespace CircuitCompiler.Rectangular.Taped
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n t : ℕ}
/-- Direct execution of the raw primitive samplers until the right output is nonzero. This distribution assigns each stopped raw record trace its iid proposal- product mass, including all inner row/completion proposals in every record. -/

def rawRetryDistribution (hn : 2 ≤ n) (u v : U F (n+t)) :
    PMF (StoppedTape (AttemptSampler.Record (n := n) u)) :=
  CountableRejection.distribution (AttemptSampler.sequentialDistribution (by omega) u)
    (rawAccept u v) (raw_acceptance_positive hn u v)
end
end CircuitCompiler.Rectangular.Taped
end
end Initialization

section PhysicalGates

set_option backward.isDefEq.respectTransparency false
section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open scoped Classical
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh
open _root_.CircuitCompiler.Composition _root_.CircuitCompiler.Composition.TopologicalExecution Sampling Sampling.Unbounded
noncomputable section
variable {F O A BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [Fintype A] [Fintype BL] [Fintype BR] {n t : ℕ}
namespace Taped
/-- The right party's communicated matrix history, read from raw records. -/

def rawRightView (u : U F (n+t)) (z : StoppedTape (AttemptSampler.Record (n := n) u)) :
    RightView F n (n+t) := rightView (mapStopped (AttemptSampler.returned u) z)
/-- Sample ordinary raw row/completion records until their rectangular output is nonzero, then observe the complete local raw histories. -/

def rawShorteningDirect {s : F} (hn : 2 ≤ n) (fallback : Fiber F n s)
    (left : A → O → (u : U F (n+t)) → StoppedTape (AttemptSampler.Record (n := n) u) → BL)
    (right : A → O → U F (n+t) → RightView F n (n+t) → BR)
    (o : O × O) (x : Fiber F (n+t) s) (α : A) : FiniteDistribution (Fiber F n s × (A × (BL × BR))) :=
  toFinite ((rawRetryDistribution hn x.val.L x.val.R).map (fun z =>
    (returnedOutput fallback x (AttemptSampler.returned x.val.L z.2.2),
      (α,(left α o.1 x.val.L z,right α o.2 x.val.R (rawRightView x.val.L z))))))
end Taped
namespace FullyTapedStrategy
variable {ML MR : Type*} [Fintype ML] [Fintype MR] {inputs : ℕ} {hdim : n*n+1 = n+t}
/-- Full physical execution using the direct raw-record rejection semantics for every outer shortening attempt. Matrix rejection is also uncapped. -/

def directRawExecution (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → (ML × MR) × (BL × BR)) (left right : State F n) :
    FiniteDistribution (State F n × ((ML × MR) × (BL × BR))) :=
  ((strategy.rawMatrixExecution i gate history left right).bind (fun ma =>
    Taped.rawShorteningDirect hn (TapedAugmentedStrategy.fallback (hdim := hdim) hn gate left right)
      (strategy.left i gate history) (strategy.right i gate history) (augmentedOldPorts left right)
      (refreshInFiber (gateInput (augmentedLeftFeature hdim gate.kind.affineConstant)
        (augmentedRightFeature hdim) (augmentedOldPorts left right)) ma.1) ma.2)).map
    (fun z => (z.1.val,z.2))
end FullyTapedStrategy
end
end CircuitCompiler.Rectangular
end
end PhysicalGates

/-!
## Composition and adaptive interfaces

History weights, physical operations, and adaptive public-input plans.
-/

section CommonLocalData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
namespace CompilerProof.DirectComposition
open Refresh MatrixRefresh CircuitCompiler.Composition CircuitCompiler.AveragedEnergyComparison

variable {W X A F : Type*} [Fintype W] [DecidableEq W]
  [Fintype X] [Nonempty X] [Fintype A] {S : ℕ}
/-- Independently encode every wire label and group the resulting left and right shares by party. This is a distribution before any leakage answer is observed. -/
def groupedLaw (law : F → FiniteDistribution (X × X)) (label : W → F) :
    FiniteDistribution ((W → X) × (W → X)) :=
  groupedDistribution (fun w => law (label w)) Prod.fst Prod.snd
/-- A chosen approximation and its factor representation for every operation, formal history, and answer. Error bounds are required only for valid local labelings at approximated operations; public samplers are outside that set. The factors themselves inspect only the declared scope, so separate energy trimming preserves locality. -/
structure LocalData (scope : Fin S → Finset W)
    (network : ScopedProbabilities (E := X × X) (A := A) scope)
    (law : F → FiniteDistribution (X × X))
    (valid : (W → F) → Fin S → Prop) (approximated : Finset (Fin S)) (β ε : ℝ) where
  gate : ∀ i h z,
    GateLocalEstimates (groupedLaw law)
      (fun label => valid label i ∧ i ∈ approximated)
      (fun _ left right => network.prob i h (fun w => (left w,right w)) z) β ε
  left_locality : ∀ i h z j, Scoped (scope i)
    (fun e : W → X × X => (gate i h z).factors.left (fun w => (e w).1) j)
  right_locality : ∀ i h z j, Scoped (scope i)
    (fun e : W → X × X => (gate i h z).factors.right (fun w => (e w).2) j)
/-- The true complete-history weight in the canonical experiment. The factor at position i uses exactly the earlier answer prefix. -/
def historyWeight (scope : Fin S → Finset W)
    (network : ScopedProbabilities (E := X × X) (A := A) scope)
    (z : Fin S → A) (encoding : W → X × X) : ℝ :=
  ∏ i, network.prob i ((List.ofFn z).take i.val) encoding (z i)
/-- Average the adaptive true history product under independent fixed-bit encodings. The hidden wire encodings are not part of this transcript weight. -/
def canonicalWeight (scope : Fin S → Finset W)
    (network : ScopedProbabilities (E := X × X) (A := A) scope)
    (law : F → FiniteDistribution (X × X)) (label : W → F) (z : Fin S → A) : ℝ :=
  (independentDistribution (fun w => law (label w))).expect
    (historyWeight scope network z)
end CompilerProof.DirectComposition
end
end CommonLocalData

section CompositionParameters

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CompilerProof.DirectComposition
/-- Approximation parameter used before energy trimming. -/
def betaParameter (q : ℝ) : ℝ := q ^ (-1/3 : ℝ)
/-- A convenient upper bound for the untrimmed valid-label RMS error. -/
def rawErrorParameter (q : ℝ) : ℝ := 10000*q ^ (-1/9 : ℝ)
end CompilerProof.DirectComposition
end
end CompositionParameters

section PhysicalShares

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace CircuitCompiler
open Refresh _root_.CircuitCompiler.Composition _root_.CircuitCompiler.Composition.TopologicalExecution
variable {F Alpha Beta : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype Alpha] [Fintype Beta] {n t inputs : ℕ}
/-- Uniformly encode one field element and expose its pair of nonzero shares. -/
noncomputable def encodingDistribution (hn : 2 ≤ n) (s : F) : FiniteDistribution (U F n × U F n) :=
  letI : Nonempty (Fiber F n s) := fiber_nonempty F n hn s
  ((FiniteDistribution.uniform : FiniteDistribution (Fiber F n s)).map Subtype.val).map
    (stateEquivProd F n)
end CircuitCompiler
end PhysicalShares

namespace Refresh
/-- Uniform encoding of a secret, retained for the detailed probability proofs. -/
noncomputable def mu (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) (hn : 2 ≤ n) (s : F) : FiniteDistribution (State F n) :=
  letI : Nonempty (Fiber F n s) := fiber_nonempty F n hn s
  (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s)).map Subtype.val
end Refresh

section Operations

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace CircuitCompiler.Operations
open Refresh MatrixRefresh Sampling Sampling.Unbounded _root_.CircuitCompiler.Composition _root_.CircuitCompiler.Composition.TopologicalExecution

/-- One active operation, with all predecessor ports strictly earlier than its new output position. `sample s` is permitted only for the public label `s`. -/
inductive Instruction (F : Type*) (wires : ℕ) where
  | compute (gate : Gate F wires)
  | refresh (old : Fin wires)
  | sample (value : F)
universe u
/-- A chronological program with one fresh output per active operation. -/
inductive Program (F : Type u) (inputs : ℕ) : ℕ → Type u where
  | nil : Program F inputs 0
  | snoc {S : ℕ} (prior : Program F inputs S)
      (instruction : Instruction F (inputs+S)) : Program F inputs (S+1)
/-- A heterogeneous physical transition interface. The concrete strategy below supplies these distributions by the actual samplers. The conditional answer is derived from the joint transition, so it retains correlations with the new encoding. -/
structure Protocol (F E A : Type*) [Fintype E] [Fintype A] (inputs : ℕ) where
  real : (i : ℕ) → Instruction F (inputs+i) → (Fin i → A) →
    (Fin (inputs+i) → E) → FiniteDistribution (E × A)
namespace Protocol
variable {F E A : Type*} [Fintype E] [DecidableEq E] [Fintype A] {inputs S : ℕ}
/-- Execute the actual transitions in the physical forward order. -/
def realRunner (protocol : Protocol F E A inputs) :
    {S : ℕ} → Program F inputs S → Runner E A inputs S
  | 0, .nil => .nil
  | _+1, .snoc prior instruction => (protocol.realRunner prior).snoc
      (fun state => protocol.real _ instruction state.2 state.1)
end Protocol
/-- Regroup two strings per party into the computation phase ordering. -/
def answerRegroupForward (ML MR BL BR : Type*)
    (z : (ML × BL) × (MR × BR)) : (ML × MR) × (BL × BR) :=
  ((z.1.1,z.2.1),(z.1.2,z.2.2))

/- The inverse permutation is used by the detailed proof infrastructure. -/
def answerRegroup (ML MR BL BR : Type*) :
    ((ML × BL) × (MR × BR)) ≃ ((ML × MR) × (BL × BR)) where
  toFun := answerRegroupForward ML MR BL BR
  invFun z := ((z.1.1,z.2.1),(z.1.2,z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
variable {F ML MR BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
  {n t inputs : ℕ} {hdim : n*n+1 = n+t}
/-- A complete operation answer contains the two parties’ first and second answer strings. -/
abbrev Answer (ML MR BL BR : Type*) := (ML × MR) × (BL × BR)
/-- The complete rejected-matrix prefix together with its accepted square-matrix proposal. -/
abbrev MatrixTape (F : Type*) (n : ℕ) := StoppedTape (Matrix (Fin n) (Fin n) F)
/-- The complete rejected raw-pair prefix together with its accepted public encoding. -/
abbrev PublicTape (F : Type*) (n : ℕ) := StoppedTape (RawEncoding.Raw F n)
/-- The admissible deterministic local functions for all active operations. The computation field is exactly the rectangular-shortening implementation of the selector-core theorem. -/
structure Strategy (F ML MR BL BR : Type*) [Field F] [Fintype F] [DecidableEq F]
    [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
    (n t inputs : ℕ) (hdim : n*n+1 = n+t) where
  compute : Rectangular.FullyTapedStrategy F ML MR BL BR n t inputs hdim
  refreshLeft : (i : ℕ) → Fin (inputs+i) → (Fin i → Answer ML MR BL BR) →
    U F n → MatrixTape F n → ML × BL
  refreshRight : (i : ℕ) → Fin (inputs+i) → (Fin i → Answer ML MR BL BR) →
    U F n → MatrixTape F n → MR × BR
  publicLeft : (i : ℕ) → F → (Fin i → Answer ML MR BL BR) → PublicTape F n → ML × BL
  publicRight : (i : ℕ) → F → (Fin i → Answer ML MR BL BR) → U F n → MR × BR
namespace Strategy
/-- A raw square-matrix refresh. Both local functions inspect the same complete matrix tape and their own old share; their new shares are determined by these arguments. The two answers are selected in one phase. -/
def refreshExecution (strategy : Strategy F ML MR BL BR n t inputs hdim)
    (i : ℕ) (port : Fin (inputs+i)) (history : Fin i → Answer ML MR BL BR)
    (old : U F n × U F n) : FiniteDistribution ((U F n × U F n) × Answer ML MR BL BR) :=
  toFinite ((distribution (FiniteDistribution.uniform :
      FiniteDistribution (Matrix (Fin n) (Fin n) F)) invertibleTest
        (matrixAcceptancePositive (F := F) n)).map fun tape =>
    let M := matrixReturned tape.2.2
    ((rowRefresh old.1 M,columnRefresh old.2 M),
      answerRegroupForward ML MR BL BR
        (strategy.refreshLeft i port history old.1 tape,
         strategy.refreshRight i port history old.2 tape)))
/-- Direct public sampling under leakage. The left party samples the full raw pair and retains every rejected proposal; the right sees its received share. The label is fixed public data and never changes along the comparison. -/
def publicExecution (strategy : Strategy F ML MR BL BR n t inputs hdim) (hn : 2 ≤ n)
    (i : ℕ) (value : F) (history : Fin i → Answer ML MR BL BR) :
    FiniteDistribution ((U F n × U F n) × Answer ML MR BL BR) :=
  toFinite ((RawEncoding.tapeDistribution hn value).map fun tape =>
    let output := (RawEncoding.returned hn value tape.2.2).val
    ((output.L,output.R),answerRegroupForward ML MR BL BR
      (strategy.publicLeft i value history tape,
       strategy.publicRight i value history output.R)))
/-- The actual physical operation distribution. Only selected predecessor encodings are passed to the local functions; public sampling receives no old encoding. -/
def protocol (strategy : Strategy F ML MR BL BR n t inputs hdim) (hn : 2 ≤ n) :
    Protocol F (U F n × U F n) (Answer ML MR BL BR) inputs where
  real i instruction history old := match instruction with
    | .compute gate =>
        (strategy.compute.directRawExecution hn i gate history
          ((stateEquivProd F n).symm (old gate.left))
          ((stateEquivProd F n).symm (old gate.right))).map
            (fun z => (stateEquivProd F n z.1,z.2))
    | .refresh port => strategy.refreshExecution i port history (old port)
    | .sample value => strategy.publicExecution hn i value history
end Strategy
end CircuitCompiler.Operations
end
end Operations

section AdaptiveCompiler

section AdaptiveCanonical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
namespace Compiler.Adaptive
open Refresh CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution
universe u v
/-- A chronological canonical experiment with P initial wires and one newly sampled wire per operation. The new wire's law may depend on earlier answers, while the answer may depend on all allocated wires. -/
inductive Plan (E : Type u) (A : Type v) [Fintype E] [Fintype A] (P : ℕ) : ℕ → Type (max u v) where
  | nil : Plan E A P 0
  | snoc {S : ℕ} (prior : Plan E A P S)
      (output : (Fin S → A) → FiniteDistribution E)
      (answer : RunState E A P S → E → FiniteDistribution A) : Plan E A P (S+1)
namespace Plan
variable {E A : Type*} [Fintype E] [Fintype A] {P S : ℕ}
/-- The actual forward sampler: sample the fresh encoding using the incoming history, then its conditional leakage answer. -/
def runner : {S : ℕ} → Plan E A P S → Runner E A P S
  | 0, .nil => .nil
  | _+1, .snoc prior output answer => prior.runner.snoc
      (fun state => (output state.2).joint (answer state))
/-- Along one formal transcript, retain the initial laws and the law prescribed when each later wire was produced. -/
def wireLaws (initial : Fin P → FiniteDistribution E) :
    {S : ℕ} → Plan E A P S → (Fin S → A) → Fin (P+S) → FiniteDistribution E
  | 0, .nil, _ => initial
  | _+1, .snoc prior output _, z =>
      Fin.snoc (prior.wireLaws initial (Fin.init z)) (output (Fin.init z))
/-- The true conditional answer factors at every position along a complete formal transcript and encoding assignment. -/
def factors : {S : ℕ} → Plan E A P S →
    (Fin (P+S) → E) → (Fin S → A) → Fin S → ℝ
  | 0, .nil, _, _ => Fin.elim0
  | _+1, .snoc prior _ answer, e, z =>
      Fin.snoc (prior.factors (Fin.init e) (Fin.init z))
        ((answer (Fin.init e, Fin.init z) (e (Fin.last _))).weight (z (Fin.last _)))
end Plan
end Compiler.Adaptive
end
end AdaptiveCanonical
section AdaptiveModel
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
namespace Compiler.Adaptive
open Refresh CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution CircuitCompiler.AveragedEnergyComparison

variable {W E A F : Type*} [Fintype W] [DecidableEq W] [Fintype E] [Fintype A]
  {S : ℕ} {scope : Fin S → Finset W}
/-- A concrete causal realization allocates one new wire per operation after a fixed initial boundary. The wire equivalence permits arbitrary mathematical wire names. Its two identities connect the forward sampler to the history-dependent encoding laws and the actual scoped answer probabilities. -/
structure Realization (network : ScopedProbabilities (E := E) (A := A) scope)
    (law : F → FiniteDistribution E) (label : (Fin S → A) → W → F) where
  inputs : ℕ
  addresses : Fin (inputs+S) ≃ W
  initial : Fin inputs → FiniteDistribution E
  plan : Plan E A inputs S
  wire_laws : ∀ z j, plan.wireLaws initial z j = law (label z (addresses j))
  answer_factors : ∀ e z i, plan.factors e z i =
    network.prob i ((List.ofFn z).take i.val) (fun w => e (addresses.symm w)) (z i)
namespace Realization
variable {network : ScopedProbabilities (E := E) (A := A) scope}
  {law : F → FiniteDistribution E} {label : (Fin S → A) → W → F}
/-- The observable leakage transcript of the causal sampler, with all allocated encodings marginalized. -/
def transcript (r : Realization network law label) : FiniteDistribution (Fin S → A) :=
  (r.plan.runner.execute (independentDistribution r.initial)).map Prod.snd
end Realization
end Compiler.Adaptive
end
end AdaptiveModel
section AdaptiveProgram
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
namespace Compiler.Adaptive
open Refresh CircuitCompiler CircuitCompiler.Operations CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution CircuitCompiler.AveragedEnergyComparison

variable {F E A : Type*} {P S : ℕ}
/-- An online sampler policy supplies the public bit using only the complete incoming answer vector at that position. Values at refresh and computation positions are ignored. -/
abbrev SampleValues (F A : Type*) (S : ℕ) := (i : Fin S) → (Fin i.val → A) → F
/-- Substitute a public sampling value without changing any operation's predecessor ports or gate kind. -/
def selectInstruction {wires : ℕ} (instruction : Instruction F wires) (value : F) :
    Instruction F wires :=
  match instruction with
  | .sample _ => .sample value
  | .refresh old => .refresh old
  | .compute gate => .compute gate
variable [Fintype E] [DecidableEq E] [Fintype A]
/-- Execute the real physical operations, substituting an online public value immediately before its sampler runs. -/
def realRunner (protocol : Operations.Protocol F E A P) :
    {S : ℕ} → Operations.Program F P S → SampleValues F A S → Runner E A P S
  | 0, .nil, _ => .nil
  | _+1, .snoc prior instruction, values =>
      (realRunner protocol prior (fun i => values i.castSucc)).snoc
        (fun state => protocol.real _
          (selectInstruction instruction (values (Fin.last _) state.2)) state.2 state.1)
end Compiler.Adaptive
end
end AdaptiveProgram
end AdaptiveCompiler

/-!
# Compiler model

The public model collects the NAND source, its input-port refresh-chain compilation and physical view, the causal execution interface, and the stateful extension. Its encoding, sampling, execution, and local-interface definitions appear above the model. Small construction certificates accompany those definitions. Its mathematical proofs are in Proofs.Compiler.

The main theorem statement will appear below. The proof environment uses an independent data-only copy and proves the theorem without importing this reference file.
-/

section DirectSource

/-!
## NAND sources for the direct compiler

A source is a chronological NAND program. Operand positions may repeat and may have arbitrary fanout; zero source gates and empty output tuples are allowed. Public values are part of the source, while private inputs are supplied separately. Basis conversion is the mathematical preprocessing described in the paper and is outside this interface.

The source has no selector, control, offset, positive-size, or fanout hypothesis. Its designated output list may repeat positions and may directly name input wires. The compiler will insert distinct refreshed encodings at the two input-port occurrences of each NAND gate.
-/

set_option autoImplicit false
noncomputable section

namespace Compiler.Direct

/-- A chronological NAND program with the given input and source-gate counts; both operand addresses precede their new output. -/
inductive NandProgram (inputs : ℕ) : ℕ → Type where
  | nil : NandProgram inputs 0
  | snoc {gates : ℕ} (prior : NandProgram inputs gates)
      (left right : Fin (inputs+gates)) : NandProgram inputs (gates+1)

namespace NandProgram

/-- Evaluate every original source wire, keeping the input prefix and appending one NAND value at each source gate. -/
def eval {inputs : ℕ} (input : Fin inputs → Refreshing.Bit) :
    {gates : ℕ} → NandProgram inputs gates → Fin (inputs+gates) → Refreshing.Bit
  | 0, .nil => input
  | _+1, .snoc prior left right =>
      let old := prior.eval input
      Fin.snoc old (1+old left*old right)

end NandProgram

/-- A direct source has P private inputs, U public inputs or constants, T NAND gates, and k designated output positions; no output encoding is disclosed. -/
structure Source (privateInputs publicInputs gates outputs : ℕ) where
  program : NandProgram (privateInputs+publicInputs) gates
  publicValues : Fin publicInputs → Refreshing.Bit
  outputWires : Fin outputs → Fin (privateInputs+publicInputs+gates)

namespace Source

variable {P U T k : ℕ} (source : Source P U T k)

/-- Assemble the source input from the actual private values and fixed public values, without dropping unused or directly disclosed inputs. -/
def input (privateValues : Fin P → Refreshing.Bit) : Fin (P+U) → Refreshing.Bit :=
  Fin.addCases privateValues source.publicValues

/-- The plaintext carried by each original source wire during this single evaluation. -/
def evaluate (privateValues : Fin P → Refreshing.Bit) : Fin (P+U+T) → Refreshing.Bit :=
  source.program.eval (source.input privateValues)

/-- The authorized output tuple preserves its original order, repetitions, and direct input positions. -/
def outputValues (privateValues : Fin P → Refreshing.Bit) (j : Fin k) : Refreshing.Bit :=
  source.evaluate privateValues (source.outputWires j)

end Source
end Compiler.Direct
end
end DirectSource

section DirectProgram

/-!
## Executable input-port refresh chains

Public samplers run first. Each source NAND then refreshes its left current chain endpoint, refreshes its right updated endpoint, and computes on the two fresh encodings. The second refresh follows the first when the source operands coincide. Thus repeated source operands still receive distinct computation inputs. Original source-wire addresses are retained separately for the hidden trusted decoder.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Compiler.Direct
open CircuitCompiler

/-- A compilation prefix contains its actual physical program, exact operation count, original source-wire locations, and current endpoints of the input-port refresh chains. -/
structure Compilation (privateInputs publicInputs sourceGates : ℕ) where
  operations : ℕ
  program : Operations.Program Refreshing.Bit privateInputs operations
  count : operations=publicInputs+3*sourceGates
  original : Fin (privateInputs+publicInputs+sourceGates) → Fin (privateInputs+operations)
  live : Fin (privateInputs+publicInputs+sourceGates) → Fin (privateInputs+operations)

namespace Compilation

/-- One direct public sampler per supplied public input or constant, in its fixed public order. -/
def publicProgram {P : ℕ} : {U : ℕ} → (Fin U → Refreshing.Bit) → Operations.Program Refreshing.Bit P U
  | 0, _ => .nil
  | u+1, values => (publicProgram (fun i => values i.castSucc)).snoc
      (.sample (values (Fin.last u)))

/-- Initially the trusted private prefix is followed by the freshly sampled public inputs; every original input is its own current chain endpoint. -/
def initial {P U : ℕ} (values : Fin U → Refreshing.Bit) : Compilation P U 0 where
  operations := U
  program := publicProgram values
  count := by simp
  original := id
  live := id

variable {P U T : ℕ}

/-- Append the left refresh, right refresh, and protected NAND of one source gate, updating each selected source-wire chain exactly once per input-port occurrence. -/
def step (state : Compilation P U T) (left right : Fin (P+U+T)) : Compilation P U (T+1) :=
  let N := P+state.operations
  let afterLeft : Fin (P+U+T) → Fin (N+1) :=
    fun w => if w=left then Fin.last N else (state.live w).castSucc
  let afterRight : Fin (P+U+T) → Fin (N+1+1) :=
    fun w => if w=right then Fin.last (N+1) else (afterLeft w).castSucc
  { operations := state.operations+3
    program := ((state.program.snoc (.refresh (state.live left))).snoc
      (.refresh (afterLeft right))).snoc
        (.compute ⟨.complement 1,(Fin.last N).castSucc,Fin.last (N+1)⟩)
    count := by have h := state.count; omega
    original := Fin.lastCases (Fin.last (N+1+1))
      (fun w => (state.original w).castSucc.castSucc.castSucc)
    live := Fin.lastCases (Fin.last (N+1+1)) (fun w => (afterRight w).castSucc) }

end Compilation

namespace NandProgram

/-- Compile the actual source syntax, retaining all input wires even when no gate uses them. -/
def compile {P U : ℕ} (publicValues : Fin U → Refreshing.Bit) :
    {T : ℕ} → NandProgram (P+U) T → Compilation P U T
  | 0, .nil => Compilation.initial publicValues
  | _+1, .snoc prior left right => (prior.compile publicValues).step left right

end NandProgram

namespace Source
variable {P U T k : ℕ} (source : Source P U T k)

/-- The executable direct compiler and both address maps, fixed solely by the public source description. -/
def compilation : Compilation P U T := source.program.compile source.publicValues

/-- Every source gate contributes one NAND and two port refreshes; every public input contributes one sampler. -/
def operationCount : ℕ := source.compilation.operations

/-- Its trusted boundary contains precisely the P private input encodings. -/
def compiledProgram : Operations.Program Refreshing.Bit P source.operationCount := source.compilation.program

/-- Designated source outputs are read from their original encoding locations, preserving aliases while keeping those pairs hidden. -/
def outputSlot (j : Fin k) : Fin (P+source.operationCount) :=
  source.compilation.original (source.outputWires j)

/-- The number of persistent encoding locations allocated during this evaluation is P + S. -/
def wireCount : ℕ := P+source.operationCount

end Source
end Compiler.Direct
end
end DirectProgram

section DirectExecution

/-!
## Physical execution and the trusted plaintext decoder

The direct protocol initializes only private input encodings and then runs its actual heterogeneous instruction program. The same complete rejected proposal tapes and phase-local leakage callbacks as in the common physical implementation are used. A computation is NAND and has two phases; each input-port refresh and public sampler has one phase. Unrelated retained encodings never enter a callback.

The only visible output after all answers is the tuple of plaintext bits obtained by the trusted decoder. The wire-share array and output encoding pairs are absent from the view. The simulated view executes zero private input encodings, discards every resulting pair, and reports its supplied authorized output.
-/

set_option autoImplicit false
noncomputable section

namespace Compiler.Direct
open CircuitCompiler

variable {P U T k : ℕ}

/-- The complete leakage transcript has one answer for every actual computation, input-port refresh, and public sampler. -/
abbrev History (source : Source P U T k) (ml sl : ℕ) :=
  Composition.Answers (Compiler.Answer ml sl) source.operationCount

/-- The observable view is the entire leakage transcript and the plaintext output tuple; it contains no wire-share pair. -/
abbrev View (source : Source P U T k) (ml sl : ℕ) :=
  History source ml sl × (Fin k → Refreshing.Bit)

/-- Admissible deterministic callbacks read exactly the active operation's permitted local data. Only the P private inputs are trusted initial encodings. -/
abbrev Strategy (_source : Source P U T k) (n ml sl : ℕ) :=
  CircuitCompiler.Operations.Strategy Refreshing.Bit
    (Refreshing.LeakageOutput ml) (Refreshing.LeakageOutput ml) (Refreshing.LeakageOutput sl) (Refreshing.LeakageOutput sl)
    n (shorteningExtra n) P (longDimension n)

/-- Initialize the actual private values and execute all public samplers, ordinary refreshes and protected NAND computations in their compiled chronological order. -/
def runState {source : Source P U T k} {n ml sl : ℕ}
    (strategy : Strategy source n ml sl) (hn : 2≤n) (privateValues : Fin P → Refreshing.Bit) :=
  ((strategy.protocol hn).realRunner source.compiledProgram).execute
    (Sampling.Unbounded.toFinite (Sampling.RawEncoding.initializeShares hn privateValues))

/-- Forget the retained encodings and keep only the complete leakage answers. Unused private inputs and hidden output pairs are not additional observations. -/
def transcript {source : Source P U T k} {n ml sl : ℕ}
    (strategy : Strategy source n ml sl) (hn : 2≤n) (privateValues : Fin P → Refreshing.Bit) :
    Refresh.FiniteDistribution (History source ml sl) :=
  (runState strategy hn privateValues).map fun state =>
    Composition.vectorToAnswers _ _ state.2

/-- The trusted decoder reads the designated original source-wire encodings and returns only their inner products. -/
def decode (source : Source P U T k) {n : ℕ}
    (wires : Fin (P+source.operationCount) → Refreshing.Share n × Refreshing.Share n) (j : Fin k) : Refreshing.Bit :=
  Refreshing.secret (wires (source.outputSlot j))

/-- The real physical view includes the trusted decoder result only after all local leakage answers have been produced. -/
def realView {source : Source P U T k} {n ml sl : ℕ}
    (strategy : Strategy source n ml sl) (hn : 2≤n) (privateValues : Fin P → Refreshing.Bit) :
    Refresh.FiniteDistribution (View source ml sl) :=
  (runState strategy hn privateValues).map fun state =>
    (Composition.vectorToAnswers _ _ state.2,decode source state.1)

/-- The output-only target runs the same protocol with every private input set to zero, discards the dummy output encodings, and appends the supplied plaintext output. -/
def simulatedView {source : Source P U T k} {n ml sl : ℕ}
    (strategy : Strategy source n ml sl) (hn : 2≤n) (authorizedOutput : Fin k → Refreshing.Bit) :
    Refresh.FiniteDistribution (View source ml sl) :=
  (transcript strategy hn (fun _=>0)).map fun history=>(history,authorizedOutput)

end Compiler.Direct
end
end DirectExecution

section StatefulSource

/-!
## Stateful NAND source circuits

The transition circuit consumes the current private register state, a public input, and fixed public constants. Its designated wires specify the next state and the public output. Register and output positions may repeat or directly name inputs. The ideal oracle retains the private state between requests.
-/

set_option autoImplicit false
noncomputable section

namespace Compiler.Stateful
open Compiler.Direct

/-- A stateful transition circuit in the NAND source model of Sec. 6.3. The initial state is supplied separately and is not part of the public source. -/
structure Circuit (stateBits inputBits constants gates outputBits : ℕ) where
  program : NandProgram (stateBits+inputBits+constants) gates
  constantValues : Fin constants → Refreshing.Bit
  nextState : Fin stateBits → Fin (stateBits+inputBits+constants+gates)
  outputs : Fin outputBits → Fin (stateBits+inputBits+constants+gates)

namespace Circuit
variable {m d c g k : ℕ} (circuit : Circuit m d c g k)

/-- Evaluate all wires of one transition on the supplied register state and public input. -/
def values (state : Fin m → Refreshing.Bit) (input : Fin d → Refreshing.Bit) : Fin (m+d+c+g) → Refreshing.Bit :=
  circuit.program.eval (Fin.addCases (Fin.addCases state input) circuit.constantValues)

/-- The private state retained for the next invocation. -/
def step (state : Fin m → Refreshing.Bit) (input : Fin d → Refreshing.Bit) : Fin m → Refreshing.Bit :=
  fun j => circuit.values state input (circuit.nextState j)

/-- The authorized plaintext output of one invocation. -/
def output (state : Fin m → Refreshing.Bit) (input : Fin d → Refreshing.Bit) : Fin k → Refreshing.Bit :=
  fun j => circuit.values state input (circuit.outputs j)

/-- The ideal state after a chronological list of public requests. This definition does not expose any encoding or leakage. -/
def afterInputs (initial : Fin m → Refreshing.Bit) (inputs : List (Fin d → Refreshing.Bit)) : Fin m → Refreshing.Bit :=
  inputs.foldl circuit.step initial

/-- Oracle access to the ideal stateful circuit: after earlier requests, submit the current input and receive only its authorized output. -/
def oracle (initial : Fin m → Refreshing.Bit) (earlier : List (Fin d → Refreshing.Bit)) (input : Fin d → Refreshing.Bit) : Fin k → Refreshing.Bit :=
  circuit.output (circuit.afterInputs initial earlier) input

/-- The ideal private state after a chronological public-input stream has been used for the stated number of invocations. -/
def stateAt (initial : Fin m → Refreshing.Bit) (inputs : ℕ → Fin d → Refreshing.Bit) : ℕ → Fin m → Refreshing.Bit
  | 0 => initial
  | t+1 => circuit.step (stateAt initial inputs t) (inputs t)

/-- The ideal public output at one position of that stream. -/
def outputAt (initial : Fin m → Refreshing.Bit) (inputs : ℕ → Fin d → Refreshing.Bit) (t : ℕ) : Fin k → Refreshing.Bit :=
  circuit.output (circuit.stateAt initial inputs t) (inputs t)

/-- The total operation count after T invocations, with public constants sampled only once. -/
def operationCount (_circuit : Circuit m d c g k) (T : ℕ) : ℕ := 3*T*g+T*d+c

/-- Every invocation evaluates four leakage strings per NAND and two per input-port refresh or public sampler. -/
def callbackCount (_circuit : Circuit m d c g k) (T : ℕ) : ℕ := 8*T*g+2*(T*d+c)

end Circuit
end Compiler.Stateful
end
end StatefulSource

section StatefulProgram

/-!
## Interleaving public samplers and NAND gates

The stateful execution samples constants once and the next invocation's public input only when that invocation begins. A chronological source schedule supports these interleavings. Its NAND compilation reuses the same two input-port refreshes and protected computation as Compiler.Direct, with one shared live chain per logical source wire across all invocations.
-/

set_option autoImplicit false
noncomputable section

namespace Compiler.Direct.Compilation
open CircuitCompiler

/-- Append a leaky public sampler after any compiled prefix. The logical and physical fresh slots are appended chronologically; the old chain endpoints are preserved. -/
def publicStep {P U T : ℕ} (state : Compilation P U T) : Compilation P (U+1) T :=
  let rename : Fin (P+(U+1)+T) → Fin (P+U+T+1) := Fin.cast (by omega)
  { operations := state.operations+1
    program := state.program.snoc (.sample 0)
    count := by have h := state.count; omega
    original := fun w => Fin.lastCases (Fin.last (P+state.operations))
      (fun j => (state.original j).castSucc) (rename w)
    live := fun w => Fin.lastCases (Fin.last (P+state.operations))
      (fun j => (state.live j).castSucc) (rename w) }

end Compiler.Direct.Compilation

namespace Compiler.Stateful
open Compiler.Direct

universe u

/-- A chronological NAND source with tagged public samplers. Its indices count the public samplers and NAND gates already appended, independently of their interleaving. -/
inductive Schedule (J : Type u) (P : ℕ) : ℕ → ℕ → Type u where
  | nil : Schedule J P 0 0
  | sample {U T : ℕ} (prior : Schedule J P U T) (tag : J) : Schedule J P (U+1) T
  | nand {U T : ℕ} (prior : Schedule J P U T)
      (left right : Fin (P+U+T)) : Schedule J P U (T+1)

namespace Schedule
variable {J : Type*} {P U T : ℕ}

/-- Compile the interleaved source. Public sampler values are zero placeholders subsequently supplied by the causal online policy. The wiring, fresh slots, and refresh chains are fixed. -/
def compile : {U T : ℕ} → Schedule J P U T → Compilation P U T
  | _, _, .nil => Compilation.initial Fin.elim0
  | _, _, .sample prior _ => prior.compile.publicStep
  | _, _, .nand prior left right => prior.compile.step left right

/-- Append a block of public samplers in its stated input order. -/
def appendSamples (schedule : Schedule J P U T) :
    {d : ℕ} → (Fin d → J) → Schedule J P (U+d) T
  | 0, _ => schedule
  | d+1, tags => (appendSamples schedule (fun i => tags i.castSucc)).sample (tags (Fin.last d))

/-- A first block of public samplers, with no arithmetic transport on its sampler count. -/
def initialSamples : {d : ℕ} → (Fin d → J) → Schedule J P d 0
  | 0, _ => .nil
  | d+1, tags => (initialSamples (fun j => tags j.castSucc)).sample (tags (Fin.last d))

/-- An ordinary source NAND program embedded after a chronological prefix, together with the addresses of all its source wires. -/
structure GateExtension (J : Type*) (P U T inputs gates : ℕ) where
  schedule : Schedule J P U (T+gates)
  wires : Fin (inputs+gates) → Fin (P+U+(T+gates))

/-- Append a transition's NAND syntax, renaming its inputs to the existing state, fresh public inputs, and persistent constants. -/
def appendGates {inputs : ℕ} (schedule : Schedule J P U T)
    (input : Fin inputs → Fin (P+U+T)) :
    {g : ℕ} → NandProgram inputs g → GateExtension J P U T inputs g
  | 0, .nil => ⟨schedule, input⟩
  | _+1, .snoc prior left right =>
      let previous := appendGates schedule input prior
      { schedule := previous.schedule.nand (previous.wires left) (previous.wires right)
        wires := Fin.snoc (fun w => (previous.wires w).castSucc) (Fin.last _) }

/-- The public sampler tag at a chronological physical position; refreshes and NANDs have no tag. Positions beyond the prefix return none. -/
def sampleAt : {U T : ℕ} → Schedule J P U T → ℕ → Option J
  | _, _, .nil, _ => none
  | _, _, .sample prior tag, i =>
      if i = prior.compile.operations then some tag else prior.sampleAt i
  | _, _, .nand prior _ _, i => prior.sampleAt i

/-- Ordinary plaintext evaluation of the interleaved source for fixed public tag values. These values are instantiated separately along each formal transcript in the online proof. -/
def evaluate (input : Fin P → Refreshing.Bit) (publicValues : J → Refreshing.Bit) :
    {U T : ℕ} → Schedule J P U T → Fin (P+U+T) → Refreshing.Bit
  | _, _, .nil => input
  | U+1, T, .sample prior tag =>
      fun w => Fin.snoc (α := fun _ => Refreshing.Bit) (evaluate input publicValues prior)
        (publicValues tag) (Fin.cast (by omega) w)
  | _, _, .nand prior left right =>
      let old := evaluate input publicValues prior
      Fin.snoc old (1+old left*old right)

end Schedule

/-- Public constants and invocation-indexed public input bits are the only sampler tags. -/
abbrev PublicPort (constants inputBits invocations : ℕ) :=
  Fin constants ⊕ (Fin invocations × Fin inputBits)

/-- The number of public samplers in a prefix, counting constants once. The recursive form keeps the unrolled source's chronological types simple. -/
def publicCount (constants inputBits : ℕ) : ℕ → ℕ
  | 0 => constants
  | t+1 => publicCount constants inputBits t + inputBits

/-- The number of source NAND gates in a prefix of invocations. -/
def gateCount (gates : ℕ) : ℕ → ℕ
  | 0 => 0
  | t+1 => gateCount gates t + gates

/-- A prefix of the unrolled stateful source, including the current register addresses, persistent constant addresses, and every output position already designated. -/
structure Unrolling {m d c g k : ℕ} (_circuit : Circuit m d c g k) (invocations done : ℕ) where
  schedule : Schedule (PublicPort c d invocations) m (publicCount c d done) (gateCount g done)
  state : Fin m → Fin (m+publicCount c d done+gateCount g done)
  constants : Fin c → Fin (m+publicCount c d done+gateCount g done)
  outputs : Fin done → Fin k → Fin (m+publicCount c d done+gateCount g done)

namespace Circuit
variable {m d c g k : ℕ} (circuit : Circuit m d c g k)

/-- Before the first invocation, sample the constants once and retain the trusted register-state input slots. -/
def initialUnrolling (invocations : ℕ) : Unrolling circuit invocations 0 where
  schedule := Schedule.initialSamples (fun j : Fin c => Sum.inl j)
  state j := Fin.castAdd c j
  constants j := Fin.natAdd m j
  outputs := Fin.elim0

/-- Append one invocation, feeding the preceding registers into the transition and retaining its designated next-state wires. Old outputs remain designated only for the trusted decoder. -/
def nextUnrolling {invocations done : ℕ} (previous : Unrolling circuit invocations done)
    (h : done < invocations) : Unrolling circuit invocations (done+1) :=
  let U := publicCount c d done
  let G := gateCount g done
  let inputs := previous.schedule.appendSamples
    (fun j : Fin d => Sum.inr (⟨done,h⟩,j))
  let old : Fin (m+U+G) → Fin (m+(U+d)+G) :=
    fun w => Fin.castLE (by omega) w
  let fresh : Fin d → Fin (m+(U+d)+G) :=
    fun j => ⟨m + U + G + j.val, by have := j.isLt; omega⟩
  let ports : Fin (m+d+c) → Fin (m+(U+d)+G) :=
    Fin.addCases (Fin.addCases (fun j => old (previous.state j)) fresh)
      (fun j => old (previous.constants j))
  let extended := inputs.appendGates ports circuit.program
  let retained : Fin (m+U+G) → Fin (m+(U+d)+(G+g)) :=
    fun w => Fin.castLE (by omega) w
  { schedule := extended.schedule
    state := fun j => extended.wires (circuit.nextState j)
    constants := fun j => retained (previous.constants j)
    outputs := Fin.snoc (fun t j => retained (previous.outputs t j))
      (fun j => extended.wires (circuit.outputs j)) }

/-- Unroll any finite number of invocations while preserving their public-input sampling times and state feedback. -/
def unrollPrefix (invocations : ℕ) : (done : ℕ) → done ≤ invocations → Unrolling circuit invocations done
  | 0, _ => circuit.initialUnrolling invocations
  | done+1, h => circuit.nextUnrolling
      (unrollPrefix invocations done (Nat.le_of_succ_le h)) (Nat.lt_of_succ_le h)

/-- The complete chronological stateful source for the requested number of invocations. -/
def unrolling (invocations : ℕ) : Unrolling circuit invocations invocations :=
  circuit.unrollPrefix invocations invocations (le_refl _)

end Circuit
end Compiler.Stateful
end
end StatefulProgram

section StatefulInteraction

/-!
## Public interaction at invocation boundaries

The deterministic adversary chooses each input from earlier leakage and earlier input/output records. An oracle returns only the authorized plaintext output for the request history. The recursive public records are a denotational description of that interaction: request t uses leakage strictly before its invocation and outputs from invocations strictly before t. The simulator can evaluate these functions with a cache of the responses already released, without knowing the oracle's private state.
-/

set_option autoImplicit false
noncomputable section

namespace Compiler.Stateful
open Compiler.Direct

/-- An ideal interface returns the current output on the chronological request history, without exposing a register state. -/
abbrev Oracle (d k : ℕ) := List (Fin d → Refreshing.Bit) → (Fin d → Refreshing.Bit) → (Fin k → Refreshing.Bit)

/-- The adversary's deterministic input choice. A fixed auxiliary input and random tape can be captured by this function. -/
abbrev InputChoice (A : Type*) (d k : ℕ) :=
  ℕ → List A → List ((Fin d → Refreshing.Bit) × (Fin k → Refreshing.Bit)) → (Fin d → Refreshing.Bit)

/-- Physical operation index at which an invocation starts. Constants are sampled before invocation zero. -/
def startTime (c d g t : ℕ) : ℕ := c+t*(d+3*g)

/-- Reconstruct only the already authorized public records. At step t, choose x_t using the leakage prefix at its start, then obtain y_t from the ideal oracle. Later policies use that response only after the invocation has finished. -/
def records {A : Type*} {d k : ℕ} (c g : ℕ) (choose : InputChoice A d k)
    (oracle : Oracle d k) (history : List A) : ℕ → List ((Fin d → Refreshing.Bit) × (Fin k → Refreshing.Bit))
  | 0 => []
  | t+1 =>
    let prior := records c g choose oracle history t
    let input := choose t (history.take (startTime c d g t)) prior
    prior ++ [(input,oracle (prior.map Prod.fst) input)]

/-- Public input of invocation t, selected before any operation of that invocation. -/
def inputAt {A : Type*} {d k : ℕ} (c g : ℕ) (choose : InputChoice A d k)
    (oracle : Oracle d k) (history : List A) (t : ℕ) : Fin d → Refreshing.Bit :=
  choose t (history.take (startTime c d g t)) (records c g choose oracle history t)

/-- The public request/response record of invocation t. Only its output component requires the ideal oracle. -/
def recordAt {A : Type*} {d k : ℕ} (c g : ℕ) (choose : InputChoice A d k)
    (oracle : Oracle d k) (history : List A) (t : ℕ) : (Fin d → Refreshing.Bit) × (Fin k → Refreshing.Bit) :=
  let input := inputAt c g choose oracle history t
  (input,oracle ((records c g choose oracle history t).map Prod.fst) input)

/-- How many invocation outputs have been released by an operation's incoming physical index. Zero-operation transitions also have a well-defined boundary. -/
def completed (c d g : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | T+1, i => if startTime c d g (T+1) ≤ i then T+1 else completed c d g T i

/-- How many public inputs have been announced by an incoming operation index. -/
def started (c d g : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | T+1, i => if startTime c d g T ≤ i then T+1 else started c d g T i

/-- The public information available when a local leakage function is chosen. Share encodings and unpublished output values are absent. -/
structure PublicHistory (d k : ℕ) where
  inputs : List (Fin d → Refreshing.Bit)
  outputs : List (Fin k → Refreshing.Bit)

/-- Extract the public inputs already announced and the outputs already released. Responses are used only at completed invocation boundaries. -/
def publicHistory {A : Type*} {d k : ℕ} (c g T : ℕ) (choose : InputChoice A d k)
    (oracle : Oracle d k) (history : List A) : PublicHistory d k where
  inputs := (List.range (started c d g T history.length)).map
    (inputAt c g choose oracle history)
  outputs := (records c g choose oracle history (completed c d g T history.length)).map Prod.snd

end Compiler.Stateful
end
end StatefulInteraction

section StatefulExecution

/-!
## Stateful physical execution and its oracle simulator

The initial register state is the only trusted private encoding boundary. Public constants and invocation inputs use the leaky sampler at their chronological positions. The adversary's local callbacks receive the previously published inputs and outputs as well as the existing leakage prefix. A fixed auxiliary input and tape are captured in the adversary's functions.

The simulator below is a single function of an ideal oracle. It encodes zero registers once and runs the actual physical operations. Public responses are obtained from the oracle at invocation ends. The recursive public interface records past responses as a cache. No private initial state is an argument of the simulator. The real view uses the actual trusted decoder; its equality with the authorized oracle responses is proved separately.
-/

set_option autoImplicit false
noncomputable section
namespace Compiler.Stateful
open Refresh CircuitCompiler Compiler.Adaptive
  CircuitCompiler.Composition.TopologicalExecution
  CircuitCompiler.Sampling.Unbounded

/-- The physical leakage callbacks, with both phases and all rejected sampler tapes. -/
abbrev LocalStrategy (m n ml sl : ℕ) :=
  CircuitCompiler.Operations.Strategy Refreshing.Bit
    (Refreshing.LeakageOutput ml) (Refreshing.LeakageOutput ml) (Refreshing.LeakageOutput sl) (Refreshing.LeakageOutput sl)
    n (shorteningExtra n) m (longDimension n)

/-- An adaptive adversary chooses each invocation's public input and selects local leakage callbacks using already public information. Its fixed auxiliary input and random tape are part of these functions. -/
structure Adversary (m d k n ml sl : ℕ) where
  choose : InputChoice (Compiler.Answer ml sl) d k
  leakage : PublicHistory d k → LocalStrategy m n ml sl

namespace Adversary
variable {m d k n ml sl : ℕ}

/-- Flatten the already public interaction into ordinary incoming-history callbacks. Matrix-phase answers are still selected before observing either party's answer, and shortening may use the matrix-phase answer as before. -/
def strategy (adversary : Adversary m d k n ml sl) (c g T : ℕ) (oracle : Oracle d k) :
    LocalStrategy m n ml sl where
  compute := {
    matrixLeft := fun i gate history =>
      (adversary.leakage (publicHistory c g T adversary.choose oracle (List.ofFn history))).compute.matrixLeft i gate history
    matrixRight := fun i gate history =>
      (adversary.leakage (publicHistory c g T adversary.choose oracle (List.ofFn history))).compute.matrixRight i gate history
    left := fun i gate history =>
      (adversary.leakage (publicHistory c g T adversary.choose oracle (List.ofFn history))).compute.left i gate history
    right := fun i gate history =>
      (adversary.leakage (publicHistory c g T adversary.choose oracle (List.ofFn history))).compute.right i gate history }
  refreshLeft := fun i port history =>
    (adversary.leakage (publicHistory c g T adversary.choose oracle (List.ofFn history))).refreshLeft i port history
  refreshRight := fun i port history =>
    (adversary.leakage (publicHistory c g T adversary.choose oracle (List.ofFn history))).refreshRight i port history
  publicLeft := fun i value history =>
    (adversary.leakage (publicHistory c g T adversary.choose oracle (List.ofFn history))).publicLeft i value history
  publicRight := fun i value history =>
    (adversary.leakage (publicHistory c g T adversary.choose oracle (List.ofFn history))).publicRight i value history

end Adversary

namespace Circuit
variable {m d c g k : ℕ} (circuit : Circuit m d c g k)

/-- The public bit selected immediately before a physical sampler. At all non-sampler positions the value is ignored. Invocation-tagged bits use the adversary's input choice on the incoming leakage prefix. -/
def sampleValues {n ml sl : ℕ} (T : ℕ) (adversary : Adversary m d k n ml sl)
    (oracle : Oracle d k) : SampleValues Refreshing.Bit (Compiler.Answer ml sl)
      (circuit.unrolling T).schedule.compile.operations :=
  fun i history => match (circuit.unrolling T).schedule.sampleAt i.val with
    | some (.inl j) => circuit.constantValues j
    | some (.inr (t,j)) => inputAt c g adversary.choose oracle (List.ofFn history) t.val j
    | none => 0

/-- All physical operations, with raw retries and a single trusted initialization. The oracle supplies only the already public interaction used by future policies. -/
def runState {n ml sl : ℕ} (T : ℕ) (adversary : Adversary m d k n ml sl)
    (hn : 2 ≤ n) (oracle : Oracle d k) (initial : Fin m → Refreshing.Bit) :=
  (Compiler.Adaptive.realRunner ((adversary.strategy c g T oracle).protocol hn)
    (circuit.unrolling T).schedule.compile.program (circuit.sampleValues T adversary oracle)).execute
      (toFinite (CircuitCompiler.Sampling.RawEncoding.initializeShares hn initial))

/-- The observable view contains all leakage answers and the chronological public input/output records. It contains no encoding pair. -/
abbrev View (T ml sl : ℕ) :=
  (Fin (circuit.unrolling T).schedule.compile.operations → Compiler.Answer ml sl) ×
    (Fin T → (Fin d → Refreshing.Bit) × (Fin k → Refreshing.Bit))

/-- Append the public interaction determined by this same leakage transcript and ideal oracle. -/
def observe {n ml sl : ℕ} (T : ℕ) (adversary : Adversary m d k n ml sl)
    (oracle : Oracle d k)
    (history : Fin (circuit.unrolling T).schedule.compile.operations → Compiler.Answer ml sl) :
    circuit.View T ml sl :=
  (history,fun t => recordAt c g adversary.choose oracle (List.ofFn history) t.val)

/-- The actual trusted decoder, evaluated on the designated original encoding of each invocation's output wire. Retaining inaccessible old locations in the mathematical array does not grant any callback access to them. -/
def decode {n : ℕ} (T : ℕ)
    (wires : Fin (m+(circuit.unrolling T).schedule.compile.operations) → U Refreshing.Bit n×U Refreshing.Bit n)
    (t : Fin T) (j : Fin k) : Refreshing.Bit :=
  Refreshing.secret
    (wires ((circuit.unrolling T).schedule.compile.original ((circuit.unrolling T).outputs t j)))

/-- The real view uses plaintext values decoded from the physical output encodings. Past decoder releases determine the public interaction used by the causal callbacks. -/
def realView {n ml sl : ℕ} (T : ℕ) (adversary : Adversary m d k n ml sl)
    (hn : 2 ≤ n) (initial : Fin m → Refreshing.Bit) : FiniteDistribution (circuit.View T ml sl) :=
  (circuit.runState T adversary hn (circuit.oracle initial) initial).map fun state =>
    (state.2,fun t =>
      ((recordAt c g adversary.choose (circuit.oracle initial) (List.ofFn state.2) t.val).1,
        circuit.decode T state.1 t))

/-- The simulator is independent of the private initial state. It runs the zero-register dummy execution and, at each invocation's end, queries the ideal oracle with that invocation's input and releases its authorized response. Dummy output values and encodings are omitted from the view. Encodings needed for the next state or later uses remain available internally and may be erased only after their last required use. This view projection does not model physical erasure. -/
def simulatedView {n ml sl : ℕ} (T : ℕ) (adversary : Adversary m d k n ml sl)
    (hn : 2 ≤ n) (oracle : Oracle d k) : FiniteDistribution (circuit.View T ml sl) :=
  (circuit.runState T adversary hn oracle (fun _ => 0)).map fun state =>
    circuit.observe T adversary oracle state.2

end Circuit
end Compiler.Stateful
end
end StatefulExecution

/-!
# Theorem 5.2 and supporting compiler statements

The main claim is the direct NAND compiler of Theorem 5.2. Its companion statements specify fixed-label and causal composition for Theorem 5.7 and continual stateful privacy for Theorem 6.1. Their intentional admissions are loaded only by Proofs.ReferenceClaims. Independent proofs are in Proofs.Compiler.DirectComposition, Proofs.Compiler.Direct, and Proofs.Compiler.Stateful.
-/

/-!
## Claims checked by the comparator

The four claim definitions below state fixed-label composition,
causal composition, direct compiler privacy, and stateful compiler privacy.
The only admitted main theorem in this file bundles them. Its independent
proof is under `Proofs/Compiler`.
-/

section CompilerClaims
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators Classical ENNReal

namespace Compiler.Direct
open Refresh MatrixRefresh CircuitCompiler CircuitCompiler.Composition
  CircuitCompiler.AveragedEnergyComparison
  CompilerProof.DirectComposition
def directCompositionClaim.{u,v} : Prop :=
  ∀ {W : Type u} {A : Type v} [Fintype W] [DecidableEq W] [Fintype A] [Nonempty A] {S n : ℕ} [Nonempty (U Refreshing.Bit n)] (hn : 2≤n) (scope : Fin S→Finset W)
    (network : ScopedProbabilities (E := U Refreshing.Bit n×U Refreshing.Bit n) (A := A) scope)
    (valid : (W→Refreshing.Bit)→Fin S→Prop) (approximated : Finset (Fin S))
    (data : LocalData scope network (encodingDistribution hn) valid approximated
      (betaParameter (Fintype.card (U Refreshing.Bit n):ℝ)) (rawErrorParameter (Fintype.card (U Refreshing.Bit n):ℝ)))
    (hports : ∀ i,(scope i).card≤3)
    (hdegree : ∀ w,(Finset.univ.filter (fun i=>w∈scope i)).card≤3)
    (hnonempty : ∀ i∈approximated,(scope i).Nonempty)
    (publicWires : Finset W) (hpublic : ∀ i,i∉approximated→scope i⊆publicWires)
    (first second : W→Refreshing.Bit)
    (hfirst : ∀ i∈approximated,valid first i)
    (hsecond : ∀ i∈approximated,valid second i)
    (hlabels : ∀ w∈publicWires,first w=second w)
    (P Q : FiniteDistribution (Fin S→A))
    (hP : ∀ z,P.weight z=canonicalWeight scope network (encodingDistribution hn) first z)
    (hQ : ∀ z,Q.weight z=canonicalWeight scope network (encodingDistribution hn) second z),
    Refresh.statisticalDistance P Q≤1000000*(S:ℝ)*(Fintype.card A:ℝ)^9*
      (Fintype.card (U Refreshing.Bit n):ℝ)^(-1/27:ℝ)

def adaptiveCompositionClaim.{u,v} : Prop :=
  ∀ {W : Type u} {A : Type v} [Fintype W] [DecidableEq W] [Fintype A] [Nonempty A] {S n : ℕ} [Nonempty (U Refreshing.Bit n)] (hn : 2 ≤ n) (scope : Fin S → Finset W)
    (network : ScopedProbabilities (E := U Refreshing.Bit n×U Refreshing.Bit n) (A := A) scope)
    (valid : (W → Refreshing.Bit) → Fin S → Prop) (approximated : Finset (Fin S))
    (data : LocalData scope network (encodingDistribution hn) valid approximated
      (betaParameter (Fintype.card (U Refreshing.Bit n):ℝ))
      (rawErrorParameter (Fintype.card (U Refreshing.Bit n):ℝ)))
    (hports : ∀ i, (scope i).card ≤ 3)
    (hdegree : ∀ w, (Finset.univ.filter (fun i => w ∈ scope i)).card ≤ 3)
    (hnonempty : ∀ i ∈ approximated, (scope i).Nonempty)
    (publicWires : Finset W) (hpublic : ∀ i, i ∉ approximated → scope i ⊆ publicWires)
    (first second : (Fin S → A) → W → Refreshing.Bit)
    (firstExecution : Compiler.Adaptive.Realization network (encodingDistribution hn) first)
    (secondExecution : Compiler.Adaptive.Realization network (encodingDistribution hn) second)
    (hfirst : ∀ z, ∀ i ∈ approximated, valid (first z) i)
    (hsecond : ∀ z, ∀ i ∈ approximated, valid (second z) i)
    (hlabels : ∀ z, ∀ w ∈ publicWires, first z w = second z w),
    Refresh.statisticalDistance firstExecution.transcript secondExecution.transcript ≤
      1000000*(S:ℝ)*(Fintype.card A:ℝ)^9*(Fintype.card (U Refreshing.Bit n):ℝ)^(-1/27:ℝ)

def directPrivacyClaim : Prop :=
  ∀  {P U T k n ml sl : ℕ} (source : Source P U T k)
    (strategy : Strategy source n ml sl) (hn : 2≤n) (input : Fin P → Refreshing.Bit),
    Refresh.statisticalDistance (realView strategy hn input)
      (simulatedView strategy hn (source.outputValues input)) ≤
      1000000*(source.operationCount:ℝ)*
        (((2 ^ (2 * (ml + sl)) : ℕ) : ℝ))^9*
        (((2 ^ n - 1 : ℕ) : ℝ))^(-1/27:ℝ)

end Compiler.Direct

namespace Compiler.Stateful
def statefulPrivacyClaim : Prop :=
  ∀  {m d c g k n ml sl : ℕ} (circuit : Circuit m d c g k)
    (T : ℕ) (adversary : Adversary m d k n ml sl) (hn : 2 ≤ n),
    ∃ simulate : Oracle d k → Refresh.FiniteDistribution (circuit.View T ml sl),
      simulate = circuit.simulatedView T adversary hn ∧
      ∀ initial : Fin m → Refreshing.Bit,
        Refresh.statisticalDistance (circuit.realView T adversary hn initial)
          (simulate (circuit.oracle initial)) ≤
          min 1 (1000000*(circuit.operationCount T:ℝ)*
            (((2 ^ (2 * (ml + sl)) : ℕ) : ℝ))^9*
            (((2 ^ n - 1 : ℕ) : ℝ))^(-1/27:ℝ))

end Compiler.Stateful
end
end CompilerClaims

/-! Proof-only bound names follow the reference claims so their numeral certificates do not alter the copied claim bodies. -/
noncomputable section
namespace Compiler.Direct
variable {P U T k : ℕ}
/-- The direct compiler's explicit finite privacy bound uses S = 3T + U operations, complete answer count K, and q = 2ⁿ − 1 nonzero shares. -/
def privacyBound (source : Source P U T k) (n ml sl : ℕ) : ℝ :=
  1000000*(source.operationCount:ℝ)*(Compiler.K (ml+sl):ℝ)^9*(Compiler.q n:ℝ)^(-1/27:ℝ)
end Compiler.Direct

namespace Compiler.Stateful.Circuit
variable {m d c g k : ℕ} (circuit : Compiler.Stateful.Circuit m d c g k)
/-- The explicit stateful privacy expression, with S = 3Tg+Td+c, K = 2²⁽ᵐˡ⁺ˢˡ⁾, and q = 2ⁿ−1. -/
def privacyBound (T n ml sl : ℕ) : ℝ :=
  1000000*(circuit.operationCount T:ℝ)*(Compiler.K (ml+sl):ℝ)^9*
    (Compiler.q n:ℝ)^(-1/27:ℝ)
end Compiler.Stateful.Circuit
end
