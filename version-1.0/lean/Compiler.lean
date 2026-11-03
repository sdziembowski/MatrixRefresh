import Refreshing
open scoped ENNReal

set_option autoImplicit false

/-!
# Compiler foundations

The compiler below is instantiated at `Refreshing.Bit = ZMod 2`. Its physical
gate helpers use a field parameter `F`: `V`, `U`, and `«GL»` reduce to the
carriers in `Refreshing.lean` when `F = ZMod 2`. The compiler helper `State`
has named left and right fields, while `Refreshing.State` is a pair.
-/

section Encodings

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
  sorry
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
namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Nonzero certificate for the left party's row after multiplication by the sampled invertible matrix. -/
abbrev rowRefresh_ne_zero {n : ℕ} (l : U F n) (M : «GL» F n) :
    Matrix.vecMul l.val M.val ≠ 0 := by
  sorry

def rowRefresh {n : ℕ} (l : U F n) (M : «GL» F n) : U F n :=
  ⟨Matrix.vecMul l.val M.val, rowRefresh_ne_zero l M⟩
/-- Nonzero certificate for the right party's column after multiplication by the inverse sampled matrix. -/
abbrev columnRefresh_ne_zero {n : ℕ} (r : U F n) (M : «GL» F n) :
    Matrix.mulVec (M⁻¹).val r.val ≠ 0 := by
  sorry

def columnRefresh {n : ℕ} (r : U F n) (M : «GL» F n) : U F n :=
  ⟨Matrix.mulVec (M⁻¹).val r.val, columnRefresh_ne_zero r M⟩
/-- The actual state update uses the same matrix on both sides. -/

def refresh {n : ℕ} (x : State F n) (M : «GL» F n) : State F n :=
  ⟨rowRefresh (stateLeftShare x) M, columnRefresh (stateRightShare x) M⟩
end Refresh
end Encodings

section FiniteProbability

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
/-- Nonnegativity and normalization of the point mass that assigns probability one to `a` and zero elsewhere. -/
def pure_valid [DecidableEq α] (a : α) :
    (∀ b, 0 ≤ (if b = a then (1 : ℝ) else 0)) ∧
    (∑ b, (if b = a then (1 : ℝ) else 0)) = 1 := by
  sorry
noncomputable def pure (a : α) : FiniteDistribution α :=
  letI : DecidableEq α := Classical.decEq α
  ⟨(fun b => if b = a then 1 else 0), (pure_valid a).1, (pure_valid a).2⟩
/-- Nonnegativity and normalization of equal weights `1 / card α` on a nonempty finite carrier. -/
def uniform_valid [Nonempty α] :
    (∀ _ : α, 0 ≤ (Fintype.card α : ℝ)⁻¹) ∧
    (∑ _ : α, (Fintype.card α : ℝ)⁻¹) = 1 := by
  sorry
noncomputable def uniform [Nonempty α] : FiniteDistribution α where
  weight _ := (Fintype.card α : ℝ)⁻¹
  nonneg := uniform_valid.1
  total := uniform_valid.2
/-- Nonnegativity and normalization when sampling from `P`, then from the distribution selected by the first sample. -/
def bind_valid (P : FiniteDistribution α) (Q : α → FiniteDistribution β) :
    (∀ b, 0 ≤ ∑ a, P.weight a * (Q a).weight b) ∧
    (∑ b, ∑ a, P.weight a * (Q a).weight b) = 1 := by
  sorry
noncomputable def bind (P : FiniteDistribution α) (Q : α → FiniteDistribution β) : FiniteDistribution β where
  weight b := ∑ a, P.weight a * (Q a).weight b
  nonneg := (bind_valid P Q).1
  total := (bind_valid P Q).2
/-- Push a probability distribution forward through a deterministic function, summing the masses of all inputs with the same output. -/

noncomputable def map (P : FiniteDistribution α) (f : α → β) : FiniteDistribution β :=
  P.bind (fun a => pure (f a))
/-- Nonnegativity and normalization of the joint law obtained by sampling from `P` and then from `Q a`, retaining both samples. -/
def joint_valid (P : FiniteDistribution α) (Q : α → FiniteDistribution β) :
    (∀ ab : α × β, 0 ≤ P.weight ab.1 * (Q ab.1).weight ab.2) ∧
    (∑ ab : α × β, P.weight ab.1 * (Q ab.1).weight ab.2) = 1 := by
  sorry
noncomputable def joint (P : FiniteDistribution α) (Q : α → FiniteDistribution β) : FiniteDistribution (α × β) where
  weight ab := P.weight ab.1 * (Q ab.1).weight ab.2
  nonneg := (joint_valid P Q).1
  total := (joint_valid P Q).2
end FiniteDistribution
end Refresh
namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Every secret fiber is inhabited in dimensions at least two. -/
def fiber_nonempty (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) (hn : 2 ≤ n) (s : F) : Nonempty (Fiber F n s) := by
  sorry
end Refresh
end FiniteProbability

section FiniteExpectations

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
## Matrix sampling foundations

A counted pivot scan, matrix refresh maps, and raw matrix proposals.
-/

section GaussianArithmetic

namespace CircuitCompiler.Rectangular.Gaussian
variable {F : Type*} [Field F] [DecidableEq F]
/-- A computation annotated by an explicit work counter. The pivot scan below charges one operation per zero test. Routine vector indexing and allocation are outside this counter. -/

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
/-- Scan a row in coordinate order for its first nonzero entry. -/
def findPivot {m : ℕ} (row : Vector F m) : Counted (Option (Fin m)) :=
  pivotScan row (List.finRange m)
end CircuitCompiler.Rectangular.Gaussian
end GaussianArithmetic

section MatrixRefreshing

namespace Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Certificate that a refreshed state remains in its encoding fiber. -/
abbrev refreshInFiber_mem {n : ℕ} {s : F} (x : Fiber F n s) (M : Refresh.«GL» F n) :
    secret (refresh x.val M) = s := by
  sorry

/-- Refresh an encoding while retaining its proof that the encoded secret remains in the same fiber. -/
def refreshInFiber {n : ℕ} {s : F} (x : Fiber F n s) (M : Refresh.«GL» F n) : Fiber F n s :=
  ⟨refresh x.val M, refreshInFiber_mem x M⟩
end Refresh
end MatrixRefreshing

section MatrixSampling

namespace CircuitCompiler
open Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Tensor of two share vectors, with a concrete finite coordinate ordering. -/

def tensorVector {n : ℕ} (a b : V F n) : V F (n * n) :=
  fun k => a (finProdFinEquiv.symm k).1 * b (finProdFinEquiv.symm k).2
end CircuitCompiler
namespace CircuitCompiler.Sampling
open Refresh
variable {α β : Type*} [Fintype α] [Fintype β]
/-- The probability that one proposal passes the specified acceptance test. -/
def acceptance (P : FiniteDistribution α) (accept : α → Bool) : ℝ :=
  ∑ a, if accept a then P.weight a else 0
end CircuitCompiler.Sampling
namespace CircuitCompiler.Sampling
variable {α β : Type*} [Fintype α] [Fintype β]
universe u
/-- A finite sequence of proposals, represented without any probabilistic oracle. -/

def Tape (α : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => α × Tape α n
end CircuitCompiler.Sampling
namespace CircuitCompiler.Rectangular
open Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Appending a constant coordinate to the tensor product of two nonzero shares preserves nonzeroness. -/
abbrev augmentedShare_ne_zero {n : ℕ} (c : F) (x : U F n × U F n) :
    Fin.append (tensorVector x.1.val x.2.val) (fun _ : Fin 1 => c) ≠ 0 := by
  sorry

def augmentedShare {n : ℕ} (c : F) (x : U F n × U F n) : U F (n*n+1) :=
  ⟨Fin.append (tensorVector x.1.val x.2.val) (fun _ : Fin 1 => c),
    augmentedShare_ne_zero c x⟩
end CircuitCompiler.Rectangular
namespace CircuitCompiler.Sampling
variable {α : Type*} [Fintype α] [Nonempty α]
section Matrix
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- The acceptance test uses only the determinant of the proposed matrix. -/

def invertibleTest {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : Bool :=
  decide (M.det ≠ 0)
def invertibleTest_isUnit {n : ℕ}
    (M : {M : Matrix (Fin n) (Fin n) F // invertibleTest M = true}) :
    IsUnit M.val := by
  sorry

end Matrix
end CircuitCompiler.Sampling
end MatrixSampling

/-!
## Execution and local comparison interfaces

Answer histories, causal runners, scoped networks, and local estimates.
-/

section ChronologicalPrograms

namespace CircuitCompiler.Composition
universe u
/-- A fixed-length answer history, represented recursively for summation. -/

def Answers (A : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => A × Answers A n
/-- The finite enumeration used when summing over answer histories. -/
instance answersFintype (A : Type*) [Fintype A] : (n : ℕ) → Fintype (Answers A n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => @instFintypeProd A (Answers A n) _ (answersFintype A n)
end CircuitCompiler.Composition
namespace CircuitCompiler.Composition
universe u
/-- Decode a chronological answer vector into the recursive history representation. -/
def vectorToAnswers (A : Type u) : (n : ℕ) → (Fin n → A) → Answers A n
  | 0, _ => PUnit.unit
  | n + 1, h => (h 0, vectorToAnswers A n (Fin.tail h))
end CircuitCompiler.Composition
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
namespace CircuitCompiler
/-- A gate is tagged as a product or a complemented product with a public constant. Over bits, `product` denotes AND and `complement 1` denotes NAND; the direct compiler uses only the latter. -/
inductive GateKind (F : Type*) where
  | product
  | complement (constant : F)
/-- A binary gate names its operation and its two predecessor wire addresses. -/
structure Gate (F : Type*) (wires : ℕ) where
  kind : GateKind F
  left : Fin wires
  right : Fin wires
end CircuitCompiler
namespace CircuitCompiler
variable {F Alpha Beta : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype Alpha] [Fintype Beta] {n t inputs T : ℕ}
/-- The public constant appended to the left tensor feature; the right feature appends one. -/

def GateKind.affineConstant : GateKind F → F
  | .product => 0
  | .complement c => c
end CircuitCompiler
end ChronologicalPrograms

section FactorEnergies

namespace CircuitCompiler.AveragedEnergyComparison
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

namespace CircuitCompiler.Composition
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

namespace CircuitCompiler.Composition
open Refresh
/-- Independently sample one encoding for every distinct wire. -/
/- Mathematical definition (normal notation): For one probability distribution μ_w per wire, define their product distribution on complete encoding assignments by Pr[X = x] = ∏_w μ_w(x_w). Thus all wire encodings are independent. -/
def independentDistribution_valid {W E : Type*} [Fintype W] [DecidableEq W] [Fintype E]
    (wireDistribution : W → FiniteDistribution E) :
    (∀ encoding : W → E, 0 ≤ ∏ w, (wireDistribution w).weight (encoding w)) ∧
    (∑ encoding : W → E, ∏ w, (wireDistribution w).weight (encoding w)) = 1 := by
  sorry

noncomputable def independentDistribution {W E : Type*} [Fintype W] [DecidableEq W] [Fintype E]
    (wireDistribution : W → FiniteDistribution E) : FiniteDistribution (W → E) where
  weight encoding := ∏ w, (wireDistribution w).weight (encoding w)
  nonneg := (independentDistribution_valid wireDistribution).1
  total := (independentDistribution_valid wireDistribution).2
/-- Group left coordinates and right coordinates after independently sampling whole wire encodings. Their joint distribution retains each wire's correlation. -/
/-
Mathematical definition (normal notation): For finite sets W, E, D, distributions wireDistribution ∈ W → 𝒟(E), and projections left, right : E → D, define

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

namespace CircuitCompiler.AveragedEnergyComparison
open Refresh MatrixRefresh _root_.CircuitCompiler.Composition
variable {W E A : Type*} [Fintype W] [DecidableEq W] [Fintype E] [Fintype A]
  {T : ℕ}
structure ScopedProbabilities (scope : Fin T → Finset W) where
  prob : Fin T → List A → (W → E) → A → ℝ
  nonneg : ∀ i h e a, 0 ≤ prob i h e a
  total_le : ∀ i h e, (∑ a, prob i h e a) ≤ 1
  locality : ∀ i h a, Scoped (scope i) (fun e => prob i h e a)
end CircuitCompiler.AveragedEnergyComparison
end ScopedSplit

section CommonLocalEstimates

namespace CircuitCompiler.AveragedEnergyComparison
open Refresh MatrixRefresh
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
end CircuitCompiler.AveragedEnergyComparison
end CommonLocalEstimates

/-!
## Physical sampling and gate execution

Acceptance tests, rectangular constructions, rejection tapes, and physical runs.
-/

section CompilerParameters

noncomputable section CompilerPublicModel
namespace Compiler
/-- A complete gate answer contains the two λᴹ-bit matrix-phase answers and the two λˢ-bit shortening answers. Its alphabet has 2^(2(λᴹ + λˢ)) elements. -/
abbrev Answer (matrixLeakage shorteningLeakage : ℕ) :=
  Refreshing.Answer matrixLeakage × Refreshing.Answer shorteningLeakage
/-- The rectangular sampler writes the long dimension m = n² + 1 as n + t, with t = n² + 1 − n. This is nonnegative for every natural n. -/
def shorteningExtra (n : ℕ) : ℕ := n * n + 1 - n
/-- The two descriptions of the long dimension coincide: n² + 1 = n + (n² + 1 − n). -/
def longDimension (n : ℕ) : n * n + 1 = n + shorteningExtra n := by
  sorry
end Compiler
end CompilerPublicModel
end CompilerParameters

section RectangularAlgebra

namespace CircuitCompiler.Rectangular
open Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Full row rank, in the equivalent right-inverse formulation. -/

def FullRowRank {n m : ℕ} (H : Matrix (Fin n) (Fin m) F) : Prop :=
  ∃ J : Matrix (Fin m) (Fin n) F, H * J = 1
/-- The finite carrier of rectangular matrices with full row rank. -/
abbrev FullRank (F : Type*) [Field F] (n m : ℕ) :=
  {H : Matrix (Fin n) (Fin m) F // FullRowRank H}
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
section CompletionWitness
universe u_1
/-- Every chosen nonzero short row admits a full-rank completion. -/
abbrev completion_nonempty {F : Type u_1} [Field F] [Fintype F] [DecidableEq F]
    {n t : ℕ} (u : U F (n+t)) (a : U F n) :
    Nonempty (Completion u a) := by
  sorry
end CompletionWitness
def sigmaToAttempt {n m : ℕ} (u : U F m)
    (p : ((a : U F n) × Completion u a)) : Attempt (n := n) u :=
  ⟨(p.1, p.2.val), p.2.property⟩
end CircuitCompiler.Rectangular
end RectangularAlgebra

section StoppedSampling

namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
/-- The real-valued masses of a PMF on a finite carrier sum to one. This supplies the normalization for `toFinite`. -/

def toFinite_total (P : PMF β) : (∑ b, (P b).toReal) = 1 := by
  sorry

def toFinite (P : PMF β) : FiniteDistribution β where
  weight b := (P b).toReal
  nonneg b := ENNReal.toReal_nonneg
  total := toFinite_total P
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
/-- The unbounded physical retry distribution. All its mass is on finite stopped tapes because the acceptance probability is strictly positive. -/

abbrev distribution_normalized (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) :
    HasSum (fun t : StoppedTape α => ENNReal.ofReal (traceWeight P accept t)) 1 := by
  sorry

def distribution (P : FiniteDistribution α) (accept : α → Bool) (hp : 0 < acceptance P accept) :
    PMF (StoppedTape α) :=
  ⟨fun t => ENNReal.ofReal (traceWeight P accept t), distribution_normalized P accept hp⟩
/-- Arbitrary finite-valued leakage on the entire stopped tape. -/

def observe (P : FiniteDistribution α) (accept : α → Bool) (hp : 0 < acceptance P accept)
    (f : StoppedTape α → β) : FiniteDistribution β := toFinite ((distribution P accept hp).map f)
/-- A finite rejected-proposal sequence together with its length. -/
abbrev FailedPrefix (α : Type*) := Σ k : ℕ, Tape α k
/-- Append one accepted proposal to its complete rejected prefix. -/
def joinPrefix (t : FailedPrefix α) (a : α) : StoppedTape α := ⟨t.1,(t.2,a)⟩
end
end CircuitCompiler.Sampling.Unbounded
namespace CircuitCompiler.Rectangular
open Refresh Sampling
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- All rejected proposals and the final successful proposal. -/

abbrev FullTape {n m : ℕ} (u : U F m) :=
  Unbounded.StoppedTape (Attempt (n := n) u)
end CircuitCompiler.Rectangular
namespace CircuitCompiler.Sampling
open Refresh MatrixRefresh Unbounded
noncomputable section
variable {F X L R V : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype L] [Fintype R] [Fintype V] {m : ℕ}
/-- Uniform square-matrix rejection sampling has positive acceptance probability. -/
def matrixAcceptancePositive (m : ℕ) :
    0 < acceptance (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin m) (Fin m) F)) invertibleTest := by
  sorry
/-- Return the accepted invertible matrix, using the identity on a noninvertible input. The latter case has probability zero for terminal proposals of matrix rejection sampling. -/

def matrixReturned (M : Matrix (Fin m) (Fin m) F) : Refresh.«GL» F m :=
  if h : invertibleTest M = true then (invertibleTest_isUnit ⟨M,h⟩).unit else 1
end
end CircuitCompiler.Sampling
namespace CircuitCompiler.Sampling
open Refresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Test whether a vector is nonzero. -/
def nonzeroTest {n : ℕ} (v : V F n) : Bool := decide (v ≠ 0)
end CircuitCompiler.Sampling
end StoppedSampling

section CompletionSampling

namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- All rows except the chosen pivot row of an affine matrix completion. -/
abbrev FreeRows (F : Type*) (n m : ℕ) (j : Fin n) := {i : Fin n // i ≠ j} → Fin m → F
/-- A linear scan of the short row finds a nonzero coefficient. -/

def pivotSearch {n : ℕ} (a : U F n) := Gaussian.findPivot (Vector.ofFn a.val)
def pivotSearch_ne_none {n : ℕ} (a : U F n) :
    (pivotSearch a).value ≠ none := by
  sorry
/-- The pivot is computed by a finite linear scan, not by a choice operation. -/

def pivot {n : ℕ} (a : U F n) : Fin n :=
  (pivotSearch a).value.get (Option.ne_none_iff_isSome.mp (pivotSearch_ne_none a))
/-- The free entries determine the unique remaining row. -/

def fill {n m : ℕ} (u : U F m) (a : U F n)
    (w : FreeRows F n m (pivot a)) : Matrix (Fin n) (Fin m) F := fun i k =>
  if hi : i = pivot a then
    (u.val k - ∑ r : {i : Fin n // i ≠ pivot a}, a.val r.val * w r k) / a.val (pivot a)
  else w ⟨i,hi⟩ k
def fill_constraint {n m : ℕ} (u : U F m) (a : U F n)
    (w : FreeRows F n m (pivot a)) : Matrix.vecMul a.val (fill u a w) = u.val := by
  sorry
/-- The test sees only a locally generated candidate matrix. -/

def accept {n m : ℕ} (u : U F m) (a : U F n)
    (w : FreeRows F n m (pivot a)) : Bool := by
  classical
  exact decide (FullRowRank (fill u a w))
/-- The accepted proposals are exactly the full-row-rank completions. -/

def acceptedForward_fullrank {n m : ℕ} (u : U F m) (a : U F n)
    (w : {w : FreeRows F n m (pivot a) // accept u a w = true}) :
    FullRowRank (fill u a w.val) := by
  sorry

def acceptedForward {n m : ℕ} (u : U F m) (a : U F n)
    (w : {w : FreeRows F n m (pivot a) // accept u a w = true}) : Completion u a :=
  ⟨⟨fill u a w.val, acceptedForward_fullrank u a w⟩, fill_constraint u a w.val⟩

abbrev acceptedBackward_mem {n m : ℕ} (u : U F m) (a : U F n)
    (H : Completion u a) :
    accept u a (fun i k => H.val.val i.val k) = true := by
  sorry

def acceptedBackward {n m : ℕ} (u : U F m) (a : U F n)
    (H : Completion u a) : {w : FreeRows F n m (pivot a) // accept u a w = true} :=
  ⟨(fun i k => H.val.val i.val k), acceptedBackward_mem u a H⟩

abbrev acceptance_pos {n t : ℕ} (u : U F (n+t)) (a : U F n) :
    0 < acceptance (FiniteDistribution.uniform : FiniteDistribution (FreeRows F n (n+t) (pivot a))) (accept u a) := by
  sorry
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
/-- Return the accepted completion, with an arbitrary completion on rejected inputs. That fallback has probability zero when this function is applied to the terminal proposal of `tapeDistribution`. -/

def returned {n t : ℕ} (u : U F (n+t)) (a : U F n)
    (w : FreeRows F n (n+t) (pivot a)) : Completion u a :=
  if h : accept u a w = true then acceptedForward u a ⟨w,h⟩ else
    @Classical.choice _ (completion_nonempty u a)
end
end CircuitCompiler.Rectangular.CompletionSampler
end CompletionSampling

section RectangularExecution

namespace CircuitCompiler.Rectangular.AttemptSampler
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- All rejected vector proposals followed by the accepted nonzero row. -/
abbrev RowTape (F : Type*) (n : ℕ) := StoppedTape (V F n)
/-- The rejected vector proposals preceding the accepted nonzero row. -/
abbrev RowPrefix (F : Type*) (n : ℕ) := FailedPrefix (V F n)
/-- Nonzero certificate for the coordinate vector used to complete the sampler's ambient return function. -/
def rowDefault_nonzero {n : ℕ} (hn : 1 ≤ n) :
    (Pi.single (⟨0, by omega⟩ : Fin n) 1 : V F n) ≠ 0 := by
  sorry

def rowDefault {n : ℕ} (hn : 1 ≤ n) : U F n :=
  ⟨Pi.single ⟨0, by omega⟩ 1, rowDefault_nonzero hn⟩
abbrev row_acceptance_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < acceptance (FiniteDistribution.uniform : FiniteDistribution (V F n)) nonzeroTest := by
  sorry
/-- The actual raw-vector rejection distribution used to sample a nonzero short row. -/
def rowDistribution {n : ℕ} (hn : 1 ≤ n) : PMF (RowTape F n) :=
  distribution FiniteDistribution.uniform nonzeroTest (row_acceptance_pos hn)
/-- Return a nonzero accepted row, with a fixed nonzero completion on rejected ambient inputs. -/
def rowReturned {n : ℕ} (hn : 1 ≤ n) (v : V F n) : U F n :=
  if hv : v ≠ 0 then ⟨v,hv⟩ else rowDefault hn
/-- Recover the complete vector-sampling tape from its rejected prefix and accepted nonzero row. -/
def reconstructRow {n : ℕ} (p : RowPrefix F n) (a : U F n) : RowTape F n :=
  joinPrefix p a.val
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
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- A reverse-shortening record contains a short encoding, a full-row-rank matrix, and a compatible long right share. -/
abbrev Backward (F : Type*) [Field F] (n m : ℕ) (s : F) :=
  {p : Fiber F n s × FullRank F n m × U F m // p.2.1.val.mulVec p.2.2.val = p.1.val.R.val}
/-- A successful forward-shortening record contains the long encoding, short left row, and compatible full-row-rank matrix. -/
abbrev ForwardRecord (F : Type*) [Field F] (n m : ℕ) (s : F) :=
  {p : State F m × U F n × FullRank F n m //
    secret p.1 = s ∧ Matrix.vecMul p.2.1.val p.2.2.val = p.1.L.val ∧
      p.2.2.val.mulVec p.1.R.val ≠ 0}
/-- The short state obtained from a successful forward record, with right share `H * R`, encodes the same secret. -/

def forwardToBackward_secret {n m : ℕ} {s : F} (p : ForwardRecord F n m s) :
    secret (⟨p.val.2.1,
      ⟨p.val.2.2.val.mulVec p.val.1.R.val, p.property.2.2⟩⟩ : State F n) = s := by
  sorry

def forwardToBackward {n m : ℕ} {s : F} (p : ForwardRecord F n m s) : Backward F n m s :=
  ⟨(⟨⟨p.val.2.1, ⟨p.val.2.2.val.mulVec p.val.1.R.val, p.property.2.2⟩⟩,
    forwardToBackward_secret p⟩, p.val.2.2, p.val.1.R), rfl⟩

/-- Forward successful choices, retaining the original long encoding. -/

abbrev SuccessfulJoint (F : Type*) [Field F] (n m : ℕ) (s : F) :=
  (x : Fiber F m s) × Success (n := n) x.val.L x.val.R
/-- Turn a successful choice into a reverse record, computing the short right share from its matrix and long right share. -/

def successfulJointForward {n m : ℕ} (s : F) (p : SuccessfulJoint F n m s) :
    Backward F n m s :=
  forwardToBackward ⟨(p.1.val, p.2.val.val.1, p.2.val.val.2),
    p.1.property, p.2.val.property, p.2.property⟩
end CircuitCompiler.Rectangular
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh
variable {F O A B : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [DecidableEq O] [Nonempty O] [Fintype A] [Fintype B]
variable {n t : ℕ}
/-- The long secret encoded by the two feature vectors. -/

def gateSecret (a b : O → U F (n+t)) (o : O × O) : F :=
  dot (a o.1).val (b o.2).val
/-- The initial long feature encoding, retaining its plaintext equation. -/

def gateInput (a b : O → U F (n+t)) (o : O × O) :
    Fiber F (n+t) (gateSecret a b o) := ⟨⟨a o.1,b o.2⟩,rfl⟩
/-- Return the selected short row and the matrix-times-column output when nonzero. The fallback makes this total on failed attempts; it has probability zero for terminal attempts from `rawRetryDistribution`. -/

def returnedOutput {s : F} (fallback : Fiber F n s) (x : Fiber F (n+t) s)
    (a : Attempt (n := n) x.val.L) : Fiber F n s :=
  if h : rightOutput x.val.R a ≠ 0 then
    (successfulJointForward s ⟨x,⟨a,h⟩⟩).val.1 else fallback
end CircuitCompiler.Rectangular
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh
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
end CircuitCompiler.Rectangular
namespace CircuitCompiler.Rectangular.Taped
open Refresh MatrixRefresh Sampling Sampling.Unbounded
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
end CircuitCompiler.Rectangular.Taped
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh
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
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh
open _root_.CircuitCompiler.Composition _root_.CircuitCompiler.Composition.TopologicalExecution Sampling Sampling.Unbounded
noncomputable section
variable {F ML MR BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
variable {n t inputs T : ℕ}
/-- Arbitrary bounded local leakage of the fully implemented gate. Shortening callbacks receive the matrix-phase answers but no matrix-sampler tape, enforcing the phase's erasure boundary. -/

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
end RectangularExecution


section Initialization

namespace CircuitCompiler.Sampling.RawEncoding
open Refresh MatrixRefresh Unbounded Rectangular.Gaussian
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- A raw encoding proposal consists of two vectors, which may initially be zero. -/
abbrev Raw (F : Type*) (n : ℕ) := V F n × V F n
/-- Accept a raw pair exactly when both vectors are nonzero and their inner product equals the prescribed secret. -/
def accept {n : ℕ} (s : F) (x : Raw F n) : Bool :=
  nonzeroTest x.1 && nonzeroTest x.2 && decide (dot x.1 x.2 = s)
@[simp] def accept_iff {n : ℕ} (s : F) (x : Raw F n) :
    accept s x = true ↔ x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ dot x.1 x.2 = s := by
  sorry
/-- Accepted raw pairs and valid encodings are the same finite set. -/

def acceptedToFiber {n : ℕ} (s : F)
    (x : {x : Raw F n // accept s x = true}) : Fiber F n s :=
  ⟨⟨⟨x.val.1, ((accept_iff s x.val).mp x.property).1⟩,
    ⟨x.val.2, ((accept_iff s x.val).mp x.property).2.1⟩⟩,
    ((accept_iff s x.val).mp x.property).2.2⟩

abbrev acceptance_pos {n : ℕ} (hn : 2 ≤ n) (s : F) :
    0 < acceptance (FiniteDistribution.uniform : FiniteDistribution (Raw F n)) (accept s) := by
  sorry
/-- Complete raw proposal tape, including every rejected pair. -/

def tapeDistribution {n : ℕ} (hn : 2 ≤ n) (s : F) : PMF (StoppedTape (Raw F n)) :=
  distribution FiniteDistribution.uniform (accept s) (acceptance_pos hn s)
/-- Decode an accepted raw pair, using a valid default encoding otherwise. The fallback has probability zero when this function is applied to the terminal proposal of `tapeDistribution`. -/

def returned {n : ℕ} (hn : 2 ≤ n) (s : F) (x : Raw F n) : Fiber F n s :=
  if h : accept s x = true then acceptedToFiber s ⟨x,h⟩
  else Classical.choice (fiber_nonempty F n hn s)
end
end CircuitCompiler.Sampling.RawEncoding
namespace CircuitCompiler.Sampling.RawEncoding
open Refresh MatrixRefresh Unbounded _root_.CircuitCompiler.Composition
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Real initialization performs an uncapped raw-entry sampler for each input wire. Its output distribution retains only the resulting states; initialization tapes are not exposed to leakage callbacks. -/

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
namespace CircuitCompiler.Sampling.CountableRejection
open Refresh Unbounded
noncomputable section
variable {α β : Type*}
/-- The probability that a countable proposal passes the acceptance test. -/
def probability (P : PMF α) (accept : α → Bool) : ℝ :=
  (toFinite (P.map accept)).weight true
/-- The proposal mass restricted to rejected values. -/
def rejectedMass (P : PMF α) (accept : α → Bool) (x : α) : ℝ≥0∞ :=
  if accept x then 0 else P x
/-- The proposal mass restricted to accepted values. -/
def acceptedMass (P : PMF α) (accept : α → Bool) (x : α) : ℝ≥0∞ :=
  if accept x then P x else 0
/-- The product mass of a finite sequence of rejected proposals. -/
def prefixMass (P : PMF α) (accept : α → Bool) : (k : ℕ) → Tape α k → ℝ≥0∞
  | 0,_ => 1
  | k+1,t => rejectedMass P accept t.1 * prefixMass P accept k t.2
/-- The mass of a complete rejection tape is its rejected-prefix mass times its accepted-final-proposal mass. -/
def traceMass (P : PMF α) (accept : α → Bool) (t : StoppedTape α) : ℝ≥0∞ :=
  prefixMass P accept t.1 t.2.1 * acceptedMass P accept t.2.2
/-- Direct iid rejection semantics. Every finite stopped raw trace is assigned its independent proposal-product mass, and these masses sum to one. -/
abbrev distribution_normalized (P : PMF α) (accept : α → Bool)
    (hp : 0 < probability P accept) : HasSum (traceMass P accept) 1 := by
  sorry

def distribution (P : PMF α) (accept : α → Bool) (hp : 0 < probability P accept) :
    PMF (StoppedTape α) :=
  ⟨traceMass P accept, distribution_normalized P accept hp⟩
end
end CircuitCompiler.Sampling.CountableRejection
namespace CircuitCompiler.Rectangular.Taped
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n t : ℕ}
/-- The ordinary outer acceptance test is computed from the actual raw record's returned rectangular matrix and the right party's long share. -/

abbrev rawAccept (u v : U F (n+t)) (record : AttemptSampler.Record (n := n) u) : Bool :=
  decide (rightOutput v (AttemptSampler.returned u record) ≠ 0)
/-- Positivity certificate for the raw retry sampler. The proof is supplied independently in `Proofs/Compiler/PublicModel.lean` and checked by the comparator. -/
abbrev raw_acceptance_positive (hn : 2 ≤ n) (u v : U F (n+t)) :
    0 < CountableRejection.probability (AttemptSampler.sequentialDistribution (by omega) u)
      (rawAccept u v) := by
  sorry
/-- Direct execution of the raw primitive samplers until the right output is nonzero. This distribution assigns each stopped raw record trace its independent proposal-product mass, including all inner row/completion proposals in every record. -/

def rawRetryDistribution (hn : 2 ≤ n) (u v : U F (n+t)) :
    PMF (StoppedTape (AttemptSampler.Record (n := n) u)) :=
  CountableRejection.distribution (AttemptSampler.sequentialDistribution (by omega) u)
    (rawAccept u v) (raw_acceptance_positive hn u v)
end
end CircuitCompiler.Rectangular.Taped
end Initialization

section PhysicalGates

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
end PhysicalGates

/-!
## Composition and adaptive interfaces

History weights, physical operations, and adaptive public-input plans.
-/

noncomputable section CommonLocalData

namespace CompilerProof.DirectComposition
open Refresh MatrixRefresh CircuitCompiler.Composition CircuitCompiler.AveragedEnergyComparison

variable {W X A F : Type*} [Fintype W] [DecidableEq W]
  [Fintype X] [Nonempty X] [Fintype A] {S : ℕ}
/-- Independently encode every wire label and group the resulting left and right shares by party. This is a distribution before any leakage answer is observed. -/
def groupedLaw (law : F → FiniteDistribution (X × X)) (label : W → F) :
    FiniteDistribution ((W → X) × (W → X)) :=
  groupedDistribution (fun w => law (label w)) Prod.fst Prod.snd
/-- A chosen approximation and its factor representation for every operation, formal history, and answer. Error bounds are required only for valid local labelings at approximated operations; in the compiler application, public samplers are outside that set. The factors themselves inspect only the declared scope, so separate energy trimming preserves locality. -/
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
/-- Average the adaptive true history product under independent encodings of the fixed wire labels. The hidden wire encodings are not part of this transcript weight. -/
def canonicalWeight (scope : Fin S → Finset W)
    (network : ScopedProbabilities (E := X × X) (A := A) scope)
    (law : F → FiniteDistribution (X × X)) (label : W → F) (z : Fin S → A) : ℝ :=
  (independentDistribution (fun w => law (label w))).expect
    (historyWeight scope network z)
end CompilerProof.DirectComposition
end CommonLocalData

noncomputable section CompositionParameters

namespace CompilerProof.DirectComposition
/-- Approximation parameter used before energy trimming. -/
def betaParameter (q : ℝ) : ℝ := q ^ (-1/3 : ℝ)
/-- A convenient upper bound for the untrimmed valid-label RMS error. -/
def rawErrorParameter (q : ℝ) : ℝ := 10000*q ^ (-1/9 : ℝ)
end CompilerProof.DirectComposition
end CompositionParameters

section PhysicalShares

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

noncomputable section Operations

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
/-- A heterogeneous physical transition interface. The concrete strategy below supplies these distributions by the actual samplers. Each transition returns the new encoding jointly with its leakage answer, retaining their correlations. -/
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
variable {F ML MR BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
  {n t inputs : ℕ} {hdim : n*n+1 = n+t}
/-- A complete operation answer contains the two parties’ first and second answer strings. -/
abbrev Answer (ML MR BL BR : Type*) := (ML × MR) × (BL × BR)
/-- The complete rejected-matrix prefix together with its accepted square-matrix proposal. -/
abbrev MatrixTape (F : Type*) (n : ℕ) := StoppedTape (Matrix (Fin n) (Fin n) F)
/-- The complete rejected raw-pair prefix together with its accepted raw pair encoding a public value. -/
abbrev PublicTape (F : Type*) (n : ℕ) := StoppedTape (RawEncoding.Raw F n)
/-- The admissible deterministic local functions for all active operations. The computation field supplies matrix-phase and shortening-phase leakage for the protected gates; the direct compiler instantiates them as NAND gates over bits. -/
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
end Operations

section AdaptiveCompiler

noncomputable section AdaptiveCanonical
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
end AdaptiveCanonical
noncomputable section AdaptiveModel
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
end AdaptiveModel
section AdaptiveProgram
namespace Compiler.Adaptive
open Refresh CircuitCompiler CircuitCompiler.Operations CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution CircuitCompiler.AveragedEnergyComparison

variable {F E A : Type*} {P S : ℕ}
/-- An online sampler policy supplies the public value using only the complete incoming answer vector at that position. Values at refresh and computation positions are ignored. -/
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
end AdaptiveProgram
end AdaptiveCompiler

/-!
# Compiler model

The public model collects the NAND source, its input-port refresh-chain compilation and physical view, the causal execution interface, and the stateful extension. Its encoding, sampling, execution, and local-interface definitions appear above the model. Admitted construction certificates accompany those definitions and are checked against independent proofs by the comparator. The mathematical proofs are in `Proofs/Compiler`.

The main theorem statement appears below. The proof environment uses an independent model copy with completed construction certificates and proves the theorem without importing this reference file.
-/

section DirectSource

/-!
## NAND sources for the direct compiler

A source is a chronological NAND program. Operand positions may repeat and may have arbitrary fanout; zero source gates and empty output tuples are allowed. Public values are part of the source, while private inputs are supplied separately. Basis conversion is the mathematical preprocessing described in the paper and is outside this interface.

The source has no selector, control, offset, positive-size, or fanout hypothesis. Its designated output list may repeat positions and may directly name input wires. The compiler will insert distinct refreshed encodings at the two input-port occurrences of each NAND gate.
-/


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
end DirectSource

section DirectProgram

/-!
## Executable input-port refresh chains

Public samplers run first. Each source NAND then refreshes its left current chain endpoint, refreshes its right updated endpoint, and computes on the two fresh encodings. The second refresh follows the first when the source operands coincide. Thus repeated source operands still receive distinct computation inputs. Original source-wire addresses are retained separately for the hidden trusted decoder.
-/


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

end Source
end Compiler.Direct
end DirectProgram

noncomputable section DirectExecution

/-!
## Physical execution and the trusted plaintext decoder

The direct protocol initializes only private input encodings and then runs its actual heterogeneous instruction program. The same complete rejected proposal tapes and phase-local leakage callbacks as in the common physical implementation are used. A computation is NAND and has two phases; each input-port refresh and public sampler has one phase. Unrelated retained encodings never enter a callback.

The only visible output after all answers is the tuple of plaintext bits obtained by the trusted decoder. The wire-share array and output encoding pairs are absent from the view. The simulated view runs the protocol with every private input set to zero, omits its retained encoding array from the view, and reports its supplied authorized output.
-/


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
end DirectExecution

section StatefulSource

/-!
## Stateful NAND source circuits

The transition circuit consumes the current private register state, a public input, and fixed public constants. Its designated wires specify the next state and the public output. Register and output positions may repeat or directly name inputs. The ideal oracle retains the private state between requests.
-/


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

/-- The total operation count after T invocations, with public constants sampled only once. -/
def operationCount (_circuit : Circuit m d c g k) (T : ℕ) : ℕ := 3*T*g+T*d+c

/-- Every invocation evaluates four leakage strings per NAND and two per input-port refresh or public sampler. -/
def callbackCount (_circuit : Circuit m d c g k) (T : ℕ) : ℕ := 8*T*g+2*(T*d+c)

end Circuit
end Compiler.Stateful
end StatefulSource

section StatefulProgram

/-!
## Interleaving public samplers and NAND gates

The stateful execution samples constants once and the next invocation's public input only when that invocation begins. A chronological source schedule supports these interleavings. Its NAND compilation reuses the same two input-port refreshes and protected computation as Compiler.Direct, with one shared live chain per logical source wire across all invocations.
-/


namespace Compiler.Direct.Compilation

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
end StatefulProgram

section StatefulInteraction

/-!
## Public interaction at invocation boundaries

The deterministic adversary chooses each input from earlier leakage and earlier input/output records. An oracle returns only the authorized plaintext output for the request history. The recursive public records are a denotational description of that interaction: request t uses leakage strictly before its invocation and outputs from invocations strictly before t. The simulator can evaluate these functions with a cache of the responses already released, without knowing the oracle's private state.
-/


namespace Compiler.Stateful

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
end StatefulInteraction

noncomputable section StatefulExecution

/-!
## Stateful physical execution and its oracle simulator

The initial register state is the only trusted private encoding boundary. Public constants and invocation inputs use the leaky sampler at their chronological positions. The adversary's local callbacks receive the previously published inputs and outputs as well as the existing leakage prefix. A fixed auxiliary input and tape are captured in the adversary's functions.

The simulator below is a single function of an ideal oracle. It encodes zero registers once and runs the actual physical operations. The public interface specifies oracle responses at invocation boundaries and recursively reconstructs the earlier public interaction; an implementation may cache those responses. No private initial state is an argument of the simulator. The real view uses the actual trusted decoder; its equality with the authorized oracle responses is proved separately.
-/

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

/-- The real view uses plaintext values decoded from the physical output encodings. The run uses the ideal oracle on the same initial state for its public interaction; decoder correctness identifies those responses with the physical outputs. -/
def realView {n ml sl : ℕ} (T : ℕ) (adversary : Adversary m d k n ml sl)
    (hn : 2 ≤ n) (initial : Fin m → Refreshing.Bit) : FiniteDistribution (circuit.View T ml sl) :=
  (circuit.runState T adversary hn (circuit.oracle initial) initial).map fun state =>
    (state.2,fun t =>
      ((recordAt c g adversary.choose (circuit.oracle initial) (List.ofFn state.2) t.val).1,
        circuit.decode T state.1 t))

/-- The simulator is independent of the private initial state. It runs the zero-register dummy execution using the ideal oracle through the public-history interface and reports the resulting leakage and authorized public records. Dummy output values and encodings are omitted from the view. Encodings needed for the next state or later uses remain available internally and may be erased only after their last required use. This view projection does not model physical erasure. -/
def simulatedView {n ml sl : ℕ} (T : ℕ) (adversary : Adversary m d k n ml sl)
    (hn : 2 ≤ n) (oracle : Oracle d k) : FiniteDistribution (circuit.View T ml sl) :=
  (circuit.runState T adversary hn oracle (fun _ => 0)).map fun state =>
    circuit.observe T adversary oracle state.2

end Circuit
end Compiler.Stateful
end StatefulExecution

/-!
# Theorem 5.2 and supporting compiler statements

The theorem states the direct NAND compiler of Theorem 5.2 together with fixed-label and causal composition for Theorem 5.7 and continual stateful privacy for Theorem 6.1. `Proofs.ReferenceClaims` loads its intentional admission for comparison with the independent proofs in `Proofs/Compiler/DirectComposition`, `Proofs/Compiler/Direct`, and `Proofs/Compiler/Stateful`.
-/

/-!
## Compiler claims

The four statements specify fixed-label composition, causal composition,
direct compiler privacy, and stateful compiler privacy. The main theorem
asserts them together.
-/

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

/-!
## Theorem checked by the comparator

The four conjuncts below state fixed-label composition, causal composition,
direct compiler privacy, and stateful compiler privacy in one theorem.
Its independent proof is under `Proofs/Compiler`.
-/

section CompilerMainTheorem
namespace Compiler
open Refresh MatrixRefresh CircuitCompiler CircuitCompiler.Composition
  CircuitCompiler.AveragedEnergyComparison CompilerProof.DirectComposition
theorem main_theorem.{u,v} :
    Direct.directCompositionClaim.{u,v} ∧
    Direct.adaptiveCompositionClaim.{u,v} ∧
    Direct.directPrivacyClaim ∧ Stateful.statefulPrivacyClaim := by
  sorry
end Compiler
end CompilerMainTheorem
