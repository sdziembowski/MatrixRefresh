import Compiler
open scoped ENNReal

set_option autoImplicit false

/-!
# Additional simulation foundations

Counted arithmetic and sampling constructions used by the efficient simulator.
-/

/-!
## Counted arithmetic and matrix sampling

Explicit algorithms and counters for scalar arithmetic and zero tests on matrices and tensors.
-/

section GaussianArithmetic

namespace CircuitCompiler.Rectangular.Gaussian
variable {F : Type*} [Field F] [DecidableEq F]
/-- Return a deterministic value with zero work counter. -/
def Counted.pure {α : Type*} (a : α) : Counted α := ⟨a,0⟩
/-- Compose two counted computations and add their work counters. -/
def Counted.bind {α β : Type*} (x : Counted α) (f : α → Counted β) : Counted β :=
  let y := f x.value
  ⟨y.value,x.operations+y.operations⟩
/-- Materialize the entry values and sum their supplied counters; tabulation adds no separate charge. -/

def tabulate {α : Type*} {n : ℕ} (f : Fin n → Counted α) : Counted (Vector α n) :=
  let results := Vector.ofFn f
  ⟨results.map Counted.value, ∑ i : Fin n, (results.get i).operations⟩
/-- Perform one field division and charge one primitive operation. -/

def divOp (x y : F) : Counted F := ⟨x/y,1⟩
/-- Perform one field multiplication and charge one primitive operation. -/
def mulOp (x y : F) : Counted F := ⟨x*y,1⟩
/-- Perform one field subtraction and charge one primitive operation. -/
def subOp (x y : F) : Counted F := ⟨x-y,1⟩
/-- An explicitly materialized n × m matrix stored as a vector of row vectors. -/
abbrev Data (F : Type*) (n m : ℕ) := Vector (Vector F m) n
/-- Eliminate one row with one division and two operations per coordinate. -/

def reduceRow {m : ℕ} (first row : Vector F m) (j : Fin m) : Counted (Vector F m) :=
  (divOp (row.get j) (first.get j)).bind fun factor =>
    tabulate fun k => (mulOp factor (first.get k)).bind fun product => subOp (row.get k) product
/-- The reduced matrix is stored eagerly before the next elimination step. -/

def reduceData {n m : ℕ} (H : Data F (n+1) m) (j : Fin m) : Counted (Data F n m) :=
  tabulate fun i => reduceRow (H.get 0) (H.get i.succ) j
/-- A counted nonzero-vector test using the same explicit linear scan. -/

def scanNonzero {m : ℕ} (row : Vector F m) : Counted Bool :=
  let scan := findPivot row
  ⟨scan.value.isSome,scan.operations⟩
/-- Test full row rank by Gaussian elimination, counting scalar arithmetic and pivot tests. -/

def check {m : ℕ} : (n : ℕ) → Data F n m → Counted Bool
  | 0, _ => Counted.pure true
  | n+1,H => (findPivot (H.get 0)).bind fun pivot =>
      match pivot with
      | none => Counted.pure false
      | some j => (reduceData H j).bind (check n)
/-- Store every entry of a function-valued matrix in an explicit row-vector array. -/
def materialize {n m : ℕ} (H : Fin n → Fin m → F) : Data F n m :=
  Vector.ofFn fun i => Vector.ofFn (H i)
end CircuitCompiler.Rectangular.Gaussian
namespace CircuitCompiler.Rectangular.Gaussian
variable {F : Type*} [Field F] [DecidableEq F]
/-- Perform one field addition and charge one primitive operation. -/
def addOp (x y : F) : Counted F := ⟨x+y,1⟩
/-- A concrete accumulation loop, one addition per list entry. -/

def sumLoop : List F → Counted F
  | [] => Counted.pure 0
  | x::xs => (sumLoop xs).bind fun s => addOp x s
/-- Dot product implemented by a multiplication loop and an accumulation loop. -/

def dotData {m : ℕ} (x y : Vector F m) : Counted F :=
  (tabulate fun i => mulOp (x.get i) (y.get i)).bind fun products => sumLoop products.toList
/-- Matrix-vector multiplication uses precisely `2 * n * m` scalar operations. -/

def mulVecData {n m : ℕ} (H : Data F n m) (v : Vector F m) : Counted (Vector F n) :=
  tabulate fun i => dotData (H.get i) v
/-- Solve the pivot row from the free rows, using only scalar arithmetic. -/

def fillPivotRow {n m : ℕ} (u : Vector F m) (a : Vector F n) (j : Fin n)
    (w : {i : Fin n // i ≠ j} → Fin m → F) : Counted (Vector F m) :=
  tabulate fun k =>
    (tabulate fun i : Fin n => if hi : i=j then Counted.pure (0:F)
      else mulOp (a.get i) (w ⟨i,hi⟩ k)).bind fun products =>
    (sumLoop products.toList).bind fun total =>
    (subOp (u.get k) total).bind fun residual => divOp residual (a.get j)
/-- Fill the whole matrix eagerly; copying the free rows takes no scalar arithmetic. -/

def fillData {n m : ℕ} (u : Vector F m) (a : Vector F n) (j : Fin n)
    (w : {i : Fin n // i ≠ j} → Fin m → F) : Counted (Data F n m) :=
  (fillPivotRow u a j w).bind fun pivot =>
    Counted.pure (Vector.ofFn fun i => if hi : i=j then pivot else Vector.ofFn (w ⟨i,hi⟩))
/-- Eliminate the first pivot coordinate from the remaining right-hand-side entries. -/
def reduceRhs {n m : ℕ} (H : Data F (n+1) m) (b : Vector F (n+1)) (j : Fin m) :
    Counted (Vector F n) :=
  tabulate fun i =>
    (divOp ((H.get i.succ).get j) ((H.get 0).get j)).bind fun factor =>
      (mulOp factor (b.get 0)).bind fun product => subOp (b.get i.succ) product
/-- Correct the pivot coordinate of a partial solution to satisfy the first row equation. -/
def backSubstitute {m : ℕ} (first : Vector F m) (target : F) (j : Fin m)
    (y : Vector F m) : Counted (Vector F m) :=
  (dotData first y).bind fun total =>
    (subOp target total).bind fun residual =>
    (divOp residual (first.get j)).bind fun correction =>
      tabulate fun k => if k=j then addOp (y.get k) correction else Counted.pure (y.get k)
/-- Solve a full-row-rank system by the same pivot/elimination scan as `check`. A rank-deficient input is allowed and may return `none`. -/

def solve {m : ℕ} : (n : ℕ) → Data F n m → Vector F n → Counted (Option (Vector F m))
  | 0,_,_ => Counted.pure (some (Vector.replicate m 0))
  | n+1,H,b => (findPivot (H.get 0)).bind fun pivot =>
      match pivot with
      | none => Counted.pure none
      | some j => (reduceData H j).bind fun H' =>
          (reduceRhs H b j).bind fun b' =>
          (solve n H' b').bind fun result =>
          match result with
          | none => Counted.pure none
          | some y => (backSubstitute (H.get 0) (b.get 0) j y).bind fun x => Counted.pure (some x)
end CircuitCompiler.Rectangular.Gaussian
namespace CircuitCompiler.Rectangular.Gaussian
variable {F : Type*} [Field F] [DecidableEq F]
/-- Compute and count every coordinatewise product in the two input vectors’ tensor product. -/
def tensorData {n : ℕ} (x y : Vector F n) : Counted (Vector F (n*n)) :=
  tabulate fun k => mulOp (x.get (finProdFinEquiv.symm k).1) (y.get (finProdFinEquiv.symm k).2)
/-- Multiplications build the tensor; appending the known offset only copies data. -/

def augmentedShareData {n : ℕ} (c : F) (x y : Vector F n) : Counted (Vector F (n*n+1)) :=
  (tensorData x y).bind fun tensor => Counted.pure
    (Vector.ofFn (Fin.append (fun i => tensor.get i) (fun _ : Fin 1 => c)))
end CircuitCompiler.Rectangular.Gaussian
end GaussianArithmetic

/-!
## Physical sampling and gate execution

Acceptance tests, rectangular constructions, rejection tapes, and counted runs.
-/

section RectangularAlgebra

namespace CircuitCompiler.Rectangular
open Refresh
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
instance completionFintype {n m : ℕ} (u : U F m) (A : U F n) :
    Fintype (Completion u A) := Fintype.ofFinite _
instance attemptFintype {n m : ℕ} (u : U F m) : Fintype (Attempt (n := n) u) :=
  Fintype.ofFinite _
/-- A short nonzero row exists at every dimension allowed by the sampler. The independent proof is in `Proofs/EfficientSimulaiton/PublicModel.lean`. -/
def attemptShareNonempty {n : ℕ} (_hn : 2 ≤ n) : Nonempty (U F n) := by
  sorry
/-- The actual one-attempt sampler: first choose the nonzero short row, then choose uniformly among its full-row-rank completions. -/

def attemptDistribution {n t : ℕ} (hn : 2 ≤ n) (u : U F (n+t)) :
    FiniteDistribution (Attempt (n := n) u) :=
  letI : Nonempty (U F n) := attemptShareNonempty hn
  letI : ∀ a : U F n, Nonempty (Completion u a) := fun a => completion_nonempty u a
  ((FiniteDistribution.uniform : FiniteDistribution (U F n)).bind
    (fun a => (FiniteDistribution.uniform : FiniteDistribution (Completion u a)).map (Sigma.mk a))).map
      (sigmaToAttempt u)
/-- The actual sampler has a nonzero probability of acceptance. -/
def attempt_acceptance_pos {n t : ℕ} (hn : 2 ≤ n) (u v : U F (n+t)) :
    0 < Sampling.acceptance (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0)) := by
  sorry
end
end CircuitCompiler.Rectangular
end RectangularAlgebra

section StoppedSampling

namespace CircuitCompiler.Sampling.Unbounded
open Refresh
variable {α β : Type*} [Fintype α] [Fintype β]
/-- Normalization certificate for the distribution of rejected prefixes. -/
abbrev prefixDistribution_normalized (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) :
    HasSum (fun t : FailedPrefix α =>
      ENNReal.ofReal (prefixWeight P accept t.1 t.2 * acceptance P accept)) 1 := by
  sorry
/-- Distribution of all rejected proposals, including their unbounded count. -/

def prefixDistribution (P : FiniteDistribution α) (accept : α → Bool)
    (hp : 0 < acceptance P accept) : PMF (FailedPrefix α) :=
  ⟨fun t => ENNReal.ofReal (prefixWeight P accept t.1 t.2 * acceptance P accept),
    prefixDistribution_normalized P accept hp⟩
end CircuitCompiler.Sampling.Unbounded
end StoppedSampling

section CompletionSampling

namespace CircuitCompiler.Rectangular.CompletionSampler
open Refresh MatrixRefresh Sampling
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Rejected internal choices depend on the local input pair `(U,A)`. They are independent of the particular accepted completion. -/

def rejectedDistribution {n t : ℕ} (u : U F (n+t)) (a : U F n) :
    PMF (Prefix (m := n+t) a) :=
  Unbounded.prefixDistribution FiniteDistribution.uniform (accept u a) (acceptance_pos u a)
end
end CircuitCompiler.Rectangular.CompletionSampler
namespace CircuitCompiler.Rectangular.SamplerCost
open Refresh MatrixRefresh Sampling Gaussian
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Instrumented affine fill followed by the instrumented rank test. -/

def completionProposal {n m : ℕ} (u : U F m) (a : U F n)
    (w : CompletionSampler.FreeRows F n m (CompletionSampler.pivot a)) : Counted Bool :=
  (fillData (Vector.ofFn u.val) (Vector.ofFn a.val) (CompletionSampler.pivot a) w).bind (check n)
end CircuitCompiler.Rectangular.SamplerCost
namespace CircuitCompiler.Sampling.Unbounded
open Refresh
noncomputable section
/-- Normalization certificate for dependent countable sampling. -/
def sigmaPMF_normalized {I : Type*} {J : I → Type*} (P : PMF I) (Q : ∀ i, PMF (J i)) :
    HasSum (fun z : Σ i, J i => P z.1 * Q z.1 z.2) 1 := by
  sorry
/-- A dependent pair of countable probability distributions. -/

def sigmaPMF {I : Type*} {J : I → Type*} (P : PMF I) (Q : ∀ i, PMF (J i)) :
    PMF (Σ i, J i) :=
  ⟨fun z => P z.1 * Q z.1 z.2, sigmaPMF_normalized P Q⟩
/-- Normalization certificate for independent countable sampling. -/
def productPMF_normalized {I J : Type*} (P : PMF I) (Q : PMF J) :
    HasSum (fun z : I × J => P z.1 * Q z.2) 1 := by
  sorry
/-- Sample independently from two countable probability distributions and retain both values. -/
def productPMF {I J : Type*} (P : PMF I) (Q : PMF J) : PMF (I × J) :=
  ⟨fun z => P z.1 * Q z.2, productPMF_normalized P Q⟩
variable {α β : Type*} [Fintype α]
/-- Conditional private tapes for every proposal in a finite prefix. -/

def prefixMarks (R : α → PMF β) : (k : ℕ) → Tape α k → PMF (Tape β k)
  | 0, _ => PMF.pure PUnit.unit
  | k+1, t => productPMF (R t.1) (prefixMarks R k t.2)
/-- Independently sample the private marks associated with every proposal on a complete rejection tape. -/
def traceMarks (R : α → PMF β) (t : StoppedTape α) : PMF (Tape β t.1 × β) :=
  productPMF (prefixMarks R t.1 t.2.1) (R t.2.2)
/-- A complete proposal tape together with one private mark for every rejected and accepted proposal. -/
abbrev MarkedTape (α β : Type*) := Σ t : StoppedTape α, Tape β t.1 × β
/-- Actual outer rejection with every internal sampler tape retained. -/

def markedDistribution (P : FiniteDistribution α) (accept : α → Bool) (hp : 0 < acceptance P accept)
    (R : α → PMF β) : PMF (MarkedTape α β) :=
  sigmaPMF (distribution P accept hp) (traceMarks R)
end
end CircuitCompiler.Sampling.Unbounded
namespace CircuitCompiler.Sampling.Unbounded
variable {α β : Type*} [Fintype α]
/-- Executable natural-valued counters along the actual stopped tape. -/

def prefixNatWork {γ : Type*} (cost : γ → ℕ) : (k : ℕ) → Tape γ k → ℕ
  | 0,_ => 0
  | k+1,t => cost t.1+prefixNatWork cost k t.2
/-- Sum the natural-number work of every rejected proposal and the final accepted proposal. -/
def traceNatWork {γ : Type*} (cost : γ → ℕ) (t : StoppedTape γ) : ℕ :=
  prefixNatWork cost t.1 t.2.1+cost t.2.2
end CircuitCompiler.Sampling.Unbounded
namespace CircuitCompiler.Rectangular.SamplerCost
open Refresh MatrixRefresh Sampling Sampling.Unbounded Gaussian
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ}
/-- Count the actual Gaussian tests on every raw matrix proposal. -/

def matrixTapeWork (trace : StoppedTape (Matrix (Fin m) (Fin m) F)) : ℕ :=
  traceNatWork (fun H => (check m (materialize H)).operations) trace
/-- Count the matrix-vector multiplication and linear solve used for the two refreshed shares. -/

def matrixActionWork (M : Refresh.«GL» F m) (left right : V F m) : ℕ :=
  (mulVecData (materialize M.val.transpose) (Vector.ofFn left)).operations+
  (solve m (materialize M.val) (Vector.ofFn right)).operations
/-- Arithmetic and zero-test work for the matrix phase on its stopped raw tape; random draws are counted separately. -/

def matrixPhaseWork (left right : V F m)
    (trace : StoppedTape (Matrix (Fin m) (Fin m) F)) : ℕ :=
  matrixTapeWork trace+matrixActionWork (matrixReturned trace.2.2) left right
/-- Every raw square-matrix proposal contains exactly `m²` field samples. -/

def matrixRandomWork (trace : StoppedTape (Matrix (Fin m) (Fin m) F)) : ℕ :=
  traceNatWork (fun _ => m*m) trace
/-- The total matrix-phase work includes scalar arithmetic, zero tests, and all sampled matrix coordinates. -/
def matrixPhaseTotalWork (left right : V F m)
    (trace : StoppedTape (Matrix (Fin m) (Fin m) F)) : ℕ :=
  matrixPhaseWork left right trace+matrixRandomWork trace
end
end CircuitCompiler.Rectangular.SamplerCost
end CompletionSampling

section RectangularExecution

namespace CircuitCompiler.Rectangular.AttemptSampler
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- The distribution of every rejected zero-vector proposal before the sampled nonzero row. -/
def rowRejectedDistribution {n : ℕ} (hn : 1 ≤ n) : PMF (RowPrefix F n) :=
  prefixDistribution FiniteDistribution.uniform nonzeroTest (row_acceptance_pos hn)
/-- Sample the independent internal row and affine-completion rejection records of one shortening proposal. -/
def markDistribution {n t : ℕ} (hn : 1 ≤ n) (u : U F (n+t)) (a : U F n) :
    PMF (Mark (m := n+t) a) :=
  (rowRejectedDistribution hn).bind (fun r => (CompletionSampler.rejectedDistribution u a).map (fun c => (r,c)))
end
end CircuitCompiler.Rectangular.AttemptSampler
namespace CircuitCompiler.Rectangular.Taped
open Refresh MatrixRefresh Sampling Sampling.Unbounded
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n t : ℕ}
/-- One common carrier for input-dependent private sampler marks. -/

abbrev Mark (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n m : ℕ) :=
  (a : U F n) × AttemptSampler.Mark (m := m) a
/-- All internal failed prefixes, with the sampled row retained as a tag. There is no assumption that this distribution is independent of `u` or `a`. -/

def markDistribution (hn : 2 ≤ n) (u : U F (n+t)) (a : U F n) : PMF (Mark F n (n+t)) :=
  (AttemptSampler.markDistribution (Nat.le_trans (by decide : 1 ≤ 2) hn) u a).map (Sigma.mk a)
/-- Empty prefixes make decoding total off the sampler's support. -/
def emptyMark (a : U F n) : AttemptSampler.Mark (m := n+t) a :=
  (⟨0, PUnit.unit⟩, ⟨0, PUnit.unit⟩)
/-- Recover every raw field proposal in one marked outer attempt. Off-support mismatched tags are mapped to empty prefixes without changing its `(A,H)`. -/

def rawAttempt (u : U F (n+t)) (p : Attempt (n := n) u) (mark : Mark F n (n+t)) :
    AttemptSampler.Record (n := n) u :=
  if h : mark.1 = p.val.1 then AttemptSampler.reconstruct u p (h ▸ mark.2)
  else AttemptSampler.reconstruct u p (emptyMark p.val.1)
/-- The actual outer loop, retaining internal row and completion tapes on all failed outer attempts as well as the terminal successful attempt. -/

def fullTapeDistribution (hn : 2 ≤ n) (u v : U F (n+t)) :
    PMF (MarkedTape (Attempt (n := n) u) (Mark F n (n+t))) :=
  markedDistribution (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0))
    (attempt_acceptance_pos hn u v) (fun p => markDistribution hn u p.val.1)
/-- Zip every primitive proposal with its private mark to recover its entire raw internal sampling execution. -/

def rawPrefix (u : U F (n+t)) : (k : ℕ) → Tape (Attempt (n := n) u) k →
    Tape (Mark F n (n+t)) k → Tape (AttemptSampler.Record (n := n) u) k
  | 0, _, _ => PUnit.unit
  | k+1, a, b => (rawAttempt u a.1 b.1,rawPrefix u k a.2 b.2)
/-- Reconstruct the complete physical outer-rejection trace from abstract attempts and their internal marks. -/
def rawTrace (u : U F (n+t))
    (z : MarkedTape (Attempt (n := n) u) (Mark F n (n+t))) :
    StoppedTape (AttemptSampler.Record (n := n) u) :=
  ⟨z.1.1,(rawPrefix u z.1.1 z.1.2.1 z.2.1,rawAttempt u z.1.2.2 z.2.2)⟩
end
end CircuitCompiler.Rectangular.Taped
namespace CircuitCompiler.Rectangular
open Refresh MatrixRefresh
open _root_.CircuitCompiler.Composition _root_.CircuitCompiler.Composition.TopologicalExecution Sampling Sampling.Unbounded
noncomputable section
variable {F O A BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [Fintype A] [Fintype BL] [Fintype BR] {n t : ℕ}
namespace Taped
/-- Run the shortening sampler, retain both permitted local answers, and attach the supplied work function evaluated on that same marked tape. -/
def costedShorteningExecution {s : F} (hn : 2 ≤ n) (fallback : Fiber F n s)
    (left : A → O → (u : U F (n+t)) → StoppedTape (AttemptSampler.Record (n := n) u) → BL)
    (right : A → O → U F (n+t) → RightView F n (n+t) → BR)
    (o : O × O) (x : Fiber F (n+t) s) (α : A)
    (work : MarkedTape (Attempt (n := n) x.val.L) (Mark F n (n+t)) → ℕ) :
    PMF ((Fiber F n s × (A × (BL × BR))) × ℕ) :=
  (fullTapeDistribution hn x.val.L x.val.R).map (fun z =>
    ((returnedOutput fallback x z.1.2.2,
      (α,(left α o.1 x.val.L (rawTrace x.val.L z),right α o.2 x.val.R (rightView z.1)))),work z))
end Taped
namespace FullyTapedStrategy
variable {ML MR : Type*} [Fintype ML] [Fintype MR]
variable {inputs : ℕ} {hdim : n*n+1 = n+t}
/-- Complete gate execution with supplied work functions. The matrix work function receives every raw proposal; the shortening work function receives the internal sampler tapes at every outer attempt. `costedGate` below supplies the concrete counters. -/

def costedExecution (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → (ML × MR) × (BL × BR)) (left right : State F n)
    (matrixWork : StoppedTape (Matrix (Fin (n+t)) (Fin (n+t)) F) → ℕ)
    (shorteningWork : (u v : U F (n+t)) →
      MarkedTape (Attempt (n := n) u) (Taped.Mark F n (n+t)) → ℕ) :
    PMF ((State F n × ((ML × MR) × (BL × BR))) × ℕ) :=
  (distribution FiniteDistribution.uniform invertibleTest (matrixAcceptancePositive (F := F) (n+t))).bind
    (fun matrixTape =>
      let M := matrixReturned matrixTape.2.2
      let α := (strategy.matrixLeft i gate history (augmentedOldPorts left right).1 matrixTape,
        strategy.matrixRight i gate history (augmentedOldPorts left right).2 matrixTape)
      let x := refreshInFiber (gateInput (augmentedLeftFeature hdim gate.kind.affineConstant)
        (augmentedRightFeature hdim) (augmentedOldPorts left right)) M
      (Taped.costedShorteningExecution hn
        (TapedAugmentedStrategy.fallback (hdim := hdim) hn gate left right)
        (strategy.left i gate history) (strategy.right i gate history)
        (augmentedOldPorts left right) x α (shorteningWork x.val.L x.val.R)).map
          (fun z => ((z.1.1.val,z.1.2),matrixWork matrixTape+z.2)))
/-- The same costed implementation on the compiler's share-pair carrier. -/

def costedShareExecution (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → (ML × MR) × (BL × BR)) (left right : U F n × U F n)
    (matrixWork : StoppedTape (Matrix (Fin (n+t)) (Fin (n+t)) F) → ℕ)
    (shorteningWork : (u v : U F (n+t)) →
      MarkedTape (Attempt (n := n) u) (Taped.Mark F n (n+t)) → ℕ) :
    PMF (((U F n × U F n) × ((ML × MR) × (BL × BR))) × ℕ) :=
  (strategy.costedExecution hn i gate history ((stateEquivProd F n).symm left)
    ((stateEquivProd F n).symm right) matrixWork shorteningWork).map
      (fun z => ((stateEquivProd F n z.1.1,z.1.2),z.2))
end FullyTapedStrategy
end
end CircuitCompiler.Rectangular
namespace CircuitCompiler.Rectangular.Taped
open Refresh MatrixRefresh Sampling Sampling.Unbounded Gaussian
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n t : ℕ}
/-- Multiplication by the sampled rectangular matrix, followed by the nonzero test. -/

def attemptOutputWork (u v : U F (n+t)) (p : Attempt (n := n) u) : ℕ :=
  ((mulVecData (materialize p.val.2.val) (Vector.ofFn v.val)).bind scanNonzero).operations
/-- Count both internal rejection loops, the completion pivot search, and the right-output multiplication and nonzero test. -/

def internalWork (u v : U F (n+t)) (p : Attempt (n := n) u)
    (mark : AttemptSampler.Mark (m := n+t) p.val.1) : ℕ :=
  traceNatWork (fun row => (scanNonzero (Vector.ofFn row)).operations)
      (AttemptSampler.reconstructRow mark.1 p.val.1) +
  traceNatWork (fun w => (SamplerCost.completionProposal u p.val.1 w).operations)
      (CompletionSampler.reconstruct u p.val.1 mark.2 ⟨p.val.2,p.property⟩) +
  (CompletionSampler.pivotSearch p.val.1).operations + attemptOutputWork u v p
/-- The tags merely make the mark carrier common to every attempt. -/

def markedAttemptWork (u v : U F (n+t)) (p : Attempt (n := n) u)
    (mark : Mark F n (n+t)) : ℕ :=
  if h : mark.1 = p.val.1 then internalWork u v p (h ▸ mark.2)
  else internalWork u v p (emptyMark p.val.1)
/-- Charge actual counted work to every outer attempt, including failed ones. -/

def prefixShorteningWork (u v : U F (n+t)) : (k : ℕ) → Tape (Attempt (n := n) u) k →
    Tape (Mark F n (n+t)) k → ℕ
  | 0,_,_ => 0
  | k+1,a,b => markedAttemptWork u v a.1 b.1+prefixShorteningWork u v k a.2 b.2
/-- Sum the arithmetic and zero-test work of every rejected and accepted marked shortening attempt. -/
def shorteningWork (u v : U F (n+t))
    (z : MarkedTape (Attempt (n := n) u) (Mark F n (n+t))) : ℕ :=
  prefixShorteningWork u v z.1.1 z.1.2.1 z.2.1+markedAttemptWork u v z.1.2.2 z.2.2
/-- Raw coordinates sampled by the two actual internal rejection loops. -/

def internalRandomWork (u : U F (n+t)) (p : Attempt (n := n) u)
    (mark : AttemptSampler.Mark (m := n+t) p.val.1) : ℕ :=
  traceNatWork (fun _ : V F n => n) (AttemptSampler.reconstructRow mark.1 p.val.1) +
  traceNatWork (fun _ : CompletionSampler.FreeRows F n (n+t) (CompletionSampler.pivot p.val.1) =>
    (n-1)*(n+t)) (CompletionSampler.reconstruct u p.val.1 mark.2 ⟨p.val.2,p.property⟩)
/-- Count the raw coordinates sampled by one shortening attempt, including its internal rejected proposals. -/
def markedAttemptRandomWork (u : U F (n+t)) (p : Attempt (n := n) u)
    (mark : Mark F n (n+t)) : ℕ :=
  if h : mark.1=p.val.1 then internalRandomWork u p (h ▸ mark.2)
  else internalRandomWork u p (emptyMark p.val.1)
/-- Sum all sampled-coordinate costs over a rejected outer shortening prefix. -/
def prefixRandomWork (u : U F (n+t)) : (k : ℕ) → Tape (Attempt (n := n) u) k →
    Tape (Mark F n (n+t)) k → ℕ
  | 0,_,_ => 0
  | k+1,a,b => markedAttemptRandomWork u a.1 b.1+prefixRandomWork u k a.2 b.2
/-- Count all raw coordinates sampled by the complete shortening execution. -/
def shorteningRandomWork (u : U F (n+t))
    (z : MarkedTape (Attempt (n := n) u) (Mark F n (n+t))) : ℕ :=
  prefixRandomWork u z.1.1 z.1.2.1 z.2.1+markedAttemptRandomWork u z.1.2.2 z.2.2
/-- Arithmetic, zero tests, and uniform field-coordinate samples on the whole trace. -/

def shorteningTotalWork (u v : U F (n+t))
    (z : MarkedTape (Attempt (n := n) u) (Mark F n (n+t))) : ℕ :=
  shorteningWork u v z+shorteningRandomWork u z
end CircuitCompiler.Rectangular.Taped
end RectangularExecution

section Initialization

namespace CircuitCompiler.Sampling.RawEncoding
open Refresh MatrixRefresh Unbounded Rectangular.Gaussian
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- An explicit eager test: scan the two raw rows, compute their dot product, and compare the resulting field element with the public target. -/

def proposal {n : ℕ} (s : F) (x : Raw F n) : Counted Bool :=
  (scanNonzero (Vector.ofFn x.1)).bind fun leftOK =>
  (scanNonzero (Vector.ofFn x.2)).bind fun rightOK =>
  (dotData (Vector.ofFn x.1) (Vector.ofFn x.2)).bind fun value =>
  ⟨leftOK && rightOK && decide (value=s),1⟩
end CircuitCompiler.Sampling.RawEncoding
namespace CircuitCompiler.Composition.TopologicalExecution
noncomputable section
universe u v
variable {E : Type u} {A : Type v} [Fintype E] [Fintype A] {inputs T : ℕ}
/-- A chronological runner whose next gate may depend on the current wire state and answer history. Each gate returns a fresh output, an answer, and a supplied natural-number work counter. -/

inductive CostedRunner (E : Type u) (A : Type v) [Fintype E] [Fintype A]
    (inputs : ℕ) : ℕ → Type (max u v) where
  | nil : CostedRunner E A inputs 0
  | snoc {T : ℕ} (prior : CostedRunner E A inputs T)
      (gate : RunState E A inputs T → PMF ((E × A) × ℕ)) :
      CostedRunner E A inputs (T+1)
namespace CostedRunner
/-- Chronological execution carries forward the accumulated natural cost. -/

def execute (initial : PMF ((Fin inputs → E) × ℕ)) :
    {T : ℕ} → CostedRunner E A inputs T → PMF (RunState E A inputs T × ℕ)
  | 0, .nil => initial.map (fun x => ((x.1,Fin.elim0),x.2))
  | _+1, .snoc prior gate => (prior.execute initial).bind (fun before =>
      (gate before.1).map (fun after =>
        (appendState (before.1,after.1),before.2+after.2)))
end CostedRunner
end
end CircuitCompiler.Composition.TopologicalExecution
end Initialization

section CountedExecution

namespace CircuitCompiler.Rectangular.FullyTapedStrategy
open Refresh MatrixRefresh
open _root_.CircuitCompiler.Composition _root_.CircuitCompiler.Composition.TopologicalExecution Sampling Sampling.Unbounded
noncomputable section
variable {F ML MR BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
  {n t inputs : ℕ} {hdim : n*n+1 = n+t}
/-- There are two tensor features, each using `n²` field products. The matrix phase then draws and tests every raw square matrix and applies its accepted matrix and inverse to the two long features. -/

def implementedMatrixWork {w : ℕ} (gate : Gate F w) (left right : State F n)
    (trace : StoppedTape (Matrix (Fin (n+t)) (Fin (n+t)) F)) : ℕ :=
  (Gaussian.augmentedShareData gate.kind.affineConstant
    (Vector.ofFn left.L.val) (Vector.ofFn right.L.val)).operations+
  (Gaussian.augmentedShareData (1 : F)
    (Vector.ofFn left.R.val) (Vector.ofFn right.R.val)).operations+
  SamplerCost.matrixPhaseTotalWork
    (augmentedLeftFeature hdim gate.kind.affineConstant (augmentedOldPorts left right).1).val
    (augmentedRightFeature hdim (augmentedOldPorts left right).2).val trace
end
end CircuitCompiler.Rectangular.FullyTapedStrategy
namespace CircuitCompiler.Sampling.RawEncoding
open Refresh MatrixRefresh Unbounded _root_.CircuitCompiler.Composition
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- Raw-coordinate draws plus the operations of the concrete acceptance test. -/

def proposalWork {n : ℕ} (s : F) (x : Raw F n) : ℕ := 2*n+(proposal s x).operations
/-- One initializer, retaining the actual work of all unsuccessful proposals. -/

def sampleCosted {n : ℕ} (hn : 2 ≤ n) (s : F) : PMF (State F n × ℕ) :=
  (tapeDistribution hn s).map (fun tape =>
    ((returned hn s tape.2.2).val,traceNatWork (proposalWork s) tape))
/-- Sequential raw initialization with its accumulated actual work. -/

def initializeCosted {n : ℕ} (hn : 2 ≤ n) :
    {inputs : ℕ} → (Fin inputs → F) → PMF ((Fin inputs → State F n) × ℕ)
  | 0,_ => PMF.pure (Fin.elim0,0)
  | k+1,input => (initializeCosted hn (Fin.init input)).bind (fun earlier =>
      (sampleCosted hn (input (Fin.last k))).map (fun last =>
        (Fin.snoc earlier.1 last.1,earlier.2+last.2)))
/-- The same concrete initialized states in the share-pair carrier. -/

def initializeSharesCosted {n inputs : ℕ} (hn : 2 ≤ n) (input : Fin inputs → F) :
    PMF ((Fin inputs → U F n × U F n) × ℕ) :=
  (initializeCosted hn input).map (fun x => ((fun i => stateEquivProd F n (x.1 i)),x.2))
end
end CircuitCompiler.Sampling.RawEncoding
namespace CircuitCompiler.Rectangular.Implemented
open Refresh MatrixRefresh _root_.CircuitCompiler.Composition _root_.CircuitCompiler.Composition.TopologicalExecution Sampling Sampling.Unbounded

noncomputable section
variable {F ML MR BL BR V : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ML] [Nonempty ML] [Fintype MR] [Nonempty MR]
  [Fintype BL] [Nonempty BL] [Fintype BR] [Nonempty BR] [Fintype V]
  {n t inputs T k : ℕ} {hdim : n*n+1 = n+t}
/-- Actual gate output, local answers, and work of that same sampling run. -/

def costedGate (strategy : FullyTapedStrategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → (ML × MR) × (BL × BR)) (left right : U F n × U F n) :=
  strategy.costedShareExecution hn i gate history left right
    (FullyTapedStrategy.implementedMatrixWork (hdim := hdim) gate
      ((stateEquivProd F n).symm left) ((stateEquivProd F n).symm right))
    Taped.shorteningTotalWork
end
end CircuitCompiler.Rectangular.Implemented
end CountedExecution

/-!
# Efficient simulation model

The public model collects probability and work accounting, the counted physical instruction runner, and the direct, causal, and stateful simulators. Named sections separate these interfaces. It imports the compiler model and contains the additional constructions needed by the counted simulator. It imports no Proofs module.

The reference statements appear below. Independent proofs in `Proofs.EfficientSimulaiton` use separate model copies with completed certificates and do not import these admissions.
-/

noncomputable section Probability

/-!
## Probability and cost model for efficient simulation

For any complete-view space V, a counted run is a PMF on V × ℕ. To keep the formal cost model simple, its private natural counter records random sampling, scalar arithmetic and tests, and explicitly charged preparation. Routine memory-access and address bookkeeping is left to conventional implementation analysis. Projecting to V gives the visible distribution. The direct simulator receives an authorized output, and the stateful simulator receives an ideal oracle. Their concrete interfaces appear in the direct and stateful sections below.

Nonnegative extended-real expectations allow additional work to have infinite expectation. Charging R for each of c separately costed calls adds cR to the expected counter, and an arbitrary joint accounting Q of extra work adds its actual expectation without an independence assumption. Each concrete instance supplies its own polynomial bound on this counter, including the corresponding costs of preparation, every rejected proposal, and every shortening retry.
-/


namespace EfficientSimulation

/-- Auxiliary inputs are finite binary strings, supplied identically in the real and simulated experiments. -/
abbrev AuxiliaryInput := List Bool

/-- The expected work counter is 𝔼[w] = ∑_(v,w) P(v,w)·w ∈ [0,∞]. -/
def expectedWork {V : Type*} (run : PMF (V × ℕ)) : ℝ≥0∞ :=
  ∑' z, run z * (z.2 : ℝ≥0∞)

/-- A charge R for each of c calls sends (v,w) to (v,w+cR), preserving the visible result. -/
def chargeOracleBudget {V : Type*} (run : PMF (V × ℕ)) (calls R : ℕ) : PMF (V × ℕ) :=
  run.map (fun z => (z.1, z.2 + calls * R))

/-- A joint distribution Q on ((v,w),a) records additional work a, possibly correlated with the entire run. -/
abbrev AccountingLaw (V : Type*) := PMF ((V × ℕ) × ℕ)

/-- Correct accounting has first marginal P: π₁_*Q=P. No independence or finiteness assumption is imposed. -/
def AccountsFor {V : Type*} (run : PMF (V × ℕ)) (accounting : AccountingLaw V) : Prop :=
  accounting.map Prod.fst = run

/-- Total work is obtained by the map ((v,w),a) ↦ (v,w+a). -/
def totalRun {V : Type*} (accounting : AccountingLaw V) : PMF (V × ℕ) :=
  accounting.map (fun z => (z.1.1, z.1.2 + z.2))

/-- The actual additional expectation is 𝔼_Q[a]=∑ Q((v,w),a)·a ∈ [0,∞]. -/
def additionalExpectedWork {V : Type*} (accounting : AccountingLaw V) : ℝ≥0∞ :=
  ∑' z, accounting z * (z.2 : ℝ≥0∞)

/-- Discard the private counter and retain the complete finite visible distribution. -/
def viewLaw {V : Type*} [Fintype V] (run : PMF (V × ℕ)) : Refresh.FiniteDistribution V :=
  CircuitCompiler.Sampling.Unbounded.toFinite (run.map Prod.fst)

end EfficientSimulation
end Probability

noncomputable section Execution

/-!
## Counted execution of computation, refresh, and public sampling

The sampler, leakage record, and counter come from the same run. Every rejected matrix proposal and rectangular shortening retry is charged. Each instruction's sampler receives only its active predecessor encodings and the prior answer vector.
-/


namespace CircuitCompiler.Operations.Counted

open Refresh MatrixRefresh Sampling Sampling.Unbounded
  _root_.CircuitCompiler.Composition _root_.CircuitCompiler.Composition.TopologicalExecution

variable {F ML MR BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
  {n t inputs S : ℕ} {hdim : n*n+1 = n+t}

/-- The counted refresh executes the actual raw sampler and both matrix operations, retaining the same full tape used by its leakage callbacks. -/
def refreshExecution (strategy : Operations.Strategy F ML MR BL BR n t inputs hdim)
    (i : ℕ) (port : Fin (inputs+i)) (history : Fin i → Operations.Answer ML MR BL BR)
    (old : U F n × U F n) : PMF (((U F n × U F n) × Operations.Answer ML MR BL BR) × ℕ) :=
  (distribution (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin n) (Fin n) F))
    invertibleTest (matrixAcceptancePositive (F := F) n)).map fun tape =>
      let M := matrixReturned tape.2.2
      (((rowRefresh old.1 M,columnRefresh old.2 M),answerRegroupForward ML MR BL BR
        (strategy.refreshLeft i port history old.1 tape,strategy.refreshRight i port history old.2 tape)),
        Rectangular.SamplerCost.matrixPhaseTotalWork old.1.val old.2.val tape)

/-- The sampled encoding and both answers are read from the same raw-pair tape whose field-coordinate samples and acceptance tests are counted. -/
def publicExecution (strategy : Operations.Strategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (value : F) (history : Fin i → Operations.Answer ML MR BL BR) :
    PMF (((U F n × U F n) × Operations.Answer ML MR BL BR) × ℕ) :=
  (RawEncoding.tapeDistribution hn value).map fun tape =>
    let output := (RawEncoding.returned hn value tape.2.2).val
    (((output.L,output.R),answerRegroupForward ML MR BL BR
      (strategy.publicLeft i value history tape,strategy.publicRight i value history output.R)),
      traceNatWork (RawEncoding.proposalWork value) tape)

/-- Each instruction runs its concrete sampler, with no cost supplied by an abstract oracle or hypothesis. Adversarial computation is charged separately. -/
def instructionExecution (strategy : Operations.Strategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (i : ℕ) (instruction : Instruction F (inputs+i))
    (history : Fin i → Operations.Answer ML MR BL BR) (old : Fin (inputs+i) → U F n × U F n) :=
  match instruction with
  | .compute gate => Rectangular.Implemented.costedGate strategy.compute hn i gate history
      (old gate.left) (old gate.right)
  | .refresh port => refreshExecution strategy i port history (old port)
  | .sample value => publicExecution strategy hn i value history

/-- Accumulate actual sampler work chronologically while retaining all wires and the complete answer history. -/
def runner (strategy : Operations.Strategy F ML MR BL BR n t inputs hdim) (hn : 2 ≤ n) :
    {S : ℕ} → Operations.Program F inputs S → CostedRunner (U F n × U F n) (Operations.Answer ML MR BL BR) inputs S
  | 0,.nil => .nil
  | _+1,.snoc prior instruction => (runner strategy hn prior).snoc
      (fun state => instructionExecution strategy hn _ instruction state.2 state.1)

/-- Only trusted inputs are initialized without leakage; every subsequent public sampler and control refresh belongs to the counted physical runner. -/
def execution (program : Operations.Program F inputs S)
    (strategy : Operations.Strategy F ML MR BL BR n t inputs hdim) (hn : 2 ≤ n)
    (input : Fin inputs → F) :=
  (runner strategy hn program).execute (RawEncoding.initializeSharesCosted hn input)

end CircuitCompiler.Operations.Counted
end Execution

noncomputable section DirectModel

/-!
## Actual counted dummy-input simulation

The sampler is the common counted physical instruction runner, including every rejected proposal, inner matrix rejection and outer shortening retry. The direct source has no trusted control or selector bank. The simulator materializes zero private values, executes the actual direct compiler against the supplied adversary, discards its hidden encoding array, and copies the authorized plaintext output supplied by its caller.

The probability and work-accounting section above describes the simplified cost convention. Adversary and leakage evaluation are charged separately. The exact callback count is 8T + 2U; a leakage-output bit bound does not imply any bound on the time taken by those callbacks.
-/


namespace EfficientSimulation.Direct
open Compiler Compiler.Direct CircuitCompiler
  CircuitCompiler.Rectangular.Gaussian

variable {P U T k : ℕ}

/-- The adversary selects an admissible direct-compiler strategy from its auxiliary input, independently of the actual private source values. -/
abbrev Adversary (source : Source P U T k) (n ml sl : ℕ) :=
  AuxiliaryInput → Compiler.Direct.Strategy source n ml sl

/-- Materialize the zero private input array, charging one preparation operation per entry. -/
def preparation (P : ℕ) : Counted (Vector Refreshing.Bit P) :=
  tabulate fun _ => ⟨0,1⟩

/-- Copy the supplied authorized output tuple, charging one preparation operation per output position. -/
def outputPreparation {k : ℕ} (output : Fin k → Refreshing.Bit) : Counted (Vector Refreshing.Bit k) :=
  tabulate fun j => ⟨output j,1⟩

/-- One counted run returns the visible transcript/plaintext pair jointly with its private work counter. -/
abbrev Simulator (source : Source P U T k) (n ml sl : ℕ) :=
  AuxiliaryInput → (Fin k → Refreshing.Bit) → PMF (Compiler.Direct.View source ml sl × ℕ)

/-- Execute zero private input encodings and every actual compiled operation, discard all dummy pairs, and report the independently supplied authorized plaintext output. -/
def simulator (source : Source P U T k) {n ml sl : ℕ}
    (adversary : Adversary source n ml sl) (hn : 2≤n) : Simulator source n ml sl :=
  fun aux output =>
    let prepared := preparation P
    let reported := outputPreparation output
    (CircuitCompiler.Operations.Counted.execution source.compiledProgram (adversary aux) hn
      (fun i=>prepared.value.get i)).map fun z=>
        ((Composition.vectorToAnswers _ _ z.1.2,fun j=>reported.value.get j),
          prepared.operations+reported.operations+z.2)

end EfficientSimulation.Direct
end DirectModel

noncomputable section AdaptiveModel

/-!
## Counted physical execution with online public inputs

Each operation runs the same counted matrix, refresh, public-encoding, and shortening samplers as the direct compiler. Online public values are selected from earlier answers. Work counts include every rejected proposal and retry; adversary, leakage, and ideal-oracle evaluation are charged separately.
-/


namespace EfficientSimulation.Adaptive
open Refresh CircuitCompiler Compiler.Adaptive
  CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution
  CircuitCompiler.Sampling.Unbounded

variable {ML MR BL BR : Type*} [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
  {n t P S : ℕ} {hdim : n*n+1 = n+t}

/-- The actual counted runner on the fixed chronological port graph, with each current public value selected online. -/
def runner (strategy : CircuitCompiler.Operations.Strategy Refreshing.Bit ML MR BL BR n t P hdim)
    (hn : 2 ≤ n) :
    {S : ℕ} → CircuitCompiler.Operations.Program Refreshing.Bit P S →
      SampleValues Refreshing.Bit (CircuitCompiler.Operations.Answer ML MR BL BR) S →
      CostedRunner (U Refreshing.Bit n×U Refreshing.Bit n) (CircuitCompiler.Operations.Answer ML MR BL BR) P S
  | 0, .nil, _ => .nil
  | _+1, .snoc prior instruction, values =>
      (runner strategy hn prior (fun i => values i.castSucc)).snoc (fun state =>
        CircuitCompiler.Operations.Counted.instructionExecution strategy hn _
          (selectInstruction instruction (values (Fin.last _) state.2)) state.2 state.1)

/-- Trusted initialization is performed once, followed by all interleaved public samplers, port refreshes, and computation instructions. -/
def execution (program : CircuitCompiler.Operations.Program Refreshing.Bit P S)
    (strategy : CircuitCompiler.Operations.Strategy Refreshing.Bit ML MR BL BR n t P hdim)
    (hn : 2 ≤ n) (values : SampleValues Refreshing.Bit (CircuitCompiler.Operations.Answer ML MR BL BR) S)
    (input : Fin P → Refreshing.Bit) :=
  (runner strategy hn program values).execute (CircuitCompiler.Sampling.RawEncoding.initializeSharesCosted hn input)

end EfficientSimulation.Adaptive
end AdaptiveModel

noncomputable section StatefulModel

/-!
## Counted oracle simulation for a stateful circuit

The simulator uses the same causal public interaction and zero-register execution as the security theorem, with the same cost convention as the direct simulator. Its counter adds `m + T*k` for preparing the zero state and reporting the authorized output bits. The oracle's internal computation and the adversary's input choice, public-history processing, and leakage computations are separate costs, just as callback work is separate in the stateless simulator.
-/

namespace EfficientSimulation.Stateful
open Compiler Compiler.Stateful

variable {m d c g k n ml sl : ℕ}

/-- The counted simulator is one oracle-parametric function, independent of the actual initial register state. Its private work counter is not part of the adversary's view. -/
def simulator (circuit : Circuit m d c g k) (T : ℕ)
    (adversary : Compiler.Stateful.Adversary m d k n ml sl) (hn : 2 ≤ n)
    (oracle : Oracle d k) : PMF (circuit.View T ml sl × ℕ) :=
  (EfficientSimulation.Adaptive.execution (circuit.unrolling T).schedule.compile.program
    (adversary.strategy c g T oracle) hn (circuit.sampleValues T adversary oracle)
    (fun _ => 0)).map fun result =>
      (circuit.observe T adversary oracle result.1.2,m+T*k+result.2)

end EfficientSimulation.Stateful
end StatefulModel

/-!
# Efficient simulation in Theorems 5.2 and 6.1

These reference statements specify the direct and stateful simulators, their exact visible marginals, expected counters, and privacy guarantees. The comparator loads this file's admitted theorem and certificates through `Proofs.ReferenceClaims`. It checks them against the separate proof environment, with the simulator guarantees proved in `Proofs.EfficientSimulaiton.Direct.Theorem52` and `Proofs.EfficientSimulaiton.Stateful.Theorem61`.
-/

/-!
## Claims checked by the comparator

The two claims below state the direct and stateful simulator guarantees,
including exact marginals and running time. Their independent proofs are under
`Proofs/EfficientSimulaiton`.
-/

section SimulationClaims
namespace EfficientSimulation.Direct
def directSimulationClaim : Prop :=
  ∃ C : ℝ, 1≤C ∧
      ∀ (n ml sl P U T k : ℕ) (hn : 2≤n)
        (source : Compiler.Direct.Source P U T k) (adversary : Adversary source n ml sl),
        ∃ S : Simulator source n ml sl,
          S=simulator source adversary hn ∧
          (∀ (aux : AuxiliaryInput) (y : Fin k → Refreshing.Bit),
            viewLaw (S aux y)=Compiler.Direct.simulatedView (adversary aux) hn y ∧
            expectedWork (S aux y)≤(P+k+P*(16*(6*n+1))+source.operationCount*(100*(n*n+2)^3):ℝ≥0∞) ∧
            (∀ R : ℕ, expectedWork (chargeOracleBudget (S aux y) (8*T+2*U) R)≤
              (P+k+P*(16*(6*n+1))+source.operationCount*(100*(n*n+2)^3)+(8*T+2*U)*R:ℝ≥0∞)) ∧
            (∀ accounting : AccountingLaw (Compiler.Direct.View source ml sl),
              AccountsFor (S aux y) accounting→expectedWork (totalRun accounting)≤
                (P+k+P*(16*(6*n+1))+source.operationCount*(100*(n*n+2)^3):ℝ≥0∞)+additionalExpectedWork accounting)) ∧
          (∀ (κ : ℝ) (_hκ : 1≤κ) (aux : AuxiliaryInput) (input : Fin P → Refreshing.Bit),
            C*(κ+((ml+sl:ℕ):ℝ)+Real.log ((source.operationCount:ℝ)+2))≤(n:ℝ)→
            Refresh.statisticalDistance (Compiler.Direct.realView (adversary aux) hn input)
              (viewLaw (S aux (source.outputValues input)))≤Real.rpow 2 (-κ))
end EfficientSimulation.Direct

namespace EfficientSimulation.Stateful
def statefulSimulationClaim : Prop :=
  ∀  {m d c g k n ml sl : ℕ} (circuit : Compiler.Stateful.Circuit m d c g k)
    (T : ℕ) (adversary : Compiler.Stateful.Adversary m d k n ml sl) (hn : 2 ≤ n),
    ∃ simulate : Compiler.Stateful.Oracle d k → PMF (circuit.View T ml sl × ℕ),
      simulate = simulator circuit T adversary hn ∧
      (∀ oracle,
        viewLaw (simulate oracle) = circuit.simulatedView T adversary hn oracle ∧
        expectedWork (simulate oracle) ≤ (m+T*k+(m*(16*(6*n+1))+(circuit.operationCount T)*(100*(n*n+2)^3)):ℝ≥0∞) ∧
        ∀ R : ℕ, expectedWork (chargeOracleBudget (simulate oracle) (circuit.callbackCount T) R) ≤
          (m+T*k+(m*(16*(6*n+1))+(circuit.operationCount T)*(100*(n*n+2)^3))+circuit.callbackCount T*R:ℝ≥0∞)) ∧
      ((1000000*(circuit.operationCount T:ℝ)*(((2 ^ (2 * (ml + sl)) : ℕ) : ℝ))^9*(((2 ^ n - 1 : ℕ) : ℝ))^(-1/27:ℝ)) ≤
        2000000*(circuit.operationCount T:ℝ)*(2:ℝ)^(18*((ml+sl:ℕ):ℝ)-(n:ℝ)/27)) ∧
      (∀ initial : Fin m → Refreshing.Bit,
        Refresh.statisticalDistance (circuit.realView T adversary hn initial)
          (viewLaw (simulate (circuit.oracle initial))) ≤ min 1 ((1000000*(circuit.operationCount T:ℝ)*(((2 ^ (2 * (ml + sl)) : ℕ) : ℝ))^9*(((2 ^ n - 1 : ℕ) : ℝ))^(-1/27:ℝ))) ∧
        ∀ (κ : ℝ) (_hκ : 1 ≤ κ),
          12000*(κ+((ml+sl:ℕ):ℝ)+Real.log ((circuit.operationCount T:ℝ)+2)) ≤ n →
          Refresh.statisticalDistance (circuit.realView T adversary hn initial)
            (viewLaw (simulate (circuit.oracle initial))) ≤ (2:ℝ)^(-κ))
end EfficientSimulation.Stateful
end SimulationClaims

section SimulationMainTheorem
namespace EfficientSimulation
theorem main_theorem : Direct.directSimulationClaim ∧ Stateful.statefulSimulationClaim := by
  sorry
end EfficientSimulation
end SimulationMainTheorem
