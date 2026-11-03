import Proofs.EfficientSimulaiton.Sampling.GaussianSolveCost
import Proofs.Compiler.GateApproximation.MatrixPhase.MatrixSamplerTapes
import Proofs.EfficientSimulaiton.Sampling.RectangularSamplerCost
import Proofs.EfficientSimulaiton.Sampling.SamplerPMFCost
import Proofs.Compiler.Construction.Parameters



/-!
# Work of the complete square-matrix phase

Raw matrix trials are tested by executable Gaussian elimination. The accepted matrix acts on the left vector by ordinary multiplication and on the right vector by the proved Gaussian solver. All rejected raw matrices are charged.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal

namespace CircuitCompiler.Rectangular.SamplerCost

open Refresh MatrixRefresh Sampling Sampling.Unbounded Gaussian

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

variable {m : ℕ}

/-- The actual counted pair of linear-algebra routines whose cost is charged. -/
/-
Mathematical definition (normal notation): For M ∈ GLₘ(F); left, right ∈ V(F, m), define

matrixAction(M, left, right) := bind(mulVecData(materialize(M.val.transpose), Vector.ofFn(left)), (newLeft ↦ bind(solve(m, materialize(M), Vector.ofFn(right)), (newRight ↦ Counted.pure((newLeft, newRight)))))).
-/
def matrixAction (M : Refresh.«GL» F m) (left right : V F m) :
    Counted (Vector F m × Option (Vector F m)) :=
  (mulVecData (materialize M.val.transpose) (Vector.ofFn left)).bind fun newLeft =>
    (solve m (materialize M.val) (Vector.ofFn right)).bind fun newRight =>
      Counted.pure (newLeft,newRight)

omit [Fintype F] in
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For M ∈ GLₘ(F); left, right ∈ V(F, m), we have

operations(matrixAction(M, left, right)) = matrixActionWork(M, left, right).
-/
@[simp] theorem matrixAction_operations (M : Refresh.«GL» F m) (left right : V F m) :
    (matrixAction M left right).operations = matrixActionWork M left right := by
  simp only [matrixAction,matrixActionWork,Counted.bind,Counted.pure,Nat.add_zero]

omit [Fintype F] in
/-- The counted routines return exactly both mathematical refresh equations. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For M ∈ GLₘ(F); left, right ∈ V(F, m), we have

value(matrixAction(M, left, right)) = (Vector.ofFn(Matrix.vecMul(left, M)), some(Vector.ofFn(Matrix.mulVec((M)⁻¹, right)))).
-/
theorem matrixAction_value (M : Refresh.«GL» F m) (left right : V F m) :
    (matrixAction M left right).value =
      (Vector.ofFn (Matrix.vecMul left M.val),some (Vector.ofFn (Matrix.mulVec (M⁻¹).val right))) := by
  simp only [matrixAction,Counted.bind,Counted.pure,solve_eq_inverse,get_ofFn]
  congr 1
  apply Vector.ext
  intro i hi
  have he := mulVecData_value (materialize M.val.transpose) (Vector.ofFn left) ⟨i,hi⟩
  simpa [entries_materialize,Matrix.mulVec_transpose,Vector.get] using he

omit [Fintype F] in
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For M ∈ GLₘ(F); left, right ∈ V(F, m), we have

matrixActionWork(M, left, right) ≤ 10 · (m + 1)³.
-/
theorem matrixActionWork_le (M : Refresh.«GL» F m) (left right : V F m) :
    matrixActionWork M left right ≤ 10*(m+1)^3 := by
  have hs := solve_operations_le m (materialize M.val) (Vector.ofFn right)
  simp only [matrixActionWork,mulVecData_operations]
  nlinarith

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ, we have

ENNReal.ofReal((1 / acceptance(𝒰_(F^({0,…,m−1} × {0,…,m−1})), invertibleTest))) ≤ 4.
-/
private theorem matrix_inv_acceptance_le_four (m : ℕ) :
    ENNReal.ofReal (1/acceptance (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin m) (Fin m) F))
      invertibleTest) ≤ 4 := by
  have hp := matrix_acceptance_ge_quarter (F := F) m
  have h : 1/acceptance (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin m) (Fin m) F))
      invertibleTest ≤ (4:ℝ) := by
    apply (div_le_iff₀ (matrixAcceptancePositive (F := F) m)).mpr
    linarith
  simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal h

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

workExpectation(distribution(𝒰_(F^({0,…,m−1} × {0,…,m−1})), invertibleTest, matrixAcceptancePositive(F = F, m)), ((trace ↦ matrixTapeWork(trace)))) ≤ 12 · (m + 1)³.
-/
theorem matrixTapeWork_expected_le :
    workExpectation (distribution (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin m) (Fin m) F))
      invertibleTest (matrixAcceptancePositive (F := F) m))
      (fun trace => (matrixTapeWork trace : ℝ≥0∞)) ≤ 12*(m+1)^3 := by
  simp only [matrixTapeWork,traceNatWork_cast]
  have h := workExpectation_trace_le
    (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin m) (Fin m) F)) invertibleTest
    (matrixAcceptancePositive (F := F) m)
    (fun H => ((check m (materialize H)).operations : ℝ≥0∞)) (3*(m+1)^3)
    (fun H => by
      have hc : (check m (materialize H)).operations ≤ 3*(m+1)^3 := by
        simpa only [pow_succ,mul_assoc] using rankTest_operations_le H
      exact_mod_cast hc)
  have hbound := h.trans (mul_le_mul_left (matrix_inv_acceptance_le_four (F := F) m) _)
  convert hbound using 1 <;> first | rfl | ring

/-- This is an expectation of a natural-valued cost under the actual complete matrix sampler, not a runtime assumption on a primitive uniform-GL oracle. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For left, right ∈ V(F, m), we have

workExpectation(distribution(𝒰_(F^({0,…,m−1} × {0,…,m−1})), invertibleTest, matrixAcceptancePositive(F = F, m)), ((trace ↦ matrixPhaseWork(left, right, trace)))) ≤ 22 · (m + 1)³.
-/
theorem matrixPhaseWork_expected_le (left right : V F m) :
    workExpectation (distribution (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin m) (Fin m) F))
      invertibleTest (matrixAcceptancePositive (F := F) m))
      (fun trace => (matrixPhaseWork left right trace : ℝ≥0∞)) ≤ 22*(m+1)^3 := by
  simp only [matrixPhaseWork,Nat.cast_add,workExpectation_add]
  have ha : workExpectation (distribution (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin m) (Fin m) F))
      invertibleTest (matrixAcceptancePositive (F := F) m))
      (fun trace => (matrixActionWork (matrixReturned trace.2.2) left right : ℝ≥0∞)) ≤
      10*(m+1)^3 := by
    apply (workExpectation_mono _ (fun trace => ?_)).trans_eq (workExpectation_const _ _)
    exact_mod_cast matrixActionWork_le (matrixReturned trace.2.2) left right
  convert add_le_add (matrixTapeWork_expected_le (F := F) (m := m)) ha using 1; ring

/-- Even after fixing the accepted invertible matrix, its rejected raw tape has uniformly bounded expected testing work. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For M ∈ GLₘ(F), we have

workExpectation(matrixPrefixDistribution(F = F, m), ((failures ↦ matrixTapeWork(matrixTrace(failures, M))))) ≤ 12 · (m + 1)³.
-/
theorem matrixTapeWork_conditional_le (M : Refresh.«GL» F m) :
    workExpectation (matrixPrefixDistribution (F := F) m)
      (fun failures => (matrixTapeWork (matrixTrace failures M) : ℝ≥0∞)) ≤ 12*(m+1)^3 := by
  simp only [matrixTapeWork,traceNatWork_cast,matrixTrace,matrixPrefixDistribution]
  have h := prefixDistribution_traceWork_le
    (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin m) (Fin m) F)) invertibleTest
    (matrixAcceptancePositive (F := F) m)
    (fun H => ((check m (materialize H)).operations : ℝ≥0∞)) (3*(m+1)^3)
    (fun H => by
      have hc : (check m (materialize H)).operations ≤ 3*(m+1)^3 := by
        simpa only [pow_succ,mul_assoc] using rankTest_operations_le H
      exact_mod_cast hc) M.val
  have hbound := h.trans (mul_le_mul_left (matrix_inv_acceptance_le_four (F := F) m) _)
  convert hbound using 1 <;> first | rfl | ring

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): we have

workExpectation(distribution(𝒰_(F^({0,…,m−1} × {0,…,m−1})), invertibleTest, matrixAcceptancePositive(F = F, m)), ((trace ↦ matrixRandomWork(trace)))) ≤ 4 · m · m.
-/
theorem matrixRandomWork_expected_le :
    workExpectation (distribution (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin m) (Fin m) F))
      invertibleTest (matrixAcceptancePositive (F := F) m))
      (fun trace => (matrixRandomWork trace : ℝ≥0∞)) ≤ 4*m*m := by
  simp only [matrixRandomWork,traceNatWork_cast]
  have h := workExpectation_trace_le
    (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin m) (Fin m) F)) invertibleTest
    (matrixAcceptancePositive (F := F) m)
    (fun _ => ((m*m:ℕ):ℝ≥0∞)) ((m*m:ℕ):ℝ≥0∞) (fun _ => le_rfl)
  have hb := h.trans (mul_le_mul_left (matrix_inv_acceptance_le_four (F := F) m) _)
  simpa only [Nat.cast_mul,mul_assoc] using hb

/-- Scalar arithmetic, zero tests, and unbiased field samples in the actual unbounded matrix phase together have a polynomial expectation. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For left, right ∈ V(F, m), we have

workExpectation(distribution(𝒰_(F^({0,…,m−1} × {0,…,m−1})), invertibleTest, matrixAcceptancePositive(F = F, m)), ((trace ↦ matrixPhaseTotalWork(left, right, trace)))) ≤ 26 · (m + 1)³.
-/
theorem matrixPhaseTotalWork_expected_le (left right : V F m) :
    workExpectation (distribution (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin m) (Fin m) F))
      invertibleTest (matrixAcceptancePositive (F := F) m))
      (fun trace => (matrixPhaseTotalWork left right trace : ℝ≥0∞)) ≤ 26*(m+1)^3 := by
  simp only [matrixPhaseTotalWork,Nat.cast_add,workExpectation_add]
  have h := add_le_add (matrixPhaseWork_expected_le left right)
    (matrixRandomWork_expected_le (F := F) (m := m))
  apply h.trans
  have hpow : m*m ≤ (m+1)^3 := by
    calc
      m*m ≤ (m+1)^2 := by nlinarith
      _ ≤ (m+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hc : 22*(m+1)^3+4*m*m ≤ 26*(m+1)^3 := by
    calc
      _ = 22*(m+1)^3+4*(m*m) := by ring
      _ ≤ 22*(m+1)^3+4*((m+1)^3) := Nat.add_le_add_left (Nat.mul_le_mul_left 4 hpow) _
      _ = _ := by ring
  exact_mod_cast hc

end

end CircuitCompiler.Rectangular.SamplerCost
