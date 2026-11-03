import Proofs.Compiler.GateApproximation.Canonical
import Proofs.Compiler.GateApproximation.Shortening.PrivateRetries
import Proofs.Compiler.GateApproximation.Shortening.RectangularFractionalPhysicalGate
import Proofs.Compiler.GateApproximation.Shortening.RectangularFractionalProgram

set_option autoImplicit false

/-!
# Exact freshness and conditional leakage for the full shortening loop

The full physical shortening loop has the same uniform output marginal as its first accepted attempt. Conditioning on a particular returned encoding therefore does not magnify the first-attempt error: each conditional answer changes by at most 2/2ⁿ. This pointwise estimate is averaged through the matrix phase and is charged to the local approximation, rather than to the two endpoints of the circuit comparison.
-/

noncomputable section
open scoped BigOperators

namespace CompilerProof.FullRetry

open Refresh MatrixRefresh TableAnalysis CircuitCompiler CircuitCompiler.Rectangular
  CircuitCompiler.Sampling CircuitCompiler.ShorteningTransport CircuitCompiler.Shortening

/-- Discarding an answer from a distribution with a fixed tagged output returns that fixed output. -/
theorem tag_fst {Y Z W : Type*} [Fintype Y] [Fintype Z] [Fintype W]
    (P : FiniteDistribution Z) (y : Y) (f : Z → W) :
    (P.map (fun z => (y,f z))).map Prod.fst = FiniteDistribution.pure y := by
  classical
  rw [FiniteDistribution.map_map]
  ext x
  simp only [FiniteDistribution.map, FiniteDistribution.bind, FiniteDistribution.pure,
    Function.comp_def]
  by_cases h : y = x
  · simp [h, P.total]
  · simp [h, Ne.symm h]

/-- Sampling an unused random value before the same fixed distribution changes no probabilities. -/
theorem bind_const {X Y : Type*} [Fintype X] [Fintype Y]
    (P : FiniteDistribution X) (Q : FiniteDistribution Y) : P.bind (fun _ => Q) = Q := by
  ext y
  simp only [FiniteDistribution.bind, ← Finset.sum_mul, P.total, one_mul]

variable {F O A B : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype O] [DecidableEq O] [Nonempty O] [Fintype A] [Fintype B]
  {n t : ℕ}

/-- The two implementations of a successful shortening output return the same pair (A,HV), including their harmless fallback on impossible rejected terminal attempts. -/
theorem returnedOutput_eq_outputOr (u v : U F (n+t))
    (fallback : Fiber F n (dot u.val v.val)) (p : Attempt (n := n) u) :
    returnedOutput fallback ⟨⟨u,v⟩,rfl⟩ p = outputOr fallback p := by
  unfold returnedOutput outputOr
  split_ifs
  · apply Subtype.ext
    rfl
  · rfl

/-- For every fixed long input and matrix-phase answer, the full shortening loop returns exactly μₛ, even if the leakage inspects its entire retry tape. -/
theorem shortening_output_uniform {s : F} (hn : 2 ≤ n) (fallback : Fiber F n s)
    (leak : (x : Fiber F (n+t) s) → A → FullTape (n := n) x.val.L → FiniteDistribution B)
    (x : Fiber F (n+t) s) (α : A) :
    letI := fiber_nonempty F n hn s
    (Fractional.shorteningExecution hn fallback leak x α).map Prod.fst =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s)) := by
  classical
  rcases x with ⟨⟨u,v⟩, hx⟩
  change dot u.val v.val = s at hx
  subst s
  letI := fiber_nonempty F n hn (dot u.val v.val)
  unfold Fractional.shorteningExecution fullTapeAnswerDistribution
  rw [Unbounded.observeDistribution_map]
  simp_rw [tag_fst]
  rw [Unbounded.observeDistribution_pure]
  simpa only [fullTapeObserve, returnedOutput_eq_outputOr] using fullTape_returned_uniform hn u v fallback

/-- A complete gate has an exactly fresh short output for every fixed operand encoding. Neither its matrix answer nor its shortening answer is claimed independent of that output. -/
theorem fullGate_output_uniform (hn : 2 ≤ n) (a b : O → U F (n+t))
    (p : TableRectanglePartition O (Refresh.«GL» F (n+t)) A) (o : O × O)
    (fallback : Fiber F n (gateSecret a b o))
    (leak : (x : Fiber F (n+t) (gateSecret a b o)) → A →
      FullTape (n := n) x.val.L → FiniteDistribution B) :
    letI := fiber_nonempty F n hn (gateSecret a b o)
    (Fractional.fullGateExecution hn a b p o fallback leak).map Prod.fst =
      (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (gateSecret a b o))) := by
  letI := fiber_nonempty F n hn (gateSecret a b o)
  unfold Fractional.fullGateExecution
  rw [FiniteDistribution.map_bind]
  simp_rw [shortening_output_uniform]
  exact bind_const _ _

/-- First-attempt and full-loop conditional answers differ pointwise by at most 2/2ⁿ for a fixed long input, output encoding, matrix answer, and complete answer. -/
theorem shortening_conditional_difference {s : F}
    (hq : fieldCard F = 2) (hn : 2 ≤ n) (fallback : Fiber F n s)
    (leak : (x : Fiber F (n+t) s) → A → FullTape (n := n) x.val.L → FiniteDistribution B)
    (x : Fiber F (n+t) s) (α : A) (out : Fiber F n s) (z : A × B) :
    letI := fiber_nonempty F n hn s
    let μ := (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s))
    |(Fractional.shorteningExecution hn fallback leak x α).weight (out,z) / μ.weight out -
      (Fractional.firstShorteningExecution hn fallback leak x α).weight (out,z) / μ.weight out| ≤
      2 / (2 : ℝ)^n := by
  classical
  rcases x with ⟨⟨u,v⟩, hx⟩
  change dot u.val v.val = s at hx
  subst s
  letI := fiber_nonempty F n hn (dot u.val v.val)
  have h := binary_fullTapeConditionalAnswer_conditional_answer_difference hq hn u v fallback
    (fun tape => (leak ⟨⟨u,v⟩,rfl⟩ α tape).map (fun β => (α,β))) out z
  simpa only [Fractional.shorteningExecution, Fractional.firstShorteningExecution,
    Unbounded.firstAcceptedAnswerDistribution, FiniteDistribution.map_map,
    Function.comp_def, returnedOutput_eq_outputOr] using h

/-- The first-attempt comparison distribution averages the actual accepted shortening sampler through the exactly disintegrated matrix phase. -/
def firstGate (hn : 2 ≤ n) (a b : O → U F (n+t))
    (p : TableRectanglePartition O (Refresh.«GL» F (n+t)) A) (o : O × O)
    [Nonempty (Fiber F (n+t) (gateSecret a b o))]
    (fallback : Fiber F n (gateSecret a b o))
    (leak : (x : Fiber F (n+t) (gateSecret a b o)) → A →
      FullTape (n := n) x.val.L → FiniteDistribution B) :
    FiniteDistribution (Fiber F n (gateSecret a b o) × (A × B)) :=
  (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) (gateSecret a b o))).bind
    (fun x => (longAnswer a b p o x).bind (Fractional.firstShorteningExecution hn fallback leak x))

/-- The reverse shortening description identifies the first accepted gate exactly with the transported answer distribution. -/
theorem firstGate_eq_canonical (hn : 2 ≤ n) (a b : O → U F (n+t))
    (p : TableRectanglePartition O (Refresh.«GL» F (n+t)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (O × U F n) ((O × U F n) × Kernel H)) (o : O × O)
    [Nonempty (Fiber F (n+t) (gateSecret a b o))]
    [Nonempty (FullRank F n (n+t))]
    (fallback : Fiber F n (gateSecret a b o))
    (leak : (x : Fiber F (n+t) (gateSecret a b o)) → A →
      FullTape (n := n) x.val.L → FiniteDistribution B)
    (hleak : ∀ x α (z : Success (n := n) x.val.L x.val.R),
      leak x α ⟨0,(PUnit.unit,z.val)⟩ =
        Fractional.rectangleRecordAnswer r o (successfulJointEquiv (gateSecret a b o) ⟨x,z⟩) α) :
    firstGate hn a b p o fallback leak = Fractional.fullGateCanonical hn a b p r o := by
  let s := gateSecret a b o
  letI := fiber_nonempty F n hn s
  let K := longAnswer (s := s) a b p
  calc
    _ = acceptedObservation hn s (Fractional.rectangleRecordLeak K r o) := by
      unfold firstGate acceptedObservation
      congr 1
      funext x
      exact Fractional.first_shortening_record_distribution hn fallback K r o leak hleak x
    _ = _ := accepted_observation_disintegration hn s _

/-- Averaging the pointwise conditional retry estimate over long encodings and matrix answers does not introduce an answer-count factor. -/
theorem fullGate_conditional_difference
    (hq : fieldCard F = 2) (hn : 2 ≤ n) (a b : O → U F (n+t))
    (p : TableRectanglePartition O (Refresh.«GL» F (n+t)) A)
    (r : A → (H : FullRank F n (n+t)) → FractionalRectanglePartition B
      (O × U F n) ((O × U F n) × Kernel H)) (o : O × O)
    [Nonempty (Fiber F (n+t) (gateSecret a b o))]
    [Nonempty (FullRank F n (n+t))]
    (fallback : Fiber F n (gateSecret a b o))
    (leak : (x : Fiber F (n+t) (gateSecret a b o)) → A →
      FullTape (n := n) x.val.L → FiniteDistribution B)
    (hleak : ∀ x α (z : Success (n := n) x.val.L x.val.R),
      leak x α ⟨0,(PUnit.unit,z.val)⟩ =
        Fractional.rectangleRecordAnswer r o (successfulJointEquiv (gateSecret a b o) ⟨x,z⟩) α)
    (out : Fiber F n (gateSecret a b o)) (z : A × B) :
    letI := fiber_nonempty F n hn (gateSecret a b o)
    let P := Fractional.fullGateExecution hn a b p o fallback leak
    |(Canonical.answer P out).weight z - (Fractional.shortenedAnswerDistribution (longAnswer a b p) r o out).weight z| ≤
      2 / (2 : ℝ)^n := by
  classical
  letI := fiber_nonempty F n hn (gateSecret a b o)
  dsimp only
  let μ := (FiniteDistribution.uniform : FiniteDistribution (Fiber F n (gateSecret a b o)))
  have hμ : 0 < μ.weight out := by
    change 0 < (Fintype.card (Fiber F n (gateSecret a b o)) : ℝ)⁻¹
    positivity
  have hraw := bind_conditional_difference_le
    (FiniteDistribution.uniform : FiniteDistribution (Fiber F (n+t) (gateSecret a b o)))
    (fun x => (longAnswer a b p o x).bind (Fractional.shorteningExecution hn fallback leak x))
    (fun x => (longAnswer a b p o x).bind (Fractional.firstShorteningExecution hn fallback leak x))
    μ (2 / (2 : ℝ)^n) out z (fun x => bind_conditional_difference_le
      (longAnswer a b p o x) (Fractional.shorteningExecution hn fallback leak x)
      (Fractional.firstShorteningExecution hn fallback leak x) μ (2 / (2 : ℝ)^n) out z
      (fun α => shortening_conditional_difference hq hn fallback leak x α out z))
  rw [← Fractional.fullGateExecution_eq_long hn a b p o fallback leak] at hraw
  change |(Fractional.fullGateExecution hn a b p o fallback leak).weight (out,z) / μ.weight out -
    (firstGate hn a b p o fallback leak).weight (out,z) / μ.weight out| ≤ _ at hraw
  rw [firstGate_eq_canonical hn a b p r o fallback leak hleak] at hraw
  have hfresh := fullGate_output_uniform hn a b p o fallback leak
  rw [Canonical.answer_weight _ out z (by simpa only [hfresh] using hμ), hfresh]
  change |(Fractional.fullGateExecution hn a b p o fallback leak).weight (out,z) / μ.weight out -
    (Fractional.shortenedAnswerDistribution (longAnswer a b p) r o out).weight z| ≤ _
  change |(Fractional.fullGateExecution hn a b p o fallback leak).weight (out,z) / μ.weight out -
    μ.weight out * (Fractional.shortenedAnswerDistribution (longAnswer a b p) r o out).weight z /
      μ.weight out| ≤ _ at hraw
  simpa only [mul_div_cancel_left₀ _ (ne_of_gt hμ)] using hraw

end CompilerProof.FullRetry

namespace CompilerProof.FullRetry

open Refresh MatrixRefresh TableAnalysis CircuitCompiler CircuitCompiler.Rectangular
  CircuitCompiler.Composition.TopologicalExecution

variable {F A B : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype A] [Fintype B] {n t inputs : ℕ} {hdim : n*n+1 = n+t}

/-- The exact full-retry protocol uses the actual physical transition and its true conditional answer, rather than the first-attempt analytic answer. -/
def protocol (strategy : Fractional.AugmentedStrategy F A B n t inputs hdim) (hn : 2 ≤ n) :
    GateProtocol F (U F n × U F n) (A × B) inputs :=
  Canonical.protocol (strategy.shareProtocol hn)

/-- Replacing the answer interface does not change the actual raw physical transition. -/
theorem protocol_real (strategy : Fractional.AugmentedStrategy F A B n t inputs hdim)
    (hn : 2 ≤ n) : (protocol strategy hn).real = (strategy.shareProtocol hn).real := rfl

/-- Output freshness for the actual gate on the common paired-share carrier is exact, for each fixed gate, history, and operand encodings. -/
theorem share_output_uniform (strategy : Fractional.AugmentedStrategy F A B n t inputs hdim)
    (hq : fieldCard F = 2) (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → A × B) (left right : U F n × U F n) :
    ((strategy.shareProtocol hn).real i gate history left right).map Prod.fst =
      encodingDistribution hn (gate.kind.eval
        (secret ((stateEquivProd F n).symm left)) (secret ((stateEquivProd F n).symm right))) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0,by omega⟩⟩
  let l := (stateEquivProd F n).symm left
  let r := (stateEquivProd F n).symm right
  let a := augmentedLeftFeature hdim gate.kind.affineConstant
  let b := augmentedRightFeature (F := F) hdim
  let p := matrixPartitionDimension hdim (strategy.matrix i gate history)
  let o := augmentedOldPorts l r
  have h := congrArg (fun Q : FiniteDistribution (Fiber F n (gateSecret a b o)) =>
    Q.map (fun output => stateEquivProd F n output.val))
    (fullGate_output_uniform hn a b p o (strategy.fallback i gate history l r)
      (strategy.leak i gate history l r))
  have he := augmented_gateSecret_eval hq hdim gate.kind l r
  change gateSecret a b o = gate.kind.eval (secret l) (secret r) at he
  have h' : ((strategy.shareProtocol hn).real i gate history left right).map Prod.fst =
      encodingDistribution hn (gateSecret a b o) := by
    simpa only [Fractional.AugmentedStrategy.shareProtocol, GateProtocol.transport,
      Fractional.AugmentedStrategy.protocol, FiniteDistribution.map_map, Function.comp_def,
      encodingDistribution, mu, l, r, a, b, p, o] using h
  rw [he] at h'
  exact h'

/-- On every valid encoded input/output triple, the exact full-retry conditional answer differs from the transported first-attempt answer by at most 2/2ⁿ, pointwise in each complete answer. -/
theorem share_answer_difference (strategy : Fractional.AugmentedStrategy F A B n t inputs hdim)
    (hq : fieldCard F = 2) (hn : 2 ≤ n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → A × B) (left right output : U F n × U F n)
    (hvalid : secret ((stateEquivProd F n).symm output) =
      gate.kind.eval (secret ((stateEquivProd F n).symm left))
        (secret ((stateEquivProd F n).symm right))) (z : A × B) :
    |((protocol strategy hn).answer i gate history left right output).weight z -
      ((strategy.shareProtocol hn).answer i gate history left right output).weight z| ≤
      2 / (2 : ℝ)^n := by
  classical
  letI : Nonempty (U F n) := ⟨unitShare ⟨0,by omega⟩⟩
  let l := (stateEquivProd F n).symm left
  let rr := (stateEquivProd F n).symm right
  let a := augmentedLeftFeature hdim gate.kind.affineConstant
  let b := augmentedRightFeature (F := F) hdim
  let p := matrixPartitionDimension hdim (strategy.matrix i gate history)
  let o := augmentedOldPorts l rr
  letI := fiber_nonempty F (n+t) (by omega) (gateSecret a b o)
  have he := augmented_gateSecret_eval hq hdim gate.kind l rr
  change gateSecret a b o = gate.kind.eval (secret l) (secret rr) at he
  let out : Fiber F n (gateSecret a b o) :=
    ⟨(stateEquivProd F n).symm output, hvalid.trans he.symm⟩
  let P := Fractional.fullGateExecution hn a b p o (strategy.fallback i gate history l rr)
    (strategy.leak i gate history l rr)
  let f := fun x : Fiber F n (gateSecret a b o) => stateEquivProd F n x.val
  have hf : Function.Injective f := (stateEquivProd F n).injective.comp Subtype.val_injective
  have hpos : 0 < (P.map Prod.fst).weight out := by
    rw [fullGate_output_uniform]
    change 0 < (Fintype.card (Fiber F n (gateSecret a b o)) : ℝ)⁻¹
    letI := fiber_nonempty F n hn (gateSecret a b o)
    positivity
  have hrep := Canonical.answer_map_injective P f hf out hpos
  have hphysical : (strategy.shareProtocol hn).real i gate history left right =
      P.map (fun x => (f x.1,x.2)) := by
    simp only [Fractional.AugmentedStrategy.shareProtocol, GateProtocol.transport,
      Fractional.AugmentedStrategy.protocol, FiniteDistribution.map_map, Function.comp_def]
    rfl
  have hnew : (protocol strategy hn).answer i gate history left right output =
      Canonical.answer P out := by
    change Canonical.answer ((strategy.shareProtocol hn).real i gate history left right) output = _
    rw [hphysical]
    simpa only [f, out, Equiv.apply_symm_apply] using hrep
  have hold : (strategy.shareProtocol hn).answer i gate history left right output =
      Fractional.shortenedAnswerDistribution (longAnswer a b p) (strategy.rectangles i gate history) o out := by
    change Fractional.ambientGateAnswerDistribution hn a b p (strategy.rectangles i gate history)
      o out.val = _
    exact Fractional.ambientGateAnswerDistribution_fiber hn a b p _ o out
  rw [hnew, hold]
  exact fullGate_conditional_difference hq hn a b p (strategy.rectangles i gate history) o
    (strategy.fallback i gate history l rr) (strategy.leak i gate history l rr)
    (strategy.firstLeak i gate history l rr) out z

end CompilerProof.FullRetry
