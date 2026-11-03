import Proofs.Compiler.GateApproximation.MatrixPhase.CountableMixture
import Proofs.Compiler.LocalComparisons.Framework.ProgramExecution
import Proofs.Compiler.Construction.Parameters



/-!
# Presampling independent private tapes in adaptive executions

A fresh independent countable seed may be sampled inside every adaptive gate, or all these seeds may be sampled before the execution. The resulting distribution of all wires and the transcript is exactly the same. This is an equality for the actual chronological runner, rather than an assumed representation of its output distribution.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

open scoped BigOperators

namespace CircuitCompiler.Sampling.Unbounded

open Refresh

noncomputable section

/-- A finite current state and an independent countable next seed can be sampled in either order, even when the continuation depends on both. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Ω,V,W a set; P ∈ 𝒟(V); seed ∈ PMF(Ω); next ∈ V → Ω → 𝒟(W), assume Countable(Ω); V is finite; W is finite. Then

bind(P, ((v ↦ countableMixture(seed, next(v))))) = countableMixture(seed, ((ω ↦ bind(P, ((v ↦ next(v, ω))))))).
-/
theorem finite_bind_countableMixture {Ω V W : Type*} [Countable Ω]
    [Fintype V] [Fintype W] (P : FiniteDistribution V) (seed : PMF Ω)
    (next : V → Ω → FiniteDistribution W) :
    P.bind (fun v => countableMixture seed (next v)) =
      countableMixture seed (fun ω => P.bind (fun v => next v ω)) := by
  have h : toPMF (P.bind (fun v => countableMixture seed (next v))) =
      toPMF (countableMixture seed (fun ω => P.bind (fun v => next v ω))) := by
    simp only [toPMF_bind,countableMixture,toPMF_toFinite]
    exact PMF.bind_comm _ _ _
  simpa only [toFinite_toPMF] using congrArg toFinite h

end

end CircuitCompiler.Sampling.Unbounded

namespace CircuitCompiler.Composition.TopologicalExecution

open Refresh Sampling.Unbounded

noncomputable section

universe u v w

variable {Ω : Type u} {E : Type v} {A : Type w}
  [Countable Ω] [Fintype E] [Fintype A] {inputs T : ℕ}

/-- A runner whose next gate uses a fresh independent seed with a specified countable distribution. Gates may adapt to the complete earlier history. -/
/- Mathematical definition (normal notation): A finite chronological runner in which each gate has a specified independent private-seed distribution and a transition indexed by that seed. Transitions may adapt to all earlier encodings and answers. -/
inductive SeededRunner (Ω : Type u) (E : Type v) (A : Type w)
    [Fintype E] [Fintype A] (inputs : ℕ) : ℕ → Type (max u v w) where
  | nil : SeededRunner Ω E A inputs 0
  | snoc {T : ℕ} (prior : SeededRunner Ω E A inputs T) (seed : PMF Ω)
      (gate : Ω → RunState E A inputs T → FiniteDistribution (E × A)) :
      SeededRunner Ω E A inputs (T+1)

namespace SeededRunner

/-- Sample each private seed immediately before executing its gate. -/
/- Mathematical definition (normal notation): At each gate draw that gate's private seed from its specified distribution, then run the transition determined by the seed and current state. -/
def fresh : {T : ℕ} → SeededRunner Ω E A inputs T → Runner E A inputs T
  | 0, .nil => .nil
  | _+1, .snoc prior seed gate =>
      .snoc prior.fresh (fun state => countableMixture seed (fun ω => gate ω state))

/-- Fix the entire finite tape in advance. Its entries are still private auxiliary parameters; the gate only uses its own entry. -/
/- Mathematical definition (normal notation): Given a complete finite vector of private seeds, fix gate i's transition to use seed i. Each gate reads only its own seed coordinate. -/
def fixed : {T : ℕ} → SeededRunner Ω E A inputs T →
    (Fin T → Ω) → Runner E A inputs T
  | 0, .nil, _ => .nil
  | _+1, .snoc prior _ gate, tape =>
      .snoc (prior.fixed (Fin.init tape)) (gate (tape (Fin.last _)))

/-- The independent finite sequence of seed draws, one per chronological gate. -/
/- Mathematical definition (normal notation): Sample one seed independently for every chronological gate, using that gate's specified seed distribution. Return the resulting ordered seed vector. -/
def tapeDistribution : {T : ℕ} → SeededRunner Ω E A inputs T → PMF (Fin T → Ω)
  | 0, .nil => PMF.pure Fin.elim0
  | _+1, .snoc prior seed _ =>
      prior.tapeDistribution.bind (fun tape => seed.map (fun ω => Fin.snoc tape ω))

/-- Presampling independent gate seeds does not change the full execution distribution, including all retained wire encodings and the complete adaptive transcript. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For initial ∈ 𝒟(({0,…,inputs-1} → E)); runner ∈ SeededRunner(Ω, E, A, inputs, T), we have

runner.fresh.execute(initial) = countableMixture(runner.tapeDistribution, ((tape ↦ execute(runner.fixed(tape))(initial)))) .
-/
theorem execute_fresh (initial : FiniteDistribution (Fin inputs → E))
    (runner : SeededRunner Ω E A inputs T) :
    runner.fresh.execute initial = countableMixture runner.tapeDistribution
      (fun tape => (runner.fixed tape).execute initial) := by
  induction runner with
  | nil =>
      simp only [fresh,fixed,tapeDistribution,countableMixture,PMF.pure_bind,toFinite_toPMF]
  | @snoc T prior seed gate ih =>
      rw [fresh,Runner.execute_snoc,ih,countableMixture_bind]
      simp_rw [countableMixture_map,finite_bind_countableMixture]
      rw [tapeDistribution,countableMixture_assoc]
      congr 1
      funext tape
      unfold countableMixture
      rw [PMF.bind_map]
      simp only [Function.comp_def,fixed,Fin.init_snoc,Fin.snoc_last,
        Runner.execute_snoc]

/-- The same exact identity holds for any requested finite observation. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; initial ∈ 𝒟(({0,…,inputs-1} → E)); runner ∈ SeededRunner(Ω, E, A, inputs, T); observe ∈ RunState(E, A, inputs, T) → V, assume V is finite. Then

(observe_*runner.fresh.execute(initial)) = countableMixture(runner.tapeDistribution, ((tape ↦ (observe_*execute(runner.fixed(tape))(initial))))) .
-/
theorem execute_fresh_observed {V : Type*} [Fintype V]
    (initial : FiniteDistribution (Fin inputs → E)) (runner : SeededRunner Ω E A inputs T)
    (observe : RunState E A inputs T → V) :
    (runner.fresh.execute initial).map observe = countableMixture runner.tapeDistribution
      (fun tape => ((runner.fixed tape).execute initial).map observe) := by
  rw [execute_fresh,countableMixture_map]

end SeededRunner

namespace GateProtocol

variable {F : Type*} [Mul F] [Sub F]

/-- The ordinary gate protocol with the seed at each position fixed. -/
/- Mathematical definition (normal notation): Use the protocol indexed by the fixed seed at time i for both the actual transition and its canonical conditional answer distribution. -/
def fixSeeds (tape : ℕ → Ω) (protocol : Ω → GateProtocol F E A inputs) :
    GateProtocol F E A inputs where
  real t := (protocol (tape t)).real t
  answer t := (protocol (tape t)).answer t

/-- Read the actual program's operand positions and adaptive histories. -/
/- Mathematical definition (normal notation): Traverse the actual source program and attach each gate's seed distribution and seed-indexed local transition, passing the gate's operand encodings and earlier answer history. -/
def seededRunner (seed : ℕ → PMF Ω) (protocol : Ω → GateProtocol F E A inputs) :
    {T : ℕ} → Program F inputs T → SeededRunner Ω E A inputs T
  | 0, .nil => .nil
  | t+1, .snoc prior gate => .snoc (seededRunner seed protocol prior) (seed t)
      (fun ω state => (protocol ω).real t gate state.2
        (state.1 gate.left) (state.1 gate.right))

/-- The seeded construction is definitionally the actual chronological runner with a fresh independent seed inside each transition. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For seed ∈ ℕ → PMF(Ω); protocol ∈ Ω → GateProtocol(F, E, A, inputs); program ∈ Program(F, inputs, T), we have

fresh(seededRunner(seed, protocol, program)) = realRunner(mixSeeds(seed, protocol))(program).
-/
theorem seededRunner_fresh (seed : ℕ → PMF Ω)
    (protocol : Ω → GateProtocol F E A inputs) (program : Program F inputs T) :
    (seededRunner seed protocol program).fresh = (mixSeeds seed protocol).realRunner program := by
  induction program with
  | nil => rfl
  | snoc prior gate ih => simp only [seededRunner,SeededRunner.fresh,realRunner,mixSeeds,ih]

/-- Fixing the seed vector gives the ordinary actual runner for that fixed sequence of local protocols. No hypothesis about execution distributions is required. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For seed ∈ ℕ → PMF(Ω); protocol ∈ Ω → GateProtocol(F, E, A, inputs); program ∈ Program(F, inputs, T); tape ∈ ℕ → Ω, we have

fixed(seededRunner(seed, protocol, program))(((i ↦ tape(i)))) = realRunner(fixSeeds(tape, protocol))(program).
-/
theorem seededRunner_fixed (seed : ℕ → PMF Ω)
    (protocol : Ω → GateProtocol F E A inputs) (program : Program F inputs T)
    (tape : ℕ → Ω) :
    (seededRunner seed protocol program).fixed (fun i => tape i.val) =
      (fixSeeds tape protocol).realRunner program := by
  induction program with
  | nil => rfl
  | @snoc t prior gate ih =>
      have hi : Fin.init (fun i : Fin (t + 1) => tape i.val) =
          (fun i : Fin t => tape i.val) := rfl
      simpa only [seededRunner,SeededRunner.fixed,realRunner,fixSeeds,Fin.init,Fin.castSucc_mk,
        Fin.val_last, hi] using congrArg
          (fun r => Runner.snoc r (fun state => (protocol (tape t)).real t gate state.2
            (state.1 gate.left) (state.1 gate.right))) ih

/-- Extend a finite seed tape by an unused default beyond the program length. -/
/-
Mathematical definition (normal notation): For fallback ∈ Ω; tape ∈ {0,…,T-1} → Ω; i ∈ ℕ, define

extendTape(fallback, tape, i) := { tape((i, hi)) if i < T,; fallback otherwise }.
-/
def extendTape (fallback : Ω) (tape : Fin T → Ω) (i : ℕ) : Ω :=
  if hi : i < T then tape ⟨i,hi⟩ else fallback

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For fallback ∈ Ω; tape ∈ {0,…,T-1} → Ω; i ∈ {0,…,T-1}, we have

extendTape(fallback, tape, i) = tape(i).
-/
@[simp] theorem extendTape_at (fallback : Ω) (tape : Fin T → Ω) (i : Fin T) :
    extendTape fallback tape i.val = tape i := by
  simp only [extendTape,dif_pos i.isLt]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For seed ∈ ℕ → PMF(Ω); protocol ∈ Ω → GateProtocol(F, E, A, inputs); program ∈ Program(F, inputs, T); fallback ∈ Ω; tape ∈ {0,…,T-1} → Ω, we have

fixed(seededRunner(seed, protocol, program))(tape) = realRunner(fixSeeds(extendTape(fallback, tape), protocol))(program) .
-/
theorem seededRunner_fixed_extend (seed : ℕ → PMF Ω)
    (protocol : Ω → GateProtocol F E A inputs) (program : Program F inputs T)
    (fallback : Ω) (tape : Fin T → Ω) :
    (seededRunner seed protocol program).fixed tape =
      (fixSeeds (extendTape fallback tape) protocol).realRunner program := by
  have h := seededRunner_fixed seed protocol program (extendTape fallback tape)
  simpa only [extendTape_at] using h

/-- Exact global presampling identity for the actual program runner. In particular, the seed may be the complete rejected prefix of matrix sampling. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For seed ∈ ℕ → PMF(Ω); protocol ∈ Ω → GateProtocol(F, E, A, inputs); program ∈ Program(F, inputs, T); initial ∈ 𝒟(({0,…,inputs-1} → E)), we have

execute(realRunner(mixSeeds(seed, protocol))(program))(initial) = countableMixture(tapeDistribution(seededRunner(seed, protocol, program)), ((tape ↦ execute(fixed(seededRunner(seed, protocol, program))(tape))(initial)))) .
-/
theorem realRunner_mixSeeds (seed : ℕ → PMF Ω)
    (protocol : Ω → GateProtocol F E A inputs) (program : Program F inputs T)
    (initial : FiniteDistribution (Fin inputs → E)) :
    ((mixSeeds seed protocol).realRunner program).execute initial =
      countableMixture (seededRunner seed protocol program).tapeDistribution
        (fun tape => ((seededRunner seed protocol program).fixed tape).execute initial) := by
  rw [← seededRunner_fresh]
  exact SeededRunner.execute_fresh initial _

/-- The global mixture uses ordinary chronological runners with fixed local protocols, and the fallback extension is never read by the finite program. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For seed ∈ ℕ → PMF(Ω); protocol ∈ Ω → GateProtocol(F, E, A, inputs); program ∈ Program(F, inputs, T); fallback ∈ Ω; initial ∈ 𝒟(({0,…,inputs-1} → E)), we have

execute(realRunner(mixSeeds(seed, protocol))(program))(initial) = countableMixture(tapeDistribution(seededRunner(seed, protocol, program)), ((tape ↦ execute(realRunner(fixSeeds(extendTape(fallback, tape), protocol))(program))(initial)))) .
-/
theorem realRunner_mixSeeds_fixed (seed : ℕ → PMF Ω)
    (protocol : Ω → GateProtocol F E A inputs) (program : Program F inputs T)
    (fallback : Ω) (initial : FiniteDistribution (Fin inputs → E)) :
    ((mixSeeds seed protocol).realRunner program).execute initial =
      countableMixture (seededRunner seed protocol program).tapeDistribution
        (fun tape => ((fixSeeds (extendTape fallback tape) protocol).realRunner program).execute initial) := by
  rw [realRunner_mixSeeds]
  simp only [seededRunner_fixed_extend seed protocol program fallback]

/-- Privacy established uniformly for every fixed seed vector applies to chronological fresh-seed executions, including arbitrary finite observations. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For V a set; seed ∈ ℕ → PMF(Ω); protocol ∈ Ω → GateProtocol(F, E, A, inputs); program ∈ Program(F, inputs, T); initial ∈ 𝒟(({0,…,inputs-1} → E)); observe ∈ RunState(E, A, inputs, T) → V, assume V is finite. Then

(observe_*execute(realRunner(mixSeeds(seed, protocol))(program))(initial)) = countableMixture(tapeDistribution(seededRunner(seed, protocol, program)), ((tape ↦ (observe_*execute(fixed(seededRunner(seed, protocol, program))(tape))(initial))))) .
-/
theorem realRunner_mixSeeds_observed {V : Type*} [Fintype V]
    (seed : ℕ → PMF Ω) (protocol : Ω → GateProtocol F E A inputs)
    (program : Program F inputs T) (initial : FiniteDistribution (Fin inputs → E))
    (observe : RunState E A inputs T → V) :
    (((mixSeeds seed protocol).realRunner program).execute initial).map observe =
      countableMixture (seededRunner seed protocol program).tapeDistribution
        (fun tape => (((seededRunner seed protocol program).fixed tape).execute initial).map observe) := by
  rw [realRunner_mixSeeds,countableMixture_map]

end GateProtocol

end

end CircuitCompiler.Composition.TopologicalExecution
