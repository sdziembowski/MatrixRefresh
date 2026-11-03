import Proofs.Compiler.Adaptive.Security
import Proofs.Compiler.Operations.Prefixes

/-!
# Raw physical sampling with online inputs

Every rejected matrix prefix is still part of the permitted local tape. The independent-prefix mixture holds even when the current public sampling value is selected from the preceding transcript. The fixed-prefix causal security bound can therefore be averaged to obtain the raw physical guarantee.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open scoped BigOperators Classical

namespace Compiler.Adaptive
open Refresh MatrixRefresh CircuitCompiler CircuitCompiler.Operations TableAnalysis
  CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution
  CircuitCompiler.AveragedEnergyComparison CircuitCompiler.Sampling CircuitCompiler.Sampling.Unbounded

variable {ML MR BL BR : Type*} [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
  {n t P S : ℕ} {hdim : n*n+1 = n+t}
  {Ω : Type*} [Countable Ω]

/-- Attach one independent private matrix-prefix seed to each actual chronological operation. Online public values are chosen after earlier answers, before that operation runs. -/
def seededRunner (seed : PMF Ω)
    (family : Ω → Operations.Protocol Bit (U Bit n×U Bit n) (Operations.Answer ML MR BL BR) P) :
    {S : ℕ} → Operations.Program Bit P S → SampleValues Bit (Operations.Answer ML MR BL BR) S →
      SeededRunner Ω (U Bit n×U Bit n) (Operations.Answer ML MR BL BR) P S
  | 0, .nil, _ => .nil
  | _+1, .snoc prior instruction, values =>
      .snoc (seededRunner seed family prior (fun i => values i.castSucc)) seed
        (fun ω state => (family ω).real _
          (selectInstruction instruction (values (Fin.last _) state.2)) state.2 state.1)

/-- Fixing the private seed vector gives exactly the corresponding actual adaptive physical runner. -/
theorem seededRunner_fixed (seed : PMF Ω)
    (family : Ω → Operations.FixedStrategy Bit ML MR BL BR n t P hdim) (hn : 2 ≤ n)
    (program : Operations.Program Bit P S) (values : SampleValues Bit (Operations.Answer ML MR BL BR) S)
    (tape : ℕ → Ω) :
    (seededRunner seed (fun ω => (family ω).protocol hn) program values).fixed (fun i => tape i.val) =
      realRunner ((Operations.FixedStrategy.fixSeeds tape family).protocol hn) program values := by
  induction program with
  | nil => rfl
  | @snoc S prior instruction ih =>
    simp only [seededRunner, SeededRunner.fixed, realRunner, Fin.val_last,
      Operations.FixedStrategy.fixSeeds_real]
    have hi : Fin.init (fun i : Fin (S+1) => tape i.val) = (fun i : Fin S => tape i.val) := rfl
    rw [hi, ih]

/-- Averaging independent private prefixes at each adaptive operation is the raw protocol, including all public-encoding and shortening retries. -/
theorem raw_runner_eq_fresh (strategy : CircuitCompiler.Operations.Strategy Bit ML MR BL BR n t P hdim)
    (hn : 2 ≤ n) (program : Operations.Program Bit P S)
    (values : SampleValues Bit (Operations.Answer ML MR BL BR) S) :
    realRunner (strategy.protocol hn) program values =
      (seededRunner (Operations.seedDistribution (F := Bit) (n := n) (t := t))
        (fun seed => (strategy.fixedPrefix seed).protocol hn) program values).fresh := by
  induction program with
  | nil => rfl
  | snoc prior instruction ih =>
    simp only [realRunner, seededRunner, SeededRunner.fresh, ih]
    congr 1
    funext state
    exact Operations.instruction_eq_mixture strategy hn _
      (selectInstruction instruction (values (Fin.last _) state.2)) state.2 state.1

/-- The full raw execution is the independent mixture of its fixed-prefix executions. Its initialization encodes only the original trusted private boundary. -/
theorem raw_view_eq_mixture {V : Type*} [Fintype V]
    (strategy : CircuitCompiler.Operations.Strategy Bit ML MR BL BR n t P hdim) (hn : 2 ≤ n)
    (program : Operations.Program Bit P S) (values : SampleValues Bit (Operations.Answer ML MR BL BR) S)
    (input : Fin P → Bit) (observe : RunState (U Bit n×U Bit n) (Operations.Answer ML MR BL BR) P S → V) :
    (((realRunner (strategy.protocol hn) program values).execute
      (toFinite (CircuitCompiler.Sampling.RawEncoding.initializeShares hn input))).map observe) =
    countableMixture (seededRunner (Operations.seedDistribution (F := Bit) (n := n) (t := t))
      (fun seed => (strategy.fixedPrefix seed).protocol hn) program values).tapeDistribution
      (fun tape =>
        (((realRunner ((Operations.FixedStrategy.fixSeeds
          (GateProtocol.extendTape
            ((matrixPrefixDistribution (F := Bit) (n+t)).support_nonempty.choose,
             (matrixPrefixDistribution (F := Bit) n).support_nonempty.choose) tape)
          strategy.fixedPrefix).protocol hn) program values).execute
            (toFinite (CircuitCompiler.Sampling.RawEncoding.initializeShares hn input))).map observe)) := by
  rw [raw_runner_eq_fresh, SeededRunner.execute_fresh_observed]
  congr 1
  funext tape
  have he := seededRunner_fixed (Operations.seedDistribution (F := Bit) (n := n) (t := t))
    strategy.fixedPrefix hn program values (GateProtocol.extendTape
      ((matrixPrefixDistribution (F := Bit) (n+t)).support_nonempty.choose,
       (matrixPrefixDistribution (F := Bit) n).support_nonempty.choose) tape)
  simp only [GateProtocol.extendTape_at] at he
  rw [he]

variable [Nonempty ML] [Nonempty MR] [Nonempty BL] [Nonempty BR]

/-- The raw physical transcript bound for an arbitrary online public-input policy. All leaked sampler retries are retained, and the constant has no dependence on the number of invocations. -/
theorem raw_transcript_bound (program : Operations.Program Bit P S)
    (hd : program.DistinctInputs)
    (hdegree : ∀ w, (Finset.univ.filter (fun i => w ∈ program.scope i)).card ≤ 3)
    (strategy : CircuitCompiler.Operations.Strategy Bit ML MR BL BR n t P hdim) (hn : 2 ≤ n)
    (values : SampleValues Bit (Operations.Answer ML MR BL BR) S) (first second : Fin P → Bit) :
    Refresh.statisticalDistance
      (((realRunner (strategy.protocol hn) program values).execute
        (toFinite (CircuitCompiler.Sampling.RawEncoding.initializeShares hn first))).map Prod.snd)
      (((realRunner (strategy.protocol hn) program values).execute
        (toFinite (CircuitCompiler.Sampling.RawEncoding.initializeShares hn second))).map Prod.snd) ≤
      1000000*(S:ℝ)*(Fintype.card (Operations.Answer ML MR BL BR):ℝ)^9 *
        (Fintype.card (Refresh.U Bit n):ℝ)^(-1/27:ℝ) := by
  rw [raw_view_eq_mixture, raw_view_eq_mixture]
  apply countableMixture_distance_le
  intro tape
  rw [CircuitCompiler.Sampling.RawEncoding.initializeShares_eq_independent, toFinite_toPMF,
    CircuitCompiler.Sampling.RawEncoding.initializeShares_eq_independent, toFinite_toPMF]
  exact fixed_transcript_bound program hd hdegree _ hn (Classical.choice inferInstance) values first second

end Compiler.Adaptive
