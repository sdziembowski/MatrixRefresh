import Proofs.Compiler.Operations.Execution
import Proofs.Compiler.Simulation.IndependentRunner
import Proofs.Compiler.Simulation.RawGates

/-!
# Independent rejected matrix prefixes in the heterogeneous physical program

Both square-matrix samplers retain every rejected proposal in the permitted local views. Their prefixes are independent of accepted matrices and all old shares. The equalities below presample these private prefixes, preserving the complete adaptive transcript and the designated output encodings jointly. Public encoding rejection and all H-shortening retries stay inside each kernel.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open scoped BigOperators Classical

namespace CircuitCompiler.Operations
open Refresh MatrixRefresh TableAnalysis Sampling Sampling.Unbounded
  _root_.CircuitCompiler.Composition _root_.CircuitCompiler.Composition.TopologicalExecution

variable {F ML MR BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
  {n t inputs S : ℕ} {hdim : n*n+1=n+t}

/-- The two independently sampled private prefixes. An operation uses only its own matrix dimension, so the other coordinate is ignored. -/
def seedDistribution : PMF (Seed F n t) :=
  (matrixPrefixDistribution (F:=F) (n+t)).bind fun long =>
    (matrixPrefixDistribution (F:=F) n).map fun short => (long,short)

/-- Averaging a product-indexed family of finite distributions may first average its first coordinate. -/
private theorem mixture_first {X Y V : Type*} [Countable X] [Countable Y] [Fintype V]
    (P : PMF X) (Q : PMF Y) (f : X → FiniteDistribution V) :
    countableMixture (P.bind fun x => Q.map fun y => (x,y)) (fun xy => f xy.1) =
      countableMixture P f := by
  unfold countableMixture
  simp only [PMF.bind_bind,PMF.bind_map,Function.comp_def]
  simp only [PMF.bind_const]

/-- Averaging a product-indexed family of finite distributions may first average its second coordinate. -/
private theorem mixture_second {X Y V : Type*} [Countable X] [Countable Y] [Fintype V]
    (P : PMF X) (Q : PMF Y) (f : Y → FiniteDistribution V) :
    countableMixture (P.bind fun x => Q.map fun y => (x,y)) (fun xy => f xy.2) =
      countableMixture Q f := by
  unfold countableMixture
  simp only [PMF.bind_bind,PMF.bind_map,Function.comp_def,PMF.bind_const]

/-- A constant family is unchanged by averaging over a probability distribution. -/
private theorem mixture_constant {X V : Type*} [Countable X] [Fintype V]
    (P : PMF X) (Q : FiniteDistribution V) : countableMixture P (fun _ => Q)=Q := by
  simp [countableMixture,PMF.bind_const,toFinite_toPMF]

omit [Fintype F] [DecidableEq F] in
/-- Relabeling finite rectangle answers commutes with the matrix answer distribution. -/
theorem relabelPartition_answer {A B : Type*} [Fintype A] [Fintype B]
    (p : TableRectanglePartition (U F n) (Refresh.«GL» F n) A) (e : A ≃ B)
    (x y : U F n) (g : Refresh.«GL» F n) :
    (RefreshAnalysis.fixedMatrixAnswerDistribution p x y g).map e =
      RefreshAnalysis.fixedMatrixAnswerDistribution (relabelPartition p e) x y g := by
  ext b
  rw [FiniteDistribution.map_equiv_weight]
  rfl

/-- The raw physical refresh is exactly its independent-prefix mixture. -/
theorem refresh_eq_mixture (strategy : Strategy F ML MR BL BR n t inputs hdim)
    (hn : 2 ≤ n) (long : MatrixPrefix F (n+t)) (i : ℕ) (port : Fin (inputs+i)) (history : Fin i → Answer ML MR BL BR)
    (old : U F n × U F n) :
    strategy.refreshExecution i port history old =
      countableMixture (matrixPrefixDistribution (F:=F) n) (fun failures =>
        (((strategy.fixedPrefix (long,failures)).protocol hn).real
          i (.refresh port) history (fun _ => old))) := by
  change observe _ _ _ _ = _
  rw [matrix_joint_fixedMatrixAnswerDistribution_eq
    (strategy.refreshLeft i port history) (strategy.refreshRight i port history) old.1 old.2
    (fun M a => ((rowRefresh old.1 M,columnRefresh old.2 M),answerRegroupForward ML MR BL BR a))]
  congr 1
  funext failures
  change _ = ((FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F n)).joint
    (fun M => RefreshAnalysis.fixedMatrixAnswerDistribution
      (relabelPartition _ (answerRegroup ML MR BL BR)) old.1 old.2 M)).map _
  simp_rw [← relabelPartition_answer]
  let Q := RefreshAnalysis.fixedMatrixAnswerDistribution
    (matrixTapePartition (strategy.refreshLeft i port history)
      (strategy.refreshRight i port history) failures) old.1 old.2
  let e := answerRegroup ML MR BL BR
  have hj : ((FiniteDistribution.uniform : FiniteDistribution (Refresh.«GL» F n)).joint
      (fun M => (Q M).map e)) =
      (FiniteDistribution.uniform.joint Q).map (fun z => (z.1,e z.2)) := by
    ext z
    change _ = ((FiniteDistribution.uniform.joint Q).map
      ((Equiv.refl (Refresh.«GL» F n)).prodCongr e)).weight z
    rw [FiniteDistribution.map_equiv_weight]
    change FiniteDistribution.uniform.weight z.1*((Q z.1).map e).weight z.2 = _
    rw [FiniteDistribution.map_equiv_weight]
    rfl
  change (FiniteDistribution.uniform.joint Q).map _ =
    (FiniteDistribution.uniform.joint (fun M => (Q M).map e)).map _
  rw [hj,FiniteDistribution.map_map]
  rfl


/-- Prefix averaging of each heterogeneous instruction is the physical distribution, including the public sampler's full raw-pair tape. -/
theorem instruction_eq_mixture (strategy : Strategy F ML MR BL BR n t inputs hdim)
    (hn : 2≤n) (i : ℕ) (instruction : Instruction F (inputs+i))
    (history : Fin i → Answer ML MR BL BR) (old : Fin (inputs+i) → U F n × U F n) :
    (strategy.protocol hn).real i instruction history old =
      countableMixture (seedDistribution (F:=F) (n:=n) (t:=t))
        (fun seed => ((strategy.fixedPrefix seed).protocol hn).real i instruction history old) := by
  cases instruction with
  | compute gate =>
    rw [show (fun seed : Seed F n t => ((strategy.fixedPrefix seed).protocol hn).real
        i (.compute gate) history old) =
      (fun seed => ((strategy.compute.fixedPrefix seed.1).shareProtocol hn).real
        i gate history (old gate.left) (old gate.right)) from rfl]
    rw [seedDistribution,mixture_first (matrixPrefixDistribution (F:=F) (n+t))
      (matrixPrefixDistribution (F:=F) n) (fun failures =>
        ((strategy.compute.fixedPrefix failures).shareProtocol hn).real
          i gate history (old gate.left) (old gate.right))]
    change _ = (strategy.compute.shareProtocol hn).real i gate history (old gate.left) (old gate.right)
    rw [strategy.compute.share_real_eq_rawExecution,Rectangular.FullyTapedStrategy.rawExecution_eq_direct]
    rfl
  | refresh port =>
    let long := (matrixPrefixDistribution (F:=F) (n+t)).support_nonempty.choose
    rw [show (fun seed : Seed F n t => ((strategy.fixedPrefix seed).protocol hn).real
        i (.refresh port) history old) =
      (fun seed => ((strategy.fixedPrefix (long,seed.2)).protocol hn).real
        i (.refresh port) history (fun _ => old port)) from rfl]
    rw [seedDistribution,mixture_second (matrixPrefixDistribution (F:=F) (n+t))
      (matrixPrefixDistribution (F:=F) n) (fun failures =>
        ((strategy.fixedPrefix (long,failures)).protocol hn).real
          i (.refresh port) history (fun _ => old port))]
    exact refresh_eq_mixture strategy hn long i port history (old port)
  | sample value =>
    change _ = countableMixture _ (fun _ => (strategy.protocol hn).real i (.sample value) history old)
    rw [mixture_constant]

namespace FixedStrategy

/-- At operation i the fixed strategy reads exactly entry i of the private seed vector, never a future or earlier entry. Adaptive histories are still passed. -/
def fixSeeds {Ω : Type*} (tape : ℕ → Ω)
    (family : Ω → FixedStrategy F ML MR BL BR n t inputs hdim) :
    FixedStrategy F ML MR BL BR n t inputs hdim where
  compute.matrix i := (family (tape i)).compute.matrix i
  compute.left i := (family (tape i)).compute.left i
  compute.right i := (family (tape i)).compute.right i
  refresh i := (family (tape i)).refresh i
  publicLeft i := (family (tape i)).publicLeft i
  publicRight i := (family (tape i)).publicRight i

/-- The conditional answer wrapper preserves this exact time-local selection. -/
theorem fixSeeds_real {Ω : Type*} (tape : ℕ → Ω)
    (family : Ω → FixedStrategy F ML MR BL BR n t inputs hdim) (hn : 2≤n)
    (i : ℕ) (instruction : Instruction F (inputs+i))
    (history : Fin i → Answer ML MR BL BR) (old : Fin (inputs+i) → U F n × U F n) :
    ((fixSeeds tape family).protocol hn).real i instruction history old =
      ((family (tape i)).protocol hn).real i instruction history old := by
  cases instruction <;> rfl

end FixedStrategy

namespace Protocol
variable {Ω : Type*} [Countable Ω]

/-- Attach a fresh private seed to every actual heterogeneous transition. -/
def seededRunner (seed : PMF Ω) (family : Ω → Protocol F (U F n × U F n) (Answer ML MR BL BR) inputs) :
    {S : ℕ} → Program F inputs S → SeededRunner Ω (U F n × U F n) (Answer ML MR BL BR) inputs S
  | 0,.nil => .nil
  | _+1,.snoc prior instruction => .snoc (seededRunner seed family prior) seed
      (fun ω state => (family ω).real _ instruction state.2 state.1)

omit [Countable Ω] in
/-- Fixing one independent seed per chronological operation gives the same seeded physical runner. -/
theorem seededRunner_fixed (seed : PMF Ω)
    (family : Ω → FixedStrategy F ML MR BL BR n t inputs hdim) (hn : 2≤n)
    (program : Program F inputs S) (tape : ℕ → Ω) :
    (seededRunner seed (fun ω => (family ω).protocol hn) program).fixed (fun i => tape i.val) =
      ((FixedStrategy.fixSeeds tape family).protocol hn).realRunner program := by
  induction program with
  | nil => rfl
  | @snoc S prior instruction ih =>
    simp only [seededRunner,SeededRunner.fixed,realRunner,
      Fin.val_last,FixedStrategy.fixSeeds_real] at *
    have hi : Fin.init (fun i : Fin (S+1) => tape i.val) = (fun i : Fin S => tape i.val) := rfl
    rw [hi,ih]

end Protocol

/-- The fresh seeded runner is exactly the concrete physical runner. -/
theorem raw_runner_eq_fresh (strategy : Strategy F ML MR BL BR n t inputs hdim)
    (hn : 2≤n) (program : Program F inputs S) :
    (strategy.protocol hn).realRunner program =
      (Protocol.seededRunner (seedDistribution (F:=F) (n:=n) (t:=t))
        (fun seed => (strategy.fixedPrefix seed).protocol hn) program).fresh := by
  induction program with
  | nil => rfl
  | snoc prior instruction ih =>
    simp only [Protocol.realRunner,Protocol.seededRunner,SeededRunner.fresh,ih]
    congr 1
    funext state
    exact instruction_eq_mixture strategy hn _ instruction state.2 state.1

/-- Full raw initialization followed by physical execution is the independent private-prefix mixture of the exact fixed-prefix executions. -/
theorem raw_view_eq_mixture {V : Type*} [Fintype V]
    (strategy : Strategy F ML MR BL BR n t inputs hdim) (hn : 2≤n)
    (program : Program F inputs S) (input : Fin inputs → F)
    (observe : RunState (U F n × U F n) (Answer ML MR BL BR) inputs S → V) :
    ((((strategy.protocol hn).realRunner program).execute
      (toFinite (RawEncoding.initializeShares hn input))).map observe) =
    countableMixture (Protocol.seededRunner (seedDistribution (F:=F) (n:=n) (t:=t))
      (fun seed => (strategy.fixedPrefix seed).protocol hn) program).tapeDistribution
      (fun tape =>
        ((((FixedStrategy.fixSeeds
          (GateProtocol.extendTape
            ((matrixPrefixDistribution (F:=F) (n+t)).support_nonempty.choose,
             (matrixPrefixDistribution (F:=F) n).support_nonempty.choose) tape)
          strategy.fixedPrefix).protocol hn).realRunner program).execute
            (toFinite (RawEncoding.initializeShares hn input))).map observe) := by
  rw [raw_runner_eq_fresh,SeededRunner.execute_fresh_observed]
  congr 1
  funext tape
  have he := Protocol.seededRunner_fixed (seedDistribution (F:=F) (n:=n) (t:=t))
    strategy.fixedPrefix hn program (GateProtocol.extendTape
      ((matrixPrefixDistribution (F:=F) (n+t)).support_nonempty.choose,
       (matrixPrefixDistribution (F:=F) n).support_nonempty.choose) tape)
  simp only [GateProtocol.extendTape_at] at he
  rw [he]


end CircuitCompiler.Operations
