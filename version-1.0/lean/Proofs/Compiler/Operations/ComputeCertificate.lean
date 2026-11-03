import Proofs.Compiler.Operations.OperationLaws
import Proofs.Compiler.Operations.CertificateLifts
import Proofs.Compiler.GateApproximation.FullRetryEstimates
import Proofs.Compiler.GateApproximation.Interfaces.Gadget.ScopeInterface
import Proofs.Compiler.Simulation.ShareGeometry

/-!
# The three-port certificate for an actual computation operation

The existing rectangular-shortening theorem supplies one signed table and its factor representation on the two operands and the new output. Its first-attempt conditional answer is replaced by the true full-retry conditional answer using the proved per-answer `2/2^n` bound. Nothing is conditioned on a leakage answer before charging this difference. The direct compiler instantiates this local bound at its single cutoff β=q⁻¹⁄³.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.Operations
open Refresh MatrixRefresh TableAnalysis CircuitCompiler CircuitCompiler.Operations
  CircuitCompiler.Rectangular CircuitCompiler.GadgetApproximation
  CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution
  CircuitCompiler.AveragedEnergyComparison CircuitCompiler.SimulationParameters

variable {F ML MR BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
  {n t inputs : ℕ} {hdim : n*n+1=n+t}

/-- The true complete-answer probability on the three paired encoding ports. -/
def computeProbability
    (strategy : Operations.FixedStrategy F ML MR BL BR n t inputs hdim) (hn : 2≤n)
    (i : ℕ) (gate : Gate F (inputs+i)) (history : Fin i → Operations.Answer ML MR BL BR)
    (z : Operations.Answer ML MR BL BR) (x y : GateSide F n n) : ℝ :=
  ((FullRetry.protocol (strategy.compute.stochasticStrategy hn) hn).answer i gate history
    (x.1.1,y.1.1) (x.1.2,y.1.2) (x.2,y.2)).weight z

/-- The heterogeneous computation branch uses exactly that full-retry answer. The rest of the old array is unavailable to its local leakage functions. -/
theorem fixed_compute_answer
    (strategy : Operations.FixedStrategy F ML MR BL BR n t inputs hdim) (hn : 2≤n)
    (i : ℕ) (gate : Gate F (inputs+i)) (history : Fin i → Operations.Answer ML MR BL BR)
    (old : Fin (inputs+i) → U F n × U F n) (output : U F n × U F n) :
    (strategy.protocol hn).answer i (.compute gate) history old output =
      (FullRetry.protocol (strategy.compute.stochasticStrategy hn) hn).answer i gate history
        (old gate.left) (old gate.right) output := rfl

/-- The probability table agrees with the actual physical conditional answer for any filler array whose selected operand entries are the prescribed ports. -/
theorem computeProbability_eq_answer
    (strategy : Operations.FixedStrategy F ML MR BL BR n t inputs hdim) (hn : 2≤n)
    (i : ℕ) (gate : Gate F (inputs+i)) (history : Fin i → Operations.Answer ML MR BL BR)
    (z : Operations.Answer ML MR BL BR) (x y : GateSide F n n)
    (old : Fin (inputs+i) → U F n × U F n)
    (hl : old gate.left=(x.1.1,y.1.1)) (hr : old gate.right=(x.1.2,y.1.2)) :
    computeProbability strategy hn i gate history z x y =
      ((strategy.protocol hn).answer i (.compute gate) history old (x.2,y.2)).weight z := by
  rw [fixed_compute_answer,hl,hr]
  rfl

/-- Positive mass in the independent three-encoding distribution implies that all three inner products equal their specified labels. This uses the unconditional distribution. -/
theorem three_port_support (hn : 2≤n) (labels : (F×F)×F) (x y : GateSide F n n)
    (hp : 0<(independentLabelledPortDistribution hn hn labels.1.1 labels.1.2 labels.2).weight (x,y)) :
    secret (⟨x.1.1,y.1.1⟩ : State F n)=labels.1.1 ∧
    secret (⟨x.1.2,y.1.2⟩ : State F n)=labels.1.2 ∧
    secret (⟨x.2,y.2⟩ : State F n)=labels.2 := by
  have hp0 := ne_of_gt hp
  rw [independentLabelledPortDistribution,FiniteDistribution.map_equiv_weight] at hp0
  change ((mu F n hn labels.1.1).weight ⟨x.1.1,y.1.1⟩ *
    (mu F n hn labels.1.2).weight ⟨x.1.2,y.1.2⟩) *
    (mu F n hn labels.2).weight ⟨x.2,y.2⟩≠0 at hp0
  have hpair := (mul_ne_zero_iff.mp hp0).1
  exact ⟨mu_supports n hn _ _ (mul_ne_zero_iff.mp hpair).1,
    mu_supports n hn _ _ (mul_ne_zero_iff.mp hpair).2,
    mu_supports n hn _ _ (mul_ne_zero_iff.mp hp0).2⟩

variable [Nonempty (U F n)]

/-- First-attempt accepted-table certificate, with the actual operation's AND/NAND validity predicate and its existing ambient answer completion. -/
def acceptedComputePortEstimates
    (strategy : Fractional.AugmentedStrategy F (ML×MR) (BL×BR) n t inputs hdim)
    (hq : fieldCard F=2) (hn : 2≤n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → Operations.Answer ML MR BL BR) (z : Operations.Answer ML MR BL BR)
    (β : ℝ) (hβ : 0<β) (hβone : β≤1)
    (hthreshold : 1≤(Fintype.card (U F n × U F n):ℝ)*β^3) :
    GateLocalEstimates
      (fun labels : (F×F)×F => independentLabelledPortDistribution hn hn labels.1.1 labels.1.2 labels.2)
      (fun labels => labels.2=gate.kind.eval labels.1.1 labels.1.2)
      (fun _ x y => ((strategy.shareProtocol hn).answer i gate history
        (x.1.1,y.1.1) (x.1.2,y.1.2) (x.2,y.2)).weight z)
      β (396*β^(1/3:ℝ)) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0,by omega⟩⟩
  letI : Nonempty (U F (n+t)) := ⟨unitShare ⟨0,by omega⟩⟩
  let data := shortenedGateLocalEstimates hq hn hdim gate.kind.affineConstant
    (strategy.matrix i gate history) (strategy.rectangles i gate history) z β hβ hβone hthreshold
  refine {
    approximation := data.approximation
    factors := data.factors
    left_max := data.left_max
    right_max := data.right_max
    left_mean := data.left_mean
    right_mean := data.right_mean
    all_labels_rms := data.all_labels_rms
    valid_error_rms := ?_ }
  intro labels hv
  rcases labels with ⟨⟨s₁,s₂⟩,v⟩
  dsimp only at hv ⊢
  rw [gate_eval_product_offset_binary hq] at hv
  subst v
  exact augmented_ambient_rms_error hq hn hdim gate.kind.affineConstant
    (strategy.matrix i gate history) (strategy.rectangles i gate history)
    ((strategy.shareProtocol hn).answer i gate history)
    (strategy.share_answer_on_support hn i gate history) s₁ s₂ z β hβ hβone hthreshold

/-- Complete rectangular retries preserve the factors and add only the pointwise retry allowance to the accepted-table RMS error. -/
def computePortEstimates
    (strategy : Operations.FixedStrategy F ML MR BL BR n t inputs hdim)
    (hq : fieldCard F=2) (hn : 2≤n) (i : ℕ) (gate : Gate F (inputs+i))
    (history : Fin i → Operations.Answer ML MR BL BR) (z : Operations.Answer ML MR BL BR)
    (β : ℝ) (hβ : 0<β) (hβone : β≤1)
    (hthreshold : 1≤(Fintype.card (U F n × U F n):ℝ)*β^3) :
    GateLocalEstimates
      (fun labels : (F×F)×F => independentLabelledPortDistribution hn hn labels.1.1 labels.1.2 labels.2)
      (fun labels => labels.2=gate.kind.eval labels.1.1 labels.1.2)
      (fun _ => computeProbability strategy hn i gate history z)
      β (396*β^(1/3:ℝ)+2/(2:ℝ)^n) := by
  letI : Nonempty (U F n) := ⟨unitShare ⟨0,by omega⟩⟩
  let data := acceptedComputePortEstimates (strategy.compute.stochasticStrategy hn)
    hq hn i gate history z β hβ hβone hthreshold
  apply LocalApproximation.changeOriginal data (fun _=>computeProbability strategy hn i gate history z)
    (by positivity : 0≤2/(2:ℝ)^n)
  intro labels hv x y hp
  obtain ⟨hl,hr,ho⟩ := three_port_support hn labels x y hp
  have hvalid : secret ((stateEquivProd F n).symm (x.2,y.2))=
      gate.kind.eval (secret ((stateEquivProd F n).symm (x.1.1,y.1.1)))
        (secret ((stateEquivProd F n).symm (x.1.2,y.1.2))) := by
    change secret (⟨x.2,y.2⟩ : State F n)=gate.kind.eval
      (secret (⟨x.1.1,y.1.1⟩ : State F n)) (secret (⟨x.1.2,y.1.2⟩ : State F n))
    rw [hl,hr,ho]
    exact hv
  exact FullRetry.share_answer_difference (strategy.compute.stochasticStrategy hn)
    hq hn i gate history _ _ _ hvalid z

end CompilerProof.Operations
