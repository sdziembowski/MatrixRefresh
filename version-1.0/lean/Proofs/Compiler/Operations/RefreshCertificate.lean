import Proofs.Compiler.Operations.OperationLaws
import Proofs.Compiler.Operations.CertificateLifts
import Proofs.Compiler.GateApproximation.FullRetryEstimates
import Proofs.Compiler.GateApproximation.Refreshing.LocalApproximation

/-!
# The two-port certificate for an ordinary refresh

A refresh has exactly two encoding ports: the old encoding and its freshly sampled successor. The physical conditional answer agrees with the existing square-refresh answer on consistent endpoints. The copy-gate approximation therefore applies without a retry loss. The direct compiler supplies β=q⁻¹⁄³ and proves the two-port admissibility condition.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.Operations
open Refresh MatrixRefresh TableAnalysis CircuitCompiler CircuitCompiler.Operations
  CircuitCompiler.RefreshAnalysis CircuitCompiler.RefreshApproximation
  CircuitCompiler.Composition CircuitCompiler.Composition.TopologicalExecution
  CircuitCompiler.AveragedEnergyComparison CircuitCompiler.SimulationParameters

variable {F ML MR BL BR : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ML] [Fintype MR] [Fintype BL] [Fintype BR]
  {n t inputs : ℕ} {hdim : n*n+1=n+t}

/-- A correctly labelled nonzero pair has positive mass in the uniform encoding distribution. Positivity is used before taking the physical conditional distribution. -/
theorem encoding_weight_pos_of_secret (hn : 2≤n) (s : F) (output : U F n × U F n)
    (h : secret ((stateEquivProd F n).symm output)=s) :
    0<(encodingDistribution hn s).weight output := by
  letI := fiber_nonempty F n hn s
  change 0 < ((mu F n hn s).map (stateEquivProd F n)).weight output
  rw [FiniteDistribution.map_equiv_weight,mu_weight,if_pos h]
  positivity

/-- On consistent endpoints, disintegrating the actual refresh joint distribution returns the square-refresh conditional answer, including the fixed raw prefix. -/
theorem fixed_refresh_answer_on_consistent
    (strategy : Operations.FixedStrategy F ML MR BL BR n t inputs hdim) (hn : 2≤n)
    (i : ℕ) (port : Fin (inputs+i)) (history : Fin i → Operations.Answer ML MR BL BR)
    (old : Fin (inputs+i) → U F n × U F n) (output : U F n × U F n)
    (h : secret ((stateEquivProd F n).symm output)=secret ((stateEquivProd F n).symm (old port))) :
    (strategy.protocol hn).answer i (.refresh port) history old output =
      answerDistribution id id (strategy.refresh i port history) (old port).1 (old port).2
        ((stateEquivProd F n).symm output) := by
  change Canonical.answer ((strategy.protocol hn).real i (.refresh port) history old) output=_
  rw [fixed_refresh_joint]
  exact answer_joint _ _ output (encoding_weight_pos_of_secret hn _ output h)

/-- The true refresh-answer table in grouped old/new share coordinates. The constant filler is immaterial: the refresh branch reads only its selected port. -/
def refreshProbability
    (strategy : Operations.FixedStrategy F ML MR BL BR n t inputs hdim) (hn : 2≤n)
    (i : ℕ) (port : Fin (inputs+i)) (history : Fin i → Operations.Answer ML MR BL BR)
    (z : Operations.Answer ML MR BL BR) (x y : U F n × U F n) : ℝ :=
  ((strategy.protocol hn).answer i (.refresh port) history (fun _=>(x.1,y.1)) (x.2,y.2)).weight z

/-- Any old array with the same selected encoding gives the same physical conditional answer; unrelated retained locations are never arguments of leakage. -/
theorem refreshProbability_eq_answer
    (strategy : Operations.FixedStrategy F ML MR BL BR n t inputs hdim) (hn : 2≤n)
    (i : ℕ) (port : Fin (inputs+i)) (history : Fin i → Operations.Answer ML MR BL BR)
    (z : Operations.Answer ML MR BL BR) (x y : U F n × U F n)
    (old : Fin (inputs+i) → U F n × U F n) (hold : old port=(x.1,y.1)) :
    refreshProbability strategy hn i port history z x y =
      ((strategy.protocol hn).answer i (.refresh port) history old (x.2,y.2)).weight z := by
  unfold refreshProbability Operations.Protocol.answer Operations.FixedStrategy.protocol
  simp only [hold]

variable [Nonempty (U F n)]

/-- The square-refresh certificate transfers to the true physical answer, using equality on the support of equal endpoint labels. -/
def refreshPortEstimates
    (strategy : Operations.FixedStrategy F ML MR BL BR n t inputs hdim)
    (hq : fieldCard F=2) (hn : 2≤n) (i : ℕ) (port : Fin (inputs+i))
    (history : Fin i → Operations.Answer ML MR BL BR) (z : Operations.Answer ML MR BL BR)
    (β : ℝ) (hβ : 0<β) (hβone : β≤1)
    (hthreshold : 1≤(Fintype.card (U F n):ℝ)*β^3) :
    GateLocalEstimates (fun labels : F×F=>copyLabelDistribution hn labels.1 labels.2)
      (fun labels=>labels.1=labels.2) (fun _=>refreshProbability strategy hn i port history z)
      β (396*β^(1/3:ℝ)) := by
  let data := copyGateLocalEstimates hq hn (strategy.refresh i port history) z β hβ hβone hthreshold
  have updated := LocalApproximation.changeOriginal data
    (fun _=>refreshProbability strategy hn i port history z) (ρ:=0) (by norm_num) (by
      intro labels hv x y hp
      rcases labels with ⟨s,t⟩
      dsimp only at hv ⊢
      subst t
      have hc := copyLabelDistribution_valid hn s (x,y) (ne_of_gt hp)
      have hc' : secret ((stateEquivProd F n).symm (x.2,y.2))=
          secret ((stateEquivProd F n).symm (x.1,y.1)) := hc
      rw [refreshProbability,fixed_refresh_answer_on_consistent strategy hn i port history _ _ hc']
      simp only [copyProbability,stateEquivProd,Equiv.coe_fn_symm_mk,sub_self,abs_zero,le_refl])
  simpa only [add_zero] using updated

end CompilerProof.Operations
