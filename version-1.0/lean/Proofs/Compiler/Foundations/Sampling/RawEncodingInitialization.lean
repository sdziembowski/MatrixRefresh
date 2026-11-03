import Proofs.Compiler.GateApproximation.MatrixPhase.PhysicalShares
import Proofs.Compiler.Foundations.Sampling.RawEncodingSampler
import Proofs.Compiler.GateApproximation.Shortening.RectangularPhysicalStochastic
import Proofs.Compiler.Construction.Parameters



/-!
# Exact independent initialization by concrete raw-entry samplers
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace CircuitCompiler.Sampling.RawEncoding

open Refresh MatrixRefresh Unbounded Composition

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/- Mathematical definition (normal notation): Appending one final element gives the bijection αᵏ × α ≃ αᵏ⁺¹. Its inverse separates the prefix and final coordinate. -/
private def snocEquiv {E : Type*} (k : ℕ) : (Fin k → E) × E ≃ (Fin (k+1) → E) where
  toFun x := Fin.snoc x.1 x.2
  invFun x := (Fin.init x,x (Fin.last _))
  left_inv x := by rcases x with ⟨x,last⟩; simp
  right_inv x := by simp

/-- Sequentially drawing the last coordinate gives the product distribution. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For E a set; k ∈ ℕ; P ∈ {0,…,(k + 1)-1} → 𝒟(E), assume E is finite. Then

bind(independentDistribution(Fin.init(P)), ((earlier ↦ (((last ↦ Fin.snoc(α = (x₁ ↦ E), earlier, last)))_*P(Fin.last(x)))))) = independentDistribution(P).
-/
theorem independentDistribution_snoc {E : Type*} [Fintype E] {k : ℕ}
    (P : Fin (k+1) → FiniteDistribution E) :
    (independentDistribution (Fin.init P)).bind (fun earlier =>
      (P (Fin.last _)).map (fun last => Fin.snoc (α := fun _ => E) earlier last)) = independentDistribution P := by
  have h : ((independentDistribution (Fin.init P)).prod (P (Fin.last k))).map (snocEquiv k) =
      independentDistribution P := by
    ext x
    rw [map_equiv_weight]
    simp only [FiniteDistribution.prod,FiniteDistribution.joint,independentDistribution,snocEquiv,Equiv.coe_fn_symm_mk]
    exact (Fin.prod_univ_castSucc (fun i => (P i).weight (x i))).symm
  exact (TopologicalExecution.joint_map_eq_bind (independentDistribution (Fin.init P))
    (fun _ => P (Fin.last k)) (snocEquiv k)).symm.trans h

/-- The input runner's product encoding distribution is the exact distribution of the concrete sequential initialization algorithm. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, inputs ∈ ℕ; input ∈ {0,…,inputs-1} → F, assume 2 ≤ n. Then

initializeWires(input) = toPMF(independentDistribution(((i ↦ μᵢₙₚᵤₜ₍ᵢ₎)))).
-/
theorem initialize_eq_independent {n inputs : ℕ} (hn : 2 ≤ n) (input : Fin inputs → F) :
    initializeWires hn input = toPMF (independentDistribution (fun i => mu F n hn (input i))) := by
  induction inputs with
  | zero =>
      apply PMF.ext
      intro x
      have hx : x = Fin.elim0 := funext (fun i => Fin.elim0 i)
      subst x
      simp [initializeWires,PMF.pure_apply,toPMF_apply,independentDistribution]
  | succ k ih =>
      rw [initializeWires,ih]
      have h (earlier : Fin k → State F n) :
          (tapeDistribution hn (input (Fin.last k))).map (fun tape =>
            Fin.snoc (α := fun _ => State F n) earlier (returned hn (input (Fin.last k)) tape.2.2).val) =
          (toPMF (mu F n hn (input (Fin.last k)))).map (fun last => Fin.snoc (α := fun _ => State F n) earlier last) := by
        rw [← returned_mu hn (input (Fin.last k)),PMF.map_comp]
        rfl
      simp_rw [h,← toPMF_map]
      rw [← toPMF_bind]
      congr 1
      exact independentDistribution_snoc (fun i => mu F n hn (input i))

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, inputs ∈ ℕ; input ∈ {0,…,inputs-1} → F, assume 2 ≤ n. Then

initializeShares(input) = toPMF(independentDistribution(((i ↦ encodingDistribution(input(i)))))) .
-/
theorem initializeShares_eq_independent {n inputs : ℕ} (hn : 2 ≤ n)
    (input : Fin inputs → F) :
    initializeShares hn input =
      toPMF (independentDistribution (fun i => encodingDistribution hn (input i))) := by
  rw [initializeShares,initialize_eq_independent,← toPMF_map,independentDistribution_map]
  rfl

end

end CircuitCompiler.Sampling.RawEncoding
