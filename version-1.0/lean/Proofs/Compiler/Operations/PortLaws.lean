import Proofs.Compiler.LocalComparisons.NetworkInterface
import Proofs.Compiler.GateApproximation.Interfaces.Gadget.Labelled

/-!
# Projecting independent canonical encodings onto operation ports

Only unconditional product distributions are used. Projecting onto distinct wire locations gives the product of those wires' encoding distributions. Grouping the left and right shares afterwards retains the correlation within each encoding.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
noncomputable section

namespace CompilerProof.Operations
open Refresh MatrixRefresh CircuitCompiler CircuitCompiler.Composition
  CircuitCompiler.AveragedEnergyComparison

/-- An injective choice of coordinates preserves their independent distributions. -/
theorem independent_project {W I E : Type*} [Fintype W] [DecidableEq W]
    [Fintype I] [DecidableEq I] [Fintype E]
    (laws : W → FiniteDistribution E) (f : I → W) (hf : Function.Injective f) :
    (independentDistribution laws).map (fun e i => e (f i)) =
      independentDistribution (fun i => laws (f i)) := by
  letI : Fintype (Set.range f) := Subtype.fintype (fun w => w∈Set.range f)
  let e : I ≃ Set.range f := Equiv.ofInjective f hf
  let reindex : (Set.range f → E) ≃ (I → E) :=
    Equiv.arrowCongr e.symm (Equiv.refl E)
  have hm := independentDistribution_select laws (fun w => w∈Set.range f)
  have hp := congrArg (fun P : FiniteDistribution (Set.range f → E) => P.map reindex) hm
  rw [FiniteDistribution.map_map] at hp
  change (independentDistribution laws).map (fun x i => x (f i)) = _ at hp
  rw [hp]
  ext x
  rw [FiniteDistribution.map_equiv_weight]
  change (∏ w : Set.range f, (laws w).weight (reindex.symm x w)) =
    ∏ i : I, (laws (f i)).weight (x i)
  symm
  apply Fintype.prod_equiv e
  intro i
  simp [reindex,Equiv.arrowCongr,e]

/-- Ordered three-port coordinates for the two operands and new output. -/
def tripleEquiv (E : Type*) : (Fin 3 → E) ≃ ((E × E) × E) where
  toFun e := ((e 0,e 1),e 2)
  invFun e := ![e.1.1,e.1.2,e.2]
  left_inv e := by funext i; fin_cases i <;> rfl
  right_inv e := by rcases e with ⟨⟨a,b⟩,c⟩; rfl

/-- The finite product on three coordinates is the iterated independent pair product used in the computation-gadget estimates. -/
theorem independent_triple {E : Type*} [Fintype E]
    (P : Fin 3 → FiniteDistribution E) :
    (independentDistribution P).map (tripleEquiv E) = ((P 0).prod (P 1)).prod (P 2) := by
  ext x
  rw [FiniteDistribution.map_equiv_weight]
  simp only [independentDistribution,FiniteDistribution.prod,FiniteDistribution.joint,
    tripleEquiv,Equiv.coe_fn_symm_mk,Fin.prod_univ_three,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two]
  rfl


/-- Uniform mass is preserved by an exact finite change of coordinates. -/
theorem uniform_map_equiv {E D : Type*} [Fintype E] [Nonempty E]
    [Fintype D] [Nonempty D] (e : E ≃ D) :
    (FiniteDistribution.uniform : FiniteDistribution E).map e = FiniteDistribution.uniform := by
  ext x
  rw [FiniteDistribution.map_equiv_weight]
  simp only [FiniteDistribution.uniform]
  rw [Fintype.card_congr e]

/-- Select the two operand shares and output share in that order. -/
def projectTriple {W E : Type*} (left right output : W) (e : W → E) : (E×E)×E :=
  ((e left,e right),e output)

/-- Three distinct coordinates have the exact ordered product distribution. -/
theorem independent_projectTriple {W E : Type*} [Fintype W] [DecidableEq W] [Fintype E]
    (laws : W → FiniteDistribution E) (l r o : W)
    (hlr : l≠r) (hlo : l≠o) (hro : r≠o) :
    (independentDistribution laws).map (projectTriple l r o) =
      ((laws l).prod (laws r)).prod (laws o) := by
  let f : Fin 3 → W := ![l,r,o]
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f,Ne.symm hlr,Ne.symm hlo,Ne.symm hro]
  have h := congrArg (fun P : FiniteDistribution (Fin 3 → E) => P.map (tripleEquiv E))
    (independent_project laws f hf)
  rw [FiniteDistribution.map_map,independent_triple] at h
  exact h

/-- Projecting three distinct coordinates from a uniform wire assignment gives the uniform three-port assignment. -/
theorem uniform_projectTriple {W E : Type*} [Fintype W] [DecidableEq W]
    [Fintype E] [Nonempty E] (l r o : W)
    (hlr : l≠r) (hlo : l≠o) (hro : r≠o) :
    (FiniteDistribution.uniform : FiniteDistribution (W → E)).map (projectTriple l r o) =
      FiniteDistribution.uniform := by
  let f : Fin 3 → W := ![l,r,o]
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f,Ne.symm hlr,Ne.symm hlo,Ne.symm hro]
  have h := congrArg (fun P : FiniteDistribution (Fin 3 → E) => P.map (tripleEquiv E))
    (independent_project (fun _ : W => (FiniteDistribution.uniform : FiniteDistribution E)) f hf)
  rw [FiniteDistribution.map_map,independentDistribution_uniform,independentDistribution_uniform,
    uniform_map_equiv] at h
  exact h

/-- Ordered old/output coordinates for a control refresh. -/
def pairEquiv (E : Type*) : (Fin 2 → E) ≃ (E×E) where
  toFun e := (e 0,e 1)
  invFun e := ![e.1,e.2]
  left_inv e := by funext i; fin_cases i <;> rfl
  right_inv e := by rcases e with ⟨a,b⟩; rfl

/-- Independent sampling on two coordinates is the product of their marginal distributions. -/
theorem independent_pair {E : Type*} [Fintype E] (P : Fin 2 → FiniteDistribution E) :
    (independentDistribution P).map (pairEquiv E) = (P 0).prod (P 1) := by
  ext x
  rw [FiniteDistribution.map_equiv_weight]
  simp only [independentDistribution,FiniteDistribution.prod,FiniteDistribution.joint,
    pairEquiv,Equiv.coe_fn_symm_mk,Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]

/-- Read the old and new share coordinates of a two-port refresh. -/
def projectPair {W E : Type*} (old output : W) (e : W → E) : E×E := (e old,e output)

/-- Projecting two distinct coordinates from independent wire encodings gives their independent two-port distribution. -/
theorem independent_projectPair {W E : Type*} [Fintype W] [DecidableEq W] [Fintype E]
    (laws : W → FiniteDistribution E) (l o : W) (hlo : l≠o) :
    (independentDistribution laws).map (projectPair l o) = (laws l).prod (laws o) := by
  let f : Fin 2 → W := ![l,o]
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f,Ne.symm hlo]
  have h := congrArg (fun P : FiniteDistribution (Fin 2 → E) => P.map (pairEquiv E))
    (independent_project laws f hf)
  rw [FiniteDistribution.map_map,independent_pair] at h
  exact h

/-- Projecting two distinct uniform coordinates gives the uniform two-port distribution. -/
theorem uniform_projectPair {W E : Type*} [Fintype W] [DecidableEq W]
    [Fintype E] [Nonempty E] (l o : W) (hlo : l≠o) :
    (FiniteDistribution.uniform : FiniteDistribution (W → E)).map (projectPair l o) =
      FiniteDistribution.uniform := by
  let f : Fin 2 → W := ![l,o]
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f,Ne.symm hlo]
  have h := congrArg (fun P : FiniteDistribution (Fin 2 → E) => P.map (pairEquiv E))
    (independent_project (fun _ : W => (FiniteDistribution.uniform : FiniteDistribution E)) f hf)
  rw [FiniteDistribution.map_map,independentDistribution_uniform,independentDistribution_uniform,
    uniform_map_equiv] at h
  exact h

end CompilerProof.Operations
