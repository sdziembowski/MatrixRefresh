import Proofs.Compiler.DirectComposition.TensorDiscrepancy
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.EncodingMeasure

/-!
# Fixed-bit encodings versus independent shares

Independent uniform left and right shares form an explicit mixture of the actual fixed-bit encoding distributions. Averaging the established two-secret discrepancy over that mixture gives the signed atomic bound for μᵦ − ν. The tensor theorem then supplies one small factor for each marked wire.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.DirectComposition

open Refresh MatrixRefresh CircuitCompiler

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
  [Nonempty (U F n)]

/-- The secret distribution obtained by sampling the two nonzero shares independently. -/
def independentSecretDistribution : FiniteDistribution F :=
  (FiniteDistribution.uniform : FiniteDistribution (U F n × U F n)).map
    (fun xy => secret ((stateEquivProd F n).symm xy))

/-- The fiber of the paired-share secret map is the same set as the encoding fiber on structured states. -/
def pairedSecretFiberEquiv (s : F) :
    {xy : U F n × U F n // secret ((stateEquivProd F n).symm xy)=s} ≃ Fiber F n s :=
  Equiv.subtypeEquiv (stateEquivProd F n).symm (fun _ => Iff.rfl)

/-- A secret receives the relative size of its encoding fiber under independent uniform shares. -/
theorem independentSecretDistribution_weight (s : F) :
    (independentSecretDistribution (F:=F) (n:=n)).weight s =
      (Fintype.card (Fiber F n s) : ℝ) / (Fintype.card (U F n × U F n) : ℝ) := by
  rw [independentSecretDistribution,FiniteDistribution.uniform_map_weight,
    Fintype.card_congr (pairedSecretFiberEquiv s)]

/-- The actual encoding distribution is uniform on the prescribed secret fiber on the paired-share carrier. -/
theorem paired_encoding_weight (hn : 2≤n) (s : F) (xy : U F n × U F n) :
    (encodingDistribution hn s).weight xy =
      if secret ((stateEquivProd F n).symm xy)=s
      then 1/(Fintype.card (Fiber F n s) : ℝ) else 0 := by
  change ((mu F n hn s).map (stateEquivProd F n)).weight xy = _
  rw [FiniteDistribution.map_equiv_weight,mu_weight]

/-- Sampling the secret of independent shares and then its uniform encoding recovers independent shares exactly. -/
theorem independentSecret_bind_encoding (hn : 2≤n) :
    (independentSecretDistribution (F:=F) (n:=n)).bind (encodingDistribution hn) =
      (FiniteDistribution.uniform : FiniteDistribution (U F n × U F n)) := by
  ext xy
  change (∑ s : F, (independentSecretDistribution (F:=F) (n:=n)).weight s *
    (encodingDistribution hn s).weight xy) = (Fintype.card (U F n × U F n) : ℝ)⁻¹
  simp_rw [independentSecretDistribution_weight,paired_encoding_weight,mul_ite,mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ,if_true]
  have hf : (Fintype.card (Fiber F n (secret ((stateEquivProd F n).symm xy))) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (fiber_card_pos hn _)
  have hp : (Fintype.card (U F n × U F n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp [hf,hp]

/-- One fixed-bit encoding differs from independent shares by at most the established two-secret scalar discrepancy. -/
theorem encoding_independent_scalar (hn : 2≤n) (s : F) (f g : U F n → ℝ) :
    |∑ x, ∑ y,
        ((encodingDistribution hn s).weight (x,y) -
          (FiniteDistribution.uniform : FiniteDistribution (U F n × U F n)).weight (x,y)) *
        f x * g y| ≤
      zeta F n * Real.sqrt (FiniteDistribution.uniform.expect (fun x => f x^2)) *
        Real.sqrt (FiniteDistribution.uniform.expect (fun y => g y^2)) := by
  let P := independentSecretDistribution (F:=F) (n:=n)
  let value := fun xy : U F n × U F n => f xy.1*g xy.2
  have hd : (∑ x, ∑ y,
        ((encodingDistribution hn s).weight (x,y) -
          (FiniteDistribution.uniform : FiniteDistribution (U F n × U F n)).weight (x,y)) *
        f x * g y) =
      (encodingDistribution hn s).expect value - FiniteDistribution.uniform.expect value := by
    simp only [FiniteDistribution.expect,Fintype.sum_prod_type,sub_mul,mul_assoc,
      Finset.sum_sub_distrib,value]
  have hm : (encodingDistribution hn s).expect value - FiniteDistribution.uniform.expect value =
      P.expect (fun t => (encodingDistribution hn s).expect value -
        (encodingDistribution hn t).expect value) := by
    rw [← independentSecret_bind_encoding hn,expect_bind,expect_sub,P.expect_const]
  rw [hd,hm]
  calc
    _ ≤ P.expect (fun t => |(encodingDistribution hn s).expect value -
        (encodingDistribution hn t).expect value|) := abs_expect_le_expect_abs P _
    _ ≤ P.expect (fun _ => zeta F n *
        Real.sqrt (FiniteDistribution.uniform.expect (fun x => f x^2)) *
        Real.sqrt (FiniteDistribution.uniform.expect (fun y => g y^2))) := by
      apply P.expect_mono
      intro t
      exact encodingDistribution_scalar hn s t f g
    _ = _ := P.expect_const _

/-- The actual independent encoding differences have a tensor discrepancy coefficient ζ for every marked wire. -/
theorem encoding_independent_tensor {W : Type*} [Fintype W]
    (hn : 2≤n) (label : W → F) (f g : (W → U F n) → ℝ) :
    |∑ left, ∑ right,
        (∏ w, ((encodingDistribution hn (label w)).weight (left w,right w) -
          (FiniteDistribution.uniform : FiniteDistribution (U F n × U F n)).weight (left w,right w))) *
        f left * g right| ≤
      zeta F n ^ Fintype.card W *
        Real.sqrt (FiniteDistribution.uniform.expect (fun left => f left^2)) *
        Real.sqrt (FiniteDistribution.uniform.expect (fun right => g right^2)) := by
  exact tensor_uniform_pairing _ (zeta F n) (by unfold zeta; positivity)
    (fun w => encoding_independent_scalar hn (label w)) f g

end CompilerProof.DirectComposition
