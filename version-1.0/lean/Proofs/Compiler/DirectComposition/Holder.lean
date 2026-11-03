import Proofs.Compiler.DirectComposition.Model
import Mathlib.Analysis.MeanInequalities

/-!
# Products of local errors at incidence three

The wire variables are independent before leakage. Averaging over one wire under its original encoding distribution affects at most three local factors, so cubic Hölder can remove that variable without increasing the product of the factors' cubic norms. Repeating this argument proves the finite scope inequality used for jointly marked errors.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open scoped BigOperators Classical
universe u

namespace CompilerProof.DirectComposition

open Refresh MatrixRefresh CircuitCompiler.Composition

variable {E I W : Type*} [Fintype E] [Fintype I]

/-- The cubic norm of a nonnegative function under a finite probability distribution. -/
def cubicNorm (P : FiniteDistribution E) (f : E → ℝ) : ℝ :=
  Real.rpow (P.expect (fun x => f x ^ 3)) (1/3 : ℝ)

/-- Every cubic norm is nonnegative. -/
theorem cubicNorm_nonneg (P : FiniteDistribution E) (f : E → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ cubicNorm P f := by
  exact Real.rpow_nonneg (P.expect_nonneg _ (fun x => pow_nonneg (hf x) _)) _

/-- Cubing the cubic norm returns the third moment of a nonnegative function. -/
theorem cubicNorm_cube (P : FiniteDistribution E) (f : E → ℝ)
    (hf : ∀ x, 0 ≤ f x) : (cubicNorm P f)^3 = P.expect (fun x => f x^3) := by
  unfold cubicNorm
  convert Real.rpow_inv_natCast_pow
    (P.expect_nonneg _ (fun x => pow_nonneg (hf x) _)) (by decide : 3≠0) using 1 <;> norm_num

/-- A nonnegative constant has its own value as cubic norm. -/
theorem cubicNorm_const (P : FiniteDistribution E) (c : ℝ) (hc : 0≤c) :
    cubicNorm P (fun _ => c) = c := by
  unfold cubicNorm
  rw [P.expect_const]
  convert Real.pow_rpow_inv_natCast hc (by decide : 3≠0) using 1 <;> norm_num

/-- A nonnegative function with zero third moment vanishes wherever its distribution has positive weight. -/
theorem cube_moment_zero_support (P : FiniteDistribution E) (f : E → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hzero : P.expect (fun x => f x^3)=0) (x : E) :
    P.weight x = 0 ∨ f x = 0 := by
  have hx : P.weight x * f x^3 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => mul_nonneg (P.nonneg y) (pow_nonneg (hf y) 3))).mp hzero x
        (Finset.mem_univ x)
  rcases mul_eq_zero.mp hx with h|h
  · exact Or.inl h
  · exact Or.inr ((pow_eq_zero_iff (by decide : 3≠0)).mp h)

/-- The elementary three-factor Young inequality follows from the sum of three squares. -/
theorem triple_young {a b c : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) :
    a*b*c ≤ (a^3+b^3+c^3)/3 := by
  have hq : 0 ≤ a^2+b^2+c^2-a*b-a*c-b*c := by
    nlinarith [sq_nonneg (a-b),sq_nonneg (a-c),sq_nonneg (b-c)]
  have h := mul_nonneg (add_nonneg (add_nonneg ha hb) hc) hq
  nlinarith

/-- A zero cubic moment makes every weighted product containing that factor vanish. -/
theorem expect_triple_zero (P : FiniteDistribution E) (f g h : E → ℝ)
    (hf : ∀ x,0≤f x) (hz : P.expect (fun x=>f x^3)=0) :
    P.expect (fun x=>f x*g x*h x)=0 := by
  apply Finset.sum_eq_zero
  intro x _
  rcases cube_moment_zero_support P f hf hz x with hx|hx <;> simp [hx]

/-- A normalized nonnegative function has third moment one. -/
theorem cubicNorm_normalized_moment (P : FiniteDistribution E) (f : E → ℝ)
    (hf : ∀ x,0≤f x) (hn : cubicNorm P f ≠ 0) :
    P.expect (fun x => (f x / cubicNorm P f)^3)=1 := by
  simp_rw [div_pow,div_eq_mul_inv]
  rw [MatrixRefresh.expect_mul_const P, cubicNorm_cube P f hf]
  apply mul_inv_cancel₀
  rw [← cubicNorm_cube P f hf]
  exact pow_ne_zero _ hn

/-- Cubic Hölder for three nonnegative functions under one finite probability distribution. -/
theorem expect_triple_le_cubicNorm (P : FiniteDistribution E) (f g h : E → ℝ)
    (hf : ∀ x,0≤f x) (hg : ∀ x,0≤g x) (hh : ∀ x,0≤h x) :
    P.expect (fun x => f x*g x*h x) ≤ cubicNorm P f*cubicNorm P g*cubicNorm P h := by
  have hnf := cubicNorm_nonneg P f hf
  have hng := cubicNorm_nonneg P g hg
  have hnh := cubicNorm_nonneg P h hh
  by_cases hz : cubicNorm P f=0
  · have hm : P.expect (fun x=>f x^3)=0 := by rw [← cubicNorm_cube P f hf,hz];norm_num
    rw [expect_triple_zero P f g h hf hm]
    positivity
  by_cases hz' : cubicNorm P g=0
  · have hm : P.expect (fun x=>g x^3)=0 := by rw [← cubicNorm_cube P g hg,hz'];norm_num
    have he : P.expect (fun x=>f x*g x*h x)=0 := by
      simpa only [mul_comm (f _) (g _)] using expect_triple_zero P g f h hg hm
    rw [he]
    positivity
  by_cases hz'' : cubicNorm P h=0
  · have hm : P.expect (fun x=>h x^3)=0 := by rw [← cubicNorm_cube P h hh,hz''];norm_num
    have he : P.expect (fun x=>f x*g x*h x)=0 := by
      convert expect_triple_zero P h f g hh hm using 1
      congr 1
      funext x
      ring
    rw [he]
    positivity
  have hp : 0<cubicNorm P f := lt_of_le_of_ne hnf (Ne.symm hz)
  have hq : 0<cubicNorm P g := lt_of_le_of_ne hng (Ne.symm hz')
  have hr : 0<cubicNorm P h := lt_of_le_of_ne hnh (Ne.symm hz'')
  have hnormalize : P.expect
      (fun x => (f x/cubicNorm P f)*(g x/cubicNorm P g)*(h x/cubicNorm P h)) ≤ 1 := by
    calc
      _ ≤ P.expect (fun x => ((f x/cubicNorm P f)^3+
          (g x/cubicNorm P g)^3+(h x/cubicNorm P h)^3)/3) :=
        P.expect_mono (fun x => triple_young
          (div_nonneg (hf x) hp.le) (div_nonneg (hg x) hq.le) (div_nonneg (hh x) hr.le))
      _ = 1 := by
        simp_rw [div_eq_mul_inv]
        rw [MatrixRefresh.expect_mul_const P,MatrixRefresh.expect_add P,MatrixRefresh.expect_add P]
        change (P.expect (fun x=>(f x/cubicNorm P f)^3)+
          P.expect (fun x=>(g x/cubicNorm P g)^3)+
          P.expect (fun x=>(h x/cubicNorm P h)^3))*(3:ℝ)⁻¹=1
        rw [cubicNorm_normalized_moment P f hf hz,
          cubicNorm_normalized_moment P g hg hz',cubicNorm_normalized_moment P h hh hz'']
        norm_num
  have heq : P.expect (fun x => f x*g x*h x) =
      (cubicNorm P f*cubicNorm P g*cubicNorm P h)*P.expect
        (fun x => (f x/cubicNorm P f)*(g x/cubicNorm P g)*(h x/cubicNorm P h)) := by
    rw [← MatrixRefresh.expect_smul P]
    congr 1
    funext x
    field_simp
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hnormalize (mul_nonneg (mul_nonneg hnf hng) hnh)).trans_eq
    (mul_one _)

/-- Cubic Hölder with unused positions filled by the constant one. -/
theorem expect_small_product_le (P : FiniteDistribution E) (selected : Finset I)
    (hcard : selected.card≤3) (f : I → E → ℝ) (hf : ∀ i x,0≤f i x) :
    P.expect (fun x => ∏ i∈selected,f i x) ≤ ∏ i∈selected,cubicNorm P (f i) := by
  have hc : selected.card=0 ∨ selected.card=1 ∨ selected.card=2 ∨ selected.card=3 := by omega
  rcases hc with hc|hc|hc|hc
  · have hs := Finset.card_eq_zero.mp hc
    subst selected
    simp
  · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hc
    simpa [cubicNorm_const P 1 zero_le_one] using
      expect_triple_le_cubicNorm P (f i) (fun _=>1) (fun _=>1)
        (hf i) (fun _=>zero_le_one) (fun _=>zero_le_one)
  · obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hc
    simpa [hij,cubicNorm_const P 1 zero_le_one] using
      expect_triple_le_cubicNorm P (f i) (f j) (fun _=>1)
        (hf i) (hf j) (fun _=>zero_le_one)
  · obtain ⟨i,j,k,hij,hik,hjk,rfl⟩ := Finset.card_eq_three.mp hc
    simpa [hij,hik,hjk,mul_assoc] using
      expect_triple_le_cubicNorm P (f i) (f j) (f k) (hf i) (hf j) (hf k)

/-- If at most three factors depend on a sampled variable, all the others factor out and the same cubic-norm bound holds. -/
theorem expect_product_le_of_constant [Nonempty E] (P : FiniteDistribution E)
    (selected : Finset I) (hcard : selected.card≤3) (f : I → E → ℝ)
    (hf : ∀ i x,0≤f i x)
    (hconstant : ∀ i,i∉selected → ∀ x y,f i x=f i y) :
    P.expect (fun x => ∏ i,f i x) ≤ ∏ i,cubicNorm P (f i) := by
  let x₀ : E := Classical.choice inferInstance
  let C := ∏ i∈selectedᶜ,f i x₀
  have hC : 0≤C := Finset.prod_nonneg (fun i _ => hf i x₀)
  have hc (x : E) : (∏ i∈selectedᶜ,f i x)=C := by
    apply Finset.prod_congr rfl
    intro i hi
    exact hconstant i (by simpa using hi) x x₀
  have hp (x : E) : (∏ i,f i x)=(∏ i∈selected,f i x)*C := by
    rw [← Finset.prod_mul_prod_compl selected (fun i=>f i x),hc]
  have hn : (∏ i∈selectedᶜ,cubicNorm P (f i))=C := by
    apply Finset.prod_congr rfl
    intro i hi
    have hi' : i∉selected := by simpa using hi
    have he : f i=(fun _=>f i x₀) := funext (fun x=>hconstant i hi' x x₀)
    rw [he,cubicNorm_const P _ (hf i x₀)]
  simp_rw [hp]
  rw [MatrixRefresh.expect_mul_const P,← Finset.prod_mul_prod_compl selected
    (fun i=>cubicNorm P (f i)),hn]
  exact mul_le_mul_of_nonneg_right (expect_small_product_le P selected hcard f hf) hC

variable [Fintype W] [DecidableEq W]

/-- Insert a selected wire value into an assignment of all remaining wires. -/
def completeWire (w : W) (a : E) (rest : {v : W // v≠w} → E) : W → E :=
  (Equiv.piSplitAt w (fun _=>E)).symm (a,rest)

/-- Completing an assignment gives the prescribed value at the selected wire. -/
@[simp] theorem completeWire_self (w : W) (a : E) (rest : {v : W // v≠w} → E) :
    completeWire w a rest w=a := by
  simp [completeWire,Equiv.piSplitAt]

/-- Completing an assignment leaves every other wire unchanged. -/
@[simp] theorem completeWire_other (w : W) (a : E) (rest : {v : W // v≠w} → E)
    (v : W) (hv : v≠w) : completeWire w a rest v=rest ⟨v,hv⟩ := by
  simp [completeWire,Equiv.piSplitAt,hv]

/-- Finite product expectations first average the selected wire under its own distribution and then average the independent remaining wires. -/
theorem expect_completeWire (μ : W → FiniteDistribution E) (w : W) (f : (W → E) → ℝ) :
    (independentDistribution μ).expect f =
      (independentDistribution (fun v : {v : W // v≠w}=>μ v)).expect
        (fun rest=>(μ w).expect (fun a=>f (completeWire w a rest))) := by
  rw [independentDistribution_splitAt_reverse μ w,MatrixRefresh.expect_map,
    MatrixRefresh.expect_prod,MatrixRefresh.expect_comm]
  rfl

/-- The induction removes one independent wire and replaces its at most three incident factors by their conditional cubic norms. -/
private theorem scoped_holder_aux [Nonempty E] (N : ℕ) :
    ∀ (V : Type u) [Fintype V] [DecidableEq V], Fintype.card V=N →
      ∀ (μ : V → FiniteDistribution E) (scope : I → Finset V)
        (f : I → (V → E) → ℝ),
        (∀ i x,0≤f i x) → (∀ i,Scoped (scope i) (f i)) →
        (∀ v,(Finset.univ.filter (fun i=>v∈scope i)).card≤3) →
        (independentDistribution μ).expect (fun x=>∏ i,f i x) ≤
          ∏ i,cubicNorm (independentDistribution μ) (f i) := by
  classical
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro V _ _ hcard μ scope f hf hlocal hdegree
    by_cases hempty : Fintype.card V=0
    · letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hempty
      let x₀ : V → E := fun _=>Classical.choice inferInstance
      have hc (i : I) : f i=(fun _=>f i x₀) := by
        funext x
        exact congrArg (f i) (Subsingleton.elim x x₀)
      have hp : (fun x=>∏ i,f i x)=(fun _ : V → E=>∏ i,f i x₀) := by
        funext x
        apply Finset.prod_congr rfl
        intro i _
        exact congrArg (f i) (Subsingleton.elim x x₀)
      rw [hp,FiniteDistribution.expect_const]
      apply le_of_eq
      symm
      apply Finset.prod_congr rfl
      intro i _
      rw [hc i,cubicNorm_const _ _ (hf i x₀)]
    · have hpos : 0<Fintype.card V := Nat.pos_of_ne_zero hempty
      letI : Nonempty V := Fintype.card_pos_iff.mp hpos
      let w : V := Classical.choice inferInstance
      let V' := {v : V // v≠w}
      let μ' : V' → FiniteDistribution E := fun v=>μ v.val
      let scope' : I → Finset V' := fun i=>Finset.univ.filter (fun v=>v.val∈scope i)
      let g : I → (V' → E) → ℝ := fun i rest=>
        cubicNorm (μ w) (fun a=>f i (completeWire w a rest))
      have hless : Fintype.card V'<N := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (p:=fun v : V=>v≠w) (x:=w) (by simp)
      have hg (i : I) (rest : V' → E) : 0≤g i rest :=
        cubicNorm_nonneg _ _ (fun a=>hf i _)
      have hglocal (i : I) : Scoped (scope' i) (g i) := by
        intro first second heq
        apply congrArg (cubicNorm (μ w))
        funext a
        apply hlocal i
        intro v hv
        by_cases hvw : v=w
        · subst v
          simp
        · rw [completeWire_other w a first v hvw,completeWire_other w a second v hvw]
          exact heq ⟨v,hvw⟩ (by simpa [scope'] using hv)
      have hgdegree (v : V') : (Finset.univ.filter (fun i=>v∈scope' i)).card≤3 := by
        simpa [scope'] using hdegree v.val
      have hmoment (i : I) :
          (independentDistribution μ').expect (fun rest=>g i rest^3)=
            (independentDistribution μ).expect (fun x=>f i x^3) := by
        calc
          _ = (independentDistribution μ').expect
              (fun rest=>(μ w).expect (fun a=>f i (completeWire w a rest)^3)) := by
            congr 1
            funext rest
            exact cubicNorm_cube _ _ (fun a=>hf i _)
          _ = _ := (expect_completeWire μ w (fun x=>f i x^3)).symm
      have hstep (rest : V' → E) :
          (μ w).expect (fun a=>∏ i,f i (completeWire w a rest)) ≤ ∏ i,g i rest := by
        apply expect_product_le_of_constant (μ w)
          (Finset.univ.filter (fun i=>w∈scope i)) (hdegree w)
          (fun i a=>f i (completeWire w a rest)) (fun i a=>hf i _)
        intro i hi a b
        have hi' : w∉scope i := by simpa using hi
        apply hlocal i
        intro v hv
        have hvw : v≠w := by intro h;subst v;exact hi' hv
        rw [completeWire_other w a rest v hvw,completeWire_other w b rest v hvw]
      calc
        _ = (independentDistribution μ').expect
            (fun rest=>(μ w).expect (fun a=>∏ i,f i (completeWire w a rest))) :=
              expect_completeWire μ w _
        _ ≤ (independentDistribution μ').expect (fun rest=>∏ i,g i rest) :=
          (independentDistribution μ').expect_mono hstep
        _ ≤ ∏ i,cubicNorm (independentDistribution μ') (g i) :=
          ih (Fintype.card V') hless V' rfl μ' scope' g hg hglocal hgdegree
        _ = _ := by
          apply Finset.prod_congr rfl
          intro i _
          unfold cubicNorm
          rw [hmoment i]

/-- Finite Finner–Hölder: independent wire variables and incidence at most three bound a product of nonnegative local factors by the product of their cubic norms. -/
theorem scoped_product_le_cubicNorm [Nonempty E]
    (μ : W → FiniteDistribution E) (scope : I → Finset W)
    (f : I → (W → E) → ℝ) (hf : ∀ i x,0≤f i x)
    (hlocal : ∀ i,Scoped (scope i) (f i))
    (hdegree : ∀ w,(Finset.univ.filter (fun i=>w∈scope i)).card≤3) :
    (independentDistribution μ).expect (fun x=>∏ i,f i x) ≤
      ∏ i,cubicNorm (independentDistribution μ) (f i) := by
  exact scoped_holder_aux (Fintype.card W) W rfl μ scope f hf hlocal hdegree

/-- If every local third moment is at most ε³, the joint product costs at most one factor ε per marked operation. -/
theorem scoped_product_le_pow [Nonempty E]
    (μ : W → FiniteDistribution E) (scope : I → Finset W)
    (f : I → (W → E) → ℝ) (hf : ∀ i x,0≤f i x)
    (hlocal : ∀ i,Scoped (scope i) (f i))
    (hdegree : ∀ w,(Finset.univ.filter (fun i=>w∈scope i)).card≤3)
    (ε : ℝ) (hε : 0≤ε)
    (hmoment : ∀ i,(independentDistribution μ).expect (fun x=>f i x^3)≤ε^3) :
    (independentDistribution μ).expect (fun x=>∏ i,f i x) ≤ ε^(Fintype.card I) := by
  calc
    _ ≤ ∏ i,cubicNorm (independentDistribution μ) (f i) :=
      scoped_product_le_cubicNorm μ scope f hf hlocal hdegree
    _ ≤ ∏ _i : I,ε := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact cubicNorm_nonneg _ _ (hf i)
      · intro i _
        apply le_of_pow_le_pow_left₀ (by decide : 3≠0) hε
        rw [cubicNorm_cube _ _ (hf i)]
        exact hmoment i
    _ = _ := by simp

end CompilerProof.DirectComposition
