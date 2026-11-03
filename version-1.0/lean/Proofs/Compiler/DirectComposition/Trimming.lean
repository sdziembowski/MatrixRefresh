import Proofs.Compiler.DirectComposition.Model

/-!
# Separate energy trimming and the third moment

The available local approximation controls a second moment on valid encoding tuples. Separate left and right masks keep the chosen factor energies below B. The masked table is bounded by B, while the two discarded marginal tails have total probability at most 16/B for the formal mean-energy bound eight. This proves the third-moment estimate needed by incidence-three Hölder.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical

namespace CompilerProof.DirectComposition

open Refresh MatrixRefresh CircuitCompiler.AveragedEnergyComparison

variable {X Y : Type*} {g : X → Y → ℝ}

/-- Keep a signed table precisely when both of its chosen factor energies are at most B. The two tests depend on their own party's coordinates separately. -/
def trim (a : Factors g) (B : ℝ) (x : X) (y : Y) : ℝ :=
  if a.leftEnergy x ≤ B ∧ a.rightEnergy y ≤ B then g x y else 0

/-- Masking the left and right factor families separately reconstructs the trimmed table without changing its rank. -/
def trimFactors (a : Factors g) (B : ℝ) : Factors (trim a B) where
  rank := a.rank
  left x j := if a.leftEnergy x ≤ B then a.left x j else 0
  right y j := if a.rightEnergy y ≤ B then a.right y j else 0
  reconstruct x y := by
    by_cases hl : a.leftEnergy x ≤ B <;> by_cases hr : a.rightEnergy y ≤ B
    all_goals simp [trim,hl,hr,a.reconstruct]

/-- Each retained left energy is at most B; a discarded row has energy zero. -/
theorem trimFactors_leftEnergy (a : Factors g) (B : ℝ) (hB : 0 ≤ B) (x : X) :
    (trimFactors a B).leftEnergy x ≤ B := by
  change (∑ j, (if a.leftEnergy x ≤ B then a.left x j else 0)^2) ≤ B
  by_cases h : a.leftEnergy x ≤ B
  · simp only [if_pos h]
    simpa only [Factors.leftEnergy] using h
  · simpa only [if_neg h,zero_pow (by decide : 2≠0),Finset.sum_const_zero] using hB

/-- Each retained right energy is at most B; a discarded column has energy zero. -/
theorem trimFactors_rightEnergy (a : Factors g) (B : ℝ) (hB : 0 ≤ B) (y : Y) :
    (trimFactors a B).rightEnergy y ≤ B := by
  change (∑ j, (if a.rightEnergy y ≤ B then a.right y j else 0)^2) ≤ B
  by_cases h : a.rightEnergy y ≤ B
  · simp only [if_pos h]
    simpa only [Factors.rightEnergy] using h
  · simpa only [if_neg h,zero_pow (by decide : 2≠0),Finset.sum_const_zero] using hB

/-- Separate energy bounds make every trimmed table entry at most B in absolute value. -/
theorem trim_abs_le (a : Factors g) (B : ℝ) (hB : 0 ≤ B) (x : X) (y : Y) :
    |trim a B x y| ≤ B := by
  exact (trimFactors a B).abs_le_of_energy B hB
    (trimFactors_leftEnergy a B hB) (trimFactors_rightEnergy a B hB) x y

/-- The discarded-set indicator is bounded by the sum of the two energies divided by B, pointwise. This is the separate Markov estimate and does not assume the two shares are independent. -/
theorem bad_le_energies (a : Factors g) (B : ℝ) (hB : 0 < B) (x : X) (y : Y) :
    (if a.leftEnergy x ≤ B ∧ a.rightEnergy y ≤ B then (0:ℝ) else 1) ≤
      a.leftEnergy x / B + a.rightEnergy y / B := by
  by_cases hl : a.leftEnergy x ≤ B <;> by_cases hr : a.rightEnergy y ≤ B
  · simp only [hl,hr,and_self,if_true]
    exact add_nonneg (div_nonneg (a.leftEnergy_nonneg x) hB.le)
      (div_nonneg (a.rightEnergy_nonneg y) hB.le)
  · simp only [hl,hr,and_false,if_false]
    have h : 1 ≤ a.rightEnergy y / B :=
      (le_div_iff₀ hB).2 (by linarith)
    have h0 : 0 ≤ a.leftEnergy x / B := div_nonneg (a.leftEnergy_nonneg x) hB.le
    linarith
  · simp only [hl,hr,false_and,if_false]
    have h : 1 ≤ a.leftEnergy x / B :=
      (le_div_iff₀ hB).2 (by linarith)
    have h0 : 0 ≤ a.rightEnergy y / B := div_nonneg (a.rightEnergy_nonneg y) hB.le
    linarith
  · simp only [hl,hr,false_and,if_false]
    have h : 1 ≤ a.leftEnergy x / B :=
      (le_div_iff₀ hB).2 (by linarith)
    have h0 : 0 ≤ a.rightEnergy y / B := div_nonneg (a.rightEnergy_nonneg y) hB.le
    linarith

/-- Pointwise cubic error is bounded by a bounded multiple of the original squared error plus the discarded-set indicator. -/
theorem trim_error_cube_pointwise (a : Factors g) (B : ℝ) (hB : 0 ≤ B)
    (p : X → Y → ℝ) (hp0 : ∀ x y, 0 ≤ p x y) (hp1 : ∀ x y, p x y ≤ 1)
    (x : X) (y : Y) :
    |p x y-trim a B x y|^3 ≤ (1+B)*(p x y-g x y)^2 +
      (if a.leftEnergy x ≤ B ∧ a.rightEnergy y ≤ B then (0:ℝ) else 1) := by
  by_cases h : a.leftEnergy x ≤ B ∧ a.rightEnergy y ≤ B
  · have habs : |p x y-g x y| ≤ 1+B := by
      calc
        _ ≤ |p x y|+|g x y| := abs_sub _ _
        _ ≤ 1+B := by
          rw [abs_of_nonneg (hp0 x y)]
          have hg := trim_abs_le a B hB x y
          rw [trim,if_pos h] at hg
          linarith [hp1 x y]
    simp only [trim,if_pos h,add_zero]
    calc
      _ = |p x y-g x y|^2*|p x y-g x y| := by ring
      _ ≤ |p x y-g x y|^2*(1+B) :=
        mul_le_mul_of_nonneg_left habs (sq_nonneg _)
      _ = _ := by rw [sq_abs]; ring
  · simp only [trim,if_neg h,sub_zero,abs_of_nonneg (hp0 x y)]
    have hp2 : p x y ^ 2 ≤ 1 := by nlinarith [hp0 x y,hp1 x y]
    have hp3 : p x y ^ 3 ≤ 1 := by
      calc
        _ = p x y ^ 2 * p x y := by ring
        _ ≤ 1*1 := mul_le_mul hp2 (hp1 x y) (hp0 x y) (by norm_num)
        _ = 1 := by ring
    have hx : 0 ≤ (1+B)*(p x y-g x y)^2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith

variable [Fintype X] [Fintype Y]

/-- L2-to-L3 conversion in third-moment form. With mean energies at most M, the discarded tails cost at most 2M/B; the error is evaluated under the original valid-label distribution P throughout. -/
theorem trim_error_cube (a : Factors g) (B M ε : ℝ) (hB : 0 < B)
    (P : FiniteDistribution (X × Y)) (p : X → Y → ℝ)
    (hp0 : ∀ x y, 0 ≤ p x y) (hp1 : ∀ x y, p x y ≤ 1)
    (hleft : P.expect (fun xy => a.leftEnergy xy.1) ≤ M)
    (hright : P.expect (fun xy => a.rightEnergy xy.2) ≤ M)
    (herror : rms P (fun xy => p xy.1 xy.2-g xy.1 xy.2) ≤ ε) :
    P.expect (fun xy => |p xy.1 xy.2-trim a B xy.1 xy.2|^3) ≤
      (1+B)*ε^2+2*M/B := by
  have hε : 0 ≤ ε := (rms_nonneg _ _).trans herror
  have hsquare : P.expect (fun xy => (p xy.1 xy.2-g xy.1 xy.2)^2) ≤ ε^2 := by
    rw [← rms_sq]
    exact (sq_le_sq₀ (rms_nonneg _ _) hε).2 herror
  have hbad : P.expect
      (fun xy => if a.leftEnergy xy.1 ≤ B ∧ a.rightEnergy xy.2 ≤ B then (0:ℝ) else 1)
      ≤ 2*M/B := by
    calc
      _ ≤ P.expect (fun xy => a.leftEnergy xy.1/B+a.rightEnergy xy.2/B) :=
        P.expect_mono (fun xy => bad_le_energies a B hB xy.1 xy.2)
      _ = (P.expect (fun xy => a.leftEnergy xy.1)+P.expect (fun xy => a.rightEnergy xy.2))/B := by
        simp [FiniteDistribution.expect,div_eq_mul_inv,Finset.sum_add_distrib,
          Finset.sum_mul,mul_add,mul_assoc,add_mul]
      _ ≤ 2*M/B := by gcongr <;> linarith
  calc
    _ ≤ P.expect (fun xy => (1+B)*(p xy.1 xy.2-g xy.1 xy.2)^2+
        (if a.leftEnergy xy.1 ≤ B ∧ a.rightEnergy xy.2 ≤ B then (0:ℝ) else 1)) :=
      P.expect_mono (fun xy => trim_error_cube_pointwise a B hB.le p hp0 hp1 xy.1 xy.2)
    _ = (1+B)*P.expect (fun xy => (p xy.1 xy.2-g xy.1 xy.2)^2)+
        P.expect (fun xy => if a.leftEnergy xy.1 ≤ B ∧ a.rightEnergy xy.2 ≤ B then (0:ℝ) else 1) := by
      rw [expect_add,expect_smul]
    _ ≤ (1+B)*ε^2+2*M/B := by gcongr

variable {W A F : Type*} [Fintype W] [DecidableEq W] [Fintype A]
  [Nonempty X] {S : ℕ} {scope : Fin S → Finset W}
  {network : CircuitCompiler.AveragedEnergyComparison.ScopedProbabilities
    (E := X × X) (A := A) scope}
  {law : F → FiniteDistribution (X × X)} {valid : (W → F) → Fin S → Prop}
  {approximated : Finset (Fin S)} {β ε : ℝ}

namespace LocalData

/-- The approximation at one answer, read on complete encodings solely to avoid repeated port-restriction maps. -/
def table (data : LocalData scope network law valid approximated β ε)
    (i : Fin S) (h : List A) (z : A) (encoding : W → X × X) : ℝ :=
  (data.gate i h z).approximation (fun w => (encoding w).1) (fun w => (encoding w).2)

/-- The chosen left energy is a function only of the operation's scope. -/
theorem leftEnergy_scoped (data : LocalData scope network law valid approximated β ε)
    (i : Fin S) (h : List A) (z : A) :
    CircuitCompiler.Composition.Scoped (scope i) (fun encoding : W → X × X =>
      (data.gate i h z).factors.leftEnergy (fun w => (encoding w).1)) := by
  intro first second heq
  apply Finset.sum_congr rfl
  intro j _
  have hj := data.left_locality i h z j first second heq
  dsimp only at hj
  rw [hj]

/-- The chosen right energy is a function only of the operation's scope. -/
theorem rightEnergy_scoped (data : LocalData scope network law valid approximated β ε)
    (i : Fin S) (h : List A) (z : A) :
    CircuitCompiler.Composition.Scoped (scope i) (fun encoding : W → X × X =>
      (data.gate i h z).factors.rightEnergy (fun w => (encoding w).2)) := by
  intro first second heq
  apply Finset.sum_congr rfl
  intro j _
  have hj := data.right_locality i h z j first second heq
  dsimp only at hj
  rw [hj]

/-- Reconstructing the chosen local factors proves locality of the signed table. -/
theorem table_scoped (data : LocalData scope network law valid approximated β ε)
    (i : Fin S) (h : List A) (z : A) :
    CircuitCompiler.Composition.Scoped (scope i) (data.table i h z) := by
  intro first second heq
  unfold table
  rw [(data.gate i h z).factors.reconstruct,(data.gate i h z).factors.reconstruct]
  apply Finset.sum_congr rfl
  intro j _
  have hl := data.left_locality i h z j first second heq
  have hr := data.right_locality i h z j first second heq
  dsimp only at hl hr
  rw [hl,hr]

/-- The separately trimmed answer table retains the original scope. -/
def trimmed (data : LocalData scope network law valid approximated β ε)
    (B : ℝ) (i : Fin S) (h : List A) (z : A) (encoding : W → X × X) : ℝ :=
  trim (data.gate i h z).factors B
    (fun w => (encoding w).1) (fun w => (encoding w).2)

/-- Both trim decisions and the surviving signed value are local to the operation. -/
theorem trimmed_scoped (data : LocalData scope network law valid approximated β ε)
    (B : ℝ) (i : Fin S) (h : List A) (z : A) :
    CircuitCompiler.Composition.Scoped (scope i) (data.trimmed B i h z) := by
  intro first second heq
  unfold trimmed trim
  have hl := data.leftEnergy_scoped i h z first second heq
  have hr := data.rightEnergy_scoped i h z first second heq
  dsimp only at hl hr
  rw [hl,hr]
  have htable := data.table_scoped i h z first second heq
  exact if_ctx_congr Iff.rfl (fun _ => htable) (fun _ => rfl)

/-- A local error is the true probability minus the separately trimmed approximation. -/
def error (data : LocalData scope network law valid approximated β ε)
    (B : ℝ) (i : Fin S) (h : List A) (z : A) (encoding : W → X × X) : ℝ :=
  network.prob i h encoding z-data.trimmed B i h z encoding

/-- Each error depends on its entire original scope and on no other wire. -/
theorem error_scoped (data : LocalData scope network law valid approximated β ε)
    (B : ℝ) (i : Fin S) (h : List A) (z : A) :
    CircuitCompiler.Composition.Scoped (scope i) (data.error B i h z) := by
  intro first second heq
  unfold error
  have hp := network.locality i h z first second heq
  dsimp only at hp
  rw [hp,data.trimmed_scoped B i h z first second heq]

/-- Uniform one-wire left and right marginals transfer the separate mean-energy bounds to the unconditional grouped encoding law. -/
theorem energy_means (data : LocalData scope network law valid approximated β ε)
    (hleft : ∀ s,(law s).map Prod.fst=FiniteDistribution.uniform)
    (hright : ∀ s,(law s).map Prod.snd=FiniteDistribution.uniform)
    (label : W→F) (i : Fin S) (h : List A) (z : A) :
    (groupedLaw law label).expect (fun xy=>(data.gate i h z).factors.leftEnergy xy.1)≤8 ∧
    (groupedLaw law label).expect (fun xy=>(data.gate i h z).factors.rightEnergy xy.2)≤8 := by
  have hl := CircuitCompiler.Composition.groupedDistribution_left_marginal
    (fun w=>law (label w)) Prod.fst Prod.snd (fun w=>hleft (label w))
  have hr := CircuitCompiler.Composition.groupedDistribution_right_marginal
    (fun w=>law (label w)) Prod.fst Prod.snd (fun w=>hright (label w))
  change (groupedLaw law label).map Prod.fst=FiniteDistribution.uniform at hl
  change (groupedLaw law label).map Prod.snd=FiniteDistribution.uniform at hr
  constructor
  · rw [← expect_map,hl]
    exact (data.gate i h z).left_mean
  · rw [← expect_map,hr]
    exact (data.gate i h z).right_mean

/-- Trimming upgrades the local valid-label RMS estimate to a third-moment estimate under independently sampled actual encodings. -/
theorem trimmed_error_cube (data : LocalData scope network law valid approximated β ε)
    (hε : 0≤ε) (hleft : ∀ s,(law s).map Prod.fst=FiniteDistribution.uniform)
    (hright : ∀ s,(law s).map Prod.snd=FiniteDistribution.uniform)
    (label : W→F) (i : Fin S) (hi : valid label i ∧ i∈approximated)
    (h : List A) (z : A) (B : ℝ) (hB : 0<B) :
    (CircuitCompiler.Composition.independentDistribution (fun w=>law (label w))).expect
      (fun encoding=>|data.error B i h z encoding|^3)≤(1+B)*ε^2+16/B := by
  obtain ⟨hl,hr⟩ := data.energy_means hleft hright label i h z
  have hbound := trim_error_cube (data.gate i h z).factors B 8 ε hB
    (groupedLaw law label) (fun left right=>network.prob i h (fun w=>(left w,right w)) z)
    (fun left right=>network.nonneg i h _ z)
    (fun left right=>(Finset.single_le_sum (fun a _=>network.nonneg i h _ a)
      (Finset.mem_univ z)).trans (network.total_le i h _))
    hl hr ((data.gate i h z).valid_error_rms label hi)
  simp only [groupedLaw,CircuitCompiler.Composition.groupedDistribution,expect_map,
    Prod.eta] at hbound
  norm_num only [show (2:ℝ)*8=16 by norm_num] at hbound
  exact hbound

end LocalData

end CompilerProof.DirectComposition
