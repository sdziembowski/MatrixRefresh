import Proofs.Compiler.GateApproximation.MatrixPhase.JointOrbitCounting



/-!
# Compatible linear completions with arbitrarily many prescribed columns

Extending the prescribed independent columns to a basis leaves independent choices in affine fibers of two row equations. This includes the three-column count needed to exclude singular completions by a finite union bound.
-/
set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators Classical

namespace CircuitCompiler

open Refresh MatrixRefresh Module

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Linear maps with two prescribed row actions and a specified finite family of column images. -/
/-
Mathematical definition (normal notation): For m, k ∈ ℕ; l, lout ∈ {0,…,2-1} → V(F, m); v, w ∈ {0,…,k-1} → V(F, m), define

PartialCompletion(l, lout, v, w) := {f ∈ V(F, m) —linear over F→ V(F, m) | comp(dotMap(l))(f) = dotMap(lout) ∧ ∀ j, f(v(j)) = w(j)}.
-/
abbrev PartialCompletion {m k : ℕ} (l lout : Fin 2 → V F m)
    (v w : Fin k → V F m) :=
  {f : V F m →ₗ[F] V F m // (dotMap l).comp f = dotMap lout ∧ ∀ j, f (v j) = w j}

instance partialCompletionFintype {m k : ℕ} (l lout : Fin 2 → V F m)
    (v w : Fin k → V F m) : Fintype (PartialCompletion l lout v w) := by
  letI : Fintype (V F m →ₗ[F] V F m) := Fintype.ofInjective
    (fun f : V F m →ₗ[F] V F m => (f : V F m → V F m)) DFunLike.coe_injective
  infer_instance

/-- The unprescribed basis vectors have independent images in their required affine row-pairing fibers. -/
/- Mathematical definition (normal notation): Let a basis consist of prescribed vectors vⱼ and remaining vectors bⱼ. Assume the prescribed images wⱼ satisfy all required row-pairing equations. A linear map with those images and row constraints is then determined uniquely by independent choices xⱼ for the remaining basis vectors, subject to ℓᵢ · xⱼ = ℓ'ᵢ · bⱼ for each row index i. The construction is a bijection between these two descriptions. -/
def partialCompletionEquiv {m k : ℕ} {J : Type*}
    (l lout : Fin 2 → V F m) (v w : Fin k → V F m)
    (b : Basis (Fin k ⊕ J) F (V F m)) (hb : ∀ j, b (Sum.inl j) = v j)
    (hc : ∀ i j, dot (l i) (w j) = dot (lout i) (v j)) :
    PartialCompletion l lout v w ≃
      ((j : J) → {x : V F m // dotMap l x = dotMap lout (b (Sum.inr j))}) where
  toFun f j := ⟨f.val (b (Sum.inr j)), DFunLike.congr_fun f.property.1 _⟩
  invFun g := ⟨b.constr F (Sum.elim w (fun j => (g j).val)), by
    constructor
    · apply b.ext
      intro j
      cases j with
      | inl j =>
        ext i
        simp only [LinearMap.comp_apply, Basis.constr_basis, Sum.elim_inl, dotMap_apply]
        rw [hb]
        exact hc i j
      | inr j =>
        simpa only [LinearMap.comp_apply, Basis.constr_basis, Sum.elim_inr] using (g j).property
    · intro j
      rw [← hb j, Basis.constr_basis]
      rfl⟩
  left_inv f := by
    apply Subtype.ext
    apply b.ext
    intro j
    cases j with
    | inl j =>
      simp only [Basis.constr_basis, Sum.elim_inl]
      rw [hb]
      exact (f.property.2 j).symm
    | inr j => simp only [Basis.constr_basis, Sum.elim_inr]
  right_inv g := by
    funext j
    apply Subtype.ext
    simp only [Basis.constr_basis, Sum.elim_inr]

/-- Exact number of simultaneous completions of two independent row forms and `k` independent prescribed column images. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m, k ∈ ℕ; l, lout ∈ {0,…,2-1} → V(F, m); v, w ∈ {0,…,k-1} → V(F, m), assume 2 ≤ m; LinearIndependent(F, l); LinearIndependent(F, v); ∀ i, j, (l(i) · w(j)) = (lout(i) · v(j)). Then

|PartialCompletion(l, lout, v, w)| = (|F|)^((m − 2) · (m − k)).
-/
theorem partialCompletion_card {m k : ℕ} (hm : 2 ≤ m)
    (l lout : Fin 2 → V F m) (v w : Fin k → V F m)
    (hl : LinearIndependent F l) (hv : LinearIndependent F v)
    (hc : ∀ i j, dot (l i) (w j) = dot (lout i) (v j)) :
    Fintype.card (PartialCompletion l lout v w) = fieldCard F ^ ((m - 2) * (m - k)) := by
  let b := Basis.sumExtend hv
  letI : Fintype (Basis.sumExtendIndex hv) := Fintype.ofFinite _
  have hb (j : Fin k) : b (Sum.inl j) = v j := by simp [b, Basis.sumExtend]; rfl
  have hJ : Fintype.card (Basis.sumExtendIndex hv) = m - k := by
    have hd := Module.finrank_eq_card_basis b
    simp only [Module.finrank_pi, Fintype.card_fin, Fintype.card_sum] at hd
    omega
  rw [Fintype.card_congr (partialCompletionEquiv l lout v w b hb hc), Fintype.card_pi]
  simp_rw [card_dotMap_fiber hm l hl]
  simp only [Finset.prod_const, Finset.card_univ, hJ, ← pow_mul]

/-- Prescribing an additional kernel vector is precisely one more prescribed column, with output zero. -/
/- Mathematical definition (normal notation): Prescribing that a compatible linear completion sends an additional vector x to zero is equivalent to appending x to the prescribed input-column list and zero to its prescribed output list. The underlying linear map is unchanged. -/
def kernelCompletionEquiv {m : ℕ} (l rho lout rout : Fin 2 → V F m) (x : V F m) :
    {f : LinearCompletion l rho lout rout // f.val x = 0} ≃
      PartialCompletion l lout (Fin.snoc rho x) (Fin.snoc rout 0) where
  toFun f := ⟨f.val.val, f.val.property.1, by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa [Fin.snoc, Fin.lastCases] using f.property
    · simpa using f.val.property.2 i⟩
  invFun f := ⟨⟨f.val, f.property.1, fun i => by simpa using f.property.2 i.castSucc⟩,
    by simpa [Fin.snoc, Fin.lastCases] using f.property.2 (Fin.last 2)⟩
  left_inv f := rfl
  right_inv f := rfl

/-- A third independent prescribed input column removes exactly `m-2` degrees of freedom from the completion space. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; l, rho, lout, rout ∈ {0,…,2-1} → V(F, m); x ∈ V(F, m), assume 2 ≤ m; LinearIndependent(F, l); LinearIndependent(F, rho); ExtensionCompatible(l, rho, lout, rout); x ∉ Submodule.span(F, Set.range(rho)); dotMap(lout, x) = 0. Then

|{f ∈ LinearCompletion(l, rho, lout, rout) | f(x) = 0}| = (|F|)^((m − 2) · (m − 3)).
-/
theorem kernelCompletion_card {m : ℕ} (hm : 2 ≤ m)
    (l rho lout rout : Fin 2 → V F m)
    (hl : LinearIndependent F l) (hrho : LinearIndependent F rho)
    (hc : ExtensionCompatible l rho lout rout) (x : V F m)
    (hx : x ∉ Submodule.span F (Set.range rho)) (hx0 : dotMap lout x = 0) :
    Fintype.card {f : LinearCompletion l rho lout rout // f.val x = 0} =
      fieldCard F ^ ((m - 2) * (m - 3)) := by
  rw [Fintype.card_congr (kernelCompletionEquiv l rho lout rout x)]
  apply partialCompletion_card hm l lout _ _ hl (linearIndependent_fin_snoc.2 ⟨hrho, hx⟩)
  intro i j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · have hi := congrFun hx0 i
    change dot (l i) ((Fin.snoc rout (0 : V F m) : Fin 3 → V F m) (Fin.last 2)) =
      dot (lout i) ((Fin.snoc rho x : Fin 3 → V F m) (Fin.last 2))
    rw [Fin.snoc_last, Fin.snoc_last]
    simpa [dot] using hi.symm
  · simpa using hc i k

/-- Independent prescribed column images rule out a nonzero kernel vector in the span of the prescribed input columns. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; l, rho, lout, rout ∈ {0,…,2-1} → V(F, m); f ∈ LinearCompletion(l, rho, lout, rout); x ∈ V(F, m), assume LinearIndependent(F, rout); x ≠ 0; f(x) = 0. Then

x ∉ Submodule.span(F, Set.range(rho)).
-/
theorem completion_kernel_not_mem_span {m : ℕ}
    (l rho lout rout : Fin 2 → V F m) (hrout : LinearIndependent F rout)
    (f : LinearCompletion l rho lout rout) (x : V F m) (hx : x ≠ 0) (hfx : f.val x = 0) :
    x ∉ Submodule.span F (Set.range rho) := by
  have hcomp : f.val ∘ rho = rout := funext f.property.2
  have hi : LinearIndependent F (f.val ∘ rho) := hcomp.symm ▸ hrout
  have hd := Submodule.range_ker_disjoint hi
  intro hs
  exact hx (Submodule.disjoint_def.1 hd x hs hfx)

/-- Uniform upper count for completions with any given nonzero kernel vector. The count is zero when that vector lies in the prescribed span. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; l, rho, lout, rout ∈ {0,…,2-1} → V(F, m); x ∈ V(F, m), assume 2 ≤ m; LinearIndependent(F, l); LinearIndependent(F, rho); LinearIndependent(F, rout); ExtensionCompatible(l, rho, lout, rout); x ≠ 0; dotMap(lout, x) = 0. Then

|{f ∈ LinearCompletion(l, rho, lout, rout) | f(x) = 0}| ≤ (|F|)^((m − 2) · (m − 3)).
-/
theorem kernelCompletion_card_le {m : ℕ} (hm : 2 ≤ m)
    (l rho lout rout : Fin 2 → V F m)
    (hl : LinearIndependent F l) (hrho : LinearIndependent F rho)
    (hrout : LinearIndependent F rout) (hc : ExtensionCompatible l rho lout rout)
    (x : V F m) (hx : x ≠ 0) (hx0 : dotMap lout x = 0) :
    Fintype.card {f : LinearCompletion l rho lout rout // f.val x = 0} ≤
      fieldCard F ^ ((m - 2) * (m - 3)) := by
  by_cases hspan : x ∈ Submodule.span F (Set.range rho)
  · have hz : Fintype.card {f : LinearCompletion l rho lout rout // f.val x = 0} = 0 := by
      apply Fintype.card_eq_zero_iff.mpr
      exact ⟨fun f => completion_kernel_not_mem_span l rho lout rout hrout f.val x hx f.property hspan⟩
    rw [hz]
    exact Nat.zero_le _
  · exact (kernelCompletion_card hm l rho lout rout hl hrho hc x hspan hx0).le

/-- The zero fiber of the two row equations has precisely `q^(m-2)-1` nonzero members. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; l ∈ {0,…,2-1} → V(F, m), assume 2 ≤ m; LinearIndependent(F, l). Then

|{v ∈ PairingFiber(l, 0) | v ≠ 0}| = (|F|)^(m − 2) - 1.
-/
theorem pairingKernel_nonzero_card {m : ℕ} (hm : 2 ≤ m)
    (l : Fin 2 → V F m) (hl : LinearIndependent F l) :
    Fintype.card {v : PairingFiber l 0 // v.val ≠ 0} = fieldCard F ^ (m - 2) - 1 := by
  have hzero : Fintype.card {v : PairingFiber l 0 // v.val = 0} = 1 := by
    have hpos : 0 < Fintype.card {v : PairingFiber l 0 // v.val = 0} :=
      Fintype.card_pos_iff.mpr ⟨⟨⟨0, map_zero _⟩, rfl⟩⟩
    have hle := pairingFiber_zero_card_le l 0
    omega
  rw [Fintype.card_subtype_compl, card_dotMap_fiber hm l hl, hzero]

/-- Every noninjective completion has a nonzero kernel vector satisfying the two output row equations. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; l, rho, lout, rout ∈ {0,…,2-1} → V(F, m); f ∈ LinearCompletion(l, rho, lout, rout), assume ¬ (f is injective). Then

∃ x ∈ {v ∈ PairingFiber(lout, 0) | v ≠ 0}, f(x) = 0.
-/
theorem noninjective_completion_witness {m : ℕ}
    (l rho lout rout : Fin 2 → V F m) (f : LinearCompletion l rho lout rout)
    (hf : ¬ Function.Injective f.val) :
    ∃ x : {v : PairingFiber lout 0 // v.val ≠ 0}, f.val x.val.val = 0 := by
  simp only [Function.Injective, not_forall] at hf
  obtain ⟨a, b, hab, hne⟩ := hf
  have hz : f.val (a - b) = 0 := by simp [map_sub, hab]
  have hp : dotMap lout (a - b) = 0 := by
    rw [← f.property.1]
    simp [hz]
  exact ⟨⟨⟨a - b, hp⟩, sub_ne_zero.mpr hne⟩, hz⟩

/-- A finite union bound for singular compatible completions. Choosing one nonzero kernel vector embeds every bad completion into the incidence set. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; l, rho, lout, rout ∈ {0,…,2-1} → V(F, m), assume 2 ≤ m; LinearIndependent(F, l); LinearIndependent(F, rho); LinearIndependent(F, lout); LinearIndependent(F, rout); ExtensionCompatible(l, rho, lout, rout). Then

|{f ∈ LinearCompletion(l, rho, lout, rout) | ¬ (f is injective)}| ≤ ((|F|)^(m − 2) - 1) · (|F|)^((m − 2) · (m − 3)).
-/
theorem noninjective_completion_card_le {m : ℕ} (hm : 2 ≤ m)
    (l rho lout rout : Fin 2 → V F m)
    (hl : LinearIndependent F l) (hrho : LinearIndependent F rho)
    (hlout : LinearIndependent F lout) (hrout : LinearIndependent F rout)
    (hc : ExtensionCompatible l rho lout rout) :
    Fintype.card {f : LinearCompletion l rho lout rout // ¬ Function.Injective f.val} ≤
      (fieldCard F ^ (m - 2) - 1) * fieldCard F ^ ((m - 2) * (m - 3)) := by
  let e : {f : LinearCompletion l rho lout rout // ¬ Function.Injective f.val} →
      Σ x : {v : PairingFiber lout 0 // v.val ≠ 0},
        {f : LinearCompletion l rho lout rout // f.val x.val.val = 0} :=
    fun f => ⟨(noninjective_completion_witness l rho lout rout f.val f.property).choose,
      ⟨f.val, (noninjective_completion_witness l rho lout rout f.val f.property).choose_spec⟩⟩
  have hinj : Function.Injective e := by
    intro f g h
    apply Subtype.ext
    exact congrArg (fun p => p.2.val) h
  refine (Fintype.card_le_of_injective e hinj).trans ?_
  rw [Fintype.card_sigma, ← pairingKernel_nonzero_card hm lout hlout]
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using
    (Finset.sum_le_sum (s := Finset.univ)
      (fun (x : {v : PairingFiber lout 0 // v.val ≠ 0}) _ =>
        kernelCompletion_card_le hm l rho lout rout hl hrho hrout hc x.val.val x.property x.val.property))

/-- Simultaneously prescribed independent row and column images, satisfying the four compatibility equations, admit an injective completion. The proof uses the strict finite union bound on nonzero kernel vectors. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; l, rho, lout, rout ∈ {0,…,2-1} → V(F, m), assume 3 ≤ m; LinearIndependent(F, l); LinearIndependent(F, rho); LinearIndependent(F, lout); LinearIndependent(F, rout); ExtensionCompatible(l, rho, lout, rout). Then

∃ f ∈ LinearCompletion(l, rho, lout, rout), f is injective.
-/
theorem exists_injective_completion {m : ℕ} (hm : 3 ≤ m)
    (l rho lout rout : Fin 2 → V F m)
    (hl : LinearIndependent F l) (hrho : LinearIndependent F rho)
    (hlout : LinearIndependent F lout) (hrout : LinearIndependent F rout)
    (hc : ExtensionCompatible l rho lout rout) :
    ∃ f : LinearCompletion l rho lout rout, Function.Injective f.val := by
  have hcount := noninjective_completion_card_le (by omega) l rho lout rout hl hrho hlout hrout hc
  have htotal := card_linearCompletion_of_compatible (by omega) l rho lout rout hl hrho hc
  have hq : 0 < fieldCard F ^ (m - 2) := pow_pos (fieldCard_pos (F := F)) _
  have hsmall : 0 < fieldCard F ^ ((m - 2) * (m - 3)) := pow_pos (fieldCard_pos (F := F)) _
  have hexp : (m - 2) + (m - 2) * (m - 3) = (m - 2) ^ 2 := by
    have : m - 2 = m - 3 + 1 := by omega
    nlinarith
  have hlt : (fieldCard F ^ (m - 2) - 1) * fieldCard F ^ ((m - 2) * (m - 3)) <
      Fintype.card (LinearCompletion l rho lout rout) := by
    rw [htotal, ← hexp, pow_add]
    exact Nat.mul_lt_mul_of_pos_right (Nat.sub_lt hq (by omega)) hsmall
  have hproper := hcount.trans_lt hlt
  by_contra! hnone
  have hall : Fintype.card {f : LinearCompletion l rho lout rout // ¬ Function.Injective f.val} =
      Fintype.card (LinearCompletion l rho lout rout) := by
    apply Fintype.card_congr
    exact Equiv.subtypeUnivEquiv hnone
  omega

end

end CircuitCompiler
