import Proofs.Compiler.GateApproximation.MatrixPhase.ResidualExpansion



/-!
# Zero extension preserves entry bounds and decreases energy and four-cycle
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

open scoped BigOperators Classical

namespace CircuitCompiler.RefreshAnalysis

open Refresh MatrixRefresh TableAnalysis

noncomputable section

variable {F X Y : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] {m : ℕ}

/- Mathematical definition (normal notation): The inclusion X × (𝔽ᵐ ∖ {0})↪ X × 𝔽ᵐ forgets the proof that the second coordinate is nonzero and preserves both coordinates. It is injective. -/
def featureCarrierEmbedding (X : Type*) (F : Type*) [Zero F] (m : ℕ) :
    (X × U F m) ↪ (X × V F m) where
  toFun x := (x.1,x.2.val)
  inj' := by
    intro x y h
    apply Prod.ext
    · exact congrArg (fun z : X × V F m => z.1) h
    · exact Subtype.ext (congrArg (fun z : X × V F m => z.2) h)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ; B ∈ ℝ; x ∈ X × V(F, m); y ∈ Y × V(F, m), assume 0 ≤ B; ∀ x, y, |E(x, y)| ≤ B. Then

|fullFeatureTable(E, x, y)| ≤ B.
-/
theorem fullFeatureTable_entry (E : (X × U F m) → (Y × U F m) → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hE : ∀ x y, |E x y| ≤ B)
    (x : X × V F m) (y : Y × V F m) : |fullFeatureTable E x y| ≤ B := by
  unfold fullFeatureTable featureZeroExtend
  split_ifs
  · exact hE _ _
  · simpa using hB

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A,B a set; e ∈ A ↪ B, assume A is finite; B is finite; B ≠ ∅. Then

|A| / |B| ≤ 1.
-/
private theorem embedding_ratio_le_one {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty B] (e : A ↪ B) : (Fintype.card A : ℝ) / Fintype.card B ≤ 1 := by
  apply (div_le_one (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card B)).2
  exact_mod_cast Fintype.card_le_of_injective e e.injective

section Nonempty

variable [Nonempty (U F m)]

/-- Only the uniform normalization changes: all added table entries are zero. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ, we have

𝔼_(p ∈ (X × V(F, m)) × (Y × V(F, m))) [(fullFeatureTable(E, (p)₁, (p)₂))²] ≤ 𝔼_(p ∈ (X × U(F, m)) × (Y × U(F, m))) [(E((p)₁, (p)₂))²].
-/
theorem fullFeatureTable_energy_le (E : (X × U F m) → (Y × U F m) → ℝ) :
    uavg (fun p : (X × V F m) × (Y × V F m) => fullFeatureTable E p.1 p.2 ^ 2) ≤
      uavg (fun p : (X × U F m) × (Y × U F m) => E p.1 p.2 ^ 2) := by
  let e := (featureCarrierEmbedding X F m).prodMap (featureCarrierEmbedding Y F m)
  have hs (p : (X × V F m) × (Y × V F m)) (hp : p ∉ Set.range e) :
      fullFeatureTable E p.1 p.2 ^ 2 = 0 := by
    have hn : ¬(p.1.2 ≠ 0 ∧ p.2.2 ≠ 0) := by
      intro h
      exact hp ⟨((p.1.1,⟨p.1.2,h.1⟩),(p.2.1,⟨p.2.2,h.2⟩)),rfl⟩
    simp [fullFeatureTable, featureZeroExtend, hn]
  rw [uavg_eq_card_ratio_of_embedding e _ hs]
  have he (p : (X × U F m) × (Y × U F m)) :
      fullFeatureTable E (e p).1 (e p).2 ^ 2 = E p.1 p.2 ^ 2 := by
    exact congrArg (fun t : ℝ => t ^ 2) (featureZeroExtend_nonzero E p.1.1 p.1.2 p.2.1 p.2.2)
  simp_rw [he]
  exact mul_le_of_le_one_left (uavg_nonneg (fun _ => sq_nonneg _)) (embedding_ratio_le_one e)

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ, we have

𝔼_(p ∈ (X × V(F, m)) × (Y × V(F, m))) [(fullFeatureTable(E, (p)₁, (p)₂))²] ≤ 𝔼ₓ [𝔼_y [(E(x, y))²]].
-/
theorem fullFeatureTable_energy_le_nested (E : (X × U F m) → (Y × U F m) → ℝ) :
    uavg (fun p : (X × V F m) × (Y × V F m) => fullFeatureTable E p.1 p.2 ^ 2) ≤
      uavg (fun x => uavg (fun y => E x y ^ 2)) := by
  simpa only [uavg_prod] using fullFeatureTable_energy_le E

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ, we have

fourCycle(fullFeatureTable(E)) ≤ fourCycle(E).
-/
theorem fullFeatureTable_fourCycle_le (E : (X × U F m) → (Y × U F m) → ℝ) :
    fourCycle (fullFeatureTable E) ≤ fourCycle E := by
  let eL := featureCarrierEmbedding X F m
  let eR := featureCarrierEmbedding Y F m
  let e := (eL.prodMap eL).prodMap (eR.prodMap eR)
  have hs (p : ((X × V F m) × (X × V F m)) × ((Y × V F m) × (Y × V F m)))
      (hp : p ∉ Set.range e) : cornerProduct (fullFeatureTable E) p = 0 := by
    have hn : ¬(p.1.1.2 ≠ 0 ∧ p.1.2.2 ≠ 0 ∧ p.2.1.2 ≠ 0 ∧ p.2.2.2 ≠ 0) := by
      intro h
      exact hp ⟨(((p.1.1.1,⟨p.1.1.2,h.1⟩),(p.1.2.1,⟨p.1.2.2,h.2.1⟩)),
        ((p.2.1.1,⟨p.2.1.2,h.2.2.1⟩),(p.2.2.1,⟨p.2.2.2,h.2.2.2⟩))),rfl⟩
    have hz : p.1.1.2 = 0 ∨ p.1.2.2 = 0 ∨ p.2.1.2 = 0 ∨ p.2.2.2 = 0 := by
      simpa only [not_and_or, not_not] using hn
    rcases hz with h | h | h | h <;>
      simp [cornerProduct, fullFeatureTable, featureZeroExtend, h]
  have he (p : ((X × U F m) × (X × U F m)) × ((Y × U F m) × (Y × U F m))) :
      cornerProduct (fullFeatureTable E) (e p) = cornerProduct E p := by
    simp only [cornerProduct, fullFeatureTable, e, eL, eR, Function.Embedding.prodMap,
      Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, featureCarrierEmbedding,
      featureZeroExtend_nonzero]
  have h := uavg_eq_card_ratio_of_embedding e (cornerProduct (fullFeatureTable E)) hs
  simp_rw [he] at h
  have hc (K : (X × U F m) → (Y × U F m) → ℝ) : uavg (cornerProduct K) = fourCycle K := by
    simp only [cornerProduct, uavg_prod, fourCycle_expansion]
  have hc' : uavg (cornerProduct (fullFeatureTable E)) = fourCycle (fullFeatureTable E) := by
    simp only [cornerProduct, uavg_prod, fourCycle_expansion]
  rw [hc', hc] at h
  rw [h]
  exact mul_le_of_le_one_left (fourCycle_nonneg E) (embedding_ratio_le_one e)

end Nonempty

end

end CircuitCompiler.RefreshAnalysis
