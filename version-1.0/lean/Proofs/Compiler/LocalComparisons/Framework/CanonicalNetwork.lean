import Proofs.Compiler.LocalComparisons.Framework.Composition
import Proofs.Compiler.LocalComparisons.Framework.Labels



/-!
# Composition of local signed comparisons on a finite network

This module connects local validity and the label-path combinatorics to the signed-measure estimates. The elementary estimates are stated for actual finite signed weights, so they can be supplied by `ErrorProcess` forcing and one-wire comparison. No security conclusion is hidden in a new axiom.
-/

set_option autoImplicit false

namespace CircuitCompiler.Composition

open Refresh LabelPaths

variable {W G F V : Type*} [DecidableEq W] [Fintype G] [DecidableEq G] [Fintype V]

/-- Assemble the local valid-gate switches and one-wire comparisons along a label path. Only valid gates are switched; defective gates remain signed. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For scope ∈ G → Finset(W); valid ∈ (W → F) → G → Prop; boundary ∈ Finset(W); Q ∈ (W → F) → Finset(G) → V → ℝ; canonical, actual ∈ (W → F) → 𝒟(V); label ∈ ℕ → W → F; L, d, a ∈ ℕ; error, wire, truncation, coupling ∈ ℝ, assume IsLocal(scope, valid); 0 ≤ error; ∀ w, |incident(scope, w)| ≤ d; defects(valid, label(0)) = ∅; defects(valid, label(L)) = ∅; ∀ j, <, L, ∃ w, w ∉ boundary ∧ DiffersOnly(label(j), label((j + 1)), w) ∧ |(defects(valid, label(j)) ∪ defects(valid, label((j + 1))) ∪ incident(scope, w))| ≤ a; ∀ s, A, i, (i ∈ A) ⇒ valid(s, i) → (defects(valid, s) ⊆ A.erase(i)) ⇒ (|A| ≤ a) ⇒ variationNorm(((v ↦ Q(s, A, v) - Q(s, A.erase(i), v)))) ≤ error; ∀ s, t, w, A, (w ∉ boundary) ⇒ DiffersOnly(s, t, w) → (defects(valid, s) ∪ defects(valid, t) ∪ incident(scope, w) ⊆ A) ⇒ (|A| ≤ a) ⇒ variationNorm(((v ↦ Q(s, A, v) - Q(t, A, v)))) ≤ wire; ∀ s, (defects(valid, s) = ∅) ⇒ variationNorm(((v ↦ canonical(s)(v) - Q(s, ∅, v)))) ≤ truncation; ∀ s, (defects(valid, s) = ∅) ⇒ δ(actual(s), canonical(s)) ≤ coupling. Then

δ(actual(label(0)), actual(label(L))) ≤ truncation + L · (d · error) + L / 2 · wire + 2 · coupling.
-/
theorem composition_along_label_path
    (scope : G → Finset W) (valid : (W → F) → G → Prop)
    (hlocal : IsLocal scope valid) (boundary : Finset W)
    (Q : (W → F) → Finset G → V → ℝ)
    (canonical actual : (W → F) → FiniteDistribution V)
    (label : ℕ → W → F) (L d a : ℕ)
    (error wire truncation coupling : ℝ) (herror : 0 ≤ error)
    (hdegree : ∀ w, (incident scope w).card ≤ d)
    (hstart : defects valid (label 0) = ∅) (hend : defects valid (label L) = ∅)
    (hpath : ∀ j < L, ∃ w, w ∉ boundary ∧
      DiffersOnly (label j) (label (j + 1)) w ∧
      (defects valid (label j) ∪ defects valid (label (j + 1)) ∪ incident scope w).card ≤ a)
    (hswitch : ∀ s A i, i ∈ A → valid s i → defects valid s ⊆ A.erase i → A.card ≤ a →
      variationNorm (fun v => Q s A v - Q s (A.erase i) v) ≤ error)
    (hwire : ∀ s t w A, w ∉ boundary → DiffersOnly s t w →
      defects valid s ∪ defects valid t ∪ incident scope w ⊆ A → A.card ≤ a →
      variationNorm (fun v => Q s A v - Q t A v) ≤ wire)
    (htruncation : ∀ s, defects valid s = ∅ →
      variationNorm (fun v => (canonical s).weight v - Q s ∅ v) ≤ truncation)
    (hcoupling : ∀ s, defects valid s = ∅ →
      statisticalDistance (actual s) (canonical s) ≤ coupling) :
    statisticalDistance (actual (label 0)) (actual (label L)) ≤
      truncation + (L : ℝ) * ((d : ℝ) * error) + (L : ℝ) / 2 * wire + 2 * coupling := by
  classical
  let pathWeight := fun j => Q (label j) (defects valid (label j))
  have hstep : ∀ j < L, variationNorm
      (fun v => pathWeight j v - pathWeight (j + 1) v) ≤ 2 * ((d : ℝ) * error) + wire := by
    intro j hj
    obtain ⟨w, hwb, hchange, hcard⟩ := hpath j hj
    let common := defects valid (label j) ∪ defects valid (label (j + 1)) ∪ incident scope w
    have hs : defects valid (label j) ⊆ common := by
      intro i hi
      simp only [common, Finset.mem_union]
      exact Or.inl (Or.inl hi)
    have ht : defects valid (label (j + 1)) ⊆ common := by
      intro i hi
      simp only [common, Finset.mem_union]
      exact Or.inl (Or.inr hi)
    have hreverse : DiffersOnly (label (j + 1)) (label j) w :=
      fun v hv => (hchange v hv).symm
    have hsc : (common \ defects valid (label j)).card ≤ d :=
      (added_gates_card_le scope valid hlocal hchange).trans (hdegree w)
    have htc : (common \ defects valid (label (j + 1))).card ≤ d := by
      have h := (added_gates_card_le scope valid hlocal hreverse).trans (hdegree w)
      simpa only [common, Finset.union_comm (defects valid (label j))
        (defects valid (label (j + 1)))] using h
    have hswitchAt (s : W → F) :
        ∀ S, defects valid s ⊆ S → S ⊆ common → ∀ i ∈ S, i ∉ defects valid s →
          variationNorm (fun v => Q s S v - Q s (S.erase i) v) ≤ error := by
      intro S hds hS i hi hnot
      apply hswitch s S i hi
      · simpa using hnot
      · intro k hk
        apply Finset.mem_erase.mpr
        refine ⟨?_, hds hk⟩
        intro hki
        subst k
        exact hnot hk
      · exact (Finset.card_le_card hS).trans hcard
    exact local_signed_step_bound (Q (label j)) (Q (label (j + 1)))
      (defects valid (label j)) (defects valid (label (j + 1))) common d error wire herror
      hs ht hsc htc (hswitchAt _) (hswitchAt _)
      (hwire _ _ w common hwb hchange (Finset.Subset.refl _) hcard)
  apply composition_bound (actual (label 0)) (actual (label L))
    (canonical (label 0)) (canonical (label L)) pathWeight L
    truncation ((d : ℝ) * error) wire coupling
  · simpa [pathWeight, hstart] using htruncation (label 0) hstart
  · simpa [pathWeight, hend] using htruncation (label L) hend
  · exact hstep
  · exact hcoupling (label 0) hstart
  · exact hcoupling (label L) hend

/-- For a general circuit, the direct path changes each active nonboundary wire once and uses at most `3T` steps. This discharges path existence and width from the abstract composition theorem for arbitrary gate-local predicates. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For scope ∈ G → Finset(W); valid ∈ (W → F) → G → Prop; boundary ∈ Finset(W); s, t ∈ W → F; Q ∈ (W → F) → Finset(G) → V → ℝ; canonical, actual ∈ (W → F) → 𝒟(V); d ∈ ℕ; error, wire, truncation, coupling ∈ ℝ, assume IsLocal(scope, valid); ∀ i, |scope(i)| ≤ 3; defects(valid, s) = ∅; defects(valid, t) = ∅; ∀ w ∈ boundary, s(w) = t(w); ∀ w, (w ∉ activeWires(scope)) ⇒ s(w) = t(w); 0 ≤ error; 0 ≤ wire; ∀ w, |incident(scope, w)| ≤ d; ∀ u, A, i, (i ∈ A) ⇒ valid(u, i) → (defects(valid, u) ⊆ A.erase(i)) ⇒ variationNorm(((v ↦ Q(u, A, v) - Q(u, A.erase(i), v)))) ≤ error; ∀ u, v, w, A, (w ∉ boundary) ⇒ DiffersOnly(u, v, w) → (defects(valid, u) ∪ defects(valid, v) ∪ incident(scope, w) ⊆ A) ⇒ variationNorm(((z ↦ Q(u, A, z) - Q(v, A, z)))) ≤ wire; ∀ u, (defects(valid, u) = ∅) ⇒ variationNorm(((v ↦ canonical(u)(v) - Q(u, ∅, v)))) ≤ truncation; ∀ u, (defects(valid, u) = ∅) ⇒ δ(actual(u), canonical(u)) ≤ coupling. Then

δ(actual(s), actual(t)) ≤ truncation + 3 · |G| · (d · error) + 3 · |G| / 2 · wire + 2 · coupling.
-/
theorem general_circuit_composition
    (scope : G → Finset W) (valid : (W → F) → G → Prop)
    (hlocal : IsLocal scope valid) (hports : ∀ i, (scope i).card ≤ 3)
    (boundary : Finset W) (s t : W → F)
    (hs : defects valid s = ∅) (ht : defects valid t = ∅)
    (hboundary : ∀ w ∈ boundary, s w = t w)
    (hinactive : ∀ w, w ∉ activeWires scope → s w = t w)
    (Q : (W → F) → Finset G → V → ℝ)
    (canonical actual : (W → F) → FiniteDistribution V) (d : ℕ)
    (error wire truncation coupling : ℝ) (herror : 0 ≤ error) (hwireNonneg : 0 ≤ wire)
    (hdegree : ∀ w, (incident scope w).card ≤ d)
    (hswitch : ∀ u A i, i ∈ A → valid u i → defects valid u ⊆ A.erase i →
      variationNorm (fun v => Q u A v - Q u (A.erase i) v) ≤ error)
    (hwire : ∀ u v w A, w ∉ boundary → DiffersOnly u v w →
      defects valid u ∪ defects valid v ∪ incident scope w ⊆ A →
      variationNorm (fun z => Q u A z - Q v A z) ≤ wire)
    (htruncation : ∀ u, defects valid u = ∅ →
      variationNorm (fun v => (canonical u).weight v - Q u ∅ v) ≤ truncation)
    (hcoupling : ∀ u, defects valid u = ∅ →
      statisticalDistance (actual u) (canonical u) ≤ coupling) :
    statisticalDistance (actual s) (actual t) ≤
      truncation + (3 * Fintype.card G : ℕ) * ((d : ℝ) * error) +
        (3 * Fintype.card G : ℕ) / (2 : ℝ) * wire + 2 * coupling := by
  obtain ⟨L, label, hL, hstart, hend, hsteps⟩ :=
    exists_general_circuit_path scope hports boundary s t hboundary hinactive
  have hpath : ∀ j < L, ∃ w, w ∉ boundary ∧
      DiffersOnly (label j) (label (j + 1)) w ∧
      (defects valid (label j) ∪ defects valid (label (j + 1)) ∪ incident scope w).card ≤
        Fintype.card G := by
    intro j hj
    obtain ⟨w, _, hwb, hchange⟩ := hsteps j hj
    exact ⟨w, hwb, hchange, step_width_le_card scope valid _ _ w⟩
  have h := composition_along_label_path scope valid hlocal boundary Q canonical actual label
    L d (Fintype.card G) error wire truncation coupling herror hdegree
    (by simpa [hstart] using hs) (by simpa [hend] using ht) hpath
    (fun u A i hi hv hd _ => hswitch u A i hi hv hd)
    (fun u v w A hwb hc hd _ => hwire u v w A hwb hc hd) htruncation hcoupling
  rw [hstart, hend] at h
  have hLreal : (L : ℝ) ≤ (3 * Fintype.card G : ℕ) := by exact_mod_cast hL
  have h₁ := mul_le_mul_of_nonneg_right hLreal (mul_nonneg (Nat.cast_nonneg d) herror)
  have h₂ := mul_le_mul_of_nonneg_right hLreal hwireNonneg
  nlinarith

end CircuitCompiler.Composition
