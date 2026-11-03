import Proofs.Compiler.GateApproximation.MatrixPhase.ResidualExpansion



/-!
# Exact rank coefficients with the signed main-term exclusions retained
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators Classical

namespace CircuitCompiler.FourCycleEstimate

open Refresh MatrixRefresh TableAnalysis RefreshAnalysis

noncomputable section

/-- Keep the signed full-rank contribution restricted, paying absolute values only on actual repeated full rows or columns. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For Q, e ∈ ℝ; A, U, V, C ∈ Prop, assume 0 ≤ Q. Then

({ ({ ({ ({ 2 · Q² if C,; 0 otherwise }) if V,; 4 · Q otherwise }) if U,; 0 otherwise }) if A,; ({ ({ 4 · Q if C,; 0 otherwise }) if V,; 16 otherwise }) otherwise }) · e ≤ 16 · ({ e if ¬ (A) ∧ ¬ (V),; 0 otherwise }) + 4 · Q · ({ |e| if A ∧ U,; 0 otherwise }) + 4 · Q · ({ |e| if V ∧ C,; 0 otherwise }) + 2 · Q² · ({ |e| if A ∧ U ∧ V ∧ C,; 0 otherwise }).
-/
theorem rank_coefficient_sharp (Q e : ℝ) (hQ : 0 ≤ Q) (A U V C : Prop) :
    (if A then (if U then (if V then (if C then 2*Q^2 else 0) else 4*Q) else 0)
      else (if V then (if C then 4*Q else 0) else 16)) * e ≤
      16*(if ¬A ∧ ¬V then e else 0) +
        4*Q*(if A ∧ U then |e| else 0) +
        4*Q*(if V ∧ C then |e| else 0) +
        2*Q^2*(if A ∧ U ∧ V ∧ C then |e| else 0) := by
  have h₁ := mul_le_mul_of_nonneg_left (le_abs_self e) (show 0 ≤ 4*Q by positivity)
  have h₂ := mul_le_mul_of_nonneg_left (le_abs_self e) (show 0 ≤ 2*Q^2 by positivity)
  have h₃ := mul_nonneg hQ (abs_nonneg e)
  have h₄ := mul_nonneg (sq_nonneg Q) (abs_nonneg e)
  by_cases hA : A <;> by_cases hU : U <;> by_cases hV : V <;> by_cases hC : C <;>
    simp only [hA, hU, hV, hC, ite_true, ite_false, and_self, true_and, false_and,
      and_true, and_false, not_true_eq_false, not_false_eq_true, mul_zero, zero_mul] <;>
    nlinarith [abs_nonneg e]

variable {F X Y : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] {m : ℕ}

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For a ∈ X → U(F, m); b ∈ Y → U(F, m); E ∈ (X × U(F, m)) → (Y × U(F, m)) → ℝ; p ∈ ((X × V(F, m)) × (X × V(F, m))) × ((Y × V(F, m)) × (Y × V(F, m))), assume |F| = 2; 2 ≤ m; a is injective; b is injective; ∀ x, y, ((a((x)₁) · b((y)₁)) ≠ ((x)₂ · (y)₂)) ⇒ E(x, y) = 0. Then

(|F|ᵐ)⁴ · cornerCompletionProbability(a, b, p) · cornerProduct(fullFeatureTable(E), p) ≤ 16 · ({ cornerProduct(fullFeatureTable(E), p) if (((p)₁)₁)₁ ≠ (((p)₁)₂)₁ ∧ (((p)₂)₁)₂ ≠ (((p)₂)₂)₂,; 0 otherwise }) + 4 · |F|ᵐ · ({ |cornerProduct(fullFeatureTable(E), p)| if ((p)₁)₁ = ((p)₁)₂,; 0 otherwise }) + 4 · |F|ᵐ · ({ |cornerProduct(fullFeatureTable(E), p)| if ((p)₂)₁ = ((p)₂)₂,; 0 otherwise }) + 2 · (|F|ᵐ)² · ({ |cornerProduct(fullFeatureTable(E), p)| if ((p)₁)₁ = ((p)₁)₂ ∧ ((p)₂)₁ = ((p)₂)₂,; 0 otherwise }).
-/
theorem weighted_corner_le_sharp_rank_terms (hq : fieldCard F = 2) (hm : 2 ≤ m)
    (a : X → U F m) (b : Y → U F m) (ha : Function.Injective a) (hb : Function.Injective b)
    (E : (X × U F m) → (Y × U F m) → ℝ)
    (hE : ∀ x y, dot (a x.1).val (b y.1).val ≠ dot x.2.val y.2.val → E x y = 0)
    (p : ((X × V F m) × (X × V F m)) × ((Y × V F m) × (Y × V F m))) :
    (vectorCard F m : ℝ)^4 * cornerCompletionProbability a b p * cornerProduct (fullFeatureTable E) p ≤
      16 * (if p.1.1.1 ≠ p.1.2.1 ∧ p.2.1.2 ≠ p.2.2.2 then cornerProduct (fullFeatureTable E) p else 0) +
      4*(vectorCard F m : ℝ)*(if p.1.1 = p.1.2 then |cornerProduct (fullFeatureTable E) p| else 0) +
      4*(vectorCard F m : ℝ)*(if p.2.1 = p.2.2 then |cornerProduct (fullFeatureTable E) p| else 0) +
      2*(vectorCard F m : ℝ)^2*(if p.1.1 = p.1.2 ∧ p.2.1 = p.2.2 then |cornerProduct (fullFeatureTable E) p| else 0) := by
  by_cases hz : cornerProduct (fullFeatureTable E) p = 0
  · simp [hz]
  have hv₀ : p.2.1.2 ≠ 0 := by
    intro hv
    apply hz
    simp [cornerProduct, fullFeatureTable, featureZeroExtend, hv]
  have hv₁ : p.2.2.2 ≠ 0 := by
    intro hv
    apply hz
    simp [cornerProduct, fullFeatureTable, featureZeroExtend, hv]
  have hc : RefreshAnalysis.ExtensionCompatible ![(a p.1.1.1).val,(a p.1.2.1).val]
      ![p.2.1.2,p.2.2.2] ![p.1.1.2,p.1.2.2] ![(b p.2.1.1).val,(b p.2.2.1).val] := by
    by_contra hh
    exact hz (fullFeatureCorner_incompatible a b E hE p hh)
  have hw := scaled_completion_probability hq hm (a p.1.1.1) (a p.1.2.1)
    ⟨p.2.1.2,hv₀⟩ ⟨p.2.2.2,hv₁⟩ p.1.1.2 p.1.2.2 (b p.2.1.1).val (b p.2.2.1).val hc
  have he := rank_coefficient_sharp (vectorCard F m : ℝ) (cornerProduct (fullFeatureTable E) p)
    (by positivity) (a p.1.1.1 = a p.1.2.1) (p.1.1.2 = p.1.2.2)
      (p.2.1.2 = p.2.2.2) ((b p.2.1.1).val = (b p.2.2.1).val)
  simp only [Subtype.mk.injEq] at hw
  apply (congrArg (fun w : ℝ => w * cornerProduct (fullFeatureTable E) p) hw).le.trans
  convert he using 1 <;>
    simp only [ha.eq_iff, Subtype.val_inj, hb.eq_iff, Prod.ext_iff,
      and_comm, and_left_comm, and_assoc]

end

end CircuitCompiler.FourCycleEstimate
