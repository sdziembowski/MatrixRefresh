import Proofs.Compiler.Foundations.MatrixRefreshing.Analysis.Tables
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Notation



/-!
# Reindexing the independent reference experiment

The matrix-counting argument first fixes two old left shares and two new right shares, then samples their four complementary output vectors independently. After averaging the four inputs uniformly as well and restricting the four outputs to nonzero vectors, all eight vectors are independent and uniform. They regroup into two left endpoints and two right endpoints.

`referenceEndpointsEquiv` writes this regrouping as a bijection. Its purpose is to account for every coordinate and normalization exactly, without an informal independence assertion. The resulting four-corner product is the signed four-cycle expansion from `Tables.lean`.
-/

set_option autoImplicit false

namespace MatrixRefresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open Refresh

noncomputable section

/-- Group fixed inputs and sampled outputs into endpoints `(oldShare,newShare)`. the left party's fixed inputs are old shares, whereas the right party's fixed inputs are new shares; the reversed right convention is what removes matrix inverses in the counting. -/
/- Mathematical definition (normal notation): Group eight nonzero shares into the four endpoints ((ℓ₀,u₀),(ℓ₁,u₁),(v₀,ρ₀),(v₁,ρ₁)). This is a coordinate bijection from two input-row/input-column pairs and two output pairs to the four table indices used in the reference four-cycle average. -/
def referenceEndpointsEquiv (n : ℕ) :
    (((U F n × U F n) × (U F n × U F n)) × ((Fin 2 → U F n) × (Fin 2 → U F n))) ≃
      ((Endpoint F n × Endpoint F n) × (Endpoint F n × Endpoint F n)) where
  toFun wo :=
    ((⟨wo.1.1.1, wo.2.1 0⟩, ⟨wo.1.1.2, wo.2.1 1⟩),
      (⟨wo.2.2 0, wo.1.2.1⟩, ⟨wo.2.2 1, wo.1.2.2⟩))
  invFun xy :=
    (((xy.1.1.oldShare, xy.1.2.oldShare), (xy.2.1.newShare, xy.2.2.newShare)),
      (![xy.1.1.newShare, xy.1.2.newShare], ![xy.2.1.oldShare, xy.2.2.oldShare]))
  left_inv wo := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  right_inv _ := rfl

/-- Exact normalized equality for signed tables; there are no absolute values and no independence assumptions beyond the displayed uniform averages. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; Φ ∈ Endpoint(F, n) → Endpoint(F, n) → ℝ, we have

𝔼_(w ∈ (U(F, n) × U(F, n)) × (U(F, n) × U(F, n))) [𝔼_(o ∈ ({0,…,2−1} → U(F, n)) × ({0,…,2−1} → U(F, n))) [Φ((((w)₁)₁, (o)₁(0)), ((o)₂(0), ((w)₂)₁)) · Φ((((w)₁)₂, (o)₁(1)), ((o)₂(0), ((w)₂)₁)) · Φ((((w)₁)₂, (o)₁(1)), ((o)₂(1), ((w)₂)₂)) · Φ((((w)₁)₁, (o)₁(0)), ((o)₂(1), ((w)₂)₂))]] = fourCycle(Φ).
-/
theorem nonzeroReference_eq_fourCycle {n : ℕ} (Φ : Endpoint F n → Endpoint F n → ℝ) :
    uavg (fun w : (U F n × U F n) × (U F n × U F n) =>
      uavg (fun o : (Fin 2 → U F n) × (Fin 2 → U F n) =>
        Φ ⟨w.1.1, o.1 0⟩ ⟨o.2 0, w.2.1⟩ *
        Φ ⟨w.1.2, o.1 1⟩ ⟨o.2 0, w.2.1⟩ *
        Φ ⟨w.1.2, o.1 1⟩ ⟨o.2 1, w.2.2⟩ *
        Φ ⟨w.1.1, o.1 0⟩ ⟨o.2 1, w.2.2⟩)) = fourCycle Φ := by
  let prodTable : ((Endpoint F n × Endpoint F n) × (Endpoint F n × Endpoint F n)) → ℝ := fun xy =>
    Φ xy.1.1 xy.2.1 * Φ xy.1.2 xy.2.1 * Φ xy.1.2 xy.2.2 * Φ xy.1.1 xy.2.2
  change uavg (fun w => uavg (fun o => prodTable (referenceEndpointsEquiv n (w, o)))) = _
  -- Merge the two sampling stages, apply the bijection, and expand the four-cycle. Every operation preserves uniform normalization exactly.
  rw [← uavg_prod (fun wo => prodTable (referenceEndpointsEquiv n wo)),
    uavg_equiv (referenceEndpointsEquiv n) prodTable, fourCycle_expansion]
  simp only [prodTable, uavg_prod]

end

end MatrixRefresh
