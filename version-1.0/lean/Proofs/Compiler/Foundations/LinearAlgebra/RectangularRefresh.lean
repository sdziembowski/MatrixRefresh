import Proofs.Compiler.Foundations.LinearAlgebra.GramBounds
import Proofs.Compiler.Construction.Parameters



/-!
# Rectangle round operators on uniformly measured tables

The action on the two share coordinates is explicit. Rectangles may depend arbitrarily on the common group element. All norm and pairing formulas use normalized uniform averages over both share coordinates.
-/

set_option autoImplicit false

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace TableAnalysis

open MatrixRefresh Refresh

noncomputable section

variable {X G Z : Type*} [Fintype X] [Fintype G] [Fintype Z]

/-
Mathematical definition (normal notation): For e, f ∈ FiniteRefresh(X, G), define

productRefresh(e, f) := (M ↦ Equiv.prodCongr(e(M), f(M))).
-/
def productRefresh (e f : FiniteRefresh X G) : FiniteRefresh (X × X) G :=
  fun M => Equiv.prodCongr (e M) (f M)

/-
Mathematical definition (normal notation): For e, f ∈ FiniteRefresh(X, G); p ∈ TableRectanglePartition(X, G, Z); F ∈ ℝ^(X × X); z ∈ Z, define

tableRoundOp(e, f, p, F, z) := (l, r ↦ roundOp(productRefresh(e, f), p.toRoundPartition, ((x ↦ F((x)₁, (x)₂))), z, (l, r))).
-/
def tableRoundOp (e f : FiniteRefresh X G) (p : TableRectanglePartition X G Z)
    (F : Matrix X X ℝ) (z : Z) : Matrix X X ℝ :=
  fun l r => roundOp (productRefresh e f) p.toRoundPartition
    (fun x => F x.1 x.2) z (l, r)

omit [Fintype X] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Let e_M,f_M be the two refresh bijections and let a_z^M,b_z^M be the 0/1 values of the leakage masks. The round operator acts entrywise by

𝒯_z(F)(ℓ,r) := 𝔼_M [F(e_M⁻¹(ℓ),f_M⁻¹(r)) · a_z^M(e_M⁻¹(ℓ)) · b_z^M(f_M⁻¹(r))].
-/
theorem tableRoundOp_apply (e f : FiniteRefresh X G)
    (p : TableRectanglePartition X G Z) (F : Matrix X X ℝ) (z : Z) (l r : X) :
    tableRoundOp e f p F z l r = uavg (fun M =>
      F ((e M).symm l) ((f M).symm r) *
        (p.leftIndicator z M ((e M).symm l) * p.rightIndicator z M ((f M).symm r))) :=
  rfl

/-- Changing variables in a signed pushforward preserves the dual pairing. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e ∈ FiniteRefresh(X, G); p ∈ RoundPartition(X, G, Z); F, W ∈ X → ℝ; z ∈ Z, we have

𝔼ₓ [roundOp(e, p, F, z, x) · W(x)] = 𝔼_M [𝔼ₓ [F(x) · weight(p)(z, M, x) · W(e(M, x))]].
-/
theorem roundOp_pairing (e : FiniteRefresh X G) (p : RoundPartition X G Z)
    (F W : X → ℝ) (z : Z) :
    uavg (fun x => roundOp e p F z x * W x) =
      uavg (fun M => uavg (fun x => F x * p.weight z M x * W (e M x))) := by
  unfold roundOp
  simp_rw [← uavg_mul_const]
  rw [uavg_comm]
  apply uavg_congr
  intro M
  have h := uavg_equiv (e M)
    (fun x => F ((e M).symm x) * p.weight z M ((e M).symm x) * W x)
  simpa only [Equiv.symm_apply_apply] using h.symm

-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e, f ∈ FiniteRefresh(X, G); p ∈ TableRectanglePartition(X, G, Z); F, W ∈ ℝ^(X × X); z ∈ Z, we have

pairing(tableRoundOp(e, f, p, F, z), W) = 𝔼_M [pairing(((l, r ↦ F(l, r) · W(e(M, l), f(M, r)))), ((l, r ↦ p.leftIndicator(z, M, l) · p.rightIndicator(z, M, r))))].
-/
theorem tableRoundOp_pairing_leaf (e f : FiniteRefresh X G)
    (p : TableRectanglePartition X G Z) (F W : Matrix X X ℝ) (z : Z) :
    pairing (tableRoundOp e f p F z) W =
      uavg (fun M => pairing (fun l r => F l r * W (e M l) (f M r))
        (fun l r => p.leftIndicator z M l * p.rightIndicator z M r)) := by
  unfold pairing
  rw [← uavg_prod (fun x : X × X => tableRoundOp e f p F z x.1 x.2 * W x.1 x.2)]
  change uavg (fun x : X × X =>
    roundOp (productRefresh e f) p.toRoundPartition (fun x => F x.1 x.2) z x *
      W x.1 x.2) = _
  rw [roundOp_pairing]
  apply uavg_congr
  intro M
  rw [uavg_prod]
  apply uavg_congr
  intro l
  apply uavg_congr
  intro r
  change F l r * (p.leftIndicator z M l * p.rightIndicator z M r) *
    W (e M l) (f M r) = (F l r * W (e M l) (f M r)) *
      (p.leftIndicator z M l * p.rightIndicator z M r)
  ring

/-- The signed-density update paired with one test table per answer. -/
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e, f ∈ FiniteRefresh(X, G); p ∈ TableRectanglePartition(X, G, Z); F ∈ ℝ^(X × X); W ∈ Z → ℝ^(X × X), we have

(∑_z (pairing(tableRoundOp(e, f, p, F, z), W(z)))) = 𝔼_M [∑_z (pairing(((l, r ↦ F(l, r) · W(z, e(M, l), f(M, r)))), ((l, r ↦ p.leftIndicator(z, M, l) · p.rightIndicator(z, M, r)))))].
-/
theorem tableRoundOp_pairing (e f : FiniteRefresh X G)
    (p : TableRectanglePartition X G Z) (F : Matrix X X ℝ) (W : Z → Matrix X X ℝ) :
    (∑ z, pairing (tableRoundOp e f p F z) (W z)) =
      uavg (fun M => ∑ z, pairing (fun l r => F l r * W z (e M l) (f M r))
        (fun l r => p.leftIndicator z M l * p.rightIndicator z M r)) := by
  simp_rw [tableRoundOp_pairing_leaf]
  exact (uavg_sum _).symm

omit [Fintype X] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e, f ∈ FiniteRefresh(X, G); p ∈ TableRectanglePartition(X, G, Z); F, Q ∈ ℝ^(X × X); z ∈ Z, we have

tableRoundOp(e, f, p, (F - Q), z) = tableRoundOp(e, f, p, F, z) - tableRoundOp(e, f, p, Q, z).
-/
theorem tableRoundOp_sub (e f : FiniteRefresh X G)
    (p : TableRectanglePartition X G Z) (F Q : Matrix X X ℝ) (z : Z) :
    tableRoundOp e f p (F - Q) z = tableRoundOp e f p F z - tableRoundOp e f p Q z := by
  ext l r
  simp only [tableRoundOp_apply, Matrix.sub_apply]
  rw [← uavg_sub]
  apply uavg_congr
  intro M
  ring

omit [Fintype X] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e, f ∈ FiniteRefresh(X, G); p ∈ TableRectanglePartition(X, G, Z); F, Q ∈ ℝ^(X × X); z ∈ Z, we have

tableRoundOp(e, f, p, (F + Q), z) = tableRoundOp(e, f, p, F, z) + tableRoundOp(e, f, p, Q, z).
-/
theorem tableRoundOp_add (e f : FiniteRefresh X G)
    (p : TableRectanglePartition X G Z) (F Q : Matrix X X ℝ) (z : Z) :
    tableRoundOp e f p (F + Q) z = tableRoundOp e f p F z + tableRoundOp e f p Q z := by
  ext l r
  simp only [tableRoundOp_apply, Matrix.add_apply]
  rw [← uavg_add]
  apply uavg_congr
  intro M
  ring

omit [Fintype X] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e, f ∈ FiniteRefresh(X, G); p ∈ TableRectanglePartition(X, G, Z); z ∈ Z, we have

tableRoundOp(e, f, p, 0, z) = 0.
-/
@[simp] theorem tableRoundOp_zero (e f : FiniteRefresh X G)
    (p : TableRectanglePartition X G Z) (z : Z) :
    tableRoundOp e f p (0 : Matrix X X ℝ) z = 0 := by
  ext l r
  simp only [tableRoundOp_apply, Matrix.zero_apply, zero_mul, uavg_zero]

omit [Fintype X] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e, f ∈ FiniteRefresh(X, G); p ∈ TableRectanglePartition(X, G, Z); c ∈ ℝ; F ∈ ℝ^(X × X); z ∈ Z, we have

tableRoundOp(e, f, p, (c · F), z) = c · tableRoundOp(e, f, p, F, z).
-/
theorem tableRoundOp_smul (e f : FiniteRefresh X G)
    (p : TableRectanglePartition X G Z) (c : ℝ) (F : Matrix X X ℝ) (z : Z) :
    tableRoundOp e f p (c • F) z = c • tableRoundOp e f p F z := by
  ext l r
  simp only [tableRoundOp_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← uavg_const_mul]
  apply uavg_congr
  intro M
  ring

section Norms

variable [DecidableEq X] [Nonempty X] [Nonempty G]

omit [DecidableEq X] [Nonempty X] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e, f ∈ FiniteRefresh(X, G); p ∈ TableRectanglePartition(X, G, Z); F ∈ ℝ^(X × X), we have

∑_z (tableL1(tableRoundOp(e, f, p, F, z))) ≤ tableL1(F).
-/
theorem tableRoundOp_sum_L1_le (e f : FiniteRefresh X G)
    (p : TableRectanglePartition X G Z) (F : Matrix X X ℝ) :
    ∑ z, tableL1 (tableRoundOp e f p F z) ≤ tableL1 F :=
  sum_signedL1_roundOp_le (productRefresh e f) p.toRoundPartition (fun x => F x.1 x.2)

omit [DecidableEq X] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e, f ∈ FiniteRefresh(X, G); p ∈ TableRectanglePartition(X, G, Z); pMin ∈ ℝ; F ∈ ℝ^(X × X); z ∈ Z; l, r ∈ X, assume TransitionDensityBound(productRefresh(e, f), pMin). Then

|tableRoundOp(e, f, p, F, z, l, r)| ≤ tableL1(F) / pMin.
-/
theorem abs_tableRoundOp_le (e f : FiniteRefresh X G)
    (p : TableRectanglePartition X G Z) (pMin : ℝ)
    (hker : TransitionDensityBound (productRefresh e f) pMin)
    (F : Matrix X X ℝ) (z : Z) (l r : X) :
    |tableRoundOp e f p F z l r| ≤ tableL1 F / pMin :=
  abs_roundOp_le (productRefresh e f) p.toRoundPartition pMin hker
    (fun x => F x.1 x.2) z (l, r)

omit [DecidableEq X] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e, f ∈ FiniteRefresh(X, G); p ∈ TableRectanglePartition(X, G, Z); pMin ∈ ℝ; F ∈ ℝ^(X × X), assume 0 < pMin; TransitionDensityBound(productRefresh(e, f), pMin). Then

∑_z ((‖ tableRoundOp(e, f, p, F, z)‖₂)²) ≤ (tableL1(F))² / pMin.
-/
theorem tableRoundOp_sum_HS_sq_le (e f : FiniteRefresh X G)
    (p : TableRectanglePartition X G Z) (pMin : ℝ) (hpMin : 0 < pMin)
    (hker : TransitionDensityBound (productRefresh e f) pMin) (F : Matrix X X ℝ) :
    ∑ z, tableL2Norm (tableRoundOp e f p F z) ^ 2 ≤ tableL1 F ^ 2 / pMin := by
  simp only [tableL2Norm_sq, tableRoundOp, tableL1]
  exact sum_signedL2Sq_roundOp_le (productRefresh e f) p.toRoundPartition pMin hpMin hker
    (fun x => F x.1 x.2)

omit [DecidableEq X] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e, f ∈ FiniteRefresh(X, G); p ∈ TableRectanglePartition(X, G, Z); pMin ∈ ℝ; F ∈ ℝ^(X × X), assume 0 < pMin; TransitionDensityBound(productRefresh(e, f), pMin). Then

√(∑_z ((‖ tableRoundOp(e, f, p, F, z)‖₂)²)) ≤ tableL1(F) / √pMin.
-/
theorem tableRoundOp_tuple_HS_le (e f : FiniteRefresh X G)
    (p : TableRectanglePartition X G Z) (pMin : ℝ) (hpMin : 0 < pMin)
    (hker : TransitionDensityBound (productRefresh e f) pMin) (F : Matrix X X ℝ) :
    Real.sqrt (∑ z, tableL2Norm (tableRoundOp e f p F z) ^ 2) ≤ tableL1 F / Real.sqrt pMin := by
  simp only [tableL2Norm_eq_signedL2, tableRoundOp, tableL1]
  exact tuple_signedL2_roundOp_le (productRefresh e f) p.toRoundPartition pMin hpMin hker
    (fun x => F x.1 x.2)

omit [DecidableEq X] in
-- Auxiliary lemma (linear algebra); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For e, f ∈ FiniteRefresh(X, G); p ∈ TableRectanglePartition(X, G, Z); pMin ∈ ℝ; F ∈ ℝ^(X × X), assume 0 < pMin; TransitionDensityBound(productRefresh(e, f), pMin). Then

∑_z (‖ tableRoundOp(e, f, p, F, z)‖₂) ≤ √(|Z| / pMin) · tableL1(F).
-/
theorem tableRoundOp_sum_HS_le (e f : FiniteRefresh X G)
    (p : TableRectanglePartition X G Z) (pMin : ℝ) (hpMin : 0 < pMin)
    (hker : TransitionDensityBound (productRefresh e f) pMin) (F : Matrix X X ℝ) :
    ∑ z, tableL2Norm (tableRoundOp e f p F z) ≤
      Real.sqrt ((Fintype.card Z : ℝ) / pMin) * tableL1 F := by
  simp only [tableL2Norm_eq_signedL2, tableRoundOp, tableL1]
  exact sum_signedL2_roundOp_le (productRefresh e f) p.toRoundPartition pMin hpMin hker
    (fun x => F x.1 x.2)

end Norms

end

end TableAnalysis
