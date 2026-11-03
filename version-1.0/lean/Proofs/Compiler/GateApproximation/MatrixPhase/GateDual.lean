import Proofs.Compiler.GateApproximation.MatrixPhase.GateDensity
import Proofs.Compiler.GateApproximation.MatrixPhase.JointGraphCycle
import Proofs.Compiler.GateApproximation.MatrixPhase.JointMixing



/-!
# Pairing the actual conditional matrix-answer probability table with a joint-port test
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 800000

open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical

namespace CircuitCompiler

open Refresh MatrixRefresh TableAnalysis

noncomputable section

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A,B a set; P ∈ 𝒟(A); Q ∈ A → 𝒟(B); f ∈ A × B → ℝ, assume A is finite; B is finite. Then

𝔼_(u ← P.joint(Q)) [f(u)] = 𝔼_(a ← P) [𝔼_(b ← Q(a)) [f((a, b))]].
-/
private theorem expect_joint {A B : Type*} [Fintype A] [Fintype B]
    (P : FiniteDistribution A) (Q : A → FiniteDistribution B) (f : A × B → ℝ) :
    (P.joint Q).expect f = P.expect (fun a => (Q a).expect (fun b => f (a,b))) := by
  simp only [FiniteDistribution.expect, FiniteDistribution.joint, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A,B a set; P ∈ 𝒟((A × B)); b ∈ B; f ∈ A → ℝ, assume A is finite; B is finite. Then

𝔼_(p ← P) [{ f((p)₁) if (p)₂ = b,; 0 otherwise }] = ∑ₐ (P((a, b)) · f(a)).
-/
private theorem expect_slice {A B : Type*} [Fintype A] [Fintype B]
    (P : FiniteDistribution (A × B)) (b : B) (f : A → ℝ) :
    P.expect (fun p => if p.2 = b then f p.1 else 0) = ∑ a, P.weight (a,b) * f a := by
  simp [FiniteDistribution.expect, Fintype.sum_prod_type]

variable {F Z : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype Z]

/-- Conditional averaging recovers the original shared-matrix experiment, including one complete rectangle leaf. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z); a, b ∈ State(F, n); z ∈ Z; W ∈ State(F, (n · n)) → ℝ, assume 2 ≤ n · n. Then

𝔼_(u ← μ_(secret(a) · secret(b))) [matrixAnswerProb(p, a, b, u, z) · W(u)] = 𝔼_M [matrixAnswer(p, a, b, M)(z) · W(refreshedTensor(a, b, M))].
-/
theorem matrixAnswerDistribution_pairing {n : ℕ} (hm : 2 ≤ n*n)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n)) Z)
    (a b : State F n) (z : Z) (W : State F (n*n) → ℝ) :
    (mu F (n*n) hm (secret a * secret b)).expect
      (fun u => matrixAnswerProb p a b u z * W u) =
    uavg (fun M => (matrixAnswer p a b M).weight z * W (refreshedTensor a b M)) := by
  have he : (matrixExecution p a b).expect
      (fun uz => if uz.2 = z then W uz.1 else 0) =
      (mu F (n*n) hm (secret a * secret b)).expect
        (fun u => matrixAnswerProb p a b u z * W u) := by
    rw [expect_slice]
    simp only [matrixExecution_weight hm, FiniteDistribution.expect, mul_assoc]
  rw [← he, matrixExecution, expect_map, expect_joint]
  simp only [FiniteDistribution.expect, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [FiniteDistribution.uniform, uavg, Finset.mul_sum]

/-- Group the two old encodings by party. -/
/- Mathematical definition (normal notation): Regroup the two old encodings by party: ((L₁,R₁),(L₂,R₂)) ↦ ((L₁,L₂),(R₁,R₂)). The inverse simply pairs the corresponding left and right shares. -/
def oldPortRegroup (n : ℕ) : (State F n × State F n) ≃
    ((U F n × U F n) × (U F n × U F n)) where
  toFun ab := ((ab.1.L, ab.2.L), (ab.1.R, ab.2.R))
  invFun xy := (⟨xy.1.1, xy.2.1⟩, ⟨xy.1.2, xy.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; f ∈ (U(F, n) × U(F, n)) → (U(F, n) × U(F, n)) → ℝ, assume 2 ≤ n. Then

𝔼_(ab ← (independentStateDistribution(F, n) ⊗ independentStateDistribution(F, n))) [f((ab.1.L, ab.2.L), (ab.1.R, ab.2.R))] = 𝔼ₓ [𝔼_w [f(x, w)]].
-/
theorem oldPort_expect {n : ℕ} (hn : 2 ≤ n)
    (f : (U F n × U F n) → (U F n × U F n) → ℝ) :
    ((independentStateDistribution F n hn).prod (independentStateDistribution F n hn)).expect
      (fun ab => f (ab.1.L, ab.2.L) (ab.1.R, ab.2.R)) =
    uavg (fun x => uavg (f x)) := by
  have h : ((independentStateDistribution F n hn).prod (independentStateDistribution F n hn)).map
      (oldPortRegroup (F:=F) n) =
      (uniformShare F n hn |>.prod (uniformShare F n hn)).prod
        (uniformShare F n hn |>.prod (uniformShare F n hn)) := by
    ext xy
    rw [FiniteDistribution.map_equiv_weight]
    simp only [FiniteDistribution.prod, FiniteDistribution.joint, independentStateDistribution_weight]
    change (1/(shareCard F n : ℝ)^2)*(1/(shareCard F n : ℝ)^2) =
      ((Fintype.card (U F n):ℝ)⁻¹ * (Fintype.card (U F n):ℝ)⁻¹) *
      ((Fintype.card (U F n):ℝ)⁻¹ * (Fintype.card (U F n):ℝ)⁻¹)
    rw [nonzero_vector_card]
    simp [div_eq_mul_inv, pow_two, shareCard, vectorCard]
  have he := congrArg (fun Q => FiniteDistribution.expect Q (fun xy => f xy.1 xy.2)) h
  try dsimp only at he
  rw [expect_map] at he
  simpa only [expect_prod, oldPortRegroup, Equiv.coe_fn_mk, uniformShare,
    ← uavg_eq_expect_uniform, uavg_prod, stateLeftShare, stateRightShare] using he

/-- The common conditional answer probability function on the grouped party carrier. -/
/-
Mathematical definition (normal notation): For n ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z); z ∈ Z; x, y ∈ GateSide(F, n, (n · n)), define

groupedMatrixAnswerProb(p, z, x, y) := matrixAnswerProb(p, (((x)₁)₁, ((y)₁)₁), (((x)₁)₂, ((y)₁)₂), ((x)₂, (y)₂), z).
-/
def groupedMatrixAnswerProb {n : ℕ}
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n)) Z)
    (z : Z) (x y : GateSide F n (n*n)) : ℝ :=
  matrixAnswerProb p ⟨x.1.1,y.1.1⟩ ⟨x.1.2,y.1.2⟩ ⟨x.2,y.2⟩ z

/-- Exact dual identity; both rectangle factors see the same matrix. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z); z ∈ Z; W ∈ ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))), assume 2 ≤ n; 2 ≤ n · n. Then

𝔼ₓ [𝔼_y [gateDensity(x, y) · groupedMatrixAnswerProb(p, z, x, y) · W(x, y)]] = 𝔼_M [𝔼ₓ [𝔼_y [p.leftIndicator(z, M, x) · p.rightIndicator(z, M, y) · W((x, rowRefresh(inputTensor(x), M)), (y, columnRefresh(inputTensor(y), M)))]]].
-/
theorem groupedMatrixAnswerProb_pairing {n : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ n*n)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n)) Z)
    (z : Z) (W : Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℝ) :
    uavg (fun x => uavg (fun y => gateDensity x y * groupedMatrixAnswerProb p z x y * W x y)) =
    uavg (fun M => uavg (fun x => uavg (fun y =>
      p.leftIndicator z M x * p.rightIndicator z M y *
        W (x,rowRefresh (inputTensor x) M) (y,columnRefresh (inputTensor y) M)))) := by
  have h := jointPortDistribution_expect hn hm
    (fun x y => groupedMatrixAnswerProb p z x y * W x y)
  simp only [← mul_assoc] at h
  rw [← h, jointPortDistribution, expect_map, expect_joint]
  change ((independentStateDistribution F n hn).prod (independentStateDistribution F n hn)).expect
    (fun ab => (mu F (n*n) hm (secret ab.1 * secret ab.2)).expect
      (fun u => matrixAnswerProb p ab.1 ab.2 u z *
        W ((ab.1.L,ab.2.L),u.L) ((ab.1.R,ab.2.R),u.R))) = _
  simp_rw [matrixAnswerDistribution_pairing hm]
  change ((independentStateDistribution F n hn).prod (independentStateDistribution F n hn)).expect
    (fun ab => (fun x y => uavg (fun M =>
      p.leftIndicator z M x * p.rightIndicator z M y *
        W (x,rowRefresh (inputTensor x) M) (y,columnRefresh (inputTensor y) M)))
        (ab.1.L,ab.2.L) (ab.1.R,ab.2.R)) = _
  rw [oldPort_expect hn (fun x y => uavg (fun M =>
      p.leftIndicator z M x * p.rightIndicator z M y *
        W (x,rowRefresh (inputTensor x) M) (y,columnRefresh (inputTensor y) M)))]
  conv_lhs => arg 1; ext x; rw [uavg_comm]
  rw [uavg_comm]

/-- The exact probability of one represented value differs from `1/q` by at most the reciprocal number of nonzero vectors, including the zero value. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For m ∈ ℕ; s ∈ F, assume 2 ≤ m. Then

|(densityWeight(F, m, s))⁻¹ - (|F|)⁻¹| ≤ 1 / (|F|ᵐ - 1).
-/
theorem inverse_densityWeight_sub_uniform {m : ℕ} (hm : 2 ≤ m) (s : F) :
    |(densityWeight F m s)⁻¹ - (fieldCard F : ℝ)⁻¹| ≤ 1 / ((vectorCard F m : ℝ) - 1) := by
  have hq := fieldCard_cast_pos (F:=F)
  have hq2 := fieldCard_cast_ge_two (F:=F)
  have hN := vectorCard_real_ge_four (F:=F) hm
  have hd : 0 < (vectorCard F m : ℝ) - 1 := by linarith
  by_cases hs : s = 0
  · subst s
    rw [densityWeight_zero hm, inv_div, shareCard_cast_real]
    have he : ((vectorCard F m : ℝ) - fieldCard F) / ((fieldCard F : ℝ) * ((vectorCard F m : ℝ)-1)) -
        (fieldCard F : ℝ)⁻¹ = (1-(fieldCard F : ℝ)) / ((fieldCard F : ℝ) * ((vectorCard F m : ℝ)-1)) := by
      field_simp
      ring
    rw [he, abs_div, abs_of_pos (mul_pos hq hd), abs_of_nonpos (by linarith)]
    apply (div_le_iff₀ (mul_pos hq hd)).2
    have hc : (1 / ((vectorCard F m : ℝ)-1)) * ((fieldCard F : ℝ) * ((vectorCard F m : ℝ)-1)) = fieldCard F := by
      field_simp
    rw [hc]
    linarith
  · rw [densityWeight_of_ne_zero hm s hs, inv_div, shareCard_cast_real]
    have he : (vectorCard F m : ℝ) / ((fieldCard F : ℝ) * ((vectorCard F m : ℝ)-1)) -
        (fieldCard F : ℝ)⁻¹ = 1 / ((fieldCard F : ℝ) * ((vectorCard F m : ℝ)-1)) := by
      field_simp
      ring
    rw [he, abs_of_pos (by positivity)]
    apply one_div_le_one_div_of_le hd
    nlinarith

/-- Multiplication by the reference density is invertible on its support. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; V ∈ ℝ^(GateSide(F, n, m) × GateSide(F, n, m)); x, y ∈ GateSide(F, n, m), assume 2 ≤ m; ∀ x, y, (((x)₂ · (y)₂) ≠ portProduct(x, y)) ⇒ V(x, y) = 0. Then

gateDensity(x, y) · ((densityWeight(F, m, portProduct(x, y)))⁻¹ · V(x, y)) = V(x, y).
-/
theorem supported_density_cancel {n m : ℕ} (hm : 2 ≤ m)
    (V : Matrix (GateSide F n m) (GateSide F n m) ℝ)
    (hV : ∀ x y, dot x.2.val y.2.val ≠ portProduct x y → V x y = 0)
    (x y : GateSide F n m) :
    gateDensity x y * ((densityWeight F m (portProduct x y))⁻¹ * V x y) = V x y := by
  by_cases h : dot x.2.val y.2.val = portProduct x y
  · rw [gateDensity, encodingDensity, if_pos h, ← mul_assoc,
      mul_inv_cancel₀ (densityWeight_pos hm _).ne', one_mul]
  · simp [hV x y h]

/-- A supported test pairs against the actual refresh graph with the precise secret-fiber probability. No independent matrix is introduced for either side. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z); z ∈ Z; V ∈ ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))), assume 2 ≤ n; 2 ≤ n · n; ∀ x, y, (((x)₂ · (y)₂) ≠ portProduct(x, y)) ⇒ V(x, y) = 0. Then

𝔼ₓ [𝔼_y [groupedMatrixAnswerProb(p, z, x, y) · V(x, y)]] = 𝔼_M [𝔼ₓ [𝔼_y [(densityWeight(F, (n · n), (((x)₁ · (y)₁) · ((x)₂ · (y)₂))))⁻¹ · p.leftIndicator(z, M, x) · p.rightIndicator(z, M, y) · V((x, rowRefresh(inputTensor(x), M)), (y, columnRefresh(inputTensor(y), M)))]]].
-/
theorem supported_answer_table_pairing {n : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ n*n)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n)) Z)
    (z : Z) (V : Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℝ)
    (hV : ∀ x y, dot x.2.val y.2.val ≠ portProduct x y → V x y = 0) :
    uavg (fun x => uavg (fun y => groupedMatrixAnswerProb p z x y * V x y)) =
    uavg (fun M => uavg (fun x => uavg (fun y =>
      (densityWeight F (n*n) (dot x.1.val y.1.val * dot x.2.val y.2.val))⁻¹ *
        p.leftIndicator z M x * p.rightIndicator z M y *
        V (x,rowRefresh (inputTensor x) M) (y,columnRefresh (inputTensor y) M)))) := by
  have h := groupedMatrixAnswerProb_pairing hn hm p z
    (fun x y => (densityWeight F (n*n) (portProduct x y))⁻¹ * V x y)
  have he (x y : GateSide F n (n*n)) : gateDensity x y * groupedMatrixAnswerProb p z x y *
      ((densityWeight F (n*n) (portProduct x y))⁻¹ * V x y) =
      groupedMatrixAnswerProb p z x y * V x y := by
    calc
      _ = groupedMatrixAnswerProb p z x y *
          (gateDensity x y * ((densityWeight F (n*n) (portProduct x y))⁻¹ * V x y)) := by ring
      _ = _ := by rw [supported_density_cancel hm V hV]
  simp_rw [he] at h
  rw [h]
  apply uavg_congr
  intro M
  apply uavg_congr
  intro x
  apply uavg_congr
  intro y
  dsimp [portProduct]
  ring

/-- Uniform averaging on the actual matrix graph equals the reference density average, for every real test. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; W ∈ ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))), assume 2 ≤ n; 2 ≤ n · n. Then

𝔼_(M ∈ GL_(n · n)(F)) [𝔼ₓ [𝔼_y [W((x, rowRefresh(inputTensor(x), M)), (y, columnRefresh(inputTensor(y), M)))]]] = 𝔼ₓ [𝔼_y [gateDensity(x, y) · W(x, y)]].
-/
theorem tensor_graph_average {n : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ n*n)
    (W : Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℝ) :
    uavg (fun M : Refresh.«GL» F (n*n) => uavg (fun x => uavg (fun y =>
      W (x,rowRefresh (inputTensor x) M) (y,columnRefresh (inputTensor y) M)))) =
    uavg (fun x => uavg (fun y => gateDensity x y * W x y)) := by
  have h := congrArg (fun P => FiniteDistribution.expect P (fun xy => W xy.1 xy.2))
    (jointPortDistribution_from_matrix (F:=F) hn hm)
  try dsimp only at h
  rw [expect_map, expect_joint, jointPortDistribution_expect] at h
  simp_rw [expect_map, ← uavg_eq_expect_uniform] at h
  change ((independentStateDistribution F n hn).prod (independentStateDistribution F n hn)).expect
    (fun ab => (fun x y => uavg (fun M =>
      W (x,rowRefresh (inputTensor x) M) (y,columnRefresh (inputTensor y) M)))
        (ab.1.L,ab.2.L) (ab.1.R,ab.2.R)) = _ at h
  rw [oldPort_expect hn (fun x y => uavg (fun M =>
      W (x,rowRefresh (inputTensor x) M) (y,columnRefresh (inputTensor y) M)))] at h
  conv_lhs at h => arg 1; ext x; rw [uavg_comm]
  rw [uavg_comm] at h
  exact h

/-- The graph has bounded density, so its mean absolute value is controlled by the ordinary uniform L₂ energy of the test. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; V ∈ ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))); H ∈ ℝ, assume 2 ≤ n; 2 ≤ n · n; 𝔼ₓ [𝔼_y [(V(x, y))²]] ≤ H. Then

𝔼_(M ∈ GL_(n · n)(F)) [𝔼ₓ [𝔼_y [|V((x, rowRefresh(inputTensor(x), M)), (y, columnRefresh(inputTensor(y), M)))|]]] ≤ √((|F| + 1) · H).
-/
theorem tensor_graph_abs_mean {n : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ n*n)
    (V : Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℝ) (H : ℝ)
    (henergy : uavg (fun x => uavg (fun y => (V x y)^2)) ≤ H) :
    uavg (fun M : Refresh.«GL» F (n*n) => uavg (fun x => uavg (fun y =>
      |V (x,rowRefresh (inputTensor x) M) (y,columnRefresh (inputTensor y) M)|))) ≤
    Real.sqrt (((fieldCard F : ℝ)+1)*H) := by
  rw [tensor_graph_average hn hm (fun x y => |V x y|),
    ← jointPortDistribution_expect hn hm (fun x y => |V x y|)]
  have h := expect_abs_le_rms (jointPortDistribution (F:=F) hn hm) (fun xy => V xy.1 xy.2)
  refine h.trans ?_
  unfold rms
  apply Real.sqrt_le_sqrt
  rw [jointPortDistribution_expect hn hm (fun x y => (V x y)^2)]
  calc
    _ ≤ uavg (fun x => uavg (fun y => ((fieldCard F : ℝ)+1)*(V x y)^2)) := by
      apply uavg_mono
      intro x
      apply uavg_mono
      intro y
      exact mul_le_mul_of_nonneg_right (gateDensity_le hm x y) (sq_nonneg _)
    _ = ((fieldCard F : ℝ)+1)*uavg (fun x => uavg (fun y => (V x y)^2)) := by
      simp only [uavg_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left henergy (by positivity)

/-- The marginal weights of a complete rectangle partition have square sum one, even when both sides depend on the common matrix. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X,G a set; p ∈ TableRectanglePartition(X, G, Z); M ∈ G, assume X is finite; X ≠ ∅. Then

∑_z ((rectangleWeight(p.leftIndicator(z, M), p.rightIndicator(z, M)))²) = 1.
-/
theorem gate_rectangle_weights_sq {X G : Type*} [Fintype X] [Nonempty X]
    (p : TableRectanglePartition X G Z) (M : G) :
    ∑ z, rectangleWeight (p.leftIndicator z M) (p.rightIndicator z M)^2 = 1 := by
  apply rectangleWeight_sum_sq
  · intro z x
    simp only [TableRectanglePartition.leftIndicator]
    split_ifs <;> norm_num
  · intro z x
    simp only [TableRectanglePartition.rightIndicator]
    split_ifs <;> norm_num
  · exact p.complete M

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X,G a set; p ∈ TableRectanglePartition(X, G, Z); M ∈ G; z ∈ Z, assume X is finite; X ≠ ∅. Then

rectangleWeight(p.leftIndicator(z, M), p.rightIndicator(z, M)) ≤ 1.
-/
theorem gate_rectangle_weight_le_one {X G : Type*} [Fintype X] [Nonempty X]
    (p : TableRectanglePartition X G Z) (M : G) (z : Z) :
    rectangleWeight (p.leftIndicator z M) (p.rightIndicator z M) ≤ 1 := by
  have h := Finset.single_le_sum (s:=Finset.univ)
    (fun z _ => sq_nonneg (rectangleWeight (p.leftIndicator z M) (p.rightIndicator z M)))
    (Finset.mem_univ z)
  rw [gate_rectangle_weights_sq] at h
  nlinarith

-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For X,G a set; p ∈ TableRectanglePartition(X, G, Z); M ∈ G, assume X is finite; X ≠ ∅. Then

∑_z (rectangleWeight(p.leftIndicator(z, M), p.rightIndicator(z, M))) ≤ √(|Z|).
-/
theorem gate_rectangle_weights_sum {X G : Type*} [Fintype X] [Nonempty X]
    (p : TableRectanglePartition X G Z) (M : G) :
    ∑ z, rectangleWeight (p.leftIndicator z M) (p.rightIndicator z M) ≤
      Real.sqrt (Fintype.card Z : ℝ) :=
  weights_sum_le_sqrt_card _ (gate_rectangle_weights_sq p M)

/-- Replacing the secret-dependent fiber probability by `1/q` costs only the long-dimension correction, uniformly over the adaptive rectangle leaf. -/
-- Auxiliary lemma (compiler proof infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; p ∈ TableRectanglePartition((U(F, n) × U(F, n)), GL_(n · n)(F), Z); z ∈ Z; V ∈ ℝ^(GateSide(F, n, (n · n)) × GateSide(F, n, (n · n))); H ∈ ℝ, assume 2 ≤ n; 2 ≤ n · n; ∀ x, y, (((x)₂ · (y)₂) ≠ portProduct(x, y)) ⇒ V(x, y) = 0; 𝔼ₓ [𝔼_y [(V(x, y))²]] ≤ H. Then

|𝔼ₓ [𝔼_y [groupedMatrixAnswerProb(p, z, x, y) · V(x, y)]] - (|F|)⁻¹ · 𝔼_M [𝔼ₓ [𝔼_y [p.leftIndicator(z, M, x) · p.rightIndicator(z, M, y) · V((x, rowRefresh(inputTensor(x), M)), (y, columnRefresh(inputTensor(y), M)))]]]| ≤ √((|F| + 1) · H) / (|F|^(n · n) - 1).
-/
theorem supported_answer_table_uniform_error {n : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ n*n)
    (p : TableRectanglePartition (U F n × U F n) (Refresh.«GL» F (n*n)) Z)
    (z : Z) (V : Matrix (GateSide F n (n*n)) (GateSide F n (n*n)) ℝ)
    (hV : ∀ x y, dot x.2.val y.2.val ≠ portProduct x y → V x y = 0)
    (H : ℝ) (henergy : uavg (fun x => uavg (fun y => (V x y)^2)) ≤ H) :
    |uavg (fun x => uavg (fun y => groupedMatrixAnswerProb p z x y * V x y)) -
      (fieldCard F : ℝ)⁻¹ * uavg (fun M => uavg (fun x => uavg (fun y =>
        p.leftIndicator z M x * p.rightIndicator z M y *
          V (x,rowRefresh (inputTensor x) M) (y,columnRefresh (inputTensor y) M))))| ≤
      Real.sqrt (((fieldCard F : ℝ)+1)*H) / ((vectorCard F (n*n) : ℝ)-1) := by
  let A := fun (M : Refresh.«GL» F (n*n)) (x y : U F n × U F n) =>
    V (x,rowRefresh (inputTensor x) M) (y,columnRefresh (inputTensor y) M)
  let f := fun M x y => p.leftIndicator z M x * p.rightIndicator z M y
  let e := 1 / ((vectorCard F (n*n) : ℝ)-1)
  have he : 0 ≤ e := by
    have hN := vectorCard_real_ge_four (F:=F) hm
    dsimp [e]
    exact div_nonneg zero_le_one (by linarith)
  have hp (M : Refresh.«GL» F (n*n)) (x y : U F n × U F n) :
      |((densityWeight F (n*n) (dot x.1.val y.1.val * dot x.2.val y.2.val))⁻¹ -
        (fieldCard F : ℝ)⁻¹) * f M x y * A M x y| ≤ e * |A M x y| := by
    have hprob := inverse_densityWeight_sub_uniform hm
      (dot x.1.val y.1.val * dot x.2.val y.2.val)
    have hf : |f M x y| ≤ 1 := by
      dsimp [f, TableRectanglePartition.leftIndicator, TableRectanglePartition.rightIndicator]
      split_ifs <;> norm_num
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right
      ((mul_le_mul hprob hf (abs_nonneg _) he).trans_eq (mul_one e)) (abs_nonneg _)
  rw [supported_answer_table_pairing hn hm p z V hV]
  have hre :
      uavg (fun M => uavg (fun x => uavg (fun y =>
        (densityWeight F (n*n) (dot x.1.val y.1.val * dot x.2.val y.2.val))⁻¹ *
          p.leftIndicator z M x * p.rightIndicator z M y * A M x y))) -
        (fieldCard F : ℝ)⁻¹ * uavg (fun M => uavg (fun x => uavg (fun y => f M x y * A M x y))) =
      uavg (fun M => uavg (fun x => uavg (fun y =>
        ((densityWeight F (n*n) (dot x.1.val y.1.val * dot x.2.val y.2.val))⁻¹ -
          (fieldCard F : ℝ)⁻¹) * f M x y * A M x y))) := by
    simp only [sub_mul, mul_assoc, uavg_sub, uavg_const_mul]
    congr 1
    apply uavg_congr
    intro M
    apply uavg_congr
    intro x
    apply uavg_congr
    intro y
    dsimp [f]
    ring
  rw [hre]
  calc
    _ ≤ uavg (fun M => uavg (fun x => uavg (fun y => e * |A M x y|))) := by
      refine (abs_uavg_le_uavg_abs _).trans (uavg_mono (fun M => ?_))
      refine (abs_uavg_le_uavg_abs _).trans (uavg_mono (fun x => ?_))
      exact (abs_uavg_le_uavg_abs _).trans (uavg_mono (hp M x))
    _ = e * uavg (fun M => uavg (fun x => uavg (fun y => |A M x y|))) := by
      simp only [uavg_const_mul]
    _ ≤ e * Real.sqrt (((fieldCard F : ℝ)+1)*H) :=
      mul_le_mul_of_nonneg_left (tensor_graph_abs_mean hn hm V H henergy) he
    _ = _ := by dsimp [e]; ring

end

end CircuitCompiler
