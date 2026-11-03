import Proofs.Refreshing.Model
import Proofs.Refreshing.Freshness
import Proofs.Refreshing.PrescribedEntries
import Proofs.Refreshing.Unrestricted
import Proofs.Refreshing.DoubleTransitivity

/-!
# Prescribing independent linear rows and columns of a binary matrix

Changes of basis are constructed from actual independent families. They give explicit bijections to the coordinate fibers counted in `PrescribedEntries`.
-/

noncomputable section
open scoped BigOperators Matrix ENNReal

namespace RefreshingProof
open Refreshing


/-- Multiplication by two matrix units is a bijection of all binary matrices. -/
def matrixSandwichEquiv {n : ℕ} (P Q : RefreshMatrix n) : BinaryMatrix n ≃ BinaryMatrix n where
  toFun A := (P : BinaryMatrix n) * A * (Q : BinaryMatrix n)
  invFun B := (↑(P⁻¹) : BinaryMatrix n) * B * (↑(Q⁻¹) : BinaryMatrix n)
  left_inv A := by
    calc
      _ = ((↑(P⁻¹) : BinaryMatrix n) * (P : BinaryMatrix n)) * A *
          ((Q : BinaryMatrix n) * (↑(Q⁻¹) : BinaryMatrix n)) := by noncomm_ring
      _ = A := by simp
  right_inv B := by
    calc
      _ = ((P : BinaryMatrix n) * (↑(P⁻¹) : BinaryMatrix n)) * B *
          ((↑(Q⁻¹) : BinaryMatrix n) * (Q : BinaryMatrix n)) := by noncomm_ring
      _ = B := by simp

/-- Invertibility makes the row action injective. -/
theorem vecMul_matrixUnit_injective {n : ℕ} (Q : RefreshMatrix n) :
    Function.Injective (fun z : Refreshing.Vector n => z ᵥ* (Q : BinaryMatrix n)) := by
  intro z w h
  have h' := congrArg (fun t => t ᵥ* (↑(Q⁻¹) : BinaryMatrix n)) h
  simpa using h'

/-- Invertibility makes the column action injective. -/
theorem mulVec_matrixUnit_injective {n : ℕ} (P : RefreshMatrix n) :
    Function.Injective (fun z : Refreshing.Vector n => (P : BinaryMatrix n) *ᵥ z) := by
  intro z w h
  have h' := congrArg (fun t => (↑(P⁻¹) : BinaryMatrix n) *ᵥ t) h
  simpa using h'

/-- Independent row families can be realized as images of standard rows. -/
theorem exists_matrixUnit_vecMul_family {n r : ℕ}
    (a b : Fin r → Refreshing.Vector n)
    (ha : LinearIndependent Bit a) (hb : LinearIndependent Bit b) :
    ∃ P : RefreshMatrix n, ∀ i, a i ᵥ* (P : BinaryMatrix n) = b i := by
  obtain ⟨R, hR⟩ := exists_matrixUnit_mulVec_family a b ha hb
  refine ⟨transposeMatrixUnit R, fun i => ?_⟩
  change a i ᵥ* (R : BinaryMatrix n)ᵀ = b i
  rw [Matrix.vecMul_transpose]
  exact hR i

/-- A subfamily of the standard coordinate vectors is genuinely independent. -/
theorem linearIndependent_standardFamily {n r : ℕ} (e : Fin r ↪ Fin n) :
    LinearIndependent Bit (fun i : Fin r => (Pi.single (e i) 1 : Refreshing.Vector n)) := by
  classical
  have h := (Pi.basisFun Bit (Fin n)).linearIndependent.comp e e.injective
  convert h using 1
  funext i
  exact (Pi.basisFun_apply Bit (Fin n) (e i)).symm

/-- The observed row and column images coincide with those of a witness A₀. -/
def sameLinearObservations {n r c : ℕ} (x : Fin r → Refreshing.Vector n)
    (v : Fin c → Refreshing.Vector n) (A A₀ : BinaryMatrix n) : Prop :=
  (∀ i, x i ᵥ* A = x i ᵥ* A₀) ∧ (∀ j, A *ᵥ v j = A₀ *ᵥ v j)

instance {n r c : ℕ} (x : Fin r → Refreshing.Vector n)
    (v : Fin c → Refreshing.Vector n) (A A₀ : BinaryMatrix n) :
    Decidable (sameLinearObservations x v A A₀) := by
  unfold sameLinearObservations
  infer_instance

/-- Matching selected coordinate rows and selected coordinate columns. -/
def sameCoordinateObservations {n r c : ℕ} (e : Fin r ↪ Fin n) (f : Fin c ↪ Fin n)
    (B B₀ : BinaryMatrix n) : Prop :=
  (∀ i, B.row (e i) = B₀.row (e i)) ∧ (∀ j, B.col (f j) = B₀.col (f j))

instance {n r c : ℕ} (e : Fin r ↪ Fin n) (f : Fin c ↪ Fin n)
    (B B₀ : BinaryMatrix n) : Decidable (sameCoordinateObservations e f B B₀) := by
  unfold sameCoordinateObservations
  infer_instance

/-- The selected transformed row is the original observed row times Q. -/
theorem sandwich_row {n r : ℕ} (e : Fin r ↪ Fin n)
    (x : Fin r → Refreshing.Vector n) (P Q : RefreshMatrix n)
    (hP : ∀ i, (Pi.single (e i) 1 : Refreshing.Vector n) ᵥ* (P : BinaryMatrix n) = x i)
    (A : BinaryMatrix n) (i : Fin r) :
    (matrixSandwichEquiv P Q A).row (e i) = (x i ᵥ* A) ᵥ* (Q : BinaryMatrix n) := by
  change ((P : BinaryMatrix n) * A * (Q : BinaryMatrix n)).row (e i) = _
  calc
    _ = (Pi.single (e i) 1 : Refreshing.Vector n) ᵥ*
        ((P : BinaryMatrix n) * A * (Q : BinaryMatrix n)) :=
      (Matrix.single_one_vecMul _ _).symm
    _ = (((Pi.single (e i) 1 : Refreshing.Vector n) ᵥ* (P : BinaryMatrix n)) ᵥ* A) ᵥ*
        (Q : BinaryMatrix n) := by simp only [Matrix.vecMul_vecMul]
    _ = _ := by rw [hP i]

/-- The selected transformed column is P times the original observed column. -/
theorem sandwich_col {n c : ℕ} (f : Fin c ↪ Fin n)
    (v : Fin c → Refreshing.Vector n) (P Q : RefreshMatrix n)
    (hQ : ∀ j, (Q : BinaryMatrix n) *ᵥ (Pi.single (f j) 1 : Refreshing.Vector n) = v j)
    (A : BinaryMatrix n) (j : Fin c) :
    (matrixSandwichEquiv P Q A).col (f j) = (P : BinaryMatrix n) *ᵥ (A *ᵥ v j) := by
  change ((P : BinaryMatrix n) * A * (Q : BinaryMatrix n)).col (f j) = _
  calc
    _ = ((P : BinaryMatrix n) * A * (Q : BinaryMatrix n)) *ᵥ
        (Pi.single (f j) 1 : Refreshing.Vector n) :=
      (Matrix.mulVec_single_one _ _).symm
    _ = (P : BinaryMatrix n) *ᵥ (A *ᵥ
        ((Q : BinaryMatrix n) *ᵥ (Pi.single (f j) 1 : Refreshing.Vector n))) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = _ := by rw [hQ j]

/-- The actual change of basis transports exactly the prescribed observations. -/
theorem sandwich_observations_iff {n r c : ℕ}
    (e : Fin r ↪ Fin n) (f : Fin c ↪ Fin n)
    (x : Fin r → Refreshing.Vector n) (v : Fin c → Refreshing.Vector n)
    (P Q : RefreshMatrix n)
    (hP : ∀ i, (Pi.single (e i) 1 : Refreshing.Vector n) ᵥ* (P : BinaryMatrix n) = x i)
    (hQ : ∀ j, (Q : BinaryMatrix n) *ᵥ (Pi.single (f j) 1 : Refreshing.Vector n) = v j)
    (A A₀ : BinaryMatrix n) :
    sameLinearObservations x v A A₀ ↔
      sameCoordinateObservations e f (matrixSandwichEquiv P Q A) (matrixSandwichEquiv P Q A₀) := by
  constructor
  · rintro ⟨hrow, hcol⟩
    constructor
    · intro i
      rw [sandwich_row e x P Q hP, sandwich_row e x P Q hP, hrow i]
    · intro j
      rw [sandwich_col f v P Q hQ, sandwich_col f v P Q hQ, hcol j]
  · rintro ⟨hrow, hcol⟩
    constructor
    · intro i
      apply vecMul_matrixUnit_injective Q
      change (x i ᵥ* A) ᵥ* (Q : BinaryMatrix n) = (x i ᵥ* A₀) ᵥ* (Q : BinaryMatrix n)
      rw [← sandwich_row e x P Q hP, ← sandwich_row e x P Q hP]
      exact hrow i
    · intro j
      apply mulVec_matrixUnit_injective P
      change (P : BinaryMatrix n) *ᵥ (A *ᵥ v j) = (P : BinaryMatrix n) *ᵥ (A₀ *ᵥ v j)
      rw [← sandwich_col f v P Q hQ, ← sandwich_col f v P Q hQ]
      exact hcol j

/-- Selected rows and columns are the same as fixing their union of entries. -/
def coordinateObservationsEquiv {n r c : ℕ}
    (e : Fin r ↪ Fin n) (f : Fin c ↪ Fin n) (B₀ : BinaryMatrix n) :
    {B : BinaryMatrix n // sameCoordinateObservations e f B B₀} ≃
      {B : BinaryMatrix n // ∀ i j,
        i ∈ Finset.univ.map e ∨ j ∈ Finset.univ.map f → B i j = B₀ i j} := by
  classical
  apply Equiv.subtypeEquivRight
  intro B
  constructor
  · rintro ⟨hrow, hcol⟩ i j (hi | hj)
    · obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hi
      exact congrFun (hrow k) j
    · obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hj
      exact congrFun (hcol k) i
  · intro h
    constructor
    · intro k
      funext j
      exact h (e k) j (Or.inl (Finset.mem_map.mpr ⟨k, Finset.mem_univ _, rfl⟩))
    · intro k
      funext i
      exact h i (f k) (Or.inr (Finset.mem_map.mpr ⟨k, Finset.mem_univ _, rfl⟩))

/-- Coordinate observation fibers have exactly the expected number of free bits. -/
theorem card_sameCoordinateObservations {n r c : ℕ}
    (e : Fin r ↪ Fin n) (f : Fin c ↪ Fin n) (B₀ : BinaryMatrix n) :
    Fintype.card {B : BinaryMatrix n // sameCoordinateObservations e f B B₀} =
      2 ^ ((n - r) * (n - c)) := by
  classical
  have he : Fintype.card {i : Fin n // i ∉ Finset.univ.map e} = n - r := by
    rw [Fintype.card_subtype_compl (fun i : Fin n => i ∈ Finset.univ.map e)]
    rw [Fintype.card_subtype (fun i : Fin n => i ∈ Finset.univ.map e)]
    simp only [Fintype.card_fin, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.card_map, Finset.card_univ]
  have hf : Fintype.card {j : Fin n // j ∉ Finset.univ.map f} = n - c := by
    rw [Fintype.card_subtype_compl (fun j : Fin n => j ∈ Finset.univ.map f)]
    rw [Fintype.card_subtype (fun j : Fin n => j ∈ Finset.univ.map f)]
    simp only [Fintype.card_fin, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.card_map, Finset.card_univ]
  calc
    _ = Nat.card {B : BinaryMatrix n // sameCoordinateObservations e f B B₀} :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card {B : BinaryMatrix n // ∀ i j,
        i ∈ Finset.univ.map e ∨ j ∈ Finset.univ.map f → B i j = B₀ i j} :=
      Nat.card_congr (coordinateObservationsEquiv e f B₀)
    _ = Nat.card ({i : Fin n // i ∉ Finset.univ.map e} →
        {j : Fin n // j ∉ Finset.univ.map f} → ZMod 2) :=
      Nat.card_congr (fixedRowsColumnsEquiv (Finset.univ.map e) (Finset.univ.map f) B₀)
    _ = _ := by
      rw [Nat.card_fun, Nat.card_fun]
      simp only [Nat.card_eq_fintype_card, ZMod.card, he, hf]
      rw [← pow_mul, mul_comm (n - c) (n - r)]

/-- Any witness fiber of independent row/column observations has exactly 2^((n-r)(n-c)) elements. This is derived by explicit invertible changes of basis. -/
theorem card_sameLinearObservations {n r c : ℕ}
    (x : Fin r → Refreshing.Vector n) (v : Fin c → Refreshing.Vector n)
    (hx : LinearIndependent Bit x) (hv : LinearIndependent Bit v)
    (A₀ : BinaryMatrix n) :
    Fintype.card {A : BinaryMatrix n // sameLinearObservations x v A A₀} =
      2 ^ ((n - r) * (n - c)) := by
  classical
  have hr : r ≤ n := by simpa using hx.fintype_card_le_finrank
  have hc : c ≤ n := by simpa using hv.fintype_card_le_finrank
  let e : Fin r ↪ Fin n := ⟨Fin.castLE hr, Fin.castLE_injective hr⟩
  let f : Fin c ↪ Fin n := ⟨Fin.castLE hc, Fin.castLE_injective hc⟩
  obtain ⟨P, hP⟩ := exists_matrixUnit_vecMul_family
    (fun i : Fin r => (Pi.single (e i) 1 : Refreshing.Vector n)) x
    (linearIndependent_standardFamily e) hx
  obtain ⟨Q, hQ⟩ := exists_matrixUnit_mulVec_family
    (fun j : Fin c => (Pi.single (f j) 1 : Refreshing.Vector n)) v
    (linearIndependent_standardFamily f) hv
  let E := Equiv.subtypeEquiv
    (p := fun A => sameLinearObservations x v A A₀)
    (q := fun B => sameCoordinateObservations e f B (matrixSandwichEquiv P Q A₀))
    (matrixSandwichEquiv P Q) (fun A => sandwich_observations_iff e f x v P Q hP hQ A A₀)
  rw [Fintype.card_congr E]
  exact card_sameCoordinateObservations e f _

/-- Prescribed (not merely equal-to-witness) linear row and column images. -/
def prescribedLinearRowsCols {n r c : ℕ} (x : Fin r → Refreshing.Vector n)
    (v : Fin c → Refreshing.Vector n) (u : Fin r → Refreshing.Vector n)
    (w : Fin c → Refreshing.Vector n) (A : BinaryMatrix n) : Prop :=
  (∀ i, x i ᵥ* A = u i) ∧ (∀ j, A *ᵥ v j = w j)

instance {n r c : ℕ} (x : Fin r → Refreshing.Vector n) (v : Fin c → Refreshing.Vector n)
    (u : Fin r → Refreshing.Vector n) (w : Fin c → Refreshing.Vector n) (A : BinaryMatrix n) :
    Decidable (prescribedLinearRowsCols x v u w A) := by
  unfold prescribedLinearRowsCols
  infer_instance

/-- Pairing compatibility is necessary for every prescribed matrix. -/
theorem prescribedLinearRowsCols_compatible {n r c : ℕ}
    (x : Fin r → Refreshing.Vector n) (v : Fin c → Refreshing.Vector n)
    (u : Fin r → Refreshing.Vector n) (w : Fin c → Refreshing.Vector n)
    (A : BinaryMatrix n) (hA : prescribedLinearRowsCols x v u w A) :
    ∀ i j, u i ⬝ᵥ v j = x i ⬝ᵥ w j := by
  intro i j
  rw [← hA.1 i, ← hA.2 j]
  exact (Matrix.dotProduct_mulVec _ _ _).symm

/-- A nonempty prescribed fiber has the same exact count as its witness fiber. -/
theorem card_prescribedLinearRowsCols_of_witness {n r c : ℕ}
    (x : Fin r → Refreshing.Vector n) (v : Fin c → Refreshing.Vector n)
    (u : Fin r → Refreshing.Vector n) (w : Fin c → Refreshing.Vector n)
    (hx : LinearIndependent Bit x) (hv : LinearIndependent Bit v)
    (A₀ : BinaryMatrix n) (hA₀ : prescribedLinearRowsCols x v u w A₀) :
    Fintype.card {A : BinaryMatrix n // prescribedLinearRowsCols x v u w A} =
      2 ^ ((n - r) * (n - c)) := by
  classical
  have hiff (A : BinaryMatrix n) :
      prescribedLinearRowsCols x v u w A ↔ sameLinearObservations x v A A₀ := by
    constructor
    · rintro ⟨ha, hb⟩
      constructor
      · intro i
        rw [ha i, hA₀.1 i]
      · intro j
        rw [hb j, hA₀.2 j]
    · rintro ⟨ha, hb⟩
      constructor
      · intro i
        rw [ha i, hA₀.1 i]
      · intro j
        rw [hb j, hA₀.2 j]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hiff)]
  exact card_sameLinearObservations x v hx hv A₀

/-- Pairing compatibility is also sufficient for independent row and column families. The witness is explicitly built after the two changes of basis. -/
theorem exists_prescribedLinearRowsCols {n r c : ℕ}
    (x : Fin r → Refreshing.Vector n) (v : Fin c → Refreshing.Vector n)
    (u : Fin r → Refreshing.Vector n) (w : Fin c → Refreshing.Vector n)
    (hx : LinearIndependent Bit x) (hv : LinearIndependent Bit v)
    (hcompat : ∀ i j, u i ⬝ᵥ v j = x i ⬝ᵥ w j) :
    ∃ A : BinaryMatrix n, prescribedLinearRowsCols x v u w A := by
  classical
  have hr : r ≤ n := by simpa using hx.fintype_card_le_finrank
  have hc : c ≤ n := by simpa using hv.fintype_card_le_finrank
  let e : Fin r ↪ Fin n := ⟨Fin.castLE hr, Fin.castLE_injective hr⟩
  let f : Fin c ↪ Fin n := ⟨Fin.castLE hc, Fin.castLE_injective hc⟩
  obtain ⟨P, hP⟩ := exists_matrixUnit_vecMul_family
    (fun i : Fin r => (Pi.single (e i) 1 : Refreshing.Vector n)) x
    (linearIndependent_standardFamily e) hx
  obtain ⟨Q, hQ⟩ := exists_matrixUnit_mulVec_family
    (fun j : Fin c => (Pi.single (f j) 1 : Refreshing.Vector n)) v
    (linearIndependent_standardFamily f) hv
  have hProw (i : Fin r) : (P : BinaryMatrix n).row (e i) = x i := by
    simpa only [Matrix.single_one_vecMul] using hP i
  have hQcol (j : Fin c) : (Q : BinaryMatrix n).col (f j) = v j := by
    simpa only [Matrix.mulVec_single_one] using hQ j
  have hcross (i : Fin r) (j : Fin c) :
      (u i ᵥ* (Q : BinaryMatrix n)) (f j) = ((P : BinaryMatrix n) *ᵥ w j) (e i) := by
    change u i ⬝ᵥ (Q : BinaryMatrix n).col (f j) = (P : BinaryMatrix n).row (e i) ⬝ᵥ w j
    rw [hQcol j, hProw i]
    exact hcompat i j
  let rows := Finset.univ.map e
  let U : Fin n → Refreshing.Vector n :=
    Function.extend e (fun i => u i ᵥ* (Q : BinaryMatrix n)) (fun _ => 0)
  let C : Fin n → Refreshing.Vector n :=
    Function.extend f (fun j => (P : BinaryMatrix n) *ᵥ w j) (fun _ => 0)
  have hU (i : Fin r) : U (e i) = u i ᵥ* (Q : BinaryMatrix n) :=
    e.injective.extend_apply _ _ i
  have hC (j : Fin c) : C (f j) = (P : BinaryMatrix n) *ᵥ w j :=
    f.injective.extend_apply _ _ j
  let B : BinaryMatrix n := fun a b => if a ∈ rows then U a b else C b a
  have hrow (i : Fin r) : B.row (e i) = u i ᵥ* (Q : BinaryMatrix n) := by
    funext b
    have hi : e i ∈ rows := Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
    change (if e i ∈ rows then U (e i) b else C b (e i)) = _
    rw [ite_eq_left hi, hU i]
  have hcol (j : Fin c) : B.col (f j) = (P : BinaryMatrix n) *ᵥ w j := by
    funext a
    by_cases ha : a ∈ rows
    · obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp ha
      exact (congrFun (hrow i) (f j)).trans (hcross i j)
    · change (if a ∈ rows then U a (f j) else C (f j) a) = _
      rw [ite_eq_right ha, hC j]
  let A := (matrixSandwichEquiv P Q).symm B
  refine ⟨A, ?_, ?_⟩
  · intro i
    apply vecMul_matrixUnit_injective Q
    change (x i ᵥ* A) ᵥ* (Q : BinaryMatrix n) = u i ᵥ* (Q : BinaryMatrix n)
    rw [← sandwich_row e x P Q hP]
    simpa only [A, Equiv.apply_symm_apply] using hrow i
  · intro j
    apply mulVec_matrixUnit_injective P
    change (P : BinaryMatrix n) *ᵥ (A *ᵥ v j) = (P : BinaryMatrix n) *ᵥ w j
    rw [← sandwich_col f v P Q hQ]
    simpa only [A, Equiv.apply_symm_apply] using hcol j

/-- Real event mass under an actual finite uniform PMF is its cardinal ratio. -/
theorem uniformPMF_event_mass_real {α : Type*} [Fintype α] [Nonempty α]
    (p : α → Prop) [DecidablePred p] :
    (∑ a : α, if p a then (uniformPMF α a).toReal else 0) =
      (Fintype.card {a // p a} : ℝ) / (Fintype.card α : ℝ) := by
  classical
  calc
    _ = ∑ a ∈ Finset.univ.filter p, (uniformPMF α a).toReal := by rw [Finset.sum_filter]
    _ = ∑ a : {a // p a}, (uniformPMF α a.val).toReal :=
      Finset.sum_subtype _ (by simp) _
    _ = _ := by
      simp only [uniformPMF_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv]

/-- Event probability in the uniform unrestricted binary matrix experiment. -/
def prescribedLinearProbability {n r c : ℕ}
    (x : Fin r → Refreshing.Vector n) (v : Fin c → Refreshing.Vector n)
    (u : Fin r → Refreshing.Vector n) (w : Fin c → Refreshing.Vector n) : ℝ :=
  ∑ A : BinaryMatrix n, if prescribedLinearRowsCols x v u w A then
    (uniformPMF (BinaryMatrix n) A).toReal else 0

/-- Nonempty independent prescriptions have the exact free-coordinate probability. -/
theorem prescribedLinearProbability_of_witness {n r c : ℕ}
    (x : Fin r → Refreshing.Vector n) (v : Fin c → Refreshing.Vector n)
    (u : Fin r → Refreshing.Vector n) (w : Fin c → Refreshing.Vector n)
    (hx : LinearIndependent Bit x) (hv : LinearIndependent Bit v)
    (A₀ : BinaryMatrix n) (hA₀ : prescribedLinearRowsCols x v u w A₀) :
    prescribedLinearProbability x v u w =
      (2 : ℝ) ^ ((n - r) * (n - c)) / (2 : ℝ) ^ (n * n) := by
  unfold prescribedLinearProbability
  rw [uniformPMF_event_mass_real,
    card_prescribedLinearRowsCols_of_witness x v u w hx hv A₀ hA₀,
    Nat.cast_pow, Nat.cast_ofNat, card_binaryMatrix_real]

/-- Rewriting the free-coordinate ratio into the paper's 2^(rc) Q^(-(r+c)). -/
theorem binary_prescription_probability_identity {n r c : ℕ} (hr : r ≤ n) (hc : c ≤ n) :
    (2 : ℝ) ^ ((n - r) * (n - c)) / (2 : ℝ) ^ (n * n) =
      (2 : ℝ) ^ (r * c) / ((2 : ℝ) ^ n) ^ (r + c) := by
  have hexp : (n - r) * (n - c) + n * (r + c) = r * c + n * n := by
    zify [hr, hc]
    ring
  rw [← pow_mul]
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  rw [← pow_add, ← pow_add, hexp]

/-- Exact prescribed-row/column probability for independent families. Pairing compatibility is proved sufficient; otherwise the actual event is empty. -/
theorem prescribedLinearProbability_independent {n r c : ℕ}
    (x : Fin r → Refreshing.Vector n) (v : Fin c → Refreshing.Vector n)
    (u : Fin r → Refreshing.Vector n) (w : Fin c → Refreshing.Vector n)
    (hx : LinearIndependent Bit x) (hv : LinearIndependent Bit v) :
    prescribedLinearProbability x v u w =
      if (∀ i j, u i ⬝ᵥ v j = x i ⬝ᵥ w j) then
        (2 : ℝ) ^ (r * c) / ((2 : ℝ) ^ n) ^ (r + c) else 0 := by
  classical
  split_ifs with hcompat
  · obtain ⟨A₀, hA₀⟩ := exists_prescribedLinearRowsCols x v u w hx hv hcompat
    rw [prescribedLinearProbability_of_witness x v u w hx hv A₀ hA₀]
    exact binary_prescription_probability_identity
      (by simpa using hx.fintype_card_le_finrank) (by simpa using hv.fintype_card_le_finrank)
  · unfold prescribedLinearProbability
    apply Finset.sum_eq_zero
    intro A _
    have hA : ¬ prescribedLinearRowsCols x v u w A :=
      fun h => hcompat (prescribedLinearRowsCols_compatible x v u w A h)
    rw [ite_eq_right hA]

/-- The rank of two nonzero binary vectors is one or two according to equality. -/
def nonzeroPairRank {n : ℕ} (a b : Share n) : ℕ := if a = b then 1 else 2

/-- The rank assigned to two nonzero binary rows equals the dimension of their linear span. -/
theorem nonzeroPairRank_eq_finrank {n : ℕ} (a b : Share n) :
    Module.finrank Bit (Submodule.span Bit (Set.range ![a.val, b.val])) =
      nonzeroPairRank a b := by
  classical
  by_cases hab : a = b
  · subst b
    simp only [nonzeroPairRank, ite_true]
    have hrange : Set.range ![a.val, a.val] = ({a.val} : Set (Refreshing.Vector n)) := by
      ext z
      simp [Set.mem_range, Fin.exists_fin_two, eq_comm]
    rw [hrange]
    exact finrank_span_singleton a.property
  · simp only [nonzeroPairRank, hab, ite_false]
    simpa only [Fintype.card_fin] using
      finrank_span_eq_card (distinct_binary_pair_independent ⟨(a, b), hab⟩)

/-- The span rank of two nonzero binary rows is at most their ambient dimension n. -/
theorem nonzeroPairRank_le_dim {n : ℕ} (a b : Share n) : nonzeroPairRank a b ≤ n := by
  rw [← nonzeroPairRank_eq_finrank]
  simpa using (Submodule.span Bit (Set.range ![a.val, b.val])).finrank_le

/-- A nonzero row pair, possibly repeated, is reduced to its actual independent sublist before applying the count. -/
theorem card_sameNonzeroPairRows {n c : ℕ} (a b : Share n)
    (v : Fin c → Refreshing.Vector n) (hv : LinearIndependent Bit v) (A₀ : BinaryMatrix n) :
    Fintype.card {A : BinaryMatrix n // sameLinearObservations ![a.val, b.val] v A A₀} =
      2 ^ ((n - nonzeroPairRank a b) * (n - c)) := by
  classical
  by_cases hab : a = b
  · subst b
    let E := Equiv.subtypeEquivRight
      (p := fun A : BinaryMatrix n => sameLinearObservations ![a.val, a.val] v A A₀)
      (q := fun A : BinaryMatrix n => sameLinearObservations (fun _ : Fin 1 => a.val) v A A₀)
      (fun A => by simp [sameLinearObservations, Fin.forall_fin_two, Fin.forall_fin_one])
    rw [Fintype.card_congr E]
    simpa only [nonzeroPairRank, ite_true] using
      card_sameLinearObservations (fun _ : Fin 1 => a.val) v
        (linearIndependent_unique_iff.mpr a.property) hv A₀
  · simpa only [nonzeroPairRank, hab, ite_false] using
      card_sameLinearObservations ![a.val, b.val] v
        (distinct_binary_pair_independent ⟨(a, b), hab⟩) hv A₀

/-- The exact witness-fiber count for all four repeated/distinct nonzero pair cases. The ranks are actual span dimensions by `nonzeroPairRank_eq_finrank`. -/
theorem card_sameNonzeroPairs {n : ℕ} (a b c d : Share n) (A₀ : BinaryMatrix n) :
    Fintype.card {A : BinaryMatrix n //
      sameLinearObservations ![a.val, b.val] ![c.val, d.val] A A₀} =
      2 ^ ((n - nonzeroPairRank a b) * (n - nonzeroPairRank c d)) := by
  classical
  by_cases hcd : c = d
  · subst d
    let E := Equiv.subtypeEquivRight
      (p := fun A : BinaryMatrix n => sameLinearObservations ![a.val, b.val] ![c.val, c.val] A A₀)
      (q := fun A : BinaryMatrix n =>
        sameLinearObservations ![a.val, b.val] (fun _ : Fin 1 => c.val) A A₀)
      (fun A => by simp [sameLinearObservations, Fin.forall_fin_two, Fin.forall_fin_one])
    rw [Fintype.card_congr E]
    simpa only [nonzeroPairRank, ite_true] using
      card_sameNonzeroPairRows a b (fun _ : Fin 1 => c.val)
        (linearIndependent_unique_iff.mpr c.property) A₀
  · simpa only [nonzeroPairRank, hcd, ite_false] using
      card_sameNonzeroPairRows a b ![c.val, d.val]
        (distinct_binary_pair_independent ⟨(c, d), hcd⟩) A₀

/-- Without any independence restriction, a prescribed fiber with witness is in bijection with its corresponding equal-observation fiber. -/
def prescribedWitnessEquiv {n r c : ℕ}
    (x : Fin r → Refreshing.Vector n) (v : Fin c → Refreshing.Vector n)
    (u : Fin r → Refreshing.Vector n) (w : Fin c → Refreshing.Vector n)
    (A₀ : BinaryMatrix n) (hA₀ : prescribedLinearRowsCols x v u w A₀) :
    {A : BinaryMatrix n // prescribedLinearRowsCols x v u w A} ≃
      {A : BinaryMatrix n // sameLinearObservations x v A A₀} := by
  apply Equiv.subtypeEquivRight
  intro A
  constructor
  · rintro ⟨ha, hb⟩
    constructor
    · intro i
      rw [ha i, hA₀.1 i]
    · intro j
      rw [hb j, hA₀.2 j]
  · rintro ⟨ha, hb⟩
    constructor
    · intro i
      rw [ha i, hA₀.1 i]
    · intro j
      rw [hb j, hA₀.2 j]

/-- Exact prescribed probability for nonzero pairs in all four rank cases, whenever the event is nonempty. -/
theorem prescribedLinearProbability_nonzeroPairs_of_witness {n : ℕ}
    (a b c d : Share n) (u w : Fin 2 → Refreshing.Vector n)
    (A₀ : BinaryMatrix n)
    (hA₀ : prescribedLinearRowsCols ![a.val, b.val] ![c.val, d.val] u w A₀) :
    prescribedLinearProbability ![a.val, b.val] ![c.val, d.val] u w =
      (2 : ℝ) ^ (nonzeroPairRank a b * nonzeroPairRank c d) /
        ((2 : ℝ) ^ n) ^ (nonzeroPairRank a b + nonzeroPairRank c d) := by
  classical
  unfold prescribedLinearProbability
  rw [uniformPMF_event_mass_real,
    Fintype.card_congr (prescribedWitnessEquiv _ _ u w A₀ hA₀),
    card_sameNonzeroPairs, Nat.cast_pow, Nat.cast_ofNat, card_binaryMatrix_real]
  exact binary_prescription_probability_identity (nonzeroPairRank_le_dim a b)
    (nonzeroPairRank_le_dim c d)

/-- The rank-sensitive upper bound holds without a nonemptiness assumption. Empty prescriptions have probability zero. Signed four-cycle applications use the exact consistency-indicator probability distribution below. -/
theorem prescribedLinearProbability_nonzeroPairs_le {n : ℕ}
    (a b c d : Share n) (u w : Fin 2 → Refreshing.Vector n) :
    prescribedLinearProbability ![a.val, b.val] ![c.val, d.val] u w ≤
      (2 : ℝ) ^ (nonzeroPairRank a b * nonzeroPairRank c d) /
        ((2 : ℝ) ^ n) ^ (nonzeroPairRank a b + nonzeroPairRank c d) := by
  classical
  by_cases h : ∃ A : BinaryMatrix n,
      prescribedLinearRowsCols ![a.val, b.val] ![c.val, d.val] u w A
  · obtain ⟨A₀, hA₀⟩ := h
    exact le_of_eq (prescribedLinearProbability_nonzeroPairs_of_witness a b c d u w A₀ hA₀)
  · have hz : prescribedLinearProbability ![a.val, b.val] ![c.val, d.val] u w = 0 := by
      unfold prescribedLinearProbability
      apply Finset.sum_eq_zero
      intro A _
      have hA : ¬ prescribedLinearRowsCols ![a.val, b.val] ![c.val, d.val] u w A :=
        fun hA => h ⟨A, hA⟩
      rw [ite_eq_right hA]
    rw [hz]
    positivity

/-- All relation and cross-pairing constraints for two nonzero binary rows and columns. For such pairs the only possible nontrivial relation is repetition. -/
def nonzeroPairCompatible {n : ℕ} (a b c d : Share n)
    (u w : Fin 2 → Refreshing.Vector n) : Prop :=
  (a = b → u 0 = u 1) ∧ (c = d → w 0 = w 1) ∧
    ∀ i j, u i ⬝ᵥ (![c.val, d.val] j) = (![a.val, b.val] i) ⬝ᵥ w j

instance {n : ℕ} (a b c d : Share n) (u w : Fin 2 → Refreshing.Vector n) :
    Decidable (nonzeroPairCompatible a b c d u w) := by
  unfold nonzeroPairCompatible
  infer_instance

/-- A matrix realizing the prescribed rows and columns supplies their required compatibility conditions. -/
theorem nonzeroPairCompatible_of_witness {n : ℕ} (a b c d : Share n)
    (u w : Fin 2 → Refreshing.Vector n) (A : BinaryMatrix n)
    (hA : prescribedLinearRowsCols ![a.val, b.val] ![c.val, d.val] u w A) :
    nonzeroPairCompatible a b c d u w := by
  refine ⟨?_, ?_, prescribedLinearRowsCols_compatible _ _ u w A hA⟩
  · intro hab
    have h0 : a.val ᵥ* A = u 0 := by simpa using hA.1 0
    have h1 : b.val ᵥ* A = u 1 := by simpa using hA.1 1
    rw [← h0, ← h1, hab]
  · intro hcd
    have h0 : A *ᵥ c.val = w 0 := by simpa using hA.2 0
    have h1 : A *ᵥ d.val = w 1 := by simpa using hA.2 1
    rw [← h0, ← h1, hcd]

/-- The paper's consistency conditions are sufficient in each of the four rank-one/rank-two cases of nonzero binary pairs. -/
theorem exists_prescribedNonzeroPairs {n : ℕ} (a b c d : Share n)
    (u w : Fin 2 → Refreshing.Vector n) (h : nonzeroPairCompatible a b c d u w) :
    ∃ A : BinaryMatrix n,
      prescribedLinearRowsCols ![a.val, b.val] ![c.val, d.val] u w A := by
  classical
  by_cases hab : a = b <;> by_cases hcd : c = d
  · subst b
    subst d
    have hu := h.1 rfl
    have hw := h.2.1 rfl
    obtain ⟨A, hA⟩ := exists_prescribedLinearRowsCols
      (fun _ : Fin 1 => a.val) (fun _ : Fin 1 => c.val)
      (fun _ : Fin 1 => u 0) (fun _ : Fin 1 => w 0)
      (linearIndependent_unique_iff.mpr a.property)
      (linearIndependent_unique_iff.mpr c.property)
      (fun _ _ => by simpa using h.2.2 0 0)
    refine ⟨A, ?_, ?_⟩
    · intro i
      fin_cases i
      · simpa using hA.1 0
      · change a.val ᵥ* A = u 1
        rw [← hu]
        exact hA.1 0
    · intro j
      fin_cases j
      · simpa using hA.2 0
      · change A *ᵥ c.val = w 1
        rw [← hw]
        exact hA.2 0
  · subst b
    have hu := h.1 rfl
    obtain ⟨A, hA⟩ := exists_prescribedLinearRowsCols
      (fun _ : Fin 1 => a.val) ![c.val, d.val] (fun _ : Fin 1 => u 0) w
      (linearIndependent_unique_iff.mpr a.property)
      (distinct_binary_pair_independent ⟨(c, d), hcd⟩)
      (fun _ j => by simpa using h.2.2 0 j)
    refine ⟨A, ?_, hA.2⟩
    intro i
    fin_cases i
    · simpa using hA.1 0
    · change a.val ᵥ* A = u 1
      rw [← hu]
      exact hA.1 0
  · subst d
    have hw := h.2.1 rfl
    obtain ⟨A, hA⟩ := exists_prescribedLinearRowsCols
      ![a.val, b.val] (fun _ : Fin 1 => c.val) u (fun _ : Fin 1 => w 0)
      (distinct_binary_pair_independent ⟨(a, b), hab⟩)
      (linearIndependent_unique_iff.mpr c.property)
      (fun i _ => by simpa using h.2.2 i 0)
    refine ⟨A, hA.1, ?_⟩
    intro j
    fin_cases j
    · simpa using hA.2 0
    · change A *ᵥ c.val = w 1
      rw [← hw]
      exact hA.2 0
  · exact exists_prescribedLinearRowsCols ![a.val, b.val] ![c.val, d.val] u w
      (distinct_binary_pair_independent ⟨(a, b), hab⟩)
      (distinct_binary_pair_independent ⟨(c, d), hcd⟩) h.2.2

/-- Exact unrestricted prescribed probability for all four nonzero-pair rank cases, with the paper's actual consistency conditions, not a nonemptiness axiom. -/
theorem prescribedLinearProbability_nonzeroPairs {n : ℕ} (a b c d : Share n)
    (u w : Fin 2 → Refreshing.Vector n) :
    prescribedLinearProbability ![a.val, b.val] ![c.val, d.val] u w =
      if nonzeroPairCompatible a b c d u w then
        (2 : ℝ) ^ (nonzeroPairRank a b * nonzeroPairRank c d) /
          ((2 : ℝ) ^ n) ^ (nonzeroPairRank a b + nonzeroPairRank c d) else 0 := by
  classical
  split_ifs with h
  · obtain ⟨A₀, hA₀⟩ := exists_prescribedNonzeroPairs a b c d u w h
    exact prescribedLinearProbability_nonzeroPairs_of_witness a b c d u w A₀ hA₀
  · unfold prescribedLinearProbability
    apply Finset.sum_eq_zero
    intro A _
    have hA : ¬ prescribedLinearRowsCols ![a.val, b.val] ![c.val, d.val] u w A :=
      fun hA => h (nonzeroPairCompatible_of_witness a b c d u w A hA)
    rw [ite_eq_right hA]

end RefreshingProof
