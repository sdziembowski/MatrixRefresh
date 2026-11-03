import Mathlib.Tactic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
open scoped BigOperators Matrix ENNReal

/-! ## Refreshing construction certificates -/

section RefreshingSupport


namespace Refreshing.ModelSupport

/-- Normalization certificate for uniform probability, proved in `Proofs/Refreshing/PublicModel.lean`. -/
def uniform_total (α : Type*) [Fintype α] [Nonempty α] :
    (∑ _ : α, (Fintype.card α : ℝ≥0∞)⁻¹) = 1 := by
  sorry

/-- Nonzeroness certificate for the refreshed left share, proved in `Proofs/Refreshing/PublicModel.lean`. -/
def refreshLeft_ne_zero {n : ℕ} (v : Fin n → ZMod 2) (hv : v ≠ 0)
    (M : (Matrix (Fin n) (Fin n) (ZMod 2))ˣ) :
    v ᵥ* (M : Matrix (Fin n) (Fin n) (ZMod 2)) ≠ 0 := by
  sorry

/-- Nonzeroness certificate for the refreshed right share, proved in `Proofs/Refreshing/PublicModel.lean`. -/
def refreshRight_ne_zero {n : ℕ} (v : Fin n → ZMod 2) (hv : v ≠ 0)
    (M : (Matrix (Fin n) (Fin n) (ZMod 2))ˣ) :
    (↑(M⁻¹) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v ≠ 0 := by
  sorry
end Refreshing.ModelSupport
end RefreshingSupport

noncomputable section RefreshingModel

/-!
# Matrix refreshing and its leakage experiment

Mathematical specification of the encodings, refresh protocol, and leakage experiment. Write 𝔽₂ = ℤ/2ℤ, Uₙ = 𝔽₂ⁿ ∖ {0}, Gₙ = GLₙ(𝔽₂), and Ωₛ = {(ℓ,r) ∈ Uₙ × Uₙ : ℓ · r = s}. The left share is a row and the right share is a column; their arithmetic is over 𝔽₂.

For a fixed secret s, sample X₀ uniformly from Ωₛ and sample each refresh matrix independently and uniformly from Gₙ. A refresh sends (ℓ,r) to (ℓM,M⁻¹r). A deterministic adaptive strategy selects both parties' leakage functions from the preceding public answers, and only the resulting pair of λ-bit outputs is added to the history. The old shares and matrix are then erased.

Lean coordinates are numbered 0,…,n−1. A strategy index i denotes paper round i+1, so it acts on the history of i previous answers. The mathematical parameter λ is named `leakage` in the code. The `encodingWitness` certificate supplies the nonempty encoding space used by `transcriptDistribution`. Encoding nonemptiness is also the first conjunct of `main_theorem`; the comparator checks that theorem and the certificate against independent proofs under `Proofs/Refreshing/`.
-/


namespace Refreshing

/-- The binary field 𝔽₂ = ℤ/2ℤ = {0,1}; addition and multiplication are modulo two. -/
abbrev Bit := ZMod 2

/-- The vector space 𝔽₂ⁿ, represented as functions v : {0,…,n−1} → 𝔽₂. The same coordinate representation is used for left rows and right columns. -/
abbrev Vector (n : ℕ) := Fin n → Bit

/-- The nonzero-share space Uₙ = 𝔽₂ⁿ ∖ {0}. A share consists of a vector v together with the condition v ≠ 0. -/
abbrev Share (n : ℕ) := {v : Vector n // v ≠ 0}

/-- The joint state space Uₙ × Uₙ. A state x = (ℓ,r) stores a nonzero left row ℓ and a nonzero right column r; it does not include the refresh matrix or public history. -/
abbrev State (n : ℕ) := Share n × Share n

/-- The general linear group Gₙ = GLₙ(𝔽₂), consisting of all invertible n × n binary matrices. Every M ∈ Gₙ has an inverse M⁻¹ satisfying MM⁻¹ = M⁻¹M = I. -/
abbrev RefreshMatrix (n : ℕ) := (Matrix (Fin n) (Fin n) Bit)ˣ

/-- The secret encoded by x = (ℓ,r) is secret(x) = ℓ · r = ∑₀≤k<n ℓₖrₖ ∈ 𝔽₂. Thus the stored bit is the parity of the coordinatewise products. -/
def secret {n : ℕ} (x : State n) : Bit := x.1.val ⬝ᵥ x.2.val

/-- The secret fiber Ωₛ = {(ℓ,r) ∈ Uₙ × Uₙ : ℓ · r = s}. Membership requires both shares to be nonzero and their inner product to equal the specified secret s ∈ 𝔽₂. -/
abbrev Encoding (n : ℕ) (s : Bit) := {x : State n // secret x = s}

/-- The group Gₙ is finite because it is a subset of the 2^(n²) binary n × n matrices. This instance makes its cardinality and finite sums over refresh matrices available. -/
instance (n : ℕ) : Fintype (RefreshMatrix n) := Fintype.ofFinite _

/-- The left-share update is ℓ′ = ℓM. Invertibility preserves nonzeroness: ℓM = 0 would imply ℓ = (ℓM)M⁻¹ = 0, contradicting ℓ ∈ Uₙ. -/
def refreshLeft {n : ℕ} (l : Share n) (M : RefreshMatrix n) : Share n :=
  ⟨l.val ᵥ* (M : Matrix _ _ _), ModelSupport.refreshLeft_ne_zero l.val l.property M⟩

/-- The right-share update is r′ = M⁻¹r. Invertibility preserves nonzeroness: M⁻¹r = 0 would imply r = M(M⁻¹r) = 0, contradicting r ∈ Uₙ. -/
def refreshRight {n : ℕ} (r : Share n) (M : RefreshMatrix n) : Share n :=
  ⟨(↑(M⁻¹) : Matrix _ _ _) *ᵥ r.val, ModelSupport.refreshRight_ne_zero r.val r.property M⟩

/-- For x = (ℓ,r), the refresh map is R(M,x) = (ℓM,M⁻¹r). It preserves the encoded bit because (ℓM) · (M⁻¹r) = ℓ · r; the next private state consists only of these two new shares. -/
def refresh {n : ℕ} (x : State n) (M : RefreshMatrix n) : State n :=
  (refreshLeft x.1 M, refreshRight x.2 M)


/-- Nonempty encoding certificate when `n ≥ 2`, proved in `Proofs/Refreshing/PublicModel.lean`. -/
def encodingWitness {n : ℕ} (hn : 2 ≤ n) (s : Bit) :
    Nonempty (Encoding n s) := by
  sorry

/-- One party's leakage alphabet is B(λ) = {0,1}^λ, the set of strings of exactly λ bits. For λ = 0 this is the singleton containing the empty string. -/
abbrev LeakageOutput (leakage : ℕ) := Fin leakage → Bool

/-- The complete-answer alphabet is 𝒵(λ) = B(λ) × B(λ) = {0,1}^λ × {0,1}^λ. One answer z = (zᴸ,zᴿ) contains the left and right leakage strings, for a total of 2λ bits. -/
abbrev Answer (leakage : ℕ) := LeakageOutput leakage × LeakageOutput leakage

/-- The formal history space after i rounds is ℋᵢ = 𝒵(λ)^i. A history is Hᵢ = (Z₁,…,Zᵢ), and H₀ is the empty sequence. This space includes all sequences of i answers, even those with probability zero in the actual experiment. -/
abbrev History (leakage i : ℕ) := Fin i → Answer leakage

/-- A leakage query is a pair f = (fᴸ,fᴿ) with fᴸ,fᴿ : Uₙ × Gₙ → B(λ). The left function receives (ℓ,M), the right function receives (r,M), and these inputs also determine the corresponding new share. Both functions are chosen together before either current output is known, and both can read the same entire matrix M. -/
abbrev LeakageQuery (n leakage : ℕ) :=
  (Share n → RefreshMatrix n → LeakageOutput leakage) ×
  (Share n → RefreshMatrix n → LeakageOutput leakage)

/-- A deterministic adaptive strategy is a family A = (Aᵢ)₀≤ᵢ<T with Aᵢ : ℋᵢ → ((Uₙ × Gₙ → B(λ)) × (Uₙ × Gₙ → B(λ))). Thus Aᵢ(Hᵢ) selects both leakage functions for round i+1 using only earlier answers. The strategy is defined on all formal histories and has no secret input; the same A is used in both secret experiments. -/
abbrev Strategy (n T leakage : ℕ) := (i : Fin T) → History leakage i.val → LeakageQuery n leakage

/-- The public answer to query f = (fᴸ,fᴿ), old state x = (ℓ,r), and matrix M is z = (fᴸ(ℓ,M),fᴿ(r,M)) ∈ 𝒵(λ). Both functions see their old share; the matrix is not separately disclosed. -/
def answer {n leakage : ℕ} (f : LeakageQuery n leakage) (x : State n)
    (M : RefreshMatrix n) : Answer leakage := (f.1 x.1 M, f.2 x.2 M)

/-- Deterministic execution with fixed initial state and presampled matrices. Start with (X₀,H₀) = (x₀,ε). For 0 ≤ i < T, let Mᵢ₊₁ = matrices(i) and fᵢ = Aᵢ(Hᵢ); then Zᵢ₊₁ = answer(fᵢ,Xᵢ,Mᵢ₊₁), Xᵢ₊₁ = R(Mᵢ₊₁,Xᵢ), and Hᵢ₊₁ = Hᵢ ∥ Zᵢ₊₁, where ε is the empty history and ∥ appends an answer. The result at prefix length i is (Xᵢ,Hᵢ). Only the refreshed state and accumulated answers are retained. -/
def runPrefix {n T leakage : ℕ} (A : Strategy n T leakage) (x₀ : State n)
    (matrices : Fin T → RefreshMatrix n) :
    (i : ℕ) → i ≤ T → State n × History leakage i
  | 0, _ => (x₀, Fin.elim0)
  | i + 1, hi =>
    let previous := runPrefix A x₀ matrices i (Nat.le_of_succ_le hi)
    let round : Fin T := ⟨i, Nat.lt_of_succ_le hi⟩
    let M := matrices round
    let z := answer (A round previous.2) previous.1 M
    (refresh previous.1 M, Fin.snoc previous.2 z)

/-- The sample space of physical randomness is Coins(n,T,s) = Ωₛ × Gₙᵀ. Its uniform distribution samples the initial encoding X₀ ∼ μₛ and all T refresh matrices independently, with each matrix distributed as Unif(Gₙ). Sampling the matrices in advance gives the same experiment as drawing a fresh independent matrix in every round. -/
abbrev Coins (n T : ℕ) (s : Bit) := Encoding n s × (Fin T → RefreshMatrix n)

/-- The transcript map τ(A,ω) = (Zᵢ)₁≤ᵢ≤T returns the complete history of all T answers produced from coins ω ∈ Ωₛ × Gₙᵀ. Neither the initial state nor the final state is included in the adversary's view. -/
def transcript {n T leakage : ℕ} (A : Strategy n T leakage) {s : Bit}
    (coins : Coins n T s) : History leakage T :=
  (runPrefix A coins.1.val coins.2 T le_rfl).2

/-- For a fixed strategy A and secret s, the transcript distribution is Pₛᵀ(h) = Pr[τ(A,ω) = h], with ω uniform on Ωₛ × Gₙᵀ. Equivalently, Pₛᵀ(h) = |{ω ∈ Ωₛ × Gₙᵀ : τ(A,ω) = h}| / (|Ωₛ| · |Gₙ|ᵀ). This is the distribution of the actual execution, without any security, freshness, or hybrid-experiment assumption. -/
def transcriptDistribution {n T leakage : ℕ} (hn : 2 ≤ n)
    (A : Strategy n T leakage) (s : Bit) : PMF (History leakage T) :=
  letI := encodingWitness hn s
  (PMF.ofFintype (fun _ : Coins n T s => (Fintype.card (Coins n T s) : ℝ≥0∞)⁻¹)
    (ModelSupport.uniform_total (Coins n T s))).map (transcript A)

/-- Finite statistical distance, also called total variation distance: δ(P,Q) = ½ · ∑ₐ∈α |P(a) − Q(a)|. The sum is over all outcomes without dividing by |α|; equivalently, δ(P,Q) = max { |P(E) − Q(E)| : E ⊆ α }, the greatest distinguishing advantage of a Boolean test. -/
def statisticalDistance {α : Type*} [Fintype α] (P Q : PMF α) : ℝ :=
  (1 / 2 : ℝ) * ∑ a, |(P a).toReal - (Q a).toReal|

end Refreshing

end RefreshingModel

/-! ## The continual-refreshing theorem -/
section RefreshingMainTheorem
set_option autoImplicit false
namespace Refreshing
theorem main_theorem :
    (∀ {n : ℕ} (hn : 2 ≤ n) (s : Bit), Nonempty (Encoding n s)) ∧
    (∃ C C' : ℝ, 1 ≤ C ∧ 1 ≤ C' ∧
      ∀ (n T leakage : ℕ) (hn : 2 ≤ n),
        C * (T : ℝ) * (((2 ^ (2 * leakage) : ℕ) : ℝ) ^ 3) *
            Real.rpow (((2 ^ n - 1 : ℕ) : ℝ)) (-(1 / 9 : ℝ)) ≤
          C' * (T : ℝ) *
            Real.rpow ((2 : ℕ) : ℝ) (((6 : ℕ) : ℝ) * (leakage : ℝ) - (n : ℝ) / 9) ∧
        (∀ A : Strategy n T leakage,
          statisticalDistance (transcriptDistribution hn A 0)
            (transcriptDistribution hn A 1) ≤
              C * (T : ℝ) * (((2 ^ (2 * leakage) : ℕ) : ℝ) ^ 3) *
                Real.rpow (((2 ^ n - 1 : ℕ) : ℝ)) (-(1 / 9 : ℝ)))) := by
  sorry
end Refreshing
end RefreshingMainTheorem
