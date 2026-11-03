import Proofs.Refreshing.Canonical

/-!
# Sequential execution from presampled matrix coins

This file relates the specification's tuple of independent matrix coins to the corresponding sequential PMF. It also replaces each real transition by the exact canonical transition proved in `Canonical.lean`.
-/

noncomputable section
open scoped Matrix BigOperators ENNReal
namespace RefreshingProof
open Refreshing

/-- Uniform distributions on two finite spaces sample their components independently. -/
theorem uniformPMF_prod {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] :
    uniformPMF (α × β) =
      (uniformPMF α).bind (fun a => (uniformPMF β).map (fun b => (a, b))) := by
  classical
  apply PMF.ext
  rintro ⟨a, b⟩
  simp [PMF.bind_apply, PMF.map_apply, uniformPMF_apply, Fintype.card_prod,
    ENNReal.mul_inv, tsum_fintype, ite_and]

/-- Uniform distributions are transported by an equivalence of their finite spaces. -/
theorem uniformPMF_map_finiteEquiv {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (e : α ≃ β) :
    (uniformPMF α).map e = uniformPMF β := by
  classical
  apply PMF.ext
  intro b
  simp only [PMF.map_apply, uniformPMF_apply, tsum_fintype]
  rw [← e.symm.sum_comp]
  simp [Fintype.card_congr e]

/-- Append a fresh independent coin to a tuple of preceding coins. -/
theorem uniformPMF_tuple_succ {G : Type*} [Fintype G] [Nonempty G] (i : ℕ) :
    uniformPMF (Fin (i + 1) → G) =
      (uniformPMF (Fin i → G)).bind (fun ms =>
        (uniformPMF G).map (fun M => (Fin.snoc ms M : Fin (i + 1) → G))) := by
  let e : ((Fin i → G) × G) ≃ (Fin (i + 1) → G) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => G))
  rw [← uniformPMF_map_finiteEquiv e, uniformPMF_prod, PMF.map_bind]
  apply congrArg ((uniformPMF (Fin i → G)).bind)
  funext ms
  rw [PMF.map_comp]
  rfl

/-- One operational step, retaining the secret invariant in the state type. -/
def prefixStep {n T leakage : ℕ} {s : Bit} (A : Strategy n T leakage)
    (i : ℕ) (hi : i < T) (xh : Encoding n s × History leakage i)
    (M : RefreshMatrix n) : Encoding n s × History leakage (i + 1) :=
  (refreshEncoding xh.1 M,
    appendAnswer xh.2 (answer (A ⟨i, hi⟩ xh.2) xh.1.val M))

/-- The specification's execution, taking only the coins of its actual prefix instead of a full-length tuple with unused future coins. -/
def runOnPrefix {n T leakage : ℕ} {s : Bit} (A : Strategy n T leakage)
    (x : Encoding n s) : (i : ℕ) → i ≤ T → (Fin i → RefreshMatrix n) →
      Encoding n s × History leakage i
  | 0, _, _ => (x, Fin.elim0)
  | i + 1, hi, ms =>
    prefixStep A i (by omega) (runOnPrefix A x i (by omega) (Fin.init ms))
      (ms (Fin.last i))

/-- The sequential distribution obtained by sampling a new matrix at each actual step. -/
def prefixDistribution {n T leakage : ℕ} {s : Bit} (A : Strategy n T leakage)
    (x : Encoding n s) : (i : ℕ) → i ≤ T → PMF (Encoding n s × History leakage i)
  | 0, _ => PMF.pure (x, Fin.elim0)
  | i + 1, hi => (prefixDistribution A x i (by omega)).bind (fun xh =>
      (matrixDistribution n).map (prefixStep A i (by omega) xh))

/-- Prefix coin execution has exactly the sequential transition distribution. -/
theorem prefixDistribution_eq_presampled {n T leakage : ℕ} {s : Bit}
    (A : Strategy n T leakage) (x : Encoding n s) (i : ℕ) (hi : i ≤ T) :
    prefixDistribution A x i hi =
      (uniformPMF (Fin i → RefreshMatrix n)).map (runOnPrefix A x i hi) := by
  induction i with
  | zero =>
      simp only [prefixDistribution, runOnPrefix]
      exact (PMF.map_const _ _).symm
  | succ i ih =>
      rw [prefixDistribution, ih, PMF.bind_map]
      rw [uniformPMF_tuple_succ, PMF.map_bind]
      apply congrArg ((uniformPMF (Fin i → RefreshMatrix n)).bind)
      funext ms
      rw [PMF.map_comp]
      apply congrArg (fun f => (matrixDistribution n).map f)
      funext M
      simp [runOnPrefix]

/-- Restrict a tuple to precisely its first i matrix coins. -/
def takeMatrixPrefix {n T : ℕ} (ms : Fin T → RefreshMatrix n) (i : ℕ) (hi : i ≤ T) :
    Fin i → RefreshMatrix n := fun j => ms ⟨j.val, lt_of_lt_of_le j.isLt hi⟩

/-- The invariant-typed prefix evaluator is exactly the specification's evaluator after forgetting the invariant proof in the state subtype. -/
theorem runOnPrefix_agrees {n T leakage : ℕ} {s : Bit}
    (A : Strategy n T leakage) (x : Encoding n s) (ms : Fin T → RefreshMatrix n)
    (i : ℕ) (hi : i ≤ T) :
    ((runOnPrefix A x i hi (takeMatrixPrefix ms i hi)).1.val,
      (runOnPrefix A x i hi (takeMatrixPrefix ms i hi)).2) =
      runPrefix A x.val ms i hi := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have hp := ih (by omega)
      simp only [runOnPrefix, prefixStep, refreshEncoding_val, appendAnswer, runPrefix]
      rw [← hp]
      rfl

/-- Complete observed transcripts coincide under the two executors for every individual tuple of physical coins. -/
theorem transcript_eq_runOnPrefix {n T leakage : ℕ} {s : Bit}
    (A : Strategy n T leakage) (coins : Coins n T s) :
    transcript A coins = (runOnPrefix A coins.1 T le_rfl coins.2).2 := by
  have h := runOnPrefix_agrees A coins.1 coins.2 T le_rfl
  exact (congrArg Prod.snd h).symm

/-- The original presampled-coin transcript distribution is the sequential matrix distribution. -/
theorem transcriptDistribution_eq_sequential {n T leakage : ℕ} {s : Bit}
    [Nonempty (Encoding n s)] (hn : 2 ≤ n) (A : Strategy n T leakage) :
    transcriptDistribution hn A s = (uniformPMF (Encoding n s)).bind
      (fun x => (prefixDistribution A x T le_rfl).map Prod.snd) := by
  unfold transcriptDistribution
  change (uniformPMF (Coins n T s)).map (transcript A) = _
  rw [uniformPMF_prod, PMF.map_bind]
  apply congrArg ((uniformPMF (Encoding n s)).bind)
  funext x
  rw [prefixDistribution_eq_presampled]
  simp only [PMF.map_comp]
  apply congrArg (fun f => (uniformPMF (Fin T → RefreshMatrix n)).map f)
  funext ms
  exact transcript_eq_runOnPrefix A (x, ms)

/-- The canonical forward experiment: independently sample a uniform next encoding, then sample its true conditional leakage answer. -/
def canonicalPrefixDistribution {n T leakage : ℕ} {s : Bit}
    [Nonempty (Encoding n s)] (A : Strategy n T leakage) (x : Encoding n s) :
    (i : ℕ) → i ≤ T → PMF (Encoding n s × History leakage i)
  | 0, _ => PMF.pure (x, Fin.elim0)
  | i + 1, hi => (canonicalPrefixDistribution A x i (by omega)).bind (fun xh =>
      (uniformPMF (Encoding n s)).bind (fun y =>
        (conditionalAnswer (A ⟨i, by omega⟩ xh.2) xh.1 y).map
          (fun z => (y, appendAnswer xh.2 z))))

/-- Each prefix of the physical experiment has exactly the canonical distribution. The proof preserves arbitrary correlations with the previously observed history. -/
theorem prefixDistribution_eq_canonical {n T leakage : ℕ} {s : Bit}
    [Nonempty (Encoding n s)] (A : Strategy n T leakage) (x : Encoding n s)
    (i : ℕ) (hi : i ≤ T) :
    prefixDistribution A x i hi = canonicalPrefixDistribution A x i hi := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [prefixDistribution, canonicalPrefixDistribution, ih]
      exact adaptive_round_distribution _ (fun h => A ⟨i, by omega⟩ h)

/-- The complete actual transcript distribution equals the canonical experiment of §4.2: all encodings are freshly sampled independently, and answers are then drawn by their exact conditional kernels in adaptive history order. -/
theorem transcriptDistribution_eq_canonical {n T leakage : ℕ} {s : Bit}
    [Nonempty (Encoding n s)] (hn : 2 ≤ n) (A : Strategy n T leakage) :
    transcriptDistribution hn A s = (uniformPMF (Encoding n s)).bind
      (fun x => (canonicalPrefixDistribution A x T le_rfl).map Prod.snd) := by
  rw [transcriptDistribution_eq_sequential hn A]
  apply congrArg ((uniformPMF (Encoding n s)).bind)
  funext x
  rw [prefixDistribution_eq_canonical]

end RefreshingProof
