import Proofs.Refreshing.Execution
import Proofs.Refreshing.AdaptiveBlock

/-!
# Prefixes, suffixes, and local adaptive windows of the canonical execution

The incoming prefix, preceding leakage factor, and outgoing suffix here are constructed from the actual conditional leakage kernels. The local signed window error remains explicit; its global K³ accounting is derived.
-/

noncomputable section
set_option maxSynthPendingDepth 128
open scoped Matrix BigOperators ENNReal
namespace RefreshingProof
open Refreshing

/-- Prepend one answer to a finite tuple of future answers. -/
def prependAnswer {leakage r : ℕ} (z : Answer leakage) (h : History leakage r) :
    History leakage (r + 1) := Fin.cons z h

/-- Generate precisely r future answers of the real canonical execution. -/
def canonicalSuffix {n T leakage : ℕ} {s : Bit} [Nonempty (Encoding n s)]
    (A : Strategy n T leakage) : (r i : ℕ) → i + r ≤ T →
      Encoding n s → History leakage i → PMF (History leakage r)
  | 0, _, _, _, _ => PMF.pure Fin.elim0
  | r + 1, i, hi, x, h =>
    (uniformPMF (Encoding n s)).bind (fun y =>
      (conditionalAnswer (A ⟨i, by omega⟩ h) x y).bind (fun z =>
        (canonicalSuffix A r (i + 1) (by omega) y (appendAnswer h z)).map
          (prependAnswer z)))

/-- Cast only the length index of a history. -/
def castHistory {leakage i j : ℕ} (hij : i = j) (h : History leakage i) : History leakage j :=
  fun k => h (Fin.cast hij.symm k)

/-- Combine an incoming prefix with the freshly generated future answers. -/
def concatHistory {leakage i j : ℕ} (h : History leakage i) (tail : History leakage j) :
    History leakage (i + j) := Fin.append h tail

/-- Full final-view distribution of the true canonical suffix, from any current state and any formal history, including histories of probability zero. -/
def canonicalTail {n T leakage : ℕ} {s : Bit} [Nonempty (Encoding n s)]
    (A : Strategy n T leakage) (i : ℕ) (hi : i ≤ T)
    (x : Encoding n s) (h : History leakage i) : PMF (History leakage T) :=
  (canonicalSuffix A (T - i) i (by omega) x h).map
    (fun tail => castHistory (by omega : i + (T - i) = T) (concatHistory h tail))

/-- Actual incoming joint distribution of state and history at a canonical prefix. -/
def canonicalPrefix {n T leakage : ℕ} (s : Bit) [Nonempty (Encoding n s)]
    (A : Strategy n T leakage) (i : ℕ) (hi : i ≤ T) :
    PMF (Encoding n s × History leakage i) :=
  (uniformPMF (Encoding n s)).bind (fun x => canonicalPrefixDistribution A x i hi)

/-- A backward continuation returning the entire final history. Its recurrence is convenient when exposing the first round of an unsigned suffix. -/
def canonicalContinuation {n T leakage : ℕ} {s : Bit} [Nonempty (Encoding n s)]
    (A : Strategy n T leakage) (i : ℕ) (hi : i ≤ T)
    (x : Encoding n s) (h : History leakage i) : PMF (History leakage T) :=
  if hlt : i < T then
    (uniformPMF (Encoding n s)).bind (fun y =>
      (conditionalAnswer (A ⟨i, hlt⟩ h) x y).bind (fun z =>
        canonicalContinuation A (i + 1) (by omega) y (appendAnswer h z)))
  else PMF.pure (castHistory (by omega : i = T) h)
termination_by T - i
decreasing_by omega

/-- An unfinished canonical continuation samples a fresh uniform encoding, answers the current conditional query, and continues from the appended history. -/
theorem canonicalContinuation_step {n T leakage : ℕ} {s : Bit}
    [Nonempty (Encoding n s)] (A : Strategy n T leakage) (i : ℕ) (hi : i < T)
    (x : Encoding n s) (h : History leakage i) :
    canonicalContinuation A i (by omega) x h =
      (uniformPMF (Encoding n s)).bind (fun y =>
        (conditionalAnswer (A ⟨i, hi⟩ h) x y).bind (fun z =>
          canonicalContinuation A (i + 1) (by omega) y (appendAnswer h z))) := by
  rw [canonicalContinuation, dite_eq_left hi]

/-- A canonical continuation after the last round returns its existing transcript with probability one. -/
@[simp] theorem canonicalContinuation_terminal {n T leakage : ℕ} {s : Bit}
    [Nonempty (Encoding n s)] (A : Strategy n T leakage)
    (x : Encoding n s) (h : History leakage T) :
    canonicalContinuation A T le_rfl x h = PMF.pure h := by
  rw [canonicalContinuation, dite_eq_right (Nat.lt_irrefl T)]
  rfl

/-- Expose the last true round of an incoming prefix. -/
theorem canonicalPrefix_succ {n T leakage : ℕ} (s : Bit)
    [Nonempty (Encoding n s)] (A : Strategy n T leakage) (i : ℕ) (hi : i + 1 ≤ T) :
    canonicalPrefix s A (i + 1) hi =
      (canonicalPrefix s A i (by omega)).bind (fun xh =>
        (uniformPMF (Encoding n s)).bind (fun y =>
          (conditionalAnswer (A ⟨i, by omega⟩ xh.2) xh.1 y).map
            (fun z => (y, appendAnswer xh.2 z)))) := by
  unfold canonicalPrefix
  rw [PMF.bind_bind]
  rfl

/-- Running a true prefix and then its true continuation is independent of where the execution is cut. -/
def canonicalCutView {n T leakage : ℕ} (s : Bit) [Nonempty (Encoding n s)]
    (A : Strategy n T leakage) (i : ℕ) (hi : i ≤ T) : PMF (History leakage T) :=
  (canonicalPrefix s A i hi).bind (fun xh => canonicalContinuation A i hi xh.1 xh.2)

/-- Advancing the canonical cut by one round leaves its complete transcript distribution unchanged. -/
theorem canonicalCutView_succ {n T leakage : ℕ} (s : Bit)
    [Nonempty (Encoding n s)] (A : Strategy n T leakage) (i : ℕ) (hi : i + 1 ≤ T) :
    canonicalCutView s A (i + 1) hi = canonicalCutView s A i (by omega) := by
  unfold canonicalCutView
  rw [canonicalPrefix_succ, PMF.bind_bind]
  apply congrArg ((canonicalPrefix s A i (by omega)).bind)
  funext xh
  simp only [PMF.bind_bind, PMF.bind_map]
  exact (canonicalContinuation_step A i (by omega) xh.1 xh.2).symm

/-- All cuts describe the complete actual transcript, not merely a separately postulated family of hybrids. -/
theorem canonicalCutView_eq_transcriptDistribution {n T leakage : ℕ} (s : Bit)
    [Nonempty (Encoding n s)] (hn : 2 ≤ n) (A : Strategy n T leakage)
    (i : ℕ) (hi : i ≤ T) :
    canonicalCutView s A i hi = transcriptDistribution hn A s := by
  have hc : ∀ j (hj : j ≤ T),
      canonicalCutView s A j hj = canonicalCutView s A 0 (by omega) := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
        intro hj
        rw [canonicalCutView_succ, ih]
  calc
    _ = canonicalCutView s A T le_rfl := (hc i hi).trans (hc T le_rfl).symm
    _ = transcriptDistribution hn A s := by
      unfold canonicalCutView
      simp only [canonicalContinuation_terminal]
      change (canonicalPrefix s A T le_rfl).map Prod.snd = transcriptDistribution hn A s
      unfold canonicalPrefix
      rw [PMF.map_bind]
      exact (transcriptDistribution_eq_canonical hn A).symm

/-- One global signed table per formal round/history/answer, evaluated on both old and new raw states, including unequal-secret pairs. -/
abbrev SignedTables (n T leakage : ℕ) :=
  (i : Fin T) → History leakage i.val → Answer leakage → State n → State n → ℝ

/-- The manuscript's Q_{k+1}: a real secret-one prefix, one signed cheating round, and a real secret-zero suffix. Endpoints are the actual transcript distributions. -/
def signedHybrid {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (G : SignedTables n T leakage) (k : Fin T) :
    History leakage T → ℝ :=
  fun h => ∑ c : Encoding n (1 : Bit) × History leakage k.val,
    (canonicalPrefix 1 A k.val (by omega) c).toReal *
      ∑ y : Encoding n (0 : Bit), (uniformPMF (Encoding n (0 : Bit)) y).toReal *
        ∑ z : Answer leakage, G k c.2 z c.1.val y.val *
          (canonicalContinuation A (k.val + 1) (by omega) y (appendAnswer c.2 z) h).toReal

/-- The local window's preceding answer followed by its two own answers. -/
def threeAnswerHistory {leakage i : ℕ} (h : History leakage i)
    (z : ThreeAnswers (Answer leakage)) : History leakage (i + 3) :=
  appendAnswer (appendAnswer (appendAnswer h z.1) z.2.1) z.2.2

/-- The fixed answer alphabet has exactly the cardinality K in Theorem 4.1. -/
theorem answer_card_eq_K (leakage : ℕ) : Fintype.card (Answer leakage) = K leakage := by
  simp only [Answer, LeakageOutput, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, K]
  rw [← pow_add]
  congr 1
  omega

/-- The exact global signed error obtained by inserting a two-round local window after one preceding true round of a secret-one prefix, then running the secret-zero suffix. `E` is a local outer-state error after averaging over the window's shared middle state under the prescribed secret-encoding distributions. -/
def canonicalBlockDifference {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (i : ℕ) (hi : i + 3 ≤ T)
    (E : (Encoding n (1 : Bit) × History leakage i) → ThreeAnswers (Answer leakage) →
      Encoding n (1 : Bit) → Encoding n (0 : Bit) → ℝ) : History leakage T → ℝ := by
  letI : Fintype (Encoding n (1 : Bit)) := inferInstance
  letI : Fintype (Encoding n (0 : Bit)) := inferInstance
  letI : Fintype (ThreeAnswers (Answer leakage)) := inferInstance
  letI : Fintype (Encoding n (1 : Bit) × History leakage i) := inferInstance
  exact signedKernelApply
    (blockBaseMass (canonicalPrefix 1 A i (by omega))
      (uniformPMF (Encoding n (1 : Bit))) (uniformPMF (Encoding n (0 : Bit)))
      (fun c a => conditionalAnswer (A ⟨i, by omega⟩ c.2) c.1 a) E)
    (fun v h => (canonicalContinuation A (i + 3) hi v.2.2.2
      (threeAnswerHistory v.1.2 v.2.1) h).toReal)

/-- Actual adaptive K³ accounting. Prefix and suffix normalization and the preceding-factor bound follow from their genuine probability distributions; the only remaining hypothesis is the explicit local per-answer outer-state error. -/
theorem canonicalBlockDifference_l1_le {n T leakage : ℕ}
    [Nonempty (Encoding n (0 : Bit))] [Nonempty (Encoding n (1 : Bit))]
    (A : Strategy n T leakage) (i : ℕ) (hi : i + 3 ≤ T)
    (E : (Encoding n (1 : Bit) × History leakage i) → ThreeAnswers (Answer leakage) →
      Encoding n (1 : Bit) → Encoding n (0 : Bit) → ℝ) (δ : ℝ)
    (hlocal : ∀ c z,
      (∑ a, (uniformPMF (Encoding n (1 : Bit)) a).toReal *
        (∑ b, (uniformPMF (Encoding n (0 : Bit)) b).toReal * |E c z a b|)) ≤ δ) :
    ∑ h, |canonicalBlockDifference A i hi E h| ≤ (K leakage : ℝ) ^ 3 * δ := by
  let : Fintype (Encoding n (1 : Bit)) := inferInstance
  let : Fintype (Encoding n (0 : Bit)) := inferInstance
  let : Fintype (ThreeAnswers (Answer leakage)) := inferInstance
  let : Fintype (Encoding n (1 : Bit) × History leakage i) := inferInstance
  have h := adaptive_block_K3 (canonicalPrefix 1 A i (by omega))
    (uniformPMF (Encoding n (1 : Bit))) (uniformPMF (Encoding n (0 : Bit)))
    (fun c a => conditionalAnswer (A ⟨i, by omega⟩ c.2) c.1 a) E
    (fun v => canonicalContinuation A (i + 3) hi v.2.2.2 (threeAnswerHistory v.1.2 v.2.1)) δ hlocal
  simpa only [canonicalBlockDifference, answer_card_eq_K] using h

end RefreshingProof
