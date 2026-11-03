import Proofs.Refreshing.JointFreshness
import Proofs.Refreshing.Model

/-!
# Exact transitions of the operational refreshing experiment

These results identify the actual matrix transition distribution with fresh uniform encodings. Conditional leakage kernels are built from normalized restrictions of the real matrix distribution, rather than postulated.
-/

noncomputable section
open scoped Matrix BigOperators ENNReal
namespace RefreshingProof
open Refreshing

/-- Append the current complete answer to the public history. -/
def appendAnswer {leakage i : ℕ} (h : History leakage i) (z : Answer leakage) :
    History leakage (i + 1) := Fin.snoc h z

/-- Refresh while retaining the invariant as part of the type. -/
def refreshEncoding {n : ℕ} {s : Bit} (x : Encoding n s) (M : RefreshMatrix n) :
    Encoding n s := pairRefresh x M

/-- Forgetting the secret invariant from a refreshed encoding gives the ordinary pair-refresh operation. -/
@[simp] theorem refreshEncoding_val {n : ℕ} {s : Bit}
    (x : Encoding n s) (M : RefreshMatrix n) :
    (refreshEncoding x M).val = refresh x.val M := rfl

/-- The exact uniform transition distribution on the invariant fiber. -/
theorem refreshEncoding_distribution {n : ℕ} {s : Bit} [Nonempty (Encoding n s)]
    (x : Encoding n s) :
    (matrixDistribution n).map (refreshEncoding x) = uniformPMF (Encoding n s) := by
  let : Nonempty (PairEncoding Bit (Fin n) s) := ‹Nonempty (Encoding n s)›
  exact uniform_pairRefresh s x

/-- Paper freshness lemma, stated using the actual model's distributions. -/
theorem refresh_distribution_eq_initial {n : ℕ} (hn : 2 ≤ n) (x : State n) :
    (matrixDistribution n).map (refresh x) = initialDistribution hn (secret x) := by
  let x' : Encoding n (secret x) := ⟨x, rfl⟩
  let : Nonempty (Encoding n (secret x)) := encoding_nonempty hn (secret x)
  have h := refreshEncoding_distribution x'
  have h' := congrArg (fun p => p.map Subtype.val) h
  rw [PMF.map_comp] at h'
  exact h'

/-- Every same-secret transition has at least one actual matrix realizing it. -/
theorem transition_nonempty {n : ℕ} {s : Bit} (x y : Encoding n s) :
    ∃ M : RefreshMatrix n, refreshEncoding x M = y := exists_pairRefresh_eq x y

/-- Conditional distribution of matrices given the old and new encodings. -/
def conditionalMatrix {n : ℕ} {s : Bit} (x y : Encoding n s) : PMF (RefreshMatrix n) :=
  (matrixDistribution n).filter {M | refreshEncoding x M = y} (by
    obtain ⟨M, hM⟩ := transition_nonempty x y
    refine ⟨M, hM, ?_⟩
    simp [PMF.mem_support_iff, matrixDistribution])

/-- The paper's probability table at a valid round, as a genuine PMF on answers. -/
def conditionalAnswer {n leakage : ℕ} {s : Bit} (f : LeakageQuery n leakage)
    (x y : Encoding n s) : PMF (Answer leakage) :=
  (conditionalMatrix x y).map (answer f x.val)

/-- Conditional answer probabilities sum to one on every pair of same-secret states, whether or not a particular incoming transcript is reachable. -/
theorem conditionalAnswer_normalized {n leakage : ℕ} {s : Bit}
    (f : LeakageQuery n leakage) (x y : Encoding n s) :
    ∑ z, conditionalAnswer f x y z = 1 := by
  simpa only [tsum_fintype] using (conditionalAnswer f x y).tsum_coe

/-- A normalized restriction to one fiber of an observation. -/
def conditionalValue {α β : Type*} (p : PMF α) (f : α → β)
    (hf : ∀ b, ∃ a, f a = b ∧ p a ≠ 0) (b : β) : PMF α :=
  p.filter {a | f a = b} (by
    obtain ⟨a, ha, hp⟩ := hf b
    exact ⟨a, ha, hp⟩)

/-- The normalizer of that restriction is the exact observed point mass. -/
theorem conditionalValue_normalizer {α β : Type*} (p : PMF α) (f : α → β) (b : β) :
    (∑' a, ({a | f a = b} : Set α).indicator p a) = (p.map f) b := by
  classical
  rw [PMF.map_apply]
  apply tsum_congr
  intro a
  change (if f a = b then p a else 0) = if b = f a then p a else 0
  simp only [eq_comm]

/-- Exact disintegration over a discrete observation with nonempty supported fibers. This follows from normalization and contains no independence hypothesis. -/
theorem bind_conditionalValue {α β : Type*} (p : PMF α) (f : α → β)
    (hf : ∀ b, ∃ a, f a = b ∧ p a ≠ 0) :
    (p.map f).bind (conditionalValue p f hf) = p := by
  classical
  apply PMF.ext
  intro a
  rw [PMF.bind_apply]
  calc
    (∑' b, (p.map f) b * conditionalValue p f hf b a) =
        (p.map f) (f a) * conditionalValue p f hf (f a) a := by
      apply tsum_eq_single (f a)
      intro b hb
      have hnot : a ∉ {a | f a = b} := fun h => hb h.symm
      rw [conditionalValue, PMF.filter_apply_eq_zero_of_notMem _ hnot, mul_zero]
    _ = p a := by
      have hm : (p.map f) (f a) ≠ 0 := by
        obtain ⟨a', ha', hp'⟩ := hf (f a)
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨a', hp', ha'⟩
      rw [conditionalValue, PMF.filter_apply, conditionalValue_normalizer]
      rw [Set.indicator_of_mem (show a ∈ {a' | f a' = f a} from rfl)]
      calc
        (p.map f) (f a) * (p a * ((p.map f) (f a))⁻¹) =
            p a * ((p.map f) (f a) * ((p.map f) (f a))⁻¹) := by ac_rfl
        _ = p a := by rw [ENNReal.mul_inv_cancel hm ((p.map f).apply_ne_top _)]; simp

/-- Pushforwards agree when their observation maps agree throughout the support of the input distribution. -/
theorem pmf_map_eq_of_agree_support {α β : Type*} (p : PMF α) (f g : α → β)
    (h : ∀ a, a ∈ p.support → f a = g a) : p.map f = p.map g := by
  classical
  apply PMF.ext
  intro b
  simp only [PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a ha]

/-- Observing a transition and a leakage answer can be sampled by first sampling the transition, then sampling its exact conditional answer. -/
theorem joint_disintegration {α β γ : Type*} (p : PMF α) (f : α → β) (g : α → γ)
    (hf : ∀ b, ∃ a, f a = b ∧ p a ≠ 0) :
    p.map (fun a => (f a, g a)) =
      (p.map f).bind (fun b => (conditionalValue p f hf b).map (fun a => (b, g a))) := by
  calc
    _ = ((p.map f).bind (conditionalValue p f hf)).map (fun a => (f a, g a)) := by
      rw [bind_conditionalValue]
    _ = (p.map f).bind (fun b =>
        (conditionalValue p f hf b).map (fun a => (f a, g a))) := PMF.map_bind _ _ _
    _ = _ := by
      apply congrArg ((p.map f).bind)
      funext b
      apply pmf_map_eq_of_agree_support
      intro a ha
      have hab : f a = b := (PMF.mem_support_filter_iff _).mp ha |>.1
      exact Prod.ext hab rfl

/-- Exact one-round canonical experiment for the actual refresh: sample the new encoding independently and uniformly, then sample the conditional answer. This keeps the answer correlated with both old and new states. -/
theorem round_joint_distribution {n leakage : ℕ} {s : Bit}
    [Nonempty (Encoding n s)] (f : LeakageQuery n leakage) (x : Encoding n s) :
    (matrixDistribution n).map (fun M => (refreshEncoding x M, answer f x.val M)) =
      (uniformPMF (Encoding n s)).bind (fun y =>
        (conditionalAnswer f x y).map (fun z => (y, z))) := by
  have hf : ∀ y : Encoding n s, ∃ M : RefreshMatrix n,
      refreshEncoding x M = y ∧ matrixDistribution n M ≠ 0 := by
    intro y
    obtain ⟨M, hM⟩ := transition_nonempty x y
    refine ⟨M, hM, ?_⟩
    simp [matrixDistribution]
  have h := joint_disintegration (matrixDistribution n) (refreshEncoding x)
    (answer f x.val) hf
  rw [refreshEncoding_distribution x] at h
  simpa only [conditionalAnswer, conditionalMatrix, conditionalValue, PMF.map_comp,
    Function.comp_def] using h

/-- The canonical one-round replacement remains exact for an arbitrary joint incoming distribution of the current encoding and observed history. In particular, the current state is allowed to be correlated with the history. -/
theorem adaptive_round_distribution {n leakage i : ℕ} {s : Bit}
    [Nonempty (Encoding n s)] (P : PMF (Encoding n s × History leakage i))
    (f : History leakage i → LeakageQuery n leakage) :
    P.bind (fun xh => (matrixDistribution n).map (fun M =>
      (refreshEncoding xh.1 M, appendAnswer xh.2 (answer (f xh.2) xh.1.val M)))) =
    P.bind (fun xh => (uniformPMF (Encoding n s)).bind (fun y =>
      (conditionalAnswer (f xh.2) xh.1 y).map (fun (z : Answer leakage) => (y, appendAnswer xh.2 z)))) := by
  apply congrArg P.bind
  funext xh
  have h := congrArg
    (fun p : PMF (Encoding n s × Answer leakage) =>
      p.map (fun yz => (yz.1, appendAnswer xh.2 yz.2)))
    (round_joint_distribution (f xh.2) xh.1)
  simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def] using h

end RefreshingProof
