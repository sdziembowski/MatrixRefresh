import Proofs.Compiler.GateApproximation.Shortening.RectangularShortening



/-!
# Counting rejected rectangular-shortening attempts

The kernel of an `n × (n+t)` full-row-rank matrix has exactly `q^t` elements. Invariance under changes of coordinates fixing the long left share then identifies the retry probability for each fixed input pair.
-/
set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace CircuitCompiler.Rectangular

open Refresh

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A right inverse splits a vector into its kernel component and image. -/
/-
Mathematical definition (normal notation): If H · J = I, the maps

v ↦ (v-J · H · v, H · v), (k,r) ↦ k+J · r

are inverse bijections between 𝔽ᵐ and ker H × 𝔽ⁿ.
-/
def kernelImageEquiv {n m : ℕ} (H : Matrix (Fin n) (Fin m) F)
    (J : Matrix (Fin m) (Fin n) F) (hJ : H * J = 1) :
    V F m ≃ ({v : V F m // H.mulVec v = 0} × V F n) where
  toFun v := (⟨v - J.mulVec (H.mulVec v), by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hJ, Matrix.one_mulVec, sub_self]⟩,
    H.mulVec v)
  invFun p := p.1.val + J.mulVec p.2
  left_inv v := sub_add_cancel _ _
  right_inv p := by
    have h : H.mulVec (p.1.val + J.mulVec p.2) = p.2 := by
      rw [Matrix.mulVec_add, p.1.property, Matrix.mulVec_mulVec, hJ,
        Matrix.one_mulVec, zero_add]
    apply Prod.ext
    · apply Subtype.ext
      dsimp
      rw [h]
      exact add_sub_cancel_right _ _
    · exact h

/-- Every full-row-rank rectangular matrix has the expected kernel size. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; H ∈ FullRank(F, n, (n + t)), we have

|{v ∈ V(F, (n + t)) | H.val.mulVec(v) = 0}| = (|F|)ᵗ.
-/
theorem kernel_card {n t : ℕ} (H : FullRank F n (n+t)) :
    Fintype.card {v : V F (n+t) // H.val.mulVec v = 0} = fieldCard F ^ t := by
  classical
  obtain ⟨J,hJ⟩ := H.property
  have hc := Fintype.card_congr (kernelImageEquiv H.val J hJ)
  rw [Fintype.card_prod, vector_card, vector_card, pow_add] at hc
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (fieldCard_pos (F := F)) n)
    (by simpa [Nat.mul_comm] using hc.symm)

/-- Removing the zero vector leaves exactly `q^t-1` rejected right shares. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; H ∈ FullRank(F, n, (n + t)), we have

|{v ∈ U(F, (n + t)) | H.val.mulVec(v) = 0}| = (|F|)ᵗ - 1.
-/
theorem nonzero_kernel_card {n t : ℕ} (H : FullRank F n (n+t)) :
    Fintype.card {v : U F (n+t) // H.val.mulVec v.val = 0} = fieldCard F ^ t - 1 := by
  classical
  let zeroKer : {v : V F (n+t) // H.val.mulVec v = 0} := ⟨0, by simp⟩
  let e : {v : U F (n+t) // H.val.mulVec v.val = 0} ≃
      {v : {v : V F (n+t) // H.val.mulVec v = 0} // v ≠ zeroKer} :=
    { toFun := fun v => ⟨⟨v.val.val,v.property⟩, fun h => v.val.property (congrArg Subtype.val h)⟩
      invFun := fun v => ⟨⟨v.val.val, fun h => v.property (Subtype.ext h)⟩,v.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype_compl, Fintype.card_subtype_eq, kernel_card]

/-- Right changes of coordinates fixing `u` permute the completions of `u`. -/
/- Mathematical definition (normal notation): If an invertible matrix M fixes the long row u, then H ↦ H · M permutes the full-row-rank completions of a · H = u. The inverse multiplies by M⁻¹. -/
def completionRightEquiv {n m : ℕ} (u : U F m) (a : U F n)
    (M : Refresh.«GL» F m) (hu : rowRefresh u M = u) :
    Completion u a ≃ Completion u a where
  toFun H := ⟨⟨H.val.val * M.val, fullRowRank_right H.val M⟩, by
    rw [← Matrix.vecMul_vecMul, H.property]
    exact congrArg Subtype.val hu⟩
  invFun H := ⟨⟨H.val.val * (M⁻¹).val, fullRowRank_right H.val M⁻¹⟩, by
    rw [← Matrix.vecMul_vecMul, H.property]
    have h := congrArg (fun x => rowRefresh x M⁻¹) hu
    simpa [rowRefresh, Matrix.vecMul_vecMul] using congrArg Subtype.val h.symm⟩
  left_inv H := by apply Subtype.ext; apply Subtype.ext; simp [Matrix.mul_assoc]
  right_inv H := by apply Subtype.ext; apply Subtype.ext; simp [Matrix.mul_assoc]

/-- For fixed left shares, equally labelled right shares have equal rejection counts. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, m ∈ ℕ; u ∈ U(F, m); a ∈ U(F, n); v, w ∈ U(F, m), assume (u · v) = (u · w). Then

|{H ∈ Completion(u, a) | H.val.val.mulVec(v) = 0}| = |{H ∈ Completion(u, a) | H.val.val.mulVec(w) = 0}|.
-/
theorem rejection_count_eq {n m : ℕ} (u : U F m) (a : U F n)
    (v w : U F m) (hs : dot u.val v.val = dot u.val w.val) :
    Fintype.card {H : Completion u a // H.val.val.mulVec v.val = 0} =
      Fintype.card {H : Completion u a // H.val.val.mulVec w.val = 0} := by
  classical
  obtain ⟨M,hu,hv⟩ := exists_refresh_fix_row u v w hs
  let e := completionRightEquiv u a M hu
  have hval : M.val.mulVec w.val = v.val := by
    have h := congrArg (fun r : U F m => M.val.mulVec r.val) hv
    simpa [columnRefresh, Matrix.mulVec_mulVec] using h.symm
  apply Fintype.card_congr
  exact e.subtypeEquiv (fun H => by
    change H.val.val.mulVec v.val = 0 ↔ (H.val.val * M.val).mulVec w.val = 0
    rw [← Matrix.mulVec_mulVec, hval])

/-- Double counting a finite incidence relation. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A,B a set; p ∈ A → B → Prop, assume A is finite; B is finite; DecidableRel(p). Then

(∑ₐ (|{b ∈ B | p(a, b)}|)) = ∑_b (|{a ∈ A | p(a, b)}|).
-/
theorem sum_card_fibers_comm {A B : Type*} [Fintype A] [Fintype B]
    (p : A → B → Prop) [DecidableRel p] :
    (∑ a, Fintype.card {b : B // p a b}) =
      ∑ b, Fintype.card {a : A // p a b} := by
  rw [← Fintype.card_sigma, ← Fintype.card_sigma]
  exact Fintype.card_congr
    { toFun := fun x => ⟨x.2.val,⟨x.1,x.2.property⟩⟩
      invFun := fun x => ⟨x.2.val,⟨x.1,x.2.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Count the rejected completions by counting nonzero kernel vectors instead. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; u, v ∈ U(F, (n + t)); a ∈ U(F, n), assume (u · v) = 0. Then

|Completion(u, a)| · ((|F|)ᵗ - 1) = ((|F|)^(n + t − 1) - 1) · |{H ∈ Completion(u, a) | H.val.val.mulVec(v) = 0}|.
-/
theorem rejection_count_identity {n t : ℕ} (u v : U F (n+t)) (a : U F n)
    (hs : dot u.val v.val = 0) :
    Fintype.card (Completion u a) * (fieldCard F ^ t - 1) =
      (fieldCard F ^ (n+t-1) - 1) *
        Fintype.card {H : Completion u a // H.val.val.mulVec v.val = 0} := by
  classical
  let O := {w : U F (n+t) // dot u.val w.val = 0}
  have hH (H : Completion u a) :
      Fintype.card {w : O // H.val.val.mulVec w.val.val = 0} = fieldCard F ^ t - 1 := by
    have hz (w : U F (n+t)) (hw : H.val.val.mulVec w.val = 0) : dot u.val w.val = 0 := by
      rw [← H.property]
      change dotProduct (Matrix.vecMul a.val H.val.val) w.val = 0
      rw [← Matrix.dotProduct_mulVec, hw]
      simp
    let e : {w : O // H.val.val.mulVec w.val.val = 0} ≃
        {w : U F (n+t) // H.val.val.mulVec w.val = 0} :=
      { toFun := fun w => ⟨w.val.val,w.property⟩
        invFun := fun w => ⟨⟨w.val,hz w.val w.property⟩,w.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Fintype.card_congr e).trans (nonzero_kernel_card H.val)
  have hv (w : O) :
      Fintype.card {H : Completion u a // H.val.val.mulVec w.val.val = 0} =
        Fintype.card {H : Completion u a // H.val.val.mulVec v.val = 0} :=
    rejection_count_eq u a w.val v (w.property.trans hs.symm)
  have h := sum_card_fibers_comm (fun (H : Completion u a) (w : O) =>
    H.val.val.mulVec w.val.val = 0)
  simp only [hH,hv,Finset.sum_const,Finset.card_univ,smul_eq_mul] at h
  simpa only [O,nonzero_dot_fiber_card_zero] using h

/-- The number of nonzero right shares with zero inner product is positive. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ, assume 2 ≤ n. Then

0 < (|F|)^(n + t − 1) - 1.
-/
theorem orthogonal_card_pos {n t : ℕ} (hn : 2 ≤ n) : 0 < fieldCard F ^ (n+t-1) - 1 := by
  have hp : 1 < fieldCard F ^ (n+t-1) := one_lt_pow₀ (by have := fieldCard_ge_two (F := F); omega)
    (by omega)
  omega

/-- Exact zero-output probability after fixing the sampled short row. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): Suppose n ≥ 2, u,v ∈ 𝔽ⁿ⁺ᵗ ∖ {0}, and u · v = 0. For any fixed nonzero short row a, a uniformly chosen full-row-rank completion of a · H = u satisfies

Pr[H · v = 0] = (|𝔽|ᵗ-1)/(|𝔽|ⁿ⁺ᵗ⁻¹-1).
-/
theorem completion_rejection_probability {n t : ℕ} (hn : 2 ≤ n)
    (u v : U F (n+t)) (a : U F n) (hs : dot u.val v.val = 0) :
    letI := completion_nonempty u a
    Sampling.acceptance (FiniteDistribution.uniform : FiniteDistribution (Completion u a))
      (fun H => decide (H.val.val.mulVec v.val = 0)) =
      (fieldCard F ^ t - 1 : ℕ) / (fieldCard F ^ (n+t-1) - 1 : ℕ) := by
  classical
  letI := completion_nonempty u a
  rw [Sampling.acceptance_uniform]
  have he : Fintype.card {H : Completion u a // decide (H.val.val.mulVec v.val = 0) = true} =
      Fintype.card {H : Completion u a // H.val.val.mulVec v.val = 0} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => by simp))
  rw [he]
  have hc : (0 : ℝ) < Fintype.card (Completion u a) := by exact_mod_cast Fintype.card_pos
  have hd : (0 : ℝ) < (fieldCard F ^ (n+t-1) - 1 : ℕ) := by
    exact_mod_cast orthogonal_card_pos (F := F) (t := t) hn
  apply (div_eq_div_iff (ne_of_gt hc) (ne_of_gt hd)).2
  have h := rejection_count_identity u v a hs
  exact_mod_cast (by simpa [Nat.mul_comm] using h.symm)

/-- Boolean-event probability is the expectation of its indicator. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For A a set; P ∈ 𝒟(A); b ∈ A → Bool, assume A is finite. Then

Sampling.acceptance(P, b) = 𝔼_(a ← P) [{ 1 if b(a),; 0 otherwise }].
-/
theorem acceptance_eq_expect {A : Type*} [Fintype A] (P : FiniteDistribution A) (b : A → Bool) :
    Sampling.acceptance P b = P.expect (fun a => if b a then 1 else 0) := by
  classical
  unfold Sampling.acceptance FiniteDistribution.expect
  apply Finset.sum_congr rfl
  intro a _
  cases h : b a <;> simp [h]

/-- Exact rejection probability for the sequential sampler, for each fixed long input pair. -/

/- Mathematical statement (normal notation): Let Q = |𝔽|, n ≥ 2, and let the fixed nonzero long shares u,v ∈ 𝔽ⁿ⁺ᵗ satisfy u · v = 0. One shortening attempt is rejected with probability Pr[H · v = 0] = (Qᵗ-1)/(Qⁿ⁺ᵗ⁻¹-1). -/
theorem attempt_rejection_probability {n t : ℕ} (hn : 2 ≤ n)
    (u v : U F (n+t)) (hs : dot u.val v.val = 0) :
    Sampling.acceptance (attemptDistribution hn u) (fun p => decide (rightOutput v p = 0)) =
      (fieldCard F ^ t - 1 : ℕ) / (fieldCard F ^ (n+t-1) - 1 : ℕ) := by
  classical
  letI : Nonempty (U F n) := ⟨unitShare ⟨0,by omega⟩⟩
  letI : ∀ a : U F n, Nonempty (Completion u a) := fun a => completion_nonempty u a
  rw [acceptance_eq_expect, attemptDistribution, MatrixRefresh.expect_map, MatrixRefresh.expect_bind]
  simp only [MatrixRefresh.expect_map]
  have h (a : U F n) := completion_rejection_probability hn u v a hs
  simp only [acceptance_eq_expect] at h
  change (FiniteDistribution.uniform : FiniteDistribution (U F n)).expect
    (fun a => (FiniteDistribution.uniform : FiniteDistribution (Completion u a)).expect
      (fun H => if decide (H.val.val.mulVec v.val = 0) then 1 else 0)) = _
  simp_rw [h]
  exact FiniteDistribution.expect_const _ _

/-- The exact rejection ratio is at most `q^{1-n}`. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ, assume 2 ≤ n. Then

(|F|)ᵗ - 1 / (|F|)^(n + t − 1) - 1 ≤ ((|F|)^(n − 1))⁻¹.
-/
theorem rejection_ratio_le {n t : ℕ} (hn : 2 ≤ n) :
    ((fieldCard F ^ t - 1 : ℕ) : ℝ) / (fieldCard F ^ (n+t-1) - 1 : ℕ) ≤
      (fieldCard F ^ (n-1) : ℝ)⁻¹ := by
  have hq := fieldCard_pos (F := F)
  have hpow : fieldCard F ^ (n+t-1) = fieldCard F ^ t * fieldCard F ^ (n-1) := by
    rw [← pow_add]
    congr 1
    omega
  have ht : 1 ≤ fieldCard F ^ t := Nat.one_le_pow _ _ hq
  have hn' : 1 ≤ fieldCard F ^ (n-1) := Nat.one_le_pow _ _ hq
  have hd : (0 : ℝ) < (fieldCard F ^ (n+t-1) - 1 : ℕ) := by
    exact_mod_cast orthogonal_card_pos (F := F) (t := t) hn
  have hb : (0 : ℝ) < (fieldCard F ^ (n-1) : ℕ) := by exact_mod_cast pow_pos hq (n-1)
  rw [inv_eq_one_div, le_div_iff₀ (by positivity : (0 : ℝ) < (fieldCard F : ℝ) ^ (n-1)),
    div_mul_eq_mul_div]
  apply (div_le_one hd).2
  norm_cast
  rw [hpow, Nat.sub_mul, one_mul]
  omega

/-- The two complementary tests partition an attempt. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; u, v ∈ U(F, (n + t)), assume 2 ≤ n. Then

Sampling.acceptance(attemptDistribution(u), ((p ↦ decide((rightOutput(v, p) ≠ 0))))) = 1 - Sampling.acceptance(attemptDistribution(u), ((p ↦ decide((rightOutput(v, p) = 0))))).
-/
theorem attempt_acceptance_complement {n t : ℕ} (hn : 2 ≤ n) (u v : U F (n+t)) :
    Sampling.acceptance (attemptDistribution hn u) (fun p => decide (rightOutput v p ≠ 0)) =
      1 - Sampling.acceptance (attemptDistribution hn u) (fun p => decide (rightOutput v p = 0)) := by
  classical
  rw [acceptance_eq_expect, acceptance_eq_expect, ← FiniteDistribution.expect_const (attemptDistribution hn u) 1,
    ← MatrixRefresh.expect_sub]
  apply congrArg (attemptDistribution hn u).expect
  funext p
  by_cases h : rightOutput v p = 0 <;> simp [h]

/-- No retries are possible when the encoded field value is nonzero. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; u, v ∈ U(F, (n + t)), assume 2 ≤ n; (u · v) ≠ 0. Then

Sampling.acceptance(attemptDistribution(u), ((p ↦ decide((rightOutput(v, p) = 0))))) = 0.
-/
theorem rejection_zero_of_dot_ne_zero {n t : ℕ} (hn : 2 ≤ n) (u v : U F (n+t))
    (hs : dot u.val v.val ≠ 0) :
    Sampling.acceptance (attemptDistribution hn u) (fun p => decide (rightOutput v p = 0)) = 0 := by
  rw [acceptance_eq_expect]
  simp only [no_rejection_of_dot_ne_zero hs, decide_false, Bool.false_eq_true, if_false]
  exact FiniteDistribution.expect_const _ _

/-- Uniform bound on retry probability, for every plaintext. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; u, v ∈ U(F, (n + t)), assume 2 ≤ n. Then

Sampling.acceptance(attemptDistribution(u), ((p ↦ decide((rightOutput(v, p) = 0))))) ≤ ((|F|)^(n − 1))⁻¹.
-/
theorem attempt_rejection_le {n t : ℕ} (hn : 2 ≤ n) (u v : U F (n+t)) :
    Sampling.acceptance (attemptDistribution hn u) (fun p => decide (rightOutput v p = 0)) ≤
      (fieldCard F ^ (n-1) : ℝ)⁻¹ := by
  by_cases hs : dot u.val v.val = 0
  · rw [attempt_rejection_probability hn u v hs]
    exact rejection_ratio_le hn
  · rw [rejection_zero_of_dot_ne_zero hn u v hs]
    positivity

/-- Every attempt succeeds with probability at least one half, over every field. -/

/- Mathematical statement (normal notation): For every fixed nonzero long input pair (u,v) and n ≥ 2, one shortening attempt succeeds with probability at least 1/2: Pr[H · v ≠ 0] ≥ 1/2. -/
theorem attempt_acceptance_ge_half {n t : ℕ} (hn : 2 ≤ n) (u v : U F (n+t)) :
    (1/2 : ℝ) ≤ Sampling.acceptance (attemptDistribution hn u)
      (fun p => decide (rightOutput v p ≠ 0)) := by
  have h := attempt_rejection_le hn u v
  have hp : (2 : ℝ) ≤ (fieldCard F : ℝ) ^ (n-1) := by
    have : 2 ≤ fieldCard F ^ (n-1) := (fieldCard_ge_two (F := F)).trans
      (by simpa using Nat.pow_le_pow_right (fieldCard_pos (F := F)) (show 1 ≤ n-1 by omega))
    exact_mod_cast this
  have hi : ((fieldCard F : ℝ) ^ (n-1))⁻¹ ≤ (1/2 : ℝ) := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hp
  rw [attempt_acceptance_complement]
  linarith

/-- Binary-field form of the paper's `2/N` retry estimate. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, t ∈ ℕ; u, v ∈ U(F, (n + t)), assume |F| = 2; 2 ≤ n. Then

Sampling.acceptance(attemptDistribution(u), ((p ↦ decide((rightOutput(v, p) = 0))))) ≤ 2 / 2ⁿ.
-/
theorem binary_attempt_rejection_le {n t : ℕ} (hq : fieldCard F = 2) (hn : 2 ≤ n)
    (u v : U F (n+t)) :
    Sampling.acceptance (attemptDistribution hn u) (fun p => decide (rightOutput v p = 0)) ≤
      2 / (2 : ℝ)^n := by
  have h := attempt_rejection_le hn u v
  rw [hq] at h
  have he : (n-1)+1 = n := by omega
  have hp : (2 : ℝ)^n = 2^(n-1)*2 := by rw [← he, pow_succ]; congr 2 <;> omega
  exact h.trans_eq (by norm_num only [Nat.cast_ofNat]; rw [hp]; field_simp)

/-- The square specialization never retries, also on zero plaintext. -/
-- Auxiliary lemma (compiler infrastructure); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; u, v ∈ U(F, (n + 0)), assume 2 ≤ n. Then

Sampling.acceptance(attemptDistribution(u), ((p ↦ decide((rightOutput(v, p) = 0))))) = 0.
-/
theorem square_rejection_zero {n : ℕ} (hn : 2 ≤ n) (u v : U F (n+0)) :
    Sampling.acceptance (attemptDistribution hn u) (fun p => decide (rightOutput v p = 0)) = 0 := by
  by_cases hs : dot u.val v.val = 0
  · rw [attempt_rejection_probability hn u v hs]
    simp
  · exact rejection_zero_of_dot_ne_zero hn u v hs

end

end CircuitCompiler.Rectangular
