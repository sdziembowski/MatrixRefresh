import Proofs.Compiler.GateApproximation.MatrixPhase.EncodingSampling
import Proofs.Compiler.Foundations.Sampling.GaussianAlgebraCost
import Proofs.Compiler.GateApproximation.Shortening.RectangularUnboundedSampling
import Proofs.Compiler.Foundations.Sampling.UnboundedSamplingCost
import Proofs.Compiler.Construction.Parameters



/-!
# Encoding initialization from raw uniform field entries

Each proposal is two raw vectors. The explicit predicate checks that both vectors are nonzero and that their inner product equals the requested value. The actual unbounded rejection tape returns exactly the manuscript's uniform encoding distribution. Its counted arithmetic and number of sampled field coordinates have polynomial expectation.
-/
set_option autoImplicit false

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace CircuitCompiler.Sampling.RawEncoding

open Refresh MatrixRefresh Unbounded Rectangular.Gaussian

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F; x ∈ {x ∈ Raw(F, n) | accept(s, x) = true}, assume 2 ≤ n. Then

returned(s, x) = acceptedEquiv(s, x).
-/
@[simp] theorem returned_accepted {n : ℕ} (hn : 2 ≤ n) (s : F)
    (x : {x : Raw F n // accept s x = true}) :
    returned hn s x.val = acceptedEquiv s x := by
  simp only [returned,dif_pos x.property,acceptedEquiv,Equiv.coe_fn_mk]

/-- The returned valid encoding is exactly uniform, without truncating retries. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/- Mathematical statement (normal notation): For n ≥ 2, repeat independent uniform raw-pair proposals until L ≠ 0, R ≠ 0, and L · R = s. The returned encoding has exactly the uniform distribution μₛ on {(L,R) ∈ (Fⁿ ∖ {0})²:L · R = s}. The statement concerns the actual unbounded stopped tape, with every rejected proposal retained in the sampling experiment. -/
theorem returned_uniform {n : ℕ} (hn : 2 ≤ n) (s : F) :
    letI := fiber_nonempty F n hn s
    (tapeDistribution hn s).map (fun tape => returned hn s tape.2.2) =
      toPMF (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s)) := by
  letI := fiber_nonempty F n hn s
  letI : Nonempty {x : Raw F n // accept s x = true} :=
    ⟨(acceptedEquiv s).symm (Classical.choice (fiber_nonempty F n hn s))⟩
  change (distribution FiniteDistribution.uniform (accept s) (acceptance_pos hn s)).map
    (returned hn s ∘ (fun tape : StoppedTape (Raw F n) => tape.2.2)) = _
  rw [← PMF.map_comp,last_distribution]
  rw [accepted_uniform]
  simp only [toPMF_map,PMF.map_comp,Function.comp_def,returned_accepted]
  rw [← toPMF_map,Rectangular.uniform_equiv (acceptedEquiv s)]

/-- On the common state carrier the actual initialization distribution is `mu_s`. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, assume 2 ≤ n. Then

(((tape ↦ returned(s, ((tape)₂)₂)))_*tapeDistribution(s)) = toPMF(μₛ).
-/
theorem returned_mu {n : ℕ} (hn : 2 ≤ n) (s : F) :
    (tapeDistribution hn s).map (fun tape => (returned hn s tape.2.2).val) = toPMF (mu F n hn s) := by
  letI := fiber_nonempty F n hn s
  change (tapeDistribution hn s).map
    (Subtype.val ∘ (fun tape : StoppedTape (Raw F n) => returned hn s tape.2.2)) = _
  rw [← PMF.map_comp,returned_uniform]
  exact (toPMF_map (FiniteDistribution.uniform : FiniteDistribution (Fiber F n s)) Subtype.val).symm

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F; x ∈ Raw(F, n), we have

value(proposal(s, x)) = accept(s, x).
-/
@[simp] theorem proposal_value {n : ℕ} (s : F) (x : Raw F n) :
    (proposal s x).value = accept s x := by
  apply Bool.eq_iff_iff.mpr
  simp only [proposal,Counted.bind,Bool.and_eq_true,scanNonzero_correct,dotData_value,
    get_ofFn,decide_eq_true_eq,accept_iff,← and_assoc]
  rfl

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F; x ∈ Raw(F, n), we have

operations(proposal(s, x)) ≤ 4 · n + 1.
-/
theorem proposal_operations_le {n : ℕ} (s : F) (x : Raw F n) :
    (proposal s x).operations ≤ 4*n+1 := by
  have hl := scanNonzero_operations_le (Vector.ofFn x.1)
  have hr := scanNonzero_operations_le (Vector.ofFn x.2)
  simp only [proposal,Counted.bind,dotData_operations]
  omega

/-- Expected scalar work on the actual unbounded initialization tape. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, assume 2 ≤ n. Then

expectedCost(𝒰_(Raw(F, n)), accept(s), ((x ↦ operations(proposal(s, x))))) ≤ 8 · |F| · (4 · n + 1).
-/
theorem expected_operations_le {n : ℕ} (hn : 2 ≤ n) (s : F) :
    expectedCost (FiniteDistribution.uniform : FiniteDistribution (Raw F n)) (accept s)
      (fun x => ((proposal s x).operations : ℝ)) ≤ 8*(fieldCard F:ℝ)*(4*n+1) := by
  have hp := acceptance_pos hn s
  have h := expectedCost_le _ _ hp (fun x => ((proposal s x).operations : ℝ))
    (4*(n:ℝ)+1) (by positivity) (fun _ => Nat.cast_nonneg _)
    (fun x => by exact_mod_cast proposal_operations_le s x)
  apply h.trans
  apply (div_le_iff₀ hp).mpr
  have hb := acceptance_ge hn s
  have hq := fieldCard_cast_pos (F := F)
  have hm := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ 8*(fieldCard F:ℝ)*(4*n+1))
  have he : (8*(fieldCard F:ℝ)*(4*n+1)) * (8*(fieldCard F:ℝ))⁻¹ = 4*n+1 := by field_simp
  nlinarith [hm]

/-- Each proposal samples exactly `2n` independent field coordinates. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, assume 2 ≤ n. Then

expectedCost(𝒰_(Raw(F, n)), accept(s), ((x₁ ↦ 2 · n))) ≤ 16 · |F| · n.
-/
theorem expected_coordinates_le {n : ℕ} (hn : 2 ≤ n) (s : F) :
    expectedCost (FiniteDistribution.uniform : FiniteDistribution (Raw F n)) (accept s)
      (fun _ => (2*n:ℕ)) ≤ 16*(fieldCard F:ℝ)*n := by
  have hp := acceptance_pos hn s
  have h := expectedCost_le _ _ hp (fun _ => ((2*n:ℕ):ℝ))
    (2*(n:ℝ)) (by positivity) (fun _ => by positivity) (fun _ => by simp)
  apply h.trans
  apply (div_le_iff₀ hp).mpr
  have hb := acceptance_ge hn s
  have hq := fieldCard_cast_pos (F := F)
  have hm := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ 16*(fieldCard F:ℝ)*n)
  have he : (16*(fieldCard F:ℝ)*n) * (8*(fieldCard F:ℝ))⁻¹ = 2*n := by field_simp <;> ring
  nlinarith [hm]

/-- Expected attempts in the exact uncapped initializer, including success. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ F, assume 2 ≤ n. Then

(∑_(k ∈ ℕ) ((k + 1) · toReal(map(tapeDistribution(s))((Sigma)₁, k)))) ≤ 8 · |F|.
-/
theorem expected_attempts_le {n : ℕ} (hn : 2 ≤ n) (s : F) :
    (∑' k : ℕ, ((k:ℝ)+1) * (((tapeDistribution hn s).map Sigma.fst) k).toReal) ≤
      8*(fieldCard F:ℝ) := by
  have h := Unbounded.expected_attempts (FiniteDistribution.uniform : FiniteDistribution (Raw F n))
    (accept s) (acceptance_pos hn s)
  change (∑' k : ℕ, ((k:ℝ)+1) * (((distribution _ _ _).map Sigma.fst) k).toReal) ≤ _
  rw [h.tsum_eq]
  apply (div_le_iff₀ (acceptance_pos hn s)).mpr
  have hb := acceptance_ge hn s
  have hq := fieldCard_cast_pos (F := F)
  have hm := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ 8*(fieldCard F:ℝ))
  have he : (8*(fieldCard F:ℝ))⁻¹ * (8*(fieldCard F:ℝ)) = 1 := inv_mul_cancel₀ (by positivity)
  rw [he] at hm
  simpa [mul_comm] using hm

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ ZMod(2), assume 2 ≤ n. Then

1 / 16 ≤ acceptance(𝒰_(Raw(ZMod(2), n)), accept(s)).
-/
theorem binary_acceptance_ge {n : ℕ} (hn : 2 ≤ n) (s : ZMod 2) :
    (1/16:ℝ) ≤ acceptance (FiniteDistribution.uniform : FiniteDistribution (Raw (ZMod 2) n)) (accept s) := by
  have h := acceptance_ge hn s
  norm_num [fieldCard] at h
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using h

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ ZMod(2), assume 2 ≤ n. Then

expectedCost(𝒰_(Raw(ZMod(2), n)), accept(s), ((x ↦ operations(proposal(s, x))))) ≤ 16 · (4 · n + 1).
-/
theorem binary_expected_operations_le {n : ℕ} (hn : 2 ≤ n) (s : ZMod 2) :
    expectedCost (FiniteDistribution.uniform : FiniteDistribution (Raw (ZMod 2) n)) (accept s)
      (fun x => ((proposal s x).operations : ℝ)) ≤ 16*(4*(n:ℝ)+1) := by
  have h := expected_operations_le hn s
  norm_num [fieldCard] at h
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using h

-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; s ∈ ZMod(2), assume 2 ≤ n. Then

expectedCost(𝒰_(Raw(ZMod(2), n)), accept(s), ((x₁ ↦ 2 · n))) ≤ 32 · n.
-/
theorem binary_expected_coordinates_le {n : ℕ} (hn : 2 ≤ n) (s : ZMod 2) :
    expectedCost (FiniteDistribution.uniform : FiniteDistribution (Raw (ZMod 2) n)) (accept s)
      (fun _ => (2*n:ℕ)) ≤ 32*(n:ℝ) := by
  have h := expected_coordinates_le hn s
  norm_num [fieldCard] at h
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using h

end

end CircuitCompiler.Sampling.RawEncoding
