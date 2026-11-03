import Proofs.Compiler.Construction.Parameters
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Direct binary parameter conversion

The paper bounds the error by 10⁶ S K⁹ q⁻¹⁄²⁷. Here q = 2ⁿ−1 is at least 2ⁿ⁻¹, while K⁹ = 2¹⁸λ. These two scalar identities give the binary rate directly, without an intermediate compiler or a weaker exponent.
-/

set_option autoImplicit false
noncomputable section
namespace CompilerProof.Direct
open Compiler

/-- Nonzero n-bit shares occupy at least half of the full vector space when n ≥ 2. -/
theorem half_space_le_q {n : ℕ} (hn : 2 ≤ n) : 2^(n-1) ≤ q n := by
  have hp : 1 ≤ 2^(n-1) := Nat.one_le_pow _ _ (by omega)
  have he : n = (n-1)+1 := by omega
  unfold q
  conv_rhs => rw [he, pow_succ]
  omega

/-- The nonzero-share decay obeys q(n)^(−1/27) ≤ 2 · 2^(−n/27), for n ≥ 2. -/
theorem q_decay_bound {n : ℕ} (hn : 2 ≤ n) :
    (q n : ℝ) ^ (-1 / 27 : ℝ) ≤
      2 * (2 : ℝ) ^ (-(n : ℝ) / 27) := by
  have hbase : (0 : ℝ) < 2 ^ (n - 1) := by positivity
  have hq : (2 : ℝ) ^ (n - 1) ≤ (q n : ℝ) := by
    exact_mod_cast half_space_le_q hn
  have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  calc
    (q n : ℝ) ^ (-1 / 27 : ℝ) ≤
        ((2 : ℝ) ^ (n - 1)) ^ (-1 / 27 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hbase hq (by norm_num)
    _ = (2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) * (-1 / 27 : ℝ)) := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ (1 + (-(n : ℝ) / 27)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      rw [hc]
      linarith
    _ = 2 * (2 : ℝ) ^ (-(n : ℝ) / 27) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]

/-- Raising the joint answer count to the ninth power gives K(λ)⁹ = 2^(18λ). -/
theorem answer_count_ninth (leakage : ℕ) :
    (K leakage : ℝ) ^ 9 = (2 : ℝ) ^ (18 * (leakage : ℝ)) := by
  rw [K, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
  rw [show 2 * leakage * 9 = 18 * leakage by omega]
  norm_cast

/-- The paper's direct compiler expression is bounded by 2·10⁶ S·2^(18λ−n/27). This is the binary conversion in Eq. (direct-simulation-binary), with no selector estimate. -/
theorem direct_bound_binary {n S leakage : ℕ} (hn : 2 ≤ n) :
    1000000*(S:ℝ)*(K leakage:ℝ)^9*(q n:ℝ)^(-1/27:ℝ) ≤
      2000000*(S:ℝ)*(2:ℝ)^(18*(leakage:ℝ)-(n:ℝ)/27) := by
  calc
    _ ≤ 1000000*(S:ℝ)*(K leakage:ℝ)^9*(2*(2:ℝ)^(-(n:ℝ)/27)) :=
      mul_le_mul_of_nonneg_left (q_decay_bound hn) (by positivity)
    _ = _ := by
      rw [answer_count_ninth, sub_eq_add_neg,
        Real.rpow_add (by norm_num : (0:ℝ) < 2), neg_div]
      ring

end CompilerProof.Direct
