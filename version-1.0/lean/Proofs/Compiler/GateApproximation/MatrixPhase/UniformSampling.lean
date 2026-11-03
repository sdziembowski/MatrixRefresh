import Proofs.Compiler.GateApproximation.MatrixPhase.RejectionSampling
import Proofs.Compiler.Construction.Parameters
import Proofs.Compiler.Foundations.MatrixRefreshing.Counting.InvertibilityCount



/-!
# Concrete uniform rejection samplers

Uniform proposals conditioned on a decidable predicate have the uniform distribution on its satisfying inputs. In particular, rejection by the determinant gives uniform invertible matrices, with acceptance probability at least one quarter.
-/

set_option autoImplicit false

open scoped BigOperators

namespace CircuitCompiler.Sampling

open Refresh

variable {α : Type*} [Fintype α] [Nonempty α]

section Matrix

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

instance invertibleNonempty (n : ℕ) :
    Nonempty {M : Matrix (Fin n) (Fin n) F // invertibleTest M = true} :=
  ⟨invertibleEquiv n 1⟩

omit [Nonempty α] in
/-- A capped concrete matrix sampler has error at most `(3/4)^attempts`. -/
-- Auxiliary lemma (sampling and runtime details); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n, attempts ∈ ℕ; observe ∈ F^({0,…,n−1} × {0,…,n−1}) → α, we have

δ((((tape ↦ observe(sample(invertibleTest, 1, attempts, tape))))_*tapeDistribution(𝒰_(F^({0,…,n−1} × {0,…,n−1})), attempts)), (observe_*(Subtype_*𝒰_({M ∈ F^({0,…,n−1} × {0,…,n−1}) | invertibleTest(M) = true})))) ≤ (3 / 4)^attempts.
-/
theorem matrix_sample_distance (n attempts : ℕ)
    (observe : Matrix (Fin n) (Fin n) F → α) :
    statisticalDistance
      ((tapeDistribution (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin n) (Fin n) F)) attempts).map
        (fun tape => observe (sample invertibleTest 1 attempts tape)))
      (((FiniteDistribution.uniform : FiniteDistribution {M : Matrix (Fin n) (Fin n) F //
        invertibleTest M = true}).map Subtype.val).map observe) ≤
      (3 / 4 : ℝ) ^ attempts := by
  have hp : 0 < acceptance
      (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin n) (Fin n) F)) invertibleTest :=
    lt_of_lt_of_le (by norm_num) (matrix_acceptance_ge_quarter n)
  rw [← accepted_uniform invertibleTest hp,
    show (fun tape => observe (sample invertibleTest 1 attempts tape)) =
      observe ∘ sample invertibleTest 1 attempts from rfl,
    ← FiniteDistribution.map_map, sample_distribution]
  have h := capped_distance_le_of_acceptance
    (FiniteDistribution.uniform : FiniteDistribution (Matrix (Fin n) (Fin n) F))
    invertibleTest (FiniteDistribution.pure 1) (by norm_num : (0 : ℝ) < 1 / 4)
    (matrix_acceptance_ge_quarter n) attempts
  exact (statisticalDistance_map_le _ _ _).trans (by norm_num at h ⊢; exact h)

end Matrix

end CircuitCompiler.Sampling
