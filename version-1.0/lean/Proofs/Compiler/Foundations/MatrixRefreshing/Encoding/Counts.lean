import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Proofs.Compiler.Construction.Parameters
import Proofs.Compiler.Foundations.MatrixRefreshing.Encoding.Notation



/-!
# Exact finite-field inner-product encoding counts

All nonzero rows have the same number of partners for a prescribed secret. The zero secret loses the zero column; every nonzero secret has the full linear-functional fiber. No restriction on the characteristic is used.
-/

set_option autoImplicit false

namespace Refresh

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Pairing the zero vector with any vector gives zero. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; r ∈ V(F, n), we have

(0 · r) = 0.
-/
@[simp] lemma dot_zero_left {n : ℕ} (r : V F n) : dot 0 r = 0 := by
  simp [dot]

/-!
### Uniform marginals
-/

/-- States in the fiber over `s` with prescribed left component correspond to the right components in the `dot l = s` fiber. -/
/- Mathematical definition (normal notation): For fixed s and nonzero ℓ, the encodings of s whose left share is ℓ are in bijection with {r ∈ U:ℓ · r = s}. The bijection reads the right share; its inverse pairs it with ℓ. -/
def leftMarginalEquiv {n : Nat} (s : F) (l : U F n) :
    {x : Fiber F n s // (stateLeftShare x.val) = l} ≃ {r : U F n // dot (l : V F n) (r : V F n) = s} where
  toFun x := ⟨(stateRightShare x.1.1), by
    have h : dot ((stateLeftShare x.1.1) : V F n) ((stateRightShare x.1.1) : V F n) = s := x.1.2
    rw [x.2] at h
    exact h⟩
  invFun r := ⟨⟨⟨l, r.1⟩, r.2⟩, rfl⟩
  left_inv x := by
    obtain ⟨⟨⟨L, R⟩, hx⟩, hL⟩ := x
    cases hL
    rfl
  right_inv _ := rfl

/-- States in the fiber over `s` with prescribed right component correspond to the left components in the `dot r = s` fiber. -/
/- Mathematical definition (normal notation): For fixed s and nonzero r, the encodings of s whose right share is r are in bijection with {ℓ ∈ U:r · ℓ = s}. The bijection reads the left share; its inverse pairs it with r. -/
def rightMarginalEquiv {n : Nat} (s : F) (r : U F n) :
    {x : Fiber F n s // (stateRightShare x.val) = r} ≃ {l : U F n // dot (r : V F n) (l : V F n) = s} where
  toFun x := ⟨(stateLeftShare x.1.1), by
    have h : dot ((stateLeftShare x.1.1) : V F n) ((stateRightShare x.1.1) : V F n) = s := x.1.2
    rw [x.2] at h
    rw [dot_comm]
    exact h⟩
  invFun l := ⟨⟨⟨l.1, r⟩, by
    show dot (l.1 : V F n) (r : V F n) = s
    rw [dot_comm]
    exact l.2⟩, rfl⟩
  left_inv x := by
    obtain ⟨⟨⟨L, R⟩, hx⟩, hR⟩ := x
    cases hR
    rfl
  right_inv _ := rfl

/-- The number of encodings with a fixed left share equals that share’s compatible nonzero right-partner count. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ Nat; s ∈ F; l ∈ U(F, n), we have

|{x ∈ Fiber(F, n, s) | L(x) = l}| = |{r ∈ U(F, n) | (l · r) = s}|.
-/
lemma left_marginal_card {n : Nat} (s : F) (l : U F n) :
    Fintype.card {x : Fiber F n s // (stateLeftShare x.val) = l}
      = Fintype.card {r : U F n // dot (l : V F n) (r : V F n) = s} :=
  Fintype.card_congr (leftMarginalEquiv s l)

/-- The number of encodings with a fixed right share equals that share’s compatible nonzero left-partner count. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ Nat; s ∈ F; r ∈ U(F, n), we have

|{x ∈ Fiber(F, n, s) | R(x) = r}| = |{l ∈ U(F, n) | (r · l) = s}|.
-/
lemma right_marginal_card {n : Nat} (s : F) (r : U F n) :
    Fintype.card {x : Fiber F n s // (stateRightShare x.val) = r}
      = Fintype.card {l : U F n // dot (r : V F n) (l : V F n) = s} :=
  Fintype.card_congr (rightMarginalEquiv s r)

/-- The number of `dot l = s` partners is the same for every nonzero `l`. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ Nat; l ∈ U(F, n); s ∈ F, we have

|{r ∈ U(F, n) | (l · r) = s}| = ({ (|F|)^(n − 1) - 1 if s = 0,; (|F|)^(n − 1) otherwise }).
-/
lemma partner_card_eq {n : Nat} (l : U F n) (s : F) :
    Fintype.card {r : U F n // dot (l : V F n) (r : V F n) = s}
      = (if s = 0 then fieldCard F ^ (n - 1) - 1 else fieldCard F ^ (n - 1)) := by
  by_cases hs : s = 0
  · subst s; simpa using nonzero_dot_fiber_card_zero l
  · simpa [hs] using nonzero_dot_fiber_card_of_ne_zero l s hs

/-!
## Endpoint coordinates and counting

Regrouping a state pair into local endpoints introduces no additional randomness. These equivalences account for the uniform endpoint normalization in the endpoint-distribution estimates.
-/

/-- Identify the named old/new coordinates of `Endpoint F n` with the ordered pair of nonzero shares `U F n × U F n` used directly in the manuscript. -/
/- Mathematical definition (normal notation): The endpoint type is canonically identified with U × U by reading its old and new share coordinates. -/
def endpointEquivProd (F : Type*) [Field F] (n : ℕ) : Endpoint F n ≃ U F n × U F n where
  toFun x := (x.oldShare, x.newShare)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Summing over local endpoints is the same as independently summing over the old share and the new share. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ; f ∈ Endpoint(F, n) → ℝ, we have

∑_(x ∈ Endpoint(F, n)) (f(x)) = ∑_(l ∈ U(F, n)) (∑_(l' ∈ U(F, n)) (f((l, l')))).
-/
theorem sum_endpoint {n : ℕ} (f : Endpoint F n → ℝ) :
    ∑ x : Endpoint F n, f x = ∑ l : U F n, ∑ l' : U F n, f ⟨l, l'⟩ := by
  calc
    _ = ∑ p : U F n × U F n, f ⟨p.1, p.2⟩ :=
      Fintype.sum_equiv (endpointEquivProd F n) _ _ (fun x => by cases x; rfl)
    _ = _ := by rw [Fintype.sum_prod_type]

/-- There are `(shareCard F n)^2` local endpoints, one for each ordered pair of nonzero shares. -/
-- Auxiliary lemma (finite probability and encodings); no direct numbered counterpart in the paper.
/-
Mathematical statement (normal notation): For n ∈ ℕ, we have

|Endpoint(F, n)| = (|F|ⁿ-1)².
-/
theorem endpoint_card (n : ℕ) : Fintype.card (Endpoint F n) = (shareCard F n) ^ 2 := by
  rw [Fintype.card_congr (endpointEquivProd F n)]
  simp only [Fintype.card_prod, nonzero_vector_card, shareCard, vectorCard, pow_two]

end Refresh
