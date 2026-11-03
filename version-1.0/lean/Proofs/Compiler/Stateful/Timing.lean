import Proofs.Compiler.Stateful.Resources
import Proofs.Compiler.Stateful.Interaction

/-!
# Physical timing of public-input samplers

Constants occupy the initial public-sampler block. The input bits tagged by invocation t are sampled only at or after its start. This is the link between the source invocation boundary and the prefix accepted by the physical online sampler policy.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Compiler.Stateful
open Compiler.Direct
namespace Schedule
variable {J : Type*} {P U T : ℕ}

/-- Appending a NAND program creates no public sampler tags. -/
theorem appendGates_sampleAt {inputs g : ℕ} (schedule : Schedule J P U T)
    (ports : Fin inputs → Fin (P+U+T)) (program : NandProgram inputs g) :
    (schedule.appendGates ports program).schedule.sampleAt = schedule.sampleAt := by
  induction program with
  | nil => rfl
  | snoc prior left right ih => exact ih

/-- A property of all sampler tags is preserved by appending a public block when it holds for every new tag at every position after the preceding prefix. -/
theorem appendSamples_property (schedule : Schedule J P U T) (property : J → ℕ → Prop)
    (hold : ∀ i tag, schedule.sampleAt i = some tag → property tag i)
    {d : ℕ} (tags : Fin d → J)
    (hnew : ∀ j i, schedule.compile.operations ≤ i → property (tags j) i) :
    ∀ i tag, (schedule.appendSamples tags).sampleAt i = some tag → property tag i := by
  induction d with
  | zero => exact hold
  | succ d ih =>
    intro i tag hi
    by_cases he : i = (schedule.appendSamples (fun j => tags j.castSucc)).compile.operations
    · simp only [appendSamples, sampleAt, if_pos he, Option.some.injEq] at hi
      subst tag
      apply hnew (Fin.last d) i
      have h0 := schedule.compile.count
      have h1 := (schedule.appendSamples (fun j => tags j.castSucc)).compile.count
      omega
    · simp only [appendSamples, sampleAt, if_neg he] at hi
      exact ih (fun j => tags j.castSucc) (fun j i h => hnew j.castSucc i h) i tag hi

/-- Every tag in the initial sampler block belongs to that block. -/
theorem initialSamples_property (property : J → Prop) {d : ℕ} (tags : Fin d → J)
    (htags : ∀ j, property (tags j)) :
    ∀ i tag, (initialSamples (P := P) tags).sampleAt i = some tag → property tag := by
  induction d with
  | zero => intro i tag hi; simp [initialSamples, sampleAt] at hi
  | succ d ih =>
    intro i tag hi
    by_cases he : i = (initialSamples (P := P) (fun j => tags j.castSucc)).compile.operations
    · simp only [initialSamples, sampleAt, if_pos he, Option.some.injEq] at hi
      subst tag
      exact htags (Fin.last d)
    · simp only [initialSamples, sampleAt, if_neg he] at hi
      exact ih (fun j => tags j.castSucc) (fun j => htags j.castSucc) i tag hi
end Schedule

namespace Circuit
variable {m d c g k : ℕ} (circuit : Circuit m d c g k)

/-- The operation count of an invocation prefix is exactly the next invocation's start index. -/
theorem prefix_operations {total done : ℕ} (unrolled : Unrolling circuit total done) :
    unrolled.schedule.compile.operations = startTime c d g done := by
  rw [Schedule.operationCount_eq, publicCount_eq, gateCount_eq]
  unfold startTime
  ring

/-- Every invocation-tagged sampler lies after the leakage prefix on which that invocation's public input is chosen. -/
theorem unroll_sampler_after (total done : ℕ) (h : done ≤ total) :
    ∀ i t j, (circuit.unrollPrefix total done h).schedule.sampleAt i = some (.inr (t,j)) →
      startTime c d g t.val ≤ i := by
  induction done with
  | zero =>
    intro i t j hi
    have hh := Schedule.initialSamples_property (P := m)
      (fun tag : PublicPort c d total => ∃ j : Fin c, tag = .inl j)
      (fun j : Fin c => Sum.inl j) (fun j => ⟨j,rfl⟩) i (.inr (t,j)) hi
    rcases hh with ⟨j,hj⟩
    cases hj
  | succ done ih =>
    intro i t j hi
    let previous := circuit.unrollPrefix total done (by omega)
    have hp : ∀ i tag, previous.schedule.sampleAt i = some tag →
        (∀ t j, tag = .inr (t,j) → startTime c d g t.val ≤ i) := by
      intro i tag he t j ht
      subst tag
      exact ih (by omega) i t j he
    have ha := Schedule.appendSamples_property previous.schedule
      (fun tag i => ∀ t j, tag = .inr (t,j) → startTime c d g t.val ≤ i) hp
      (fun j : Fin d => Sum.inr ((⟨done,by omega⟩ : Fin total),j)) (by
        intro j i hbound t j' he
        have ht : (⟨done,by omega⟩ : Fin total) = t := congrArg Prod.fst (Sum.inr.inj he)
        have hv := congrArg Fin.val ht
        rw [circuit.prefix_operations previous] at hbound
        simpa only [←hv] using hbound)
    change ((previous.schedule.appendSamples _).appendGates _ circuit.program).schedule.sampleAt i = _ at hi
    rw [Schedule.appendGates_sampleAt] at hi
    exact ha i (.inr (t,j)) hi t j rfl
end Circuit
end Compiler.Stateful
