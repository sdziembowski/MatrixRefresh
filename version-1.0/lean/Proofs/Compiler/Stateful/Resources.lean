import Proofs.Compiler.Model
import Proofs.Compiler.Direct.Incidence
import Proofs.Compiler.Direct.Resources

/-!
# Resources of interleaved stateful compilation

An online public sampler has no predecessor and creates one fresh chain endpoint. A NAND extends the two operand chains exactly as in the direct compiler. Consequently interleaving inputs with computation preserves incidence three and the exact counts, without new trusted encodings between invocations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical

namespace Compiler.Stateful
open Compiler.Direct Compiler.Direct.Incidence CircuitCompiler

/-- Inserting a public sampler after an arbitrary compiled prefix preserves the chain consumer invariant. -/
theorem publicStep_invariant {P U T : ℕ} (state : Compilation P U T)
    (h : ChainInvariant state) : ChainInvariant state.publicStep := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    have he := append_injective state.live h.live_injective hab
    have hv : a.val = b.val := congrArg (fun j : Fin (P+U+T+1) => j.val) he
    exact Fin.ext hv
  · intro w
    refine Fin.lastCases ?_ (fun j => ?_) w
    · simp [Compilation.publicStep, uses]
    · simpa [Compilation.publicStep, uses, useCount] using h.uses_le_two j
  · intro w
    have hh (v : Fin (P+U+T+1)) :
        uses (state.program.snoc (.sample 0))
          (Fin.lastCases (Fin.last (P+state.operations))
            (fun j => (state.live j).castSucc) v) ≤ 1 := by
      refine Fin.lastCases ?_ (fun j => ?_) v
      · simp [uses]
      · simpa [uses, useCount] using h.live_le_one j
    exact hh (Fin.cast (by omega) w)

namespace Schedule
variable {J : Type*} {P U T : ℕ}

/-- Every interleaved compiled source has distinct current chains and at most two consumers of each encoding. -/
theorem chain_invariant (schedule : Schedule J P U T) : ChainInvariant schedule.compile := by
  induction schedule with
  | nil => exact initial_invariant Fin.elim0
  | sample prior tag ih => exact publicStep_invariant prior.compile ih
  | nand prior left right ih => simpa only [compile] using step_invariant prior.compile ih left right

/-- Each physical encoding occurs in at most three operation scopes, including all uses across invocation boundaries. -/
theorem incidence_le_three (schedule : Schedule J P U T)
    (w : Fin (P+schedule.compile.operations)) :
    incidence schedule.compile.program w ≤ 3 := by
  have h := schedule.chain_invariant.uses_le_two w
  exact (incidence_le_uses_add_one schedule.compile.program w).trans (by omega)

/-- The scoped-network degree bound is the same incidence count, written as a finite set cardinality. -/
theorem degree_le_three (schedule : Schedule J P U T)
    (w : Fin (P+schedule.compile.operations)) :
    (Finset.univ.filter (fun i => w ∈ schedule.compile.program.scope i)).card ≤ 3 := by
  simpa [incidence] using schedule.incidence_le_three w

/-- Every operation retains its two-port or three-port scope bound. -/
theorem scope_le_three (schedule : Schedule J P U T)
    (i : Fin schedule.compile.operations) : (schedule.compile.program.scope i).card ≤ 3 := by
  exact scope_card_le_three schedule.compile.program i

/-- The compiled syntax contains exactly T protected NANDs, 2T refreshes, and U public samplers, regardless of their interleaving. -/
theorem counts (schedule : Schedule J P U T) :
    Physical.computations schedule.compile.program = T ∧
    Physical.refreshes schedule.compile.program = 2*T ∧
    Physical.samplers schedule.compile.program = U := by
  induction schedule with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | @sample U T prior tag ih =>
    change Physical.computations prior.compile.program+0 = T ∧
      Physical.refreshes prior.compile.program+0 = 2*T ∧
      Physical.samplers prior.compile.program+1 = U+1
    omega
  | @nand U T prior left right ih =>
    change Physical.computations prior.compile.program+1 = T+1 ∧
      Physical.refreshes prior.compile.program+1+1 = 2*(T+1) ∧
      Physical.samplers prior.compile.program = U
    omega

/-- The exact total number of leaky operations is 3T+U. -/
theorem operationCount_eq (schedule : Schedule J P U T) : schedule.compile.operations = 3*T+U := by
  have h := schedule.compile.count
  omega

/-- Counting actual local-answer evaluations gives 8T+2U. -/
theorem callbacks_eq (schedule : Schedule J P U T) :
    Physical.callbacks schedule.compile.program = 8*T+2*U := by
  rw [Physical.callbacks_eq]
  rcases schedule.counts with ⟨hc, hr, hs⟩
  rw [hc, hr, hs]
  omega

/-- Port refreshing gives two distinct physical NAND operands, including equal logical source operands. -/
theorem distinct (schedule : Schedule J P U T) : schedule.compile.program.DistinctInputs := by
  induction schedule with
  | nil => trivial
  | sample prior tag ih => exact ⟨ih, trivial⟩
  | nand prior left right ih =>
    refine ⟨⟨⟨ih,trivial⟩,trivial⟩, ?_⟩
    change (Fin.last (P+prior.compile.operations)).castSucc ≠ Fin.last (P+prior.compile.operations+1)
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_last] at hv
    omega

end Schedule

/-- The recursive public-sampler prefix count equals constants plus inputs from all completed invocations. -/
theorem publicCount_eq (c d T : ℕ) : publicCount c d T = c+T*d := by
  induction T with
  | zero => simp [publicCount]
  | succ T ih => simp [publicCount, ih, Nat.succ_mul, Nat.add_assoc]

/-- Unrolling T copies of the transition contributes exactly T times its source NAND count. -/
theorem gateCount_eq (g T : ℕ) : gateCount g T = T*g := by
  induction T with
  | zero => simp [gateCount]
  | succ T ih => simp [gateCount, ih, Nat.succ_mul]

namespace Circuit
variable {m d c g k : ℕ} (circuit : Circuit m d c g k)

/-- Eq. (stateful-size): the constructed stateful compiler, including delayed public inputs and constants sampled once, has S = 3Tg+Td+c operations. -/
theorem unrolled_operationCount (T : ℕ) :
    (circuit.unrolling T).schedule.compile.operations = circuit.operationCount T := by
  rw [Schedule.operationCount_eq, publicCount_eq, gateCount_eq]
  simp only [operationCount]
  ring

/-- The number of actual local-answer evaluations over all invocations is 8Tg+2(Td+c). -/
theorem unrolled_callbackCount (T : ℕ) :
    Physical.callbacks (circuit.unrolling T).schedule.compile.program = circuit.callbackCount T := by
  rw [Schedule.callbacks_eq, publicCount_eq, gateCount_eq]
  simp only [callbackCount]
  ring

end Circuit
end Compiler.Stateful
