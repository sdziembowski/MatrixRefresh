import Proofs.Compiler.Model
import Proofs.Compiler.Operations.Program

/-!
# Incidence three for the actual refresh chains

The proof counts occurrences at physical predecessor ports. A current source-wire chain endpoint has been consumed at most once; extending that chain consumes it once more and allocates a fresh endpoint. The two fresh gate operands are then consumed by their NAND. Consequently every encoding has at most two consumers and at most one producing operation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical

namespace Compiler.Direct.Incidence
open CircuitCompiler

/-- Count predecessor-port occurrences of an encoding in one instruction; a repeated computation operand would count twice. -/
def useCount {N : ℕ} (instruction : Operations.Instruction Bit N) (w : Fin N) : ℕ :=
  match instruction with
  | .compute gate => (if gate.left=w then 1 else 0)+(if gate.right=w then 1 else 0)
  | .refresh old => if old=w then 1 else 0
  | .sample _ => 0

/-- Count every actual consumer occurrence of each trusted or subsequently allocated encoding. -/
def uses {P : ℕ} : {S : ℕ} → Operations.Program Bit P S → Fin (P+S) → ℕ
  | 0,.nil => fun _=>0
  | _+1,.snoc prior instruction => Fin.snoc
      (fun w=>uses prior w+useCount instruction w) 0

/-- Every newly allocated encoding initially has zero consumers. -/
@[simp] theorem uses_last {P S : ℕ} (prior : Operations.Program Bit P S)
    (instruction : Operations.Instruction Bit (P+S)) :
    uses (prior.snoc instruction) (Fin.last (P+S))=0 := by
  exact Fin.snoc_last _ _

/-- An old encoding gains exactly the predecessor occurrences of the new instruction. -/
@[simp] theorem uses_old {P S : ℕ} (prior : Operations.Program Bit P S)
    (instruction : Operations.Instruction Bit (P+S)) (w : Fin (P+S)) :
    uses (prior.snoc instruction) w.castSucc=uses prior w+useCount instruction w := by
  exact Fin.snoc_castSucc _ _ _

/-- Update one logical source-wire endpoint to the fresh physical location. -/
def advance {W N : ℕ} (live : Fin W → Fin N) (u : Fin W) : Fin W → Fin (N+1) :=
  fun w=>if w=u then Fin.last N else (live w).castSucc

/-- Different source wires retain different current endpoints after extending one refresh chain. -/
theorem advance_injective {W N : ℕ} (live : Fin W → Fin N) (h : Function.Injective live)
    (u : Fin W) : Function.Injective (advance live u) := by
  intro a b hab
  by_cases ha : a=u <;> by_cases hb : b=u
  · exact ha.trans hb.symm
  · have he := congrArg Fin.val hab
    simp [advance,ha,hb] at he
    have := (live b).isLt
    omega
  · have he := congrArg Fin.val hab
    simp [advance,ha,hb] at he
    have := (live a).isLt
    omega
  · apply h
    simpa [advance,ha,hb] using hab

/-- Appending one fresh physical endpoint to an injective source-wire map preserves injectivity. -/
theorem append_injective {W N : ℕ} (f : Fin W → Fin N) (hf : Function.Injective f) :
    Function.Injective (Fin.lastCases (Fin.last N) (fun w=>(f w).castSucc)) := by
  intro a
  refine Fin.lastCases ?_ (fun a=>?_) a
  · intro b
    refine Fin.lastCases ?_ (fun b=>?_) b
    · intro h; rfl
    · intro h
      have he := congrArg Fin.val h
      simp only [Fin.lastCases_last,Fin.lastCases_castSucc,Fin.val_last,Fin.val_castSucc] at he
      have := (f b).isLt
      omega
  · intro b
    refine Fin.lastCases ?_ (fun b=>?_) b
    · intro h
      have he := congrArg Fin.val h
      simp only [Fin.lastCases_last,Fin.lastCases_castSucc,Fin.val_last,Fin.val_castSucc] at he
      have := (f a).isLt
      omega
    · intro h
      have he : f a=f b := by
        apply Fin.castSucc_injective
        simpa only [Fin.lastCases_castSucc] using h
      exact congrArg Fin.castSucc (hf he)

/-- The chain invariant records distinct current endpoints, at most two total consumers, and at most one consumer of a current endpoint. -/
structure ChainInvariant {P U T : ℕ} (state : Compilation P U T) : Prop where
  live_injective : Function.Injective state.live
  uses_le_two : ∀ w, uses state.program w≤2
  live_le_one : ∀ u, uses state.program (state.live u)≤1

/-- Direct public sampling reads no previous encoding, so all input encodings still have zero consumers. -/
theorem public_uses {P U : ℕ} (values : Fin U → Bit) :
    ∀ w, uses (Compilation.publicProgram (P:=P) values) w=0 := by
  induction U with
  | zero => intro w; rfl
  | succ u ih =>
    intro w
    refine Fin.lastCases ?_ (fun a=>?_) w
    · exact uses_last _ _
    · change uses ((Compilation.publicProgram (fun i=>values i.castSucc)).snoc
        (.sample (values (Fin.last u)))) a.castSucc=0
      rw [uses_old,ih]
      rfl

/-- The input prefix starts with distinct endpoints and no consumer occurrences, including when either input class is empty. -/
theorem initial_invariant {P U : ℕ} (values : Fin U → Bit) :
    ChainInvariant (Compilation.initial (P:=P) values) := by
  refine ⟨Function.injective_id,?_,?_⟩
  · intro w
    simpa [Compilation.initial,public_uses] using (show (0:ℕ)≤2 by omega)
  · intro w
    simpa [Compilation.initial,public_uses] using (show (0:ℕ)≤1 by omega)

/-- The two refreshes and NAND preserve distinct logical endpoints and the consumer budget, including repeated source operands. -/
theorem step_invariant {P U T : ℕ} (state : Compilation P U T)
    (h : ChainInvariant state) (left right : Fin (P+U+T)) :
    ChainInvariant (state.step left right) := by
  let l₁ := advance state.live left
  let l₂ := advance l₁ right
  have hl₁ : Function.Injective l₁ := advance_injective state.live h.live_injective left
  have hl₂ : Function.Injective l₂ := advance_injective l₁ hl₁ right
  refine ⟨append_injective l₂ hl₂,?_,?_⟩
  · intro w
    refine Fin.lastCases ?_ (fun w=>?_) w
    · simp [Compilation.step,uses,Fin.snoc,Nat.add_assoc] <;>
        split_ifs <;> simp_all <;> omega
    · refine Fin.lastCases ?_ (fun w=>?_) w
      · simp [Compilation.step,uses,useCount,Fin.snoc,Nat.add_assoc] <;>
          split_ifs <;> simp_all <;> omega
      · refine Fin.lastCases ?_ (fun w=>?_) w
        · have hrb : (state.live right).val<P+state.operations := (state.live right).isLt
          by_cases hr : right=left <;>
            simp_all [Compilation.step,uses,useCount,Fin.snoc,Nat.add_assoc,Fin.ext_iff] <;>
            split_ifs <;> simp_all <;> omega
        · have hw := h.uses_le_two w
          have hwb : w.val<P+state.operations := w.isLt
          have hlb : (state.live left).val<P+state.operations := (state.live left).isLt
          have hrb : (state.live right).val<P+state.operations := (state.live right).isLt
          have hlone := h.live_le_one left
          have hrone := h.live_le_one right
          by_cases hrl : right=left <;>
            by_cases hl : state.live left=w <;> by_cases hr : state.live right=w
          all_goals first
            | have he : right=left := h.live_injective (by simpa only [hl,hr])
              contradiction
            | skip
          all_goals simp_all [Compilation.step,uses,useCount,Fin.snoc,Nat.add_assoc,Fin.ext_iff]
          all_goals split_ifs <;> simp_all <;> omega
  · intro w
    refine Fin.lastCases ?_ (fun w=>?_) w
    · simp [Compilation.step,uses,Fin.snoc,Nat.add_assoc] <;>
        split_ifs <;> simp_all <;> omega
    · have hw := h.live_le_one w
      have hwb : (state.live w).val<P+state.operations := (state.live w).isLt
      have hlb : (state.live left).val<P+state.operations := (state.live left).isLt
      have hrb : (state.live right).val<P+state.operations := (state.live right).isLt
      by_cases hrl : right=left <;> by_cases hr : w=right <;> by_cases hl : w=left
      all_goals first
        | have hwl : state.live left≠state.live w := by
            intro he
            exact hl (h.live_injective he).symm
          have hwr : state.live right≠state.live w := by
            intro he
            exact hr (h.live_injective he).symm
          simp_all [Compilation.step,uses,useCount,Fin.snoc,Nat.add_assoc,Fin.ext_iff]
        | simp_all [Compilation.step,uses,useCount,Fin.snoc,Nat.add_assoc,Fin.ext_iff]
      all_goals try split_ifs
      all_goals try simp_all
      all_goals
        have hb : (state.live right).val<P+state.operations := (state.live right).isLt
        omega

/-- Every concrete compiled prefix has the chain consumer invariant. -/
theorem compile_invariant {P U T : ℕ} (program : NandProgram (P+U) T)
    (values : Fin U → Bit) : ChainInvariant (program.compile values) := by
  induction program with
  | nil => exact initial_invariant values
  | snoc prior left right ih => exact step_invariant _ ih left right

/-- Count the operation scopes containing one physical encoding location; decoder access is outside this leakage graph. -/
def incidence {P S : ℕ} (program : Operations.Program Bit P S) (w : Fin (P+S)) : ℕ :=
  ∑ i : Fin S, if w∈program.scope i then 1 else 0

/-- A predecessor's set-membership charge is no larger than its input-port occurrence count. -/
theorem input_indicator_le {N : ℕ} (instruction : Operations.Instruction Bit N) (w : Fin N) :
    (if w∈instruction.inputs then 1 else 0)≤useCount instruction w := by
  cases instruction with
  | compute gate =>
    by_cases hl : gate.left=w <;> by_cases hr : gate.right=w <;>
      simp_all [Operations.Instruction.inputs,useCount,eq_comm]
  | refresh old => simp [Operations.Instruction.inputs,useCount,eq_comm]
  | sample value => simp [Operations.Instruction.inputs,useCount]

/-- No earlier physical encoding is the fresh output appended at the end of an operation. -/
theorem last_not_mem_map {N : ℕ} (set : Finset (Fin N)) :
    Fin.last N∉set.map Fin.castSuccEmb := by
  intro h
  obtain ⟨a,ha,he⟩ := Finset.mem_map.mp h
  have hv := congrArg Fin.val he
  have hb : a.val<N := a.isLt
  simp only [Fin.castSuccEmb_apply,Fin.val_castSucc,Fin.val_last] at hv
  omega

/-- Appending one operation increases an old encoding's incidence by precisely its membership in the new predecessor scope. -/
theorem incidence_snoc_old {P S : ℕ} (prior : Operations.Program Bit P S)
    (instruction : Operations.Instruction Bit (P+S)) (w : Fin (P+S)) :
    incidence (prior.snoc instruction) w.castSucc=
      incidence prior w+(if w∈instruction.inputs then 1 else 0) := by
  have hmem (set : Finset (Fin (P+S))) :
      (∃ a∈set,Fin.castSuccEmb a=w.castSucc) ↔ w∈set := by
    constructor
    · rintro ⟨a,ha,he⟩
      have haw : a=w := Fin.castSuccEmb.injective he
      simpa only [haw] using ha
    · intro hw
      exact ⟨w,hw,rfl⟩
  unfold incidence
  rw [Fin.sum_univ_castSucc]
  simp only [Operations.Program.scope_snoc_old,Operations.Program.scope_snoc_last,
    Finset.mem_insert,Finset.mem_map,Fin.castSucc_ne_last,false_or]
  have hif (set : Finset (Fin (P+S))) :
      (if ∃a∈set,Fin.castSuccEmb a=w.castSucc then 1 else 0)=
        (if w∈set then 1 else 0) := by
    congr 1
    exact propext (hmem set)
  exact congrArg₂ Nat.add (Finset.sum_congr rfl (fun i _=>hif (prior.scope i)))
    (hif instruction.inputs)

/-- A newly allocated encoding belongs only to its producing operation at the time it is allocated. -/
theorem incidence_snoc_last {P S : ℕ} (prior : Operations.Program Bit P S)
    (instruction : Operations.Instruction Bit (P+S)) :
    incidence (prior.snoc instruction) (Fin.last (P+S))=1 := by
  unfold incidence
  rw [Fin.sum_univ_castSucc]
  simp only [Operations.Program.scope_snoc_old,Operations.Program.scope_snoc_last,
    last_not_mem_map,Finset.mem_insert_self,ite_false,ite_true,Finset.sum_const_zero,zero_add]

/-- A physical location has at most one producing operation in addition to its counted predecessor-port occurrences. -/
theorem incidence_le_uses_add_one {P S : ℕ} (program : Operations.Program Bit P S) :
    ∀ w, incidence program w≤uses program w+1 := by
  induction program with
  | nil => intro w; simp [incidence,uses]
  | @snoc S prior instruction ih =>
    intro w
    refine Fin.lastCases ?_ (fun a=>?_) w
    · change incidence (prior.snoc instruction) (Fin.last (P+S))≤
        uses (prior.snoc instruction) (Fin.last (P+S))+1
      rw [incidence_snoc_last,uses_last]
    · rw [incidence_snoc_old,uses_old]
      have h := ih a
      have h' := input_indicator_le instruction a
      omega

/-- Every ordinary operation scope contains at most its two predecessor encodings and its fresh output. -/
theorem scope_card_le_three {P S : ℕ} (program : Operations.Program Bit P S) (i : Fin S) :
    (program.scope i).card≤3 := by
  cases hi : program.sourceInstruction i with
  | compute gate =>
    simpa only [Operations.Program.scope,hi,Operations.Instruction.inputs] using
      (Finset.card_le_three (a:=Fin.natAdd P i) (b:=gate.left) (c:=gate.right))
  | refresh old =>
    exact (show (program.scope i).card≤2 by
      simpa only [Operations.Program.scope,hi,Operations.Instruction.inputs] using
        (Finset.card_le_two (a:=Fin.natAdd P i) (b:=old))).trans (by omega)
  | sample value => simp [Operations.Program.scope,hi,Operations.Instruction.inputs]

end Compiler.Direct.Incidence

namespace Compiler.Direct.Source
variable {P U T k : ℕ} (source : Source P U T k)

/-- Every retained encoding belongs to at most three active-operation scopes, irrespective of source fanout or repeated operands. -/
theorem incidence_le_three (w : Fin (P+source.operationCount)) :
    Incidence.incidence source.compiledProgram w≤3 := by
  have h := Incidence.compile_invariant source.program source.publicValues
  have huses : Incidence.uses source.compiledProgram w≤2 := h.uses_le_two w
  exact (Incidence.incidence_le_uses_add_one source.compiledProgram w).trans (by omega)

/-- Each actual operation reads and writes at most three distinct encoding locations. -/
theorem scope_card_le_three (i : Fin source.operationCount) :
    (source.compiledProgram.scope i).card≤3 := by
  exact Incidence.scope_card_le_three source.compiledProgram i

end Compiler.Direct.Source
