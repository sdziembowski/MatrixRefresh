import Proofs.Compiler.Direct.Network

/-!
# Complete privacy of the actual direct compiler

The proof instantiates direct composition with the actual instruction scopes and the established physical operation certificates. Exact raw-prefix averaging preserves the same bound. Correctness of the trusted decoder lets us append the authorized plaintext to both transcripts without disclosing output encodings.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace CompilerProof.Direct
open Refresh MatrixRefresh Compiler CircuitCompiler.SimulationParameters

/-- The direct model's complete answer alphabet is exactly K(λᴹ + λˢ), including formal answers having probability zero. -/
theorem answer_card (ml sl : ℕ) : Fintype.card (Compiler.Answer ml sl)=Compiler.K (ml+sl) := by
  simp only [Compiler.Answer,LeakageOutput,Compiler.K,Fintype.card_prod,Fintype.card_fun,
    Fintype.card_bool,Fintype.card_fin]
  rw [←pow_add,←pow_add,←pow_add]
  congr 1
  omega

/-- The number of actual nonzero binary shares is precisely q(n) = 2ⁿ − 1. -/
theorem share_card (n : ℕ) : (Fintype.card (Refresh.U Bit n):ℝ)=(Compiler.q n:ℝ) := by
  have hbinary : fieldCard Bit=2 := by simp [fieldCard,Bit]
  rw [share_card_binary hbinary]
  have hp : 1≤(2:ℕ)^n := Nat.one_le_pow _ _ (by norm_num)
  rw [Compiler.q,Nat.cast_sub hp,Nat.cast_pow]
  norm_num

end CompilerProof.Direct

namespace Compiler.Direct

/-- Complete physical-view privacy of the direct compiler against every admissible adaptive local leakage strategy. Its single dummy-input target executes the actual operations and appends only the authorized plaintext output. -/
theorem theorem_direct {P U T k n ml sl : ℕ} (source : Source P U T k)
    (strategy : Strategy source n ml sl) (hn : 2≤n) (input : Fin P → Bit) :
    Compiler.statisticalDistance (realView strategy hn input)
      (simulatedView strategy hn (source.outputValues input))≤privacyBound source n ml sl := by
  rw [CompilerProof.Direct.realView_eq_transcript_output]
  apply (Refresh.statisticalDistance_map_le _ _ (fun history=>(history,source.outputValues input))).trans
  have h := CompilerProof.Direct.raw_transcript_bound source strategy hn input (fun _=>0)
  simpa only [privacyBound,CompilerProof.Direct.answer_card,CompilerProof.Direct.share_card] using h

end Compiler.Direct
