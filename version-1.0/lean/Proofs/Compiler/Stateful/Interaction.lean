import Proofs.Compiler.Model

/-!
# Causality of the public interface

Only leakage before invocation t can affect its public input. An oracle reply used by a leakage callback belongs to an invocation whose end precedes that operation. The ideal stateful oracle agrees exactly with the recursive source transition on the request stream determined by the same leakage transcript.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace Compiler.Stateful
open Compiler.Direct
variable {A : Type*} {d k : ℕ}

/-- Invocation start times are nondecreasing, including transitions with no operations. -/
theorem startTime_mono (c d g : ℕ) {s t : ℕ} (h : s ≤ t) :
    startTime c d g s ≤ startTime c d g t := by
  exact Nat.add_le_add_left (Nat.mul_le_mul_right (d+3*g) h) c

/-- Equal leakage at each earlier invocation start gives equal public records. No later leakage is inspected by this reconstruction. -/
theorem records_congr (c g : ℕ) (choose : InputChoice A d k) (oracle : Oracle d k)
    (first second : List A) (t : ℕ)
    (h : ∀ s, s<t → first.take (startTime c d g s) = second.take (startTime c d g s)) :
    records c g choose oracle first t = records c g choose oracle second t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [records, ih (fun s hs => h s (by omega)), h t (by omega)]

/-- An invocation's chosen input depends only on its own incoming leakage prefix and the already completed request/response records. -/
theorem inputAt_congr (c g : ℕ) (choose : InputChoice A d k) (oracle : Oracle d k)
    (first second : List A) (t : ℕ)
    (h : first.take (startTime c d g t) = second.take (startTime c d g t)) :
    inputAt c g choose oracle first t = inputAt c g choose oracle second t := by
  have hr := records_congr c g choose oracle first second t (fun s hs => by
    have he := congrArg (List.take (startTime c d g s)) h
    simpa only [List.take_take, Nat.min_eq_left (startTime_mono c d g (Nat.le_of_lt hs))] using he)
  simp only [inputAt, h, hr]

/-- A completed output can be consulted only after that invocation's final operation. -/
theorem completed_before (c d g T i s : ℕ) (h : s < completed c d g T i) :
    startTime c d g (s+1) ≤ i := by
  induction T with
  | zero => simp [completed] at h
  | succ T ih =>
    by_cases ht : startTime c d g (T+1) ≤ i
    · simp only [completed, if_pos ht] at h
      exact (startTime_mono c d g (by omega)).trans ht
    · simp only [completed, if_neg ht] at h
      exact ih h

/-- A published input has reached its invocation start, so evaluating its policy uses only earlier leakage. -/
theorem started_before (c d g T i s : ℕ) (h : s < started c d g T i) :
    startTime c d g s ≤ i := by
  induction T with
  | zero => simp [started] at h
  | succ T ih =>
    by_cases ht : startTime c d g T ≤ i
    · simp only [started, if_pos ht] at h
      exact (startTime_mono c d g (by omega)).trans ht
    · simp only [started, if_neg ht] at h
      exact ih h

/-- Replaying the ideal oracle's request list reaches exactly the state obtained by repeated source transitions on the causally chosen input stream. -/
theorem records_state {m c g : ℕ} (circuit : Circuit m d c g k)
    (choose : InputChoice A d k) (initial : Fin m → Bit) (history : List A) (t : ℕ) :
    circuit.afterInputs initial
      ((records c g choose (circuit.oracle initial) history t).map Prod.fst) =
    circuit.stateAt initial (inputAt c g choose (circuit.oracle initial) history) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [records, List.map_append, List.map_cons, List.map_nil,
      List.foldl_append, Circuit.afterInputs, List.foldl_cons, List.foldl_nil, Circuit.stateAt]
    exact congrArg (fun state => circuit.step state
      (inputAt c g choose (circuit.oracle initial) history t)) ih

/-- Each authorized response equals the designated source output on the adaptively chosen input stream. -/
theorem recordAt_output {m c g : ℕ} (circuit : Circuit m d c g k)
    (choose : InputChoice A d k) (initial : Fin m → Bit) (history : List A) (t : ℕ) :
    (recordAt c g choose (circuit.oracle initial) history t).2 =
      circuit.outputAt initial (inputAt c g choose (circuit.oracle initial) history) t := by
  exact congrArg (fun state => circuit.output state
    (inputAt c g choose (circuit.oracle initial) history t))
      (records_state circuit choose initial history t)

end Compiler.Stateful
