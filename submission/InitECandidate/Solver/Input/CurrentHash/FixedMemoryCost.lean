import InitECandidate.Solver.Input.CurrentHash.MemoryCost
import InitECandidate.Solver.Input.ClockCostCallReached

namespace InitECandidate.Solver.Input.CurrentHash.FixedMemoryCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- A fixed-length actual zero call has a uniform all-outcome price even
when its pointer expression fails or evaluates to a malformed structured value. -/
theorem zero (code) (installed : OriginalCode.Installed code) (destination : Option (Option MlS))
    (pointer : ExpHOL 64) (length : Nat) (small : length + 32 < 2^64) :
    ClockCost.Bound code (.call (LocalEffects.callInfo destination) (ofString "memzero") [pointer, .const (BitVec.ofNat 64 length)])
      (ZeroAny.price length + 1) := by
  classical
  intro source codeEq
  apply ClockCost.call_arguments_current source destination (ofString "memzero") _ (ZeroAny.price length)
  intro values body callee shape args called
  have entry : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one) := by
    rw [codeEq]
    exact MemoryCost.zero_entry code installed
  have argsEq : ∃ value, values = [value, .val (.word (BitVec.ofNat 64 length))] := by
    change evalListHOLExact source.toExact [pointer, .const (BitVec.ofNat 64 length)] = some values at args
    cases read : evalHOLExact source.toExact pointer with
    | none => simp [evalListHOLExact, read] at args
    | some value => exact ⟨value, Option.some.inj (by simpa [evalListHOLExact, read, evalHOLExact] using args.symm)⟩
  obtain ⟨value, rfl⟩ := argsEq
  have raw := lookupCodeHOLFinite_eq_some source.code.lookup (ofString "memzero") _ body callee shape called
  simp only [lookupCodeHOLExact, entry] at raw
  split at raw
  · have bodyEq : Zero.body = body := congrArg Prod.fst (Option.some.inj raw)
    have localsEq := congrArg (fun triple => triple.2.1) (Option.some.inj raw)
    dsimp only at localsEq
    have cell : callee.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))) := by
      rw [← localsEq]
      simp [Zero.formals]
    rw [← bodyEq]
    exact ZeroAny.body_cost (callEntryStateHOLFinite source callee) length small cell
  · cases raw

/-- The same treatment for both copy pointer expressions; only the literal
byte length constrains the source-clock work. -/
theorem copy (code) (installed : OriginalCode.Installed code) (destination : Option (Option MlS))
    (output input : ExpHOL 64) (length : Nat) (small : length + 32 < 2^64) :
    ClockCost.Bound code (.call (LocalEffects.callInfo destination) (ofString "memcpy") [output, input, .const (BitVec.ofNat 64 length)])
      (CopyAny.price length + 1) := by
  classical
  intro source codeEq
  apply ClockCost.call_arguments_current source destination (ofString "memcpy") _ (CopyAny.price length)
  intro values body callee shape args called
  have entry : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one) := by
    rw [codeEq]
    exact MemoryCost.copy_entry code installed
  have argsEq : ∃ outputValue inputValue, values = [outputValue, inputValue, .val (.word (BitVec.ofNat 64 length))] := by
    change evalListHOLExact source.toExact [output, input, .const (BitVec.ofNat 64 length)] = some values at args
    cases outputRead : evalHOLExact source.toExact output with
    | none => simp [evalListHOLExact, outputRead] at args
    | some outputValue =>
      cases inputRead : evalHOLExact source.toExact input with
      | none => simp [evalListHOLExact, outputRead, inputRead] at args
      | some inputValue => exact ⟨outputValue, inputValue,
          Option.some.inj (by simpa [evalListHOLExact, outputRead, inputRead, evalHOLExact] using args.symm)⟩
  obtain ⟨outputValue, inputValue, rfl⟩ := argsEq
  have raw := lookupCodeHOLFinite_eq_some source.code.lookup (ofString "memcpy") _ body callee shape called
  simp only [lookupCodeHOLExact, entry] at raw
  split at raw
  · have bodyEq : Copy32.body = body := congrArg Prod.fst (Option.some.inj raw)
    have localsEq := congrArg (fun triple => triple.2.1) (Option.some.inj raw)
    dsimp only at localsEq
    have cell : callee.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))) := by
      rw [← localsEq]
      simp [CopyGeneral.formals]
    rw [← bodyEq]
    exact CopyAny.body_cost (callEntryStateHOLFinite source callee) length small cell
  · cases raw

end InitECandidate.Solver.Input.CurrentHash.FixedMemoryCost

#print axioms InitECandidate.Solver.Input.CurrentHash.FixedMemoryCost.zero
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedMemoryCost.copy
