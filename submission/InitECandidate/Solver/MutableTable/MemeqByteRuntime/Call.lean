import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Environment
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Mapped
import InitECandidate.Solver.WitnessRadix.MemeqEnvironment
import InitECandidate.Solver.Input.PureReturn

namespace InitECandidate.Solver.MutableTable.MemeqByteRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

/-- Entire actual unaligned small-key memeq caller. It returns0or1, preserves
all memory/FFI/globals and consumes at most length/8+length%8+1 source clocks.
Only actual entry code/arguments/mapped regions and clock remain as premises. -/
theorem unaligned_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64) (length : Nat)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values a b length))
    (known : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (small : length ≤ 64) (unaligned : (a ||| b) &&& 7#64 ≠ 0#64)
    (leftMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress a offset)))
    (rightMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress b offset)))
    (enough : price length + 1 ≤ source.clock) :
    ∃ (spent : Nat) (answer : BitVec 64), spent ≤ price length ∧ (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "memeq") arguments continuation) =
        (let output := evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind {source with clock := source.clock - (spent + 1)} name answer) continuation
         (output.1, restore source name output.2)) := by
  obtain ⟨callee, called, aLocal, bLocal, lengthLocal⟩ := environment source.code.lookup a b length known
  let entry := callEntryStateHOLFinite source callee
  have inputs := inputs_of_mapped entry a b length aLocal bLocal lengthLocal leftMapped rightMapped
  obtain ⟨spent, answer, spentBound, answerBound, bodyRun⟩ := unaligned_execute entry a b length _ _ inputs small unaligned
    (by change price length ≤ source.clock - 1; omega)
  have frame : emptyLocalsHOLFinite (restore entry "i" (emptyLocalsHOLFinite {entry with clock := entry.clock - spent})) =
      emptyLocalsHOLFinite {source with clock := source.clock - 1 - spent} := rfl
  have actual := Input.CallNormal.pure_return_execute source _ name (ofString "memeq") arguments _ Memeq32.body continuation callee
    answer spent args called (by omega) bodyRun frame
  have clocks : source.clock - 1 - spent = source.clock - (spent + 1) := by omega
  exact ⟨spent, answer, spentBound, answerBound, by simpa only [clocks] using actual⟩

theorem caller_price20 : price 20 + 1 = 7 := by decide
theorem caller_price52 : price 52 + 1 = 11 := by decide
theorem caller_price60 : price 60 + 1 = 12 := by decide

end InitECandidate.Solver.MutableTable.MemeqByteRuntime

#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.environment
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.unaligned_call
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.caller_price20
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.caller_price52
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.caller_price60
