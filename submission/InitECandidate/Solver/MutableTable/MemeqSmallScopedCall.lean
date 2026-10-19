import InitECandidate.Solver.MutableTable.MemeqSmallExecution

namespace InitECandidate.Solver.MutableTable.MemeqSmall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64) (length : Nat)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some (MemeqByteRuntime.values a b length))
    (code : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (small : length ≤ 64) (aFits : a.toNat + length < 2^64) (bFits : b.toNat + length < 2^64)
    (leftMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress a offset)))
    (rightMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress b offset)))
    (enough : MemeqByteRuntime.price length + 1 ≤ source.clock) :
    ∃ (paid : Nat) (answer : BitVec 64), 1 ≤ paid ∧ paid ≤ MemeqByteRuntime.price length + 1 ∧
      paid ≤ source.clock ∧ (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "memeq") arguments continuation) =
        (let output := evaluateHOLFiniteState (bind {source with clock := source.clock - paid} name answer) continuation
         (output.1, restore source name output.2)) := by
  obtain ⟨callee, called, aLocal, bLocal, lengthLocal⟩ := MemeqByteRuntime.environment source.code.lookup a b length code
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨spent, answer, post, bound, binary, run, fields⟩ := execute entry a b length aLocal bLocal lengthLocal
    small aFits bFits leftMapped rightMapped (by change MemeqByteRuntime.price length ≤ source.clock - 1; omega)
  have frame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - 1 - spent} := fields
  have actual := Input.CallNormal.pure_return_execute source post name (ofString "memeq") arguments _ Memeq32.body continuation
    callee answer spent args called (by omega) run frame
  have clocks : source.clock - 1 - spent = source.clock - (spent + 1) := by omega
  exact ⟨spent + 1, answer, by omega, by omega, by omega, binary, by simpa only [clocks] using actual⟩

end InitECandidate.Solver.MutableTable.MemeqSmall

#print axioms InitECandidate.Solver.MutableTable.MemeqSmall.call_execute
