import InitECandidate.Solver.WitnessRadix.Keccak256PairedExecution
import InitECandidate.Solver.WitnessRadix.Keccak256Environment

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact MemoryRegion
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 10000

/-- Actual complete hash calls have identical observable events and public
memory results despite different unrelated code/private allocations. -/
theorem paired_call_execute (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (sourceArguments rightArguments : List (ExpHOL 64))
    (stp pointer scratch out : BitVec 64) (length : Nat)
    (sourceArgs : evalListHOLFinite source
      (h := fun query => Classical.propDecidable (source.memaddrs query)) sourceArguments = some (values pointer out length))
    (rightArgs : evalListHOLFinite right
      (h := fun query => Classical.propDecidable (right.memaddrs query)) rightArguments = some (values pointer out length))
    (sourceCode : source.code.lookup (ofString "keccak256") = some (formals, body, .one))
    (rightCode : right.code.lookup (ofString "keccak256") = some (formals, body, .one))
    (sourceData : EntryData source stp pointer scratch out length)
    (rightData : EntryData right stp pointer scratch out length)
    (domain : source.memaddrs = right.memaddrs) (endian : source.be = right.be)
    (ffi : source.ffi = right.ffi) (region : BitVec 64 → Prop)
    (same : Agree region source.memory right.memory)
    (blockReads : ∀ index, index + 136 ≤ length →
      KeccakAbsorb.ReadRegion region stp (byteAddress pointer index)
        (KeccakAbsorb.isUnaligned (byteAddress pointer index)))
    (stateBytes : ∀ offset < 200, region (panByteAlignHOL (width := 64) (byteAddress stp offset)))
    (tailReads : TailReads region stp pointer scratch (136 * (length / 136)) (length - 136 * (length / 136)))
    (small : length + 136 < 2^64)
    (sourceClock : price length + 1 ≤ source.clock) (rightClock : price length + 1 ≤ right.clock) :
    ∃ leftOutput rightOutput : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source
        (.call (some (none, none)) (ofString "keccak256") sourceArguments) = (none, leftOutput) ∧
      evaluateHOLFiniteState right
        (.call (some (none, none)) (ofString "keccak256") rightArguments) = (none, rightOutput) ∧
      leftOutput.locals = source.locals ∧ rightOutput.locals = right.locals ∧
      leftOutput.clock ≤ source.clock ∧ source.clock - (price length + 1) ≤ leftOutput.clock ∧
      rightOutput.clock ≤ right.clock ∧ right.clock - (price length + 1) ≤ rightOutput.clock ∧
      KeccakAbsorb.hashControl leftOutput = KeccakAbsorb.hashControl source ∧
      KeccakAbsorb.hashControl rightOutput = KeccakAbsorb.hashControl right ∧
      leftOutput.ffi = rightOutput.ffi ∧ Agree region leftOutput.memory rightOutput.memory ∧
      (∀ query, Protected stp scratch out query → leftOutput.memory query = source.memory query) ∧
      (∀ query, Protected stp scratch out query → rightOutput.memory query = right.memory query) := by
  classical
  obtain ⟨leftCallee, leftLookup, leftPointer, leftLength, leftOut⟩ :=
    environment source.code.lookup pointer out length sourceCode
  obtain ⟨rightCallee, rightLookup, rightPointer, rightLength, rightOut⟩ :=
    environment right.code.lookup pointer out length rightCode
  let leftEntry := callEntryStateHOLFinite source leftCallee
  let rightEntry := callEntryStateHOLFinite right rightCallee
  have leftLocals : EntryLocals leftEntry pointer out length := ⟨leftPointer, leftLength, leftOut⟩
  have rightLocals : EntryLocals rightEntry pointer out length := ⟨rightPointer, rightLength, rightOut⟩
  have leftData := EntryData.of_control source leftEntry stp pointer scratch out length rfl sourceData
  have rightData' := EntryData.of_control right rightEntry stp pointer scratch out length rfl rightData
  obtain ⟨leftFinished, rightFinished, leftRun, rightRun, leftUpper, leftLower, rightUpper, rightLower,
    leftControl, rightControl, finalFfi, finalMemory, leftAway, rightAway⟩ :=
    paired_execute leftEntry rightEntry stp pointer scratch out length leftLocals rightLocals leftData rightData'
      domain endian ffi region same blockReads stateBytes tailReads small
      (by change price length ≤ source.clock - 1; omega) (by change price length ≤ right.clock - 1; omega)
  have leftCall := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "keccak256")
    sourceArguments (values pointer out length) body leftCallee .one (.val (.word 0#64)) leftFinished
    sourceArgs leftLookup (by omega) leftRun (by simp [shapeEqHOL, shapeOfHOLExact])
  have rightCall := evaluateHOLFiniteState_call_return_caller_locals right none (ofString "keccak256")
    rightArguments (values pointer out length) body rightCallee .one (.val (.word 0#64)) rightFinished
    rightArgs rightLookup (by omega) rightRun (by simp [shapeEqHOL, shapeOfHOLExact])
  refine ⟨{leftFinished with locals := source.locals}, {rightFinished with locals := right.locals},
    leftCall, rightCall, rfl, rfl, ?_, ?_, ?_, ?_, leftControl, rightControl,
    finalFfi, finalMemory, leftAway, rightAway⟩
  · change leftFinished.clock ≤ source.clock
    change leftFinished.clock ≤ source.clock - 1 at leftUpper
    omega
  · change source.clock - (price length + 1) ≤ leftFinished.clock
    change source.clock - 1 - price length ≤ leftFinished.clock at leftLower
    omega
  · change rightFinished.clock ≤ right.clock
    change rightFinished.clock ≤ right.clock - 1 at rightUpper
    omega
  · change right.clock - (price length + 1) ≤ rightFinished.clock
    change right.clock - 1 - price length ≤ rightFinished.clock at rightLower
    omega

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.paired_call_execute
