import InitECandidate.Solver.WitnessRadix.KeccakAbsorbPaired
import InitECandidate.Solver.WitnessRadix.KeccakAbsorbTarget
import InitECandidate.Solver.WitnessRadix.KeccakAbsorbEnvironment

namespace InitECandidate.Solver.WitnessRadix.KeccakAbsorb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 10000

set_option maxHeartbeats 1000000 in
/-- Lift public-memory and event agreement through the actual block ABI.
The two callers may have different locals, clocks and unrelated code. -/
theorem paired_call (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (sourceArguments rightArguments : List (ExpHOL 64)) (stp blk : BitVec 64)
    (sourceArgs : evalListHOLFinite source
      (h := fun query => Classical.propDecidable (source.memaddrs query)) sourceArguments = some (values stp blk))
    (rightArgs : evalListHOLFinite right
      (h := fun query => Classical.propDecidable (right.memaddrs query)) rightArguments = some (values stp blk))
    (sourceCode : source.code.lookup (ofString "keccak_absorb_block") = some (formals, body, .one))
    (rightCode : right.code.lookup (ofString "keccak_absorb_block") = some (formals, body, .one))
    (sourcePerm : source.code.lookup (ofString "keccak_f1600") = some (Keccak.formals, Keccak.f1600Body, .one))
    (rightPerm : right.code.lookup (ofString "keccak_f1600") = some (Keccak.formals, Keccak.f1600Body, .one))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle)
    (domain : source.memaddrs = right.memaddrs) (endian : source.be = right.be)
    (ffi : source.ffi = right.ffi)
    (region : BitVec 64 → Prop) (reads : ReadRegion region stp blk (isUnaligned blk))
    (stateBytes : ∀ offset < 200,
      region (panByteAlignHOL (width := 64) (byteAddress stp offset)))
    (same : ∀ query, region query → source.memory query = right.memory query)
    (mapped : Mapped source stp blk (isUnaligned blk))
    (aligned : stp.toNat % 8 = 0) (fits : stp.toNat + 200 < 2^64)
    (sourceClock : 19 ≤ source.clock) (rightClock : 19 ≤ right.clock) :
    ∃ leftOutput rightOutput : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source
        (.call (some (none, none)) (ofString "keccak_absorb_block") sourceArguments) = (none, leftOutput) ∧
      evaluateHOLFiniteState right
        (.call (some (none, none)) (ofString "keccak_absorb_block") rightArguments) = (none, rightOutput) ∧
      leftOutput.locals = source.locals ∧ rightOutput.locals = right.locals ∧
      leftOutput.clock = source.clock - 19 ∧ rightOutput.clock = right.clock - 19 ∧
      hashControl leftOutput = hashControl source ∧ hashControl rightOutput = hashControl right ∧
      leftOutput.ffi = rightOutput.ffi ∧
      (∀ query, region query → leftOutput.memory query = rightOutput.memory query) ∧
      (∀ query, Away stp query → leftOutput.memory query = source.memory query) ∧
      (∀ query, Away stp query → rightOutput.memory query = right.memory query) := by
  classical
  obtain ⟨leftCallee, leftLookup, leftStp, leftBlk⟩ := environment source.code.lookup stp blk sourceCode
  obtain ⟨rightCallee, rightLookup, rightStp, rightBlk⟩ := environment right.code.lookup stp blk rightCode
  let leftEntry := callEntryStateHOLFinite source leftCallee
  let rightEntry := callEntryStateHOLFinite right rightCallee
  have entryMapped : Mapped leftEntry stp blk (isUnaligned blk) :=
    ⟨mapped.stateWords, mapped.blockWords, mapped.blockBytes⟩
  obtain ⟨bytes, length, leftRun, rightRun, finalFfi, finalMemory⟩ :=
    paired_execute leftEntry rightEntry stp blk leftStp rightStp leftBlk rightBlk domain endian ffi
      region reads stateBytes same entryMapped sourcePerm rightPerm oracleEq aligned fits
      (by change 18 ≤ source.clock - 1; omega) (by change 18 ≤ right.clock - 1; omega)
  let leftOutput := { target leftEntry stp blk bytes with locals := source.locals }
  let rightOutput := { target rightEntry stp blk bytes with locals := right.locals }
  have leftCall := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "keccak_absorb_block")
    sourceArguments (values stp blk) body leftCallee .one (.val (.word 0#64))
    (target leftEntry stp blk bytes) sourceArgs leftLookup (by omega) leftRun
    (by simp [shapeEqHOL, shapeOfHOLExact])
  have rightCall := evaluateHOLFiniteState_call_return_caller_locals right none (ofString "keccak_absorb_block")
    rightArguments (values stp blk) body rightCallee .one (.val (.word 0#64))
    (target rightEntry stp blk bytes) rightArgs rightLookup (by omega) rightRun
    (by simp [shapeEqHOL, shapeOfHOLExact])
  refine ⟨leftOutput, rightOutput, leftCall, rightCall, rfl, rfl, ?_, ?_, ?_, ?_,
    finalFfi, finalMemory, ?_, ?_⟩
  · change (target leftEntry stp blk bytes).clock = source.clock - 19
    rw [target_clock]
    change source.clock - 1 - 18 = source.clock - 19
    omega
  · change (target rightEntry stp blk bytes).clock = right.clock - 19
    rw [target_clock]
    change right.clock - 1 - 18 = right.clock - 19
    omega
  · exact target_control leftEntry stp blk bytes
  · exact target_control rightEntry stp blk bytes
  · intro query away
    exact target_memory_away leftEntry stp blk query bytes away
  · intro query away
    exact target_memory_away rightEntry stp blk query bytes away

end InitECandidate.Solver.WitnessRadix.KeccakAbsorb

#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.paired_call
