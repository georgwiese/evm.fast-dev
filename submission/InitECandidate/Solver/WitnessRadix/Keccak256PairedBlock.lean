import InitECandidate.Solver.WitnessRadix.KeccakAbsorbPairedCall
import InitECandidate.Solver.WitnessRadix.Keccak256Context

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- The literal full-block body preserves public memory and event agreement
while updating each caller's own index and spending nineteen source clocks. -/
theorem paired_block_execute (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (stp pointer : BitVec 64) (index length : Nat)
    (sourceArgs : Args source stp pointer length) (rightArgs : Args right stp pointer length)
    (sourceCode : Code source) (rightCode : Code right) (mapped : Mapped source stp pointer length)
    (sourceIndex : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (rightIndex : right.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (domain : source.memaddrs = right.memaddrs) (endian : source.be = right.be)
    (ffi : source.ffi = right.ffi)
    (region : BitVec 64 → Prop)
    (reads : KeccakAbsorb.ReadRegion region stp (byteAddress pointer index)
      (KeccakAbsorb.isUnaligned (byteAddress pointer index)))
    (stateBytes : ∀ offset < 200,
      region (panByteAlignHOL (width := 64) (byteAddress stp offset)))
    (same : ∀ query, region query → source.memory query = right.memory query)
    (inside : index + 136 ≤ length) (aligned : stp.toNat % 8 = 0) (fits : stp.toNat + 200 < 2^64)
    (sourceClock : 19 ≤ source.clock) (rightClock : 19 ≤ right.clock) :
    ∃ leftOutput rightOutput : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source blockBody = (none, leftOutput) ∧
      evaluateHOLFiniteState right blockBody = (none, rightOutput) ∧
      leftOutput.locals = (bind source "i" (BitVec.ofNat 64 (index + 136))).locals ∧
      rightOutput.locals = (bind right "i" (BitVec.ofNat 64 (index + 136))).locals ∧
      leftOutput.clock = source.clock - 19 ∧ rightOutput.clock = right.clock - 19 ∧
      KeccakAbsorb.hashControl leftOutput = KeccakAbsorb.hashControl source ∧
      KeccakAbsorb.hashControl rightOutput = KeccakAbsorb.hashControl right ∧
      leftOutput.ffi = rightOutput.ffi ∧
      (∀ query, region query → leftOutput.memory query = rightOutput.memory query) ∧
      (∀ query, KeccakAbsorb.Away stp query → leftOutput.memory query = source.memory query) ∧
      (∀ query, KeccakAbsorb.Away stp query → rightOutput.memory query = right.memory query) := by
  classical
  have leftEvaluated : evalListHOLFinite source
      (h := fun query => Classical.propDecidable (source.memaddrs query)) blockArguments =
      some (KeccakAbsorb.values stp (byteAddress pointer index)) := by
    simp [blockArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact, localVar, toExact,
      sourceArgs.stateLocal, sourceArgs.pointerLocal, sourceIndex, valueIsWord, valueWord,
      wordOpHOL, wordOp, KeccakAbsorb.values, byteAddress]
  have rightEvaluated : evalListHOLFinite right
      (h := fun query => Classical.propDecidable (right.memaddrs query)) blockArguments =
      some (KeccakAbsorb.values stp (byteAddress pointer index)) := by
    simp [blockArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact, localVar, toExact,
      rightArgs.stateLocal, rightArgs.pointerLocal, rightIndex, valueIsWord, valueWord,
      wordOpHOL, wordOp, KeccakAbsorb.values, byteAddress]
  obtain ⟨leftCalled, rightCalled, leftRun, rightRun, leftLocals, rightLocals,
    leftClock, rightClock, leftControl, rightControl, finalFfi, finalMemory, leftAway, rightAway⟩ :=
    KeccakAbsorb.paired_call source right blockArguments blockArguments stp (byteAddress pointer index)
      leftEvaluated rightEvaluated sourceCode.block rightCode.block sourceCode.perm rightCode.perm
      sourceCode.oracleEq domain endian ffi region reads stateBytes same (mapped index inside)
      aligned fits sourceClock rightClock
  have leftIndex : leftCalled.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))) := by
    rw [leftLocals]; exact sourceIndex
  have rightIndex' : rightCalled.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))) := by
    rw [rightLocals]; exact rightIndex
  have leftIncrement := StateSteps.assign_execute leftCalled "i" (addConst (localVar "i") 136#64)
    (BitVec.ofNat 64 index) (BitVec.ofNat 64 (index + 136)) leftIndex (by
      simp [eval, addConst, localVar, evalHOLExact, evalListHOLExact, toExact, leftIndex,
        valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.ofNat_add])
  have rightIncrement := StateSteps.assign_execute rightCalled "i" (addConst (localVar "i") 136#64)
    (BitVec.ofNat 64 index) (BitVec.ofNat 64 (index + 136)) rightIndex' (by
      simp [eval, addConst, localVar, evalHOLExact, evalListHOLExact, toExact, rightIndex',
        valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.ofNat_add])
  refine ⟨bind leftCalled "i" (BitVec.ofNat 64 (index + 136)),
    bind rightCalled "i" (BitVec.ofNat 64 (index + 136)), ?_, ?_, ?_, ?_,
    leftClock, rightClock, leftControl, rightControl, finalFfi, finalMemory, leftAway, rightAway⟩
  · rw [blockBody, StateSteps.next_sequence source leftCalled _ _ leftRun (by omega)]
    exact leftIncrement
  · rw [blockBody, StateSteps.next_sequence right rightCalled _ _ rightRun (by omega)]
    exact rightIncrement
  · simp only [QueryBranch.bind, setVarHOLFinite, leftLocals]
  · simp only [QueryBranch.bind, setVarHOLFinite, rightLocals]

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.paired_block_execute
