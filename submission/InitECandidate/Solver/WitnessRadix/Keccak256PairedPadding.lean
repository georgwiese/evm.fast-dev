import InitECandidate.Solver.WitnessRadix.Keccak256PaddingAgreement
import InitECandidate.Solver.WitnessRadix.Keccak256OutputAgreement
import InitECandidate.Solver.WitnessRadix.KeccakAbsorbPairedCall
import InitECandidate.Solver.WitnessRadix.Keccak256Padding

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact MemoryRegion
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

structure TailReads (region : BitVec 64 → Prop) (stp pointer scratch : BitVec 64) (index rem : Nat) : Prop where
  inputWords : CopyGeneral.aligned (byteAddress pointer index) scratch →
    ∀ offset < rem, offset % 8 = 0 → region (byteAddress (byteAddress pointer index) offset)
  inputBytes : ∀ offset < rem,
    region (panByteAlignHOL (width := 64) (byteAddress (byteAddress pointer index) offset))
  lastPad : region (panByteAlignHOL (width := 64) (scratch + 135#64))
  absorb : KeccakAbsorb.ReadRegion region stp scratch (KeccakAbsorb.isUnaligned scratch)
  stateBytes : ∀ offset < 200, region (panByteAlignHOL (width := 64) (byteAddress stp offset))
  outputWords : ∀ offset < 32, offset % 8 = 0 → region (byteAddress stp offset)
  outputBytes : ∀ offset < 32, region (panByteAlignHOL (width := 64) (byteAddress stp offset))

theorem paired_padding_execute (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (stp pointer scratch out : BitVec 64) (index rem : Nat)
    (sourceLocals : TailLocals source stp pointer out index rem)
    (rightLocals : TailLocals right stp pointer out index rem)
    (sourceData : TailData source stp pointer scratch out index rem)
    (rightData : TailData right stp pointer scratch out index rem)
    (domain : source.memaddrs = right.memaddrs) (endian : source.be = right.be)
    (ffi : source.ffi = right.ffi) (region : BitVec 64 → Prop)
    (reads : TailReads region stp pointer scratch index rem)
    (same : Agree region source.memory right.memory) (remBound : rem < 136)
    (sourceClock : 194 ≤ source.clock) (rightClock : 194 ≤ right.clock) :
    ∃ leftOutput rightOutput : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source paddingTail = (some (.returned (.val (.word 0#64))), leftOutput) ∧
      evaluateHOLFiniteState right paddingTail = (some (.returned (.val (.word 0#64))), rightOutput) ∧
      leftOutput.clock ≤ source.clock ∧ source.clock - 194 ≤ leftOutput.clock ∧
      rightOutput.clock ≤ right.clock ∧ right.clock - 194 ≤ rightOutput.clock ∧
      KeccakAbsorb.hashControl leftOutput = KeccakAbsorb.hashControl source ∧
      KeccakAbsorb.hashControl rightOutput = KeccakAbsorb.hashControl right ∧
      leftOutput.ffi = rightOutput.ffi ∧ Agree region leftOutput.memory rightOutput.memory ∧
      (∀ query, Away stp scratch out query → leftOutput.memory query = source.memory query) ∧
      (∀ query, Away stp scratch out query → rightOutput.memory query = right.memory query) := by
  classical
  let leftPad := paddingPrefixState source pointer scratch index rem
  let rightPad := paddingPrefixState right pointer scratch index rem
  have leftControl := paddingPrefix_control source pointer scratch index rem
  have rightControl := paddingPrefix_control right pointer scratch index rem
  have leftData := TailData.of_control source leftPad stp pointer scratch out index rem leftControl sourceData
  have rightData' := TailData.of_control right rightPad stp pointer scratch out index rem rightControl rightData
  have leftLocals := TailLocals.of_locals source leftPad stp pointer out index rem
    (paddingPrefix_locals source pointer scratch index rem) sourceLocals
  have rightLocals' := TailLocals.of_locals right rightPad stp pointer out index rem
    (paddingPrefix_locals right pointer scratch index rem) rightLocals
  have leftClock := paddingPrefix_clock source pointer scratch index rem
  have rightClock' := paddingPrefix_clock right pointer scratch index rem
  have costBound := CopyGeneral.cost_le (byteAddress pointer index) scratch rem
  have padDomain : leftPad.memaddrs = rightPad.memaddrs :=
    (congrArg (fun state => state.memaddrs) leftControl).trans
      (domain.trans (congrArg (fun state => state.memaddrs) rightControl).symm)
  have padEndian : leftPad.be = rightPad.be :=
    (congrArg (fun state => state.be) leftControl).trans
      (endian.trans (congrArg (fun state => state.be) rightControl).symm)
  have padFfi : leftPad.ffi = rightPad.ffi :=
    (paddingPrefix_ffi source pointer scratch index rem).trans
      (ffi.trans (paddingPrefix_ffi right pointer scratch index rem).symm)
  have padMemory := paddingPrefix_memory_agrees source right endian region same pointer scratch index rem
    reads.inputWords reads.inputBytes reads.lastPad
  have leftArgs : evalListHOLFinite leftPad
      (h := fun query => Classical.propDecidable (leftPad.memaddrs query)) [localVar "stp", pad] =
      some (KeccakAbsorb.values stp scratch) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, localVar, pad, toExact,
      leftLocals.stateLocal, leftData.scratchGlobal, KeccakAbsorb.values]
  have rightArgs : evalListHOLFinite rightPad
      (h := fun query => Classical.propDecidable (rightPad.memaddrs query)) [localVar "stp", pad] =
      some (KeccakAbsorb.values stp scratch) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, localVar, pad, toExact,
      rightLocals'.stateLocal, rightData'.scratchGlobal, KeccakAbsorb.values]
  obtain ⟨leftAbs, rightAbs, leftAbsRun, rightAbsRun, leftAbsLocals, rightAbsLocals,
    leftAbsClock, rightAbsClock, leftAbsControl, rightAbsControl, absFfi, absMemory,
    leftAbsAway, rightAbsAway⟩ :=
    KeccakAbsorb.paired_call leftPad rightPad [localVar "stp", pad] [localVar "stp", pad] stp scratch
      leftArgs rightArgs leftData.hashCode.block rightData'.hashCode.block
      leftData.hashCode.perm rightData'.hashCode.perm leftData.hashCode.oracleEq
      padDomain padEndian padFfi region reads.absorb reads.stateBytes padMemory leftData.absorbMapped
      leftData.stateAligned leftData.stateFits (by rw [leftClock]; omega) (by rw [rightClock']; omega)
  change evaluateHOLFiniteState leftPad absorbPad = (none, leftAbs) at leftAbsRun
  change evaluateHOLFiniteState rightPad absorbPad = (none, rightAbs) at rightAbsRun
  have leftFinalData := TailData.of_control source leftAbs stp pointer scratch out index rem
    (leftAbsControl.trans leftControl) sourceData
  have rightFinalData := TailData.of_control right rightAbs stp pointer scratch out index rem
    (rightAbsControl.trans rightControl) rightData
  have leftFinalLocals := TailLocals.of_locals leftPad leftAbs stp pointer out index rem leftAbsLocals leftLocals
  have rightFinalLocals := TailLocals.of_locals rightPad rightAbs stp pointer out index rem rightAbsLocals rightLocals'
  have leftEnough : 33 ≤ leftAbs.clock := by rw [leftAbsClock, leftClock]; omega
  have rightEnough : 33 ≤ rightAbs.clock := by rw [rightAbsClock, rightClock']; omega
  have leftOutputRun := outputState_execute leftAbs stp out leftFinalLocals.stateLocal leftFinalLocals.outputLocal
    leftFinalData.outputMapped leftFinalData.copyCode leftEnough
  have rightOutputRun := outputState_execute rightAbs stp out rightFinalLocals.stateLocal rightFinalLocals.outputLocal
    rightFinalData.outputMapped rightFinalData.copyCode rightEnough
  have absEndian : leftAbs.be = rightAbs.be :=
    (congrArg (fun state => state.be) leftAbsControl).trans
      (padEndian.trans (congrArg (fun state => state.be) rightAbsControl).symm)
  have finalMemory := outputState_memory_agrees leftAbs rightAbs absEndian region absMemory stp out
    reads.outputWords reads.outputBytes
  have finalFfi := (outputState_ffi leftAbs stp out).trans (absFfi.trans (outputState_ffi rightAbs stp out).symm)
  have leftOutputClock := outputState_clock leftAbs stp out
  have rightOutputClock := outputState_clock rightAbs stp out
  refine ⟨emptyLocalsHOLFinite (outputState leftAbs stp out), emptyLocalsHOLFinite (outputState rightAbs stp out),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, finalFfi, finalMemory, ?_, ?_⟩
  · rw [paddingTail, paddingPrefix_execute source stp pointer scratch out index rem sourceLocals sourceData remBound sourceClock]
    change evaluateHOLFiniteState leftPad (.seq absorbPad (.seq outProgram (.return (.const 0#64)))) = _
    rw [StateSteps.next_sequence leftPad leftAbs _ _ leftAbsRun (by rw [leftAbsClock]; omega),
      StateSteps.next_sequence leftAbs (outputState leftAbs stp out) _ _ leftOutputRun leftOutputClock.1]
    exact BuildEntry.zero_return _
  · rw [paddingTail, paddingPrefix_execute right stp pointer scratch out index rem rightLocals rightData remBound rightClock]
    change evaluateHOLFiniteState rightPad (.seq absorbPad (.seq outProgram (.return (.const 0#64)))) = _
    rw [StateSteps.next_sequence rightPad rightAbs _ _ rightAbsRun (by rw [rightAbsClock]; omega),
      StateSteps.next_sequence rightAbs (outputState rightAbs stp out) _ _ rightOutputRun rightOutputClock.1]
    exact BuildEntry.zero_return _
  · change (outputState leftAbs stp out).clock ≤ source.clock
    rw [leftAbsClock, leftClock] at leftOutputClock
    omega
  · change source.clock - 194 ≤ (outputState leftAbs stp out).clock
    rw [leftAbsClock, leftClock] at leftOutputClock
    omega
  · change (outputState rightAbs stp out).clock ≤ right.clock
    rw [rightAbsClock, rightClock'] at rightOutputClock
    omega
  · change right.clock - 194 ≤ (outputState rightAbs stp out).clock
    rw [rightAbsClock, rightClock'] at rightOutputClock
    omega
  · exact (outputState_control leftAbs stp out).trans (leftAbsControl.trans leftControl)
  · exact (outputState_control rightAbs stp out).trans (rightAbsControl.trans rightControl)
  · intro query away
    exact (outputState_memory_away leftAbs stp out query away.2.2).trans ((leftAbsAway query away.1).trans
      (paddingPrefix_memory_away source pointer scratch query index rem remBound away.2.1))
  · intro query away
    exact (outputState_memory_away rightAbs stp out query away.2.2).trans ((rightAbsAway query away.1).trans
      (paddingPrefix_memory_away right pointer scratch query index rem remBound away.2.1))

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.paired_padding_execute
