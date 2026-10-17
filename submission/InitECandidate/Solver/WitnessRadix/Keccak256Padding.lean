import InitECandidate.Solver.WitnessRadix.Keccak256PaddingPrefix

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def Away (stp scratch out query : BitVec 64) : Prop :=
  KeccakAbsorb.Away stp query ∧ CopyGeneral.Away scratch query 136 ∧ CopyGeneral.Away out query 32

/-- Complete literal final-block padding, absorption, digest output and
return. The body uses at most194 source clocks and preserves outside cells. -/
theorem padding_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pointer scratch out : BitVec 64) (index rem : Nat)
    (locals : TailLocals source stp pointer out index rem) (data : TailData source stp pointer scratch out index rem)
    (remBound : rem<136) (enough : 194≤source.clock) :
    ∃ output : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source paddingTail=(some (.returned (.val (.word 0#64))),output) ∧
      output.clock≤source.clock ∧ source.clock-194≤output.clock ∧ KeccakAbsorb.hashControl output=KeccakAbsorb.hashControl source ∧
      ∀ query,Away stp scratch out query → output.memory query=source.memory query := by
  classical
  let padded := paddingPrefixState source pointer scratch index rem
  have prefixControl : KeccakAbsorb.hashControl padded=KeccakAbsorb.hashControl source := paddingPrefix_control source pointer scratch index rem
  have paddedData := TailData.of_control source padded stp pointer scratch out index rem prefixControl data
  have paddedLocals := TailLocals.of_locals source padded stp pointer out index rem (paddingPrefix_locals source pointer scratch index rem) locals
  have paddedClock : padded.clock=source.clock-(CopyGeneral.cost (byteAddress pointer index) scratch rem+7) := paddingPrefix_clock source pointer scratch index rem
  have costBound := CopyGeneral.cost_le (byteAddress pointer index) scratch rem
  have args : evalListHOLFinite padded (h := fun address => Classical.propDecidable (padded.memaddrs address)) [localVar "stp",pad]=some (KeccakAbsorb.values stp scratch) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,pad,toExact,paddedLocals.stateLocal,paddedData.scratchGlobal,KeccakAbsorb.values]
  obtain ⟨absorbed,absRun,absLocals,absClock,absControl,absMemory⟩ := KeccakAbsorb.call_execute padded [localVar "stp",pad] stp scratch args
    paddedData.hashCode.block paddedData.hashCode.perm paddedData.hashCode.oracleEq paddedData.stateAligned paddedData.stateFits paddedData.absorbMapped
    (by rw [paddedClock]; omega)
  change evaluateHOLFiniteState padded absorbPad=(none,absorbed) at absRun
  have absorbedData := TailData.of_control source absorbed stp pointer scratch out index rem (absControl.trans prefixControl) data
  have absorbedLocals := TailLocals.of_locals padded absorbed stp pointer out index rem absLocals paddedLocals
  obtain ⟨written,outRun,outLocals,outUpper,outLower,outControl,outMemory⟩ := output_execute absorbed stp out
    absorbedLocals.stateLocal absorbedLocals.outputLocal absorbedData.outputMapped absorbedData.copyCode
    (by rw [absClock,paddedClock]; omega)
  refine ⟨emptyLocalsHOLFinite written,?_,?_,?_,?_,?_⟩
  · rw [paddingTail,paddingPrefix_execute source stp pointer scratch out index rem locals data remBound enough]
    change evaluateHOLFiniteState padded (.seq absorbPad (.seq outProgram (.return (.const 0#64))))=_
    rw [StateSteps.next_sequence padded absorbed _ _ absRun (by rw [absClock]; omega),
      StateSteps.next_sequence absorbed written _ _ outRun outUpper]
    exact BuildEntry.zero_return written
  · change written.clock≤source.clock
    rw [absClock,paddedClock] at outUpper
    omega
  · change source.clock-194≤written.clock
    rw [absClock,paddedClock] at outLower
    omega
  · exact outControl.trans (absControl.trans prefixControl)
  · intro query away
    exact (outMemory query away.2.2).trans ((absMemory query away.1).trans
      (paddingPrefix_memory_away source pointer scratch query index rem remBound away.2.1))

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.padding_execute
