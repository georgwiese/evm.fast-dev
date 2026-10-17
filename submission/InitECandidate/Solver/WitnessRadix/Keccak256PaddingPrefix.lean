import InitECandidate.Solver.WitnessRadix.Keccak256TailContext

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def zeroPadState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  {source with memory := Zero.finalMemory source.memory scratch 136,clock := source.clock-6}
def paddingPrefixState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer scratch : BitVec 64) (index rem : Nat) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  lastPadState (firstPadState (CopyGeneral.callState (zeroPadState source scratch) (byteAddress pointer index) scratch rem)
    scratch (BitVec.ofNat 64 rem)) scratch

theorem paddingPrefix_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer scratch : BitVec 64) (index rem : Nat) :
    (paddingPrefixState source pointer scratch index rem).locals=source.locals := rfl

theorem paddingPrefix_control (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer scratch : BitVec 64) (index rem : Nat) :
    KeccakAbsorb.hashControl (paddingPrefixState source pointer scratch index rem)=KeccakAbsorb.hashControl source := rfl

theorem paddingPrefix_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer scratch : BitVec 64) (index rem : Nat) :
    (paddingPrefixState source pointer scratch index rem).clock=source.clock-(CopyGeneral.cost (byteAddress pointer index) scratch rem+7) := by
  change source.clock-6-(CopyGeneral.cost (byteAddress pointer index) scratch rem+1)=_
  omega

theorem paddingPrefix_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pointer scratch out : BitVec 64) (index rem : Nat)
    (locals : TailLocals source stp pointer out index rem) (data : TailData source stp pointer scratch out index rem)
    (remBound : rem<136) (enough : 194≤source.clock) (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (.seq zeroPad (.seq copyPad (.seq padFirst (.seq padLast continuation))))=
      evaluateHOLFiniteState (paddingPrefixState source pointer scratch index rem) continuation := by
  classical
  let zeroed := zeroPadState source scratch
  let copied := CopyGeneral.callState zeroed (byteAddress pointer index) scratch rem
  let first := firstPadState copied scratch (BitVec.ofNat 64 rem)
  have zeroArgs : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [pad,.const 136#64]=some (Zero.values scratch 136) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,pad,toExact,data.scratchGlobal,Zero.values]
  have zeroRun : evaluateHOLFiniteState source zeroPad=(none,zeroed) :=
    Zero.call_execute source [pad,.const 136#64] scratch 136 zeroArgs data.zeroCode (by decide) (by decide)
      data.scratchAligned data.zeroMapped (by change 6≤source.clock; omega)
  have zeroData := TailData.of_control source zeroed stp pointer scratch out index rem rfl data
  have zeroLocals := TailLocals.of_locals source zeroed stp pointer out index rem rfl locals
  have copyArgs : evalListHOLFinite zeroed (h := fun address => Classical.propDecidable (zeroed.memaddrs address))
      [pad,.op .add [localVar "p",localVar "i"],localVar "rem"]=some (CopyGeneral.values scratch (byteAddress pointer index) rem) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,evalListHOLExact,pad,localVar,toExact,
      zeroData.scratchGlobal,zeroLocals.pointerLocal,zeroLocals.indexLocal,zeroLocals.remLocal,
      valueIsWord,valueWord,wordOpHOL,wordOp,CopyGeneral.values,byteAddress]
  have costBound := CopyGeneral.cost_le (byteAddress pointer index) scratch rem
  have copyRun : evaluateHOLFiniteState zeroed copyPad=(none,copied) :=
    CopyGeneral.call_execute zeroed _ (byteAddress pointer index) scratch rem copyArgs zeroData.copyCode zeroData.copyMapped
      (by omega) (by change CopyGeneral.cost (byteAddress pointer index) scratch rem+1≤source.clock-6; omega)
  have copiedData := TailData.of_control source copied stp pointer scratch out index rem rfl data
  have copiedLocals := TailLocals.of_locals source copied stp pointer out index rem rfl locals
  have firstRun := pad_first_execute copied scratch (BitVec.ofNat 64 rem) copiedData.scratchGlobal copiedLocals.remLocal copiedData.firstMapped
  have firstData := TailData.of_control source first stp pointer scratch out index rem rfl data
  have lastRun := pad_last_execute first scratch firstData.scratchGlobal firstData.lastMapped
  rw [StateSteps.next_sequence source zeroed _ _ zeroRun (by change source.clock-6≤source.clock; omega),
    StateSteps.next_sequence zeroed copied _ _ copyRun (by change zeroed.clock-(CopyGeneral.cost (byteAddress pointer index) scratch rem+1)≤zeroed.clock; omega),
    StateSteps.next_sequence copied first _ _ firstRun (Nat.le_refl _),
    StateSteps.next_sequence first (lastPadState first scratch) _ _ lastRun (Nat.le_refl _)]
  rfl

theorem paddingPrefix_memory_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer scratch query : BitVec 64) (index rem : Nat)
    (remBound : rem<136) (away : CopyGeneral.Away scratch query 136) :
    (paddingPrefixState source pointer scratch index rem).memory query=source.memory query := by
  let zeroed := zeroPadState source scratch
  let copied := CopyGeneral.callState zeroed (byteAddress pointer index) scratch rem
  let first := firstPadState copied scratch (BitVec.ofNat 64 rem)
  have lastFrame : (lastPadState first scratch).memory query=first.memory query :=
    ByteStore.away first.memory first.be (scratch+135#64) query
      (BitVec.ofNat 8 (lastPadWord first scratch).toNat) (away 135 (by decide)).2
  have firstFrame : first.memory query=copied.memory query :=
    ByteStore.away copied.memory copied.be (scratch+BitVec.ofNat 64 rem) query 1#8 (away rem remBound).2
  have copyFrame := CopyGeneral.call_memory_away zeroed (byteAddress pointer index) scratch query rem
    (by intro offset inside; exact away offset (by omega))
  have zeroFrame : zeroed.memory query=source.memory query :=
    Zero.final_memory_away source.memory scratch query 136 (by intro offset inside; exact (away offset inside).1)
  exact lastFrame.trans (firstFrame.trans (copyFrame.trans zeroFrame))

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.paddingPrefix_locals
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.paddingPrefix_control
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.paddingPrefix_clock
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.paddingPrefix_execute
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.paddingPrefix_memory_away
