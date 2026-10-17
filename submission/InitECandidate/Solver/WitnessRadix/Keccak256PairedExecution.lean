import InitECandidate.Solver.WitnessRadix.Keccak256PairedAfter
import InitECandidate.Solver.WitnessRadix.Keccak256PairedLoop
import InitECandidate.Solver.WitnessRadix.Keccak256Composition

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact MemoryRegion
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- Complete actual keccak256 executions agree on public memory and every
observable FFI event when their actual input/read buffers agree. The two
programs' other code entries, private memory, caller locals and clocks may
differ. Each source execution retains its own checked clock allowance. -/
theorem paired_execute (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (stp pointer scratch out : BitVec 64) (length : Nat)
    (sourceLocals : EntryLocals source pointer out length) (rightLocals : EntryLocals right pointer out length)
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
    (small : length + 136 < 2^64) (sourceClock : price length ≤ source.clock) (rightClock : price length ≤ right.clock) :
    ∃ leftOutput rightOutput : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))), leftOutput) ∧
      evaluateHOLFiniteState right body = (some (.returned (.val (.word 0#64))), rightOutput) ∧
      leftOutput.clock ≤ source.clock ∧ source.clock - price length ≤ leftOutput.clock ∧
      rightOutput.clock ≤ right.clock ∧ right.clock - price length ≤ rightOutput.clock ∧
      KeccakAbsorb.hashControl leftOutput = KeccakAbsorb.hashControl source ∧
      KeccakAbsorb.hashControl rightOutput = KeccakAbsorb.hashControl right ∧
      leftOutput.ffi = rightOutput.ffi ∧ Agree region leftOutput.memory rightOutput.memory ∧
      (∀ query, Protected stp scratch out query → leftOutput.memory query = source.memory query) ∧
      (∀ query, Protected stp scratch out query → rightOutput.memory query = right.memory query) := by
  classical
  let leftEntry := hashingEntry source stp
  let rightEntry := hashingEntry right stp
  have leftArgs := hashingEntry_args source stp pointer out length sourceLocals
  have rightArgs := hashingEntry_args right stp pointer out length rightLocals
  have leftOut : leftEntry.locals.lookup (ofString "out") = some (.val (.word out)) :=
    (hashingEntry_other source stp "out" (by decide) (by decide)).trans sourceLocals.outputLocal
  have rightOut : rightEntry.locals.lookup (ofString "out") = some (.val (.word out)) :=
    (hashingEntry_other right stp "out" (by decide) (by decide)).trans rightLocals.outputLocal
  have leftData := EntryData.of_control source leftEntry stp pointer scratch out length rfl sourceData
  have rightData' := EntryData.of_control right rightEntry stp pointer scratch out length rfl rightData
  have entrySame : Agree region leftEntry.memory rightEntry.memory :=
    Zero.finalMemory_agrees region source.memory right.memory same stp 200
  have div := Nat.mod_add_div length 136
  have rem := Nat.mod_lt length (by decide : 0 < 136)
  obtain ⟨leftLoop, rightLoop, leftLoopRun, rightLoopRun, leftLoopClock, rightLoopClock,
    leftLoopControl, rightLoopControl, leftLoopIndex, rightLoopIndex, leftOther, rightOther,
    loopFfi, loopMemory, leftLoopAway, rightLoopAway⟩ :=
    paired_loop_execute leftEntry rightEntry stp pointer 0 length (length / 136) leftArgs rightArgs
      leftData.hashCode rightData'.hashCode leftData.blockMapped (bind_lookup_same _ _ _) (bind_lookup_same _ _ _)
      domain endian ffi region blockReads stateBytes entrySame small (by omega) (by omega)
      sourceData.stateAligned sourceData.stateFits
      (by change 20 * (length / 136) ≤ source.clock - 8; unfold price at sourceClock; omega)
      (by change 20 * (length / 136) ≤ right.clock - 8; unfold price at rightClock; omega)
  let index := 136 * (length / 136)
  have ordered : index ≤ length := by dsimp [index]; omega
  have remBound : length - index < 136 := by dsimp [index]; omega
  have leftAfterArgs : Args leftLoop stp pointer length :=
    ⟨(leftOther (ofString "stp") (by decide)).trans leftArgs.stateLocal,
      (leftOther (ofString "p") (by decide)).trans leftArgs.pointerLocal,
      (leftOther (ofString "n") (by decide)).trans leftArgs.lengthLocal⟩
  have rightAfterArgs : Args rightLoop stp pointer length :=
    ⟨(rightOther (ofString "stp") (by decide)).trans rightArgs.stateLocal,
      (rightOther (ofString "p") (by decide)).trans rightArgs.pointerLocal,
      (rightOther (ofString "n") (by decide)).trans rightArgs.lengthLocal⟩
  have leftAfterOut := (leftOther (ofString "out") (by decide)).trans leftOut
  have rightAfterOut := (rightOther (ofString "out") (by decide)).trans rightOut
  have leftAfterIndex : leftLoop.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))) := by
    simpa only [Nat.zero_add] using leftLoopIndex
  have rightAfterIndex : rightLoop.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))) := by
    simpa only [Nat.zero_add] using rightLoopIndex
  have leftAfterData := EntryData.of_control leftEntry leftLoop stp pointer scratch out length leftLoopControl leftData
  have rightAfterData := EntryData.of_control rightEntry rightLoop stp pointer scratch out length rightLoopControl rightData'
  have loopDomain : leftLoop.memaddrs = rightLoop.memaddrs :=
    (congrArg (fun state => state.memaddrs) leftLoopControl).trans
      (domain.trans (congrArg (fun state => state.memaddrs) rightLoopControl).symm)
  have loopEndian : leftLoop.be = rightLoop.be :=
    (congrArg (fun state => state.be) leftLoopControl).trans
      (endian.trans (congrArg (fun state => state.be) rightLoopControl).symm)
  obtain ⟨leftFinished, rightFinished, leftTail, rightTail, leftUpper, leftLower, rightUpper, rightLower,
    leftControl, rightControl, finalFfi, finalMemory, leftAway, rightAway⟩ :=
    paired_after_blocks_execute leftLoop rightLoop stp pointer scratch out index length leftAfterArgs rightAfterArgs
      leftAfterOut rightAfterOut leftAfterIndex rightAfterIndex
      (leftAfterData.tailData index ordered remBound) (rightAfterData.tailData index ordered remBound)
      loopDomain loopEndian loopFfi region tailReads loopMemory (by omega) ordered remBound
      (by rw [leftLoopClock]; change 194 ≤ source.clock - 8 - 20 * (length / 136); unfold price at sourceClock; omega)
      (by rw [rightLoopClock]; change 194 ≤ right.clock - 8 - 20 * (length / 136); unfold price at rightClock; omega)
  have leftRun := body_from_blocks source stp pointer scratch out length sourceData
    (by unfold price at sourceClock; omega) leftLoop leftFinished leftLoopRun
    (by change leftLoop.clock ≤ leftEntry.clock; rw [leftLoopClock]; omega) leftTail
  have rightRun := body_from_blocks right stp pointer scratch out length rightData
    (by unfold price at rightClock; omega) rightLoop rightFinished rightLoopRun
    (by change rightLoop.clock ≤ rightEntry.clock; rw [rightLoopClock]; omega) rightTail
  refine ⟨hashingExit source stp leftFinished, hashingExit right stp rightFinished,
    leftRun, rightRun, ?_, ?_, ?_, ?_, ?_, ?_, finalFfi, finalMemory, ?_, ?_⟩
  · change leftFinished.clock ≤ source.clock
    rw [leftLoopClock] at leftUpper
    change leftFinished.clock ≤ source.clock - 8 - 20 * (length / 136) at leftUpper
    omega
  · change source.clock - price length ≤ leftFinished.clock
    rw [leftLoopClock] at leftLower
    change source.clock - 8 - 20 * (length / 136) - 194 ≤ leftFinished.clock at leftLower
    unfold price
    omega
  · change rightFinished.clock ≤ right.clock
    rw [rightLoopClock] at rightUpper
    change rightFinished.clock ≤ right.clock - 8 - 20 * (length / 136) at rightUpper
    omega
  · change right.clock - price length ≤ rightFinished.clock
    rw [rightLoopClock] at rightLower
    change right.clock - 8 - 20 * (length / 136) - 194 ≤ rightFinished.clock at rightLower
    unfold price
    omega
  · exact (KeccakAbsorb.hashControl_restore source _ "stp").trans
      ((KeccakAbsorb.hashControl_restore _ leftFinished "i").trans (leftControl.trans leftLoopControl))
  · exact (KeccakAbsorb.hashControl_restore right _ "stp").trans
      ((KeccakAbsorb.hashControl_restore _ rightFinished "i").trans (rightControl.trans rightLoopControl))
  · intro query protection
    exact (leftAway query (Protected.tail stp scratch out query protection)).trans
      ((leftLoopAway query (Protected.tail stp scratch out query protection).1).trans
        (Zero.final_memory_away source.memory stp query 200
          (by intro offset inside; exact (protection.1 offset inside).1)))
  · intro query protection
    exact (rightAway query (Protected.tail stp scratch out query protection)).trans
      ((rightLoopAway query (Protected.tail stp scratch out query protection).1).trans
        (Zero.final_memory_away right.memory stp query 200
          (by intro offset inside; exact (protection.1 offset inside).1)))

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.paired_execute
