import InitECandidate.Solver.WitnessRadix.Keccak256PairedPadding
import InitECandidate.Solver.WitnessRadix.Keccak256After

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact MemoryRegion
open Flapjack.Basis.Pure.MlString QueryBranch

theorem after_blocks_from_padding (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (stp pointer out : BitVec 64) (index length : Nat)
    (args : Args source stp pointer length)
    (outLocal : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (small : length < 2^64) (ordered : index ≤ length)
    (finished : PanSemStateFiniteExact 64 Guest.HostMemory)
    (run : evaluateHOLFiniteState (bind source "rem" (BitVec.ofNat 64 (length - index))) paddingTail =
      (some (.returned (.val (.word 0#64))), finished)) :
    evaluateHOLFiniteState source afterBlocks =
      (some (.returned (.val (.word 0#64))), restore source "rem" finished) := by
  have sub : BitVec.ofNat 64 length - BitVec.ofNat 64 index = BitVec.ofNat 64 (length - index) :=
    BitVec.ofNat_sub_ofNat_of_le length index (by omega) ordered
  have read : eval source remainder = some (.val (.word (BitVec.ofNat 64 (length - index)))) := by
    simp [eval, remainder, localVar, evalHOLExact, evalListHOLExact, toExact,
      args.lengthLocal, indexLocal, valueIsWord, valueWord, wordOpHOL, wordOp, sub]
  simp only [eval] at read
  rw [afterBlocks_shape, evaluateHOLFiniteState_dec_total]
  simp only [read, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let result := evaluateHOLFiniteState (bind source "rem" (BitVec.ofNat 64 (length - index))) paddingTail
    (result.1, restore source "rem" result.2)) = _
  rw [run]

theorem after_entry_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (stp pointer out : BitVec 64) (index length : Nat) (args : Args source stp pointer length)
    (outLocal : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index)))) :
    TailLocals (bind source "rem" (BitVec.ofNat 64 (length - index))) stp pointer out index (length - index) := by
  constructor
  · exact (bind_lookup_other source "rem" "stp" _ (by decide)).trans args.stateLocal
  · exact (bind_lookup_other source "rem" "p" _ (by decide)).trans args.pointerLocal
  · exact (bind_lookup_other source "rem" "out" _ (by decide)).trans outLocal
  · exact (bind_lookup_other source "rem" "i" _ (by decide)).trans indexLocal
  · exact bind_lookup_same source "rem" _

theorem paired_after_blocks_execute (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (stp pointer scratch out : BitVec 64) (index length : Nat)
    (sourceArgs : Args source stp pointer length) (rightArgs : Args right stp pointer length)
    (sourceOut : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (rightOut : right.locals.lookup (ofString "out") = some (.val (.word out)))
    (sourceIndex : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (rightIndex : right.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (sourceData : TailData source stp pointer scratch out index (length - index))
    (rightData : TailData right stp pointer scratch out index (length - index))
    (domain : source.memaddrs = right.memaddrs) (endian : source.be = right.be)
    (ffi : source.ffi = right.ffi) (region : BitVec 64 → Prop)
    (reads : TailReads region stp pointer scratch index (length - index))
    (same : Agree region source.memory right.memory)
    (small : length < 2^64) (ordered : index ≤ length) (remBound : length - index < 136)
    (sourceClock : 194 ≤ source.clock) (rightClock : 194 ≤ right.clock) :
    ∃ leftOutput rightOutput : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source afterBlocks = (some (.returned (.val (.word 0#64))), leftOutput) ∧
      evaluateHOLFiniteState right afterBlocks = (some (.returned (.val (.word 0#64))), rightOutput) ∧
      leftOutput.clock ≤ source.clock ∧ source.clock - 194 ≤ leftOutput.clock ∧
      rightOutput.clock ≤ right.clock ∧ right.clock - 194 ≤ rightOutput.clock ∧
      KeccakAbsorb.hashControl leftOutput = KeccakAbsorb.hashControl source ∧
      KeccakAbsorb.hashControl rightOutput = KeccakAbsorb.hashControl right ∧
      leftOutput.ffi = rightOutput.ffi ∧ Agree region leftOutput.memory rightOutput.memory ∧
      (∀ query, Away stp scratch out query → leftOutput.memory query = source.memory query) ∧
      (∀ query, Away stp scratch out query → rightOutput.memory query = right.memory query) := by
  let leftEntry := bind source "rem" (BitVec.ofNat 64 (length - index))
  let rightEntry := bind right "rem" (BitVec.ofNat 64 (length - index))
  have leftLocals := after_entry_locals source stp pointer out index length sourceArgs sourceOut sourceIndex
  have rightLocals := after_entry_locals right stp pointer out index length rightArgs rightOut rightIndex
  have leftData := TailData.of_control source leftEntry stp pointer scratch out index (length - index) rfl sourceData
  have rightData' := TailData.of_control right rightEntry stp pointer scratch out index (length - index) rfl rightData
  obtain ⟨leftFinished, rightFinished, leftRun, rightRun, leftUpper, leftLower, rightUpper, rightLower,
    leftControl, rightControl, finalFfi, finalMemory, leftAway, rightAway⟩ :=
    paired_padding_execute leftEntry rightEntry stp pointer scratch out index (length - index)
      leftLocals rightLocals leftData rightData' domain endian ffi region reads same remBound sourceClock rightClock
  refine ⟨restore source "rem" leftFinished, restore right "rem" rightFinished,
    after_blocks_from_padding source stp pointer out index length sourceArgs sourceOut sourceIndex small ordered leftFinished leftRun,
    after_blocks_from_padding right stp pointer out index length rightArgs rightOut rightIndex small ordered rightFinished rightRun,
    leftUpper, leftLower, rightUpper, rightLower, ?_, ?_, finalFfi, finalMemory, leftAway, rightAway⟩
  · exact (KeccakAbsorb.hashControl_restore source leftFinished "rem").trans leftControl
  · exact (KeccakAbsorb.hashControl_restore right rightFinished "rem").trans rightControl

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.after_blocks_from_padding
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.after_entry_locals
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.paired_after_blocks_execute
