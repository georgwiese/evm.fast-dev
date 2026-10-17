import InitECandidate.Solver.WitnessRadix.Keccak256PairedBlock
import InitECandidate.Solver.WitnessRadix.Keccak256Loop

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- Full-block hashing preserves the agreed public region and identical
observable event history through arbitrarily many blocks. -/
theorem paired_loop_execute (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (stp pointer : BitVec 64) (index length rounds : Nat)
    (sourceArgs : Args source stp pointer length) (rightArgs : Args right stp pointer length)
    (sourceCode : Code source) (rightCode : Code right) (mapped : Mapped source stp pointer length)
    (sourceIndex : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (rightIndex : right.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (domain : source.memaddrs = right.memaddrs) (endian : source.be = right.be)
    (ffi : source.ffi = right.ffi)
    (region : BitVec 64 → Prop)
    (reads : ∀ offset, offset + 136 ≤ length →
      KeccakAbsorb.ReadRegion region stp (byteAddress pointer offset)
        (KeccakAbsorb.isUnaligned (byteAddress pointer offset)))
    (stateBytes : ∀ offset < 200,
      region (panByteAlignHOL (width := 64) (byteAddress stp offset)))
    (same : ∀ query, region query → source.memory query = right.memory query)
    (small : length + 136 < 2^64)
    (lower : index + 136 * rounds ≤ length) (upper : length < index + 136 * (rounds + 1))
    (aligned : stp.toNat % 8 = 0) (fits : stp.toNat + 200 < 2^64)
    (sourceClock : 20 * rounds ≤ source.clock) (rightClock : 20 * rounds ≤ right.clock) :
    ∃ leftOutput rightOutput : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source blocks = (none, leftOutput) ∧
      evaluateHOLFiniteState right blocks = (none, rightOutput) ∧
      leftOutput.clock = source.clock - 20 * rounds ∧ rightOutput.clock = right.clock - 20 * rounds ∧
      KeccakAbsorb.hashControl leftOutput = KeccakAbsorb.hashControl source ∧
      KeccakAbsorb.hashControl rightOutput = KeccakAbsorb.hashControl right ∧
      leftOutput.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (index + 136 * rounds)))) ∧
      rightOutput.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (index + 136 * rounds)))) ∧
      (∀ name : MlS, ofString "i" ≠ name → leftOutput.locals.lookup name = source.locals.lookup name) ∧
      (∀ name : MlS, ofString "i" ≠ name → rightOutput.locals.lookup name = right.locals.lookup name) ∧
      leftOutput.ffi = rightOutput.ffi ∧
      (∀ query, region query → leftOutput.memory query = rightOutput.memory query) ∧
      (∀ query, KeccakAbsorb.Away stp query → leftOutput.memory query = source.memory query) ∧
      (∀ query, KeccakAbsorb.Away stp query → rightOutput.memory query = right.memory query) := by
  classical
  induction rounds generalizing source right index with
  | zero =>
    have leftTest := condition_read source index length small (by omega) sourceIndex sourceArgs.lengthLocal
    have rightTest := condition_read right index length small (by omega) rightIndex rightArgs.lengthLocal
    have inactive : ¬ index + 136 ≤ length := by omega
    simp only [if_neg inactive] at leftTest rightTest
    refine ⟨source, right, ?_, ?_, by simp, by simp, rfl, rfl, ?_, ?_, ?_, ?_, ffi, same, ?_, ?_⟩
    · rw [blocks, evaluateHOLFiniteState_while_total, leftTest]; simp
    · rw [blocks, evaluateHOLFiniteState_while_total, rightTest]; simp
    · simpa using sourceIndex
    · simpa using rightIndex
    · intro name different; rfl
    · intro name different; rfl
    · intro query away; rfl
    · intro query away; rfl
  | succ rounds ih =>
    have active : index + 136 ≤ length := by omega
    let leftEntry := decClockHOLFinite source
    let rightEntry := decClockHOLFinite right
    have leftEntryControl : KeccakAbsorb.hashControl leftEntry = KeccakAbsorb.hashControl source :=
      KeccakAbsorb.hashControl_clock source (source.clock - 1)
    have rightEntryControl : KeccakAbsorb.hashControl rightEntry = KeccakAbsorb.hashControl right :=
      KeccakAbsorb.hashControl_clock right (right.clock - 1)
    have leftEntryArgs : Args leftEntry stp pointer length :=
      ⟨sourceArgs.stateLocal, sourceArgs.pointerLocal, sourceArgs.lengthLocal⟩
    have rightEntryArgs : Args rightEntry stp pointer length :=
      ⟨rightArgs.stateLocal, rightArgs.pointerLocal, rightArgs.lengthLocal⟩
    have leftEntryCode := Code.of_control source leftEntry leftEntryControl sourceCode
    have rightEntryCode := Code.of_control right rightEntry rightEntryControl rightCode
    have entryMapped := mapped_of_control source leftEntry stp pointer length leftEntryControl mapped
    obtain ⟨leftNext, rightNext, leftBody, rightBody, leftLocals, rightLocals,
      leftBodyClock, rightBodyClock, leftBodyControl, rightBodyControl, nextFfi, nextMemory,
      leftBodyAway, rightBodyAway⟩ := paired_block_execute leftEntry rightEntry stp pointer index length
        leftEntryArgs rightEntryArgs leftEntryCode rightEntryCode entryMapped sourceIndex rightIndex
        domain endian ffi region (reads index active) stateBytes same active aligned fits
        (by change 19 ≤ source.clock - 1; omega) (by change 19 ≤ right.clock - 1; omega)
    have leftNextArgs := Args.of_index leftEntry leftNext stp pointer length
      (BitVec.ofNat 64 (index + 136)) leftLocals leftEntryArgs
    have rightNextArgs := Args.of_index rightEntry rightNext stp pointer length
      (BitVec.ofNat 64 (index + 136)) rightLocals rightEntryArgs
    have leftNextCode := Code.of_control leftEntry leftNext leftBodyControl leftEntryCode
    have rightNextCode := Code.of_control rightEntry rightNext rightBodyControl rightEntryCode
    have nextMapped := mapped_of_control leftEntry leftNext stp pointer length leftBodyControl entryMapped
    have leftNextIndex : leftNext.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (index + 136)))) := by
      rw [leftLocals, bind_lookup_same]
    have rightNextIndex : rightNext.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (index + 136)))) := by
      rw [rightLocals, bind_lookup_same]
    have leftClock : leftNext.clock = source.clock - 20 := by
      rw [leftBodyClock]; change source.clock - 1 - 19 = source.clock - 20; omega
    have rightClock : rightNext.clock = right.clock - 20 := by
      rw [rightBodyClock]; change right.clock - 1 - 19 = right.clock - 20; omega
    have leftDomain : leftNext.memaddrs = source.memaddrs :=
      congrArg (fun state => state.memaddrs) (leftBodyControl.trans leftEntryControl)
    have rightDomain : rightNext.memaddrs = right.memaddrs :=
      congrArg (fun state => state.memaddrs) (rightBodyControl.trans rightEntryControl)
    have leftEndian : leftNext.be = source.be :=
      congrArg (fun state => state.be) (leftBodyControl.trans leftEntryControl)
    have rightEndian : rightNext.be = right.be :=
      congrArg (fun state => state.be) (rightBodyControl.trans rightEntryControl)
    obtain ⟨leftOutput, rightOutput, leftTail, rightTail, leftTailClock, rightTailClock,
      leftTailControl, rightTailControl, leftTailIndex, rightTailIndex, leftOther, rightOther,
      finalFfi, finalMemory, leftTailAway, rightTailAway⟩ :=
      ih leftNext rightNext (index + 136) leftNextArgs rightNextArgs leftNextCode rightNextCode nextMapped
        leftNextIndex rightNextIndex (leftDomain.trans (domain.trans rightDomain.symm))
        (leftEndian.trans (endian.trans rightEndian.symm)) nextFfi nextMemory (by omega) (by omega)
        (by rw [leftClock]; omega) (by rw [rightClock]; omega)
    refine ⟨leftOutput, rightOutput, ?_, ?_, ?_, ?_,
      leftTailControl.trans (leftBodyControl.trans leftEntryControl),
      rightTailControl.trans (rightBodyControl.trans rightEntryControl), ?_, ?_, ?_, ?_,
      finalFfi, finalMemory, ?_, ?_⟩
    · have test := condition_read source index length small (by omega) sourceIndex sourceArgs.lengthLocal
      simp only [if_pos active] at test
      rw [blocks, evaluateHOLFiniteState_while_total, test]
      simp only [show (1#64 : BitVec 64) ≠ (0 : BitVec 64) from by decide,
        ↓reduceIte, if_neg (show source.clock ≠ 0 by omega)]
      rw [leftBody, StateSteps.fixed_clock leftEntry leftNext none (by rw [leftBodyClock]; omega)]
      exact leftTail
    · have test := condition_read right index length small (by omega) rightIndex rightArgs.lengthLocal
      simp only [if_pos active] at test
      rw [blocks, evaluateHOLFiniteState_while_total, test]
      simp only [show (1#64 : BitVec 64) ≠ (0 : BitVec 64) from by decide,
        ↓reduceIte, if_neg (show right.clock ≠ 0 by omega)]
      rw [rightBody, StateSteps.fixed_clock rightEntry rightNext none (by rw [rightBodyClock]; omega)]
      exact rightTail
    · rw [leftTailClock, leftClock]; omega
    · rw [rightTailClock, rightClock]; omega
    · have total : index + 136 + 136 * rounds = index + 136 * (rounds + 1) := by omega
      simpa only [total] using leftTailIndex
    · have total : index + 136 + 136 * rounds = index + 136 * (rounds + 1) := by omega
      simpa only [total] using rightTailIndex
    · intro name different
      rw [leftOther name different, leftLocals]
      simp [QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, different, leftEntry, decClockHOLFinite]
    · intro name different
      rw [rightOther name different, rightLocals]
      simp [QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, different, rightEntry, decClockHOLFinite]
    · intro query away
      exact (leftTailAway query away).trans (leftBodyAway query away)
    · intro query away
      exact (rightTailAway query away).trans (rightBodyAway query away)

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.paired_loop_execute
