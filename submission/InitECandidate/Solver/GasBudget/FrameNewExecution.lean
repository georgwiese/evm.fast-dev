import InitECandidate.Solver.GasBudget.FrameNewFreshCanonical
import InitECandidate.Solver.GasBudget.FrameNewSuffix

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def finalScratch (scratch : BitVec 64) (length : BitVec 64) : BitVec 64 :=
  ScratchTable.cursor (ScratchList.buffer (Arenas.rounded .down (stackPointer scratch) (JumpDest.bytesWord length)) 32#64) 272

set_option maxHeartbeats 1000000 in
/-- Entire unchanged frame_new body, including every allocator, clear, bitmap
iteration, list/table constructor, count call, scalar store, return and scope.
The fresh regular ledger is exactly incoming MSG_GAS. The remaining premises
are original-entry code, mapped/separated inputs, arena room and clock; no
intermediate helper success, zero counter or memory frame is assumed.
These source clocks omit straight-line work and are not a target runtime K. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower message empty : BitVec 64) (words : MessageWords)
    (addresses keys addressCount keyCount : BitVec 64)
    (code : Code source)
    (memoryCode : source.code.lookup (ofString "frame_mem_alloc") = some (Arenas.formals, Arenas.body .up, .one))
    (jumpCode : source.code.lookup (ofString "compute_jumpdests") = some (JumpDest.formals, JumpDest.body, .one))
    (logCode : source.code.lookup (ofString "lst_new_scratch") = some (ScratchList.formals, ScratchList.body, .one))
    (tableCode : source.code.lookup (ofString "htab_new_scratch") = some (ScratchTable.formals, ScratchTable.body, .one))
    (countCode : source.code.lookup (ofString "htab_count") = some (TableCount.formals, TableCount.body, .one))
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (lowerGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word lower)))
    (messageLocal : source.locals.lookup (ofString "msg") = some (.val (.word message)))
    (emptyGlobal : source.globals.lookup (ofString "evm_empty") = some (.val (.word empty)))
    (scratchAligned : scratch.toNat % 8 = 0) (lowerAligned : lower.toNat % 8 = 0)
    (lengthFits : words.length.toNat + 63 < 2 ^ 64)
    (room : lower.toNat + JumpDest.bitmapBytes words.length.toNat + 2656 ≤ scratch.toNat)
    (arena : ArenaMapped source lower scratch)
    (messageMapped : ∀ offset ∈ messageOffsets, source.memaddrs (message + BitVec.ofNat 64 offset))
    (messageCells : ∀ offset ∈ messageOffsets,
      source.memory (message + BitVec.ofNat 64 offset) = .word (words.atOffset offset))
    (messageProtected : ∀ offset ∈ messageOffsets,
      SuffixProtected (memoryPointer lower) (framePointer scratch) (message + BitVec.ofNat 64 offset))
    (inputMapped : ∀ cell ∈ suffixCells message ⟨words.code, words.length, addresses, keys, addressCount, keyCount⟩, source.memaddrs cell.1)
    (inputCells : ∀ cell ∈ suffixCells message ⟨words.code, words.length, addresses, keys, addressCount, keyCount⟩,
      source.memory cell.1 = .word cell.2)
    (inputProtected : ∀ cell ∈ suffixCells message ⟨words.code, words.length, addresses, keys, addressCount, keyCount⟩,
      SuffixProtected (memoryPointer lower) (framePointer scratch) cell.1)
    (codeMapped : ∀ offset < words.length.toNat,
      source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress words.code offset)))
    (enough : words.length.toNat + WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 37 ≤ source.clock) :
    ∃ (target : PanSemStateFiniteExact 64 Guest.HostMemory) (spent : Nat),
      spent ≤ words.length.toNat ∧
      evaluateHOLFiniteState source body = (some (.returned (.val (.word (framePointer scratch)))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with
        globals := (source.globals.update (ofString "frame_mem_ptr", .val (.word (memoryPointer lower)))).update
          (ofString "scratch_ptr", .val (.word (finalScratch scratch words.length)))
        memory := target.memory
        clock := source.clock - (WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 37 + spent)} ∧
      regularBudget target.memory (framePointer scratch) = words.gas.toNat ∧
      (∀ cell ∈ suffixCells message ⟨words.code, words.length, addresses, keys, addressCount, keyCount⟩,
        target.memory cell.1 = source.memory cell.1) ∧
      ∀ query, Arenas.Outside lower scratch query → target.memory query = source.memory query := by
  let suffixWords : SuffixWords := ⟨words.code, words.length, addresses, keys, addressCount, keyCount⟩
  let freshState := fresh source scratch lower words
  obtain ⟨frameNumber, frameAligned, stackNumber, stackAligned, memoryNumber, memoryAligned,
    frameFits, firstRoom, laterRoom, suffixRoom, stackOrder, memoryOrder⟩ :=
    construction_geometry scratch lower (JumpDest.bitmapBytes words.length.toNat) scratchAligned lowerAligned
      (JumpDest.bytes_geometry words.length.toNat).2.1 room
  have frameMapped : ∀ offset, offset + 8 ≤ size → offset % 8 = 0 →
      source.memaddrs (WitnessRadix.byteAddress (framePointer scratch) offset) := by
    intro offset inside aligned
    exact arena_mapped_subregion source lower scratch (framePointer scratch) size arena
      (by omega) (by change (framePointer scratch).toNat + 280 ≤ scratch.toNat; omega) frameAligned offset inside aligned
  have messageSeparate : ∀ readOffset ∈ messageOffsets, ∀ writeOffset < size,
      message + BitVec.ofNat 64 readOffset ≠ WitnessRadix.byteAddress (framePointer scratch) writeOffset := by
    intro readOffset member writeOffset inside
    exact suffix_protected_away (memoryPointer lower) (framePointer scratch) _ writeOffset
      (messageProtected readOffset member) memoryOrder frameFits inside
  have inputSeparate : ∀ cell ∈ suffixCells message suffixWords, ∀ offset < size,
      cell.1 ≠ WitnessRadix.byteAddress (framePointer scratch) offset := by
    intro cell member offset inside
    exact suffix_protected_away (memoryPointer lower) (framePointer scratch) cell.1 offset
      (inputProtected cell member) memoryOrder frameFits inside
  have ready : SuffixReady freshState (framePointer scratch) message suffixWords empty :=
    fresh_suffix_ready source scratch lower message empty words suffixWords messageLocal emptyGlobal
      frameMapped inputMapped inputCells inputSeparate
  have currentScratch : freshState.globals.lookup (ofString "scratch_ptr") = some (.val (.word (stackPointer scratch))) := by
    rw [fresh_globals]
    simp [HolFiniteMapExact.update, FUPDATE, ofString]
  have currentLower : freshState.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word (memoryPointer lower))) := by
    rw [fresh_globals]
    simp [HolFiniteMapExact.update, FUPDATE]
  have suffixArena : ArenaMapped freshState (memoryPointer lower) (stackPointer scratch) := by
    intro query start finish aligned
    apply arena
    · omega
    · omega
    · exact aligned
  have suffixMaps := suffix_mapped freshState (stackPointer scratch) (memoryPointer lower) words.length
    suffixArena stackAligned lengthFits suffixRoom
  have freshClock : freshState.clock = source.clock - 17 := (fresh_budget source scratch lower words).2
  obtain ⟨suffixTarget, spent, spentBound, suffixRun, suffixFrame, suffixBudget, suffixKept⟩ := suffix_execute freshState
    (stackPointer scratch) (memoryPointer lower) (framePointer scratch) message suffixWords empty ready
    jumpCode logCode tableCode code.scratch code.zero countCode currentScratch currentLower stackAligned memoryAligned
    lengthFits suffixRoom stackOrder frameFits inputProtected codeMapped
    suffixMaps.1 suffixMaps.2.1 suffixMaps.2.2.1 suffixMaps.2.2.2
    (by change words.length.toNat + WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 20 ≤ freshState.clock; rw [freshClock]; omega)
  have prefixRun := fresh_execute source scratch lower message words code memoryCode scratchGlobal lowerGlobal
    messageLocal lowerAligned firstRoom laterRoom frameMapped messageMapped messageCells messageSeparate (by omega) afterGas
  change evaluateHOLFiniteState source (program (initializedProgram afterGas)) =
    (let output := evaluateHOLFiniteState freshState afterGas
     (output.1, freshRestore source scratch lower output.2)) at prefixRun
  rw [suffixRun] at prefixRun
  let target := freshRestore source scratch lower suffixTarget
  refine ⟨target, spent, spentBound, ?_, ?_, ?_, ?_, ?_⟩
  · rw [actual_fresh_prefix]
    exact prefixRun
  · change emptyLocalsHOLFinite suffixTarget = _
    rw [suffixFrame, fresh_final_canonical]
    have clocks : freshState.clock - (WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 20 + spent) =
        source.clock - (WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 37 + spent) := by rw [freshClock]; omega
    change emptyLocalsHOLFinite {source with
      globals := (source.globals.update (ofString "frame_mem_ptr", .val (.word (memoryPointer lower)))).update
        (ofString "scratch_ptr", .val (.word (finalScratch scratch words.length)))
      memory := suffixTarget.memory
      clock := freshState.clock - (WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 20 + spent)} = _
    rw [clocks]
    rfl
  · exact suffixBudget.trans (fresh_budget source scratch lower words).1
  · intro cell member
    change suffixTarget.memory cell.1 = source.memory cell.1
    rw [suffixKept cell.1 (suffix_protected_safe (memoryPointer lower) (framePointer scratch) cell.1 (inputProtected cell member) memoryOrder frameFits)]
    exact fresh_memory_away source scratch lower words cell.1 (inputSeparate cell member)
  · intro query outside
    have protectedRead : SuffixProtected (memoryPointer lower) (framePointer scratch) query := by
      rcases outside with below | high
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    change suffixTarget.memory query = source.memory query
    rw [suffixKept query (suffix_protected_safe (memoryPointer lower) (framePointer scratch) query protectedRead memoryOrder frameFits)]
    apply fresh_memory_away
    intro offset inside
    exact suffix_protected_away (memoryPointer lower) (framePointer scratch) query offset protectedRead memoryOrder frameFits inside

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.execute
