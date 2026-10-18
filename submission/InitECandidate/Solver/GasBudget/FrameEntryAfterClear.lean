import InitECandidate.Solver.GasBudget.MessageCallPrefix

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- Preserve the frame entry facts across the actual message-call output
allocation/clear. Ownership bounds justify every saved read; the heap update
does not change either arena cursor or the empty-buffer global. -/
theorem Entry.after_result_clear (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower message empty : BitVec 64) (words : MessageWords)
    (addresses keys addressCount keyCount : BitVec 64) (cursor : Nat)
    (entry : Entry source scratch lower message empty words addresses keys addressCount keyCount)
    (region : MemoryRegion.Valid ⟨cursor, 96⟩)
    (messageBefore : ∀ offset ∈ messageOffsets, (message + BitVec.ofNat 64 offset).toNat < cursor)
    (inputsBefore : ∀ cell ∈ suffixCells message ⟨words.code, words.length, addresses, keys, addressCount, keyCount⟩, cell.1.toNat < cursor) :
    Entry (MessageCall.clearedState source cursor) scratch lower message empty words addresses keys addressCount keyCount := by
  have globals (name : String) (different : ofString "heap_ptr" ≠ ofString name) :
      (MessageCall.clearedState source cursor).globals.lookup (ofString name) = source.globals.lookup (ofString name) := by
    simp [MessageCall.clearedState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, different, Ne.symm different]
  refine ⟨⟨entry.code.scratchMark, entry.code.memoryMark, entry.code.scratch, entry.code.zero⟩,
    entry.memoryCode, entry.jumpCode, entry.logCode, entry.tableCode, entry.countCode,
    (globals "scratch_ptr" (by decide)).trans entry.scratchGlobal,
    (globals "frame_mem_ptr" (by decide)).trans entry.lowerGlobal,
    (globals "evm_empty" (by decide)).trans entry.emptyGlobal,
    entry.scratchAligned, entry.lowerAligned, entry.lengthFits, entry.room, entry.arena, entry.messageMapped,
    ?_, entry.messageProtected, entry.inputMapped, ?_, entry.inputProtected, entry.codeMapped⟩
  · intro offset member
    exact (MessageCall.cleared_earlier source cursor region _ (messageBefore offset member)).trans (entry.messageCells offset member)
  · intro cell member
    exact (MessageCall.cleared_earlier source cursor region _ (inputsBefore cell member)).trans (entry.inputCells cell member)

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.Entry.after_result_clear
