import InitECandidate.Solver.GasBudget.FrameNewExecution

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original constructor-entry conditions, independent of callee locals/clock.
Reachability from actual transaction/message construction remains a separate
obligation. No callee execution, result or intermediate preservation is assumed. -/
structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower message empty : BitVec 64) (words : MessageWords)
    (addresses keys addressCount keyCount : BitVec 64) : Prop where
  code : Code source
  memoryCode : source.code.lookup (ofString "frame_mem_alloc") = some (Arenas.formals, Arenas.body .up, .one)
  jumpCode : source.code.lookup (ofString "compute_jumpdests") = some (JumpDest.formals, JumpDest.body, .one)
  logCode : source.code.lookup (ofString "lst_new_scratch") = some (ScratchList.formals, ScratchList.body, .one)
  tableCode : source.code.lookup (ofString "htab_new_scratch") = some (ScratchTable.formals, ScratchTable.body, .one)
  countCode : source.code.lookup (ofString "htab_count") = some (TableCount.formals, TableCount.body, .one)
  scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch))
  lowerGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word lower))
  emptyGlobal : source.globals.lookup (ofString "evm_empty") = some (.val (.word empty))
  scratchAligned : scratch.toNat % 8 = 0
  lowerAligned : lower.toNat % 8 = 0
  lengthFits : words.length.toNat + 63 < 2 ^ 64
  room : lower.toNat + JumpDest.bitmapBytes words.length.toNat + 2656 ≤ scratch.toNat
  arena : ArenaMapped source lower scratch
  messageMapped : ∀ offset ∈ messageOffsets, source.memaddrs (message + BitVec.ofNat 64 offset)
  messageCells : ∀ offset ∈ messageOffsets, source.memory (message + BitVec.ofNat 64 offset) = .word (words.atOffset offset)
  messageProtected : ∀ offset ∈ messageOffsets,
    SuffixProtected (memoryPointer lower) (framePointer scratch) (message + BitVec.ofNat 64 offset)
  inputMapped : ∀ cell ∈ suffixCells message ⟨words.code, words.length, addresses, keys, addressCount, keyCount⟩, source.memaddrs cell.1
  inputCells : ∀ cell ∈ suffixCells message ⟨words.code, words.length, addresses, keys, addressCount, keyCount⟩, source.memory cell.1 = .word cell.2
  inputProtected : ∀ cell ∈ suffixCells message ⟨words.code, words.length, addresses, keys, addressCount, keyCount⟩,
    SuffixProtected (memoryPointer lower) (framePointer scratch) cell.1
  codeMapped : ∀ offset < words.length.toNat,
    source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress words.code offset))

theorem Entry.relocals_clock {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {scratch lower message empty : BitVec 64} {words : MessageWords} {addresses keys addressCount keyCount : BitVec 64}
    (entry : Entry source scratch lower message empty words addresses keys addressCount keyCount)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat) :
    Entry {source with locals := locals, clock := clock} scratch lower message empty words addresses keys addressCount keyCount :=
  ⟨⟨entry.code.scratchMark, entry.code.memoryMark, entry.code.scratch, entry.code.zero⟩,
   entry.memoryCode, entry.jumpCode, entry.logCode, entry.tableCode, entry.countCode,
   entry.scratchGlobal, entry.lowerGlobal, entry.emptyGlobal, entry.scratchAligned, entry.lowerAligned,
   entry.lengthFits, entry.room, entry.arena, entry.messageMapped, entry.messageCells, entry.messageProtected,
   entry.inputMapped, entry.inputCells, entry.inputProtected, entry.codeMapped⟩

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.Entry.relocals_clock
