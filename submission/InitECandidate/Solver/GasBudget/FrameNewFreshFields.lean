import InitECandidate.Solver.GasBudget.FrameNewFresh
import InitECandidate.Solver.GasBudget.FrameNewSuffixData

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The complete17-clock prefix writes only the new280-byte frame. Both real
arena calls preserve memory, and all stack/gas initialization stores are inside. -/
theorem fresh_memory_away (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower : BitVec 64) (words : MessageWords) (query : BitVec 64)
    (away : ∀ offset < size, query ≠ WitnessRadix.byteAddress (Arenas.rounded .down scratch 280#64) offset) :
    (fresh source scratch lower words).memory query = source.memory query := by
  let frame := Arenas.rounded .down scratch 280#64
  change WitnessRadix.WordWrites.write
    (memoryAllocated (zeroed source scratch lower) frame lower scratch).memory
    (FieldStores.writes frame (fields lower lower words)) query = source.memory query
  rw [WitnessRadix.WordWrites.write_away]
  · rw [allocation_memory_away]
    · exact zeroed_away source scratch lower query away
    · simp only [FieldStores.writes, stackFields, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨away 208 (by decide), away 8 (by decide), away 232 (by decide)⟩
  · simp only [FieldStores.writes, fields, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨away 224 (by decide), away 24 (by decide), away 40 (by decide), away 48 (by decide),
      away 56 (by decide), away 64 (by decide), away 72 (by decide)⟩

theorem fresh_frame_local (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower : BitVec 64) (words : MessageWords) :
    (fresh source scratch lower words).locals.lookup (ofString "e") =
      some (.val (.word (Arenas.rounded .down scratch 280#64))) := by
  exact (allocation_other (zeroed source scratch lower) (Arenas.rounded .down scratch 280#64) lower scratch
    "e" (by decide) (by decide)).trans (zeroed_fields source scratch lower).2.2.1

theorem fresh_message_local (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower message : BitVec 64) (words : MessageWords)
    (messageLocal : source.locals.lookup (ofString "msg") = some (.val (.word message))) :
    (fresh source scratch lower words).locals.lookup (ofString "msg") = some (.val (.word message)) := by
  simpa [fresh, initialized, memoryAllocated, stackInitialized, stackAllocated, zeroed, allocated,
    markedMemory, markedScratch, Arenas.post, WitnessRadix.QueryBranch.bind, setVarHOLFinite,
    HolFiniteMapExact.update, FUPDATE, ofString] using messageLocal

theorem fresh_empty_global (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower empty : BitVec 64) (words : MessageWords)
    (emptyGlobal : source.globals.lookup (ofString "evm_empty") = some (.val (.word empty))) :
    (fresh source scratch lower words).globals.lookup (ofString "evm_empty") = some (.val (.word empty)) := by
  simpa [fresh, initialized, memoryAllocated, stackInitialized, stackAllocated, zeroed, allocated,
    markedMemory, markedScratch, Arenas.post, Arenas.pointerName, WitnessRadix.QueryBranch.bind,
    setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using emptyGlobal

/-- The fresh constructor prefix derives its own suffix locals and carries
all six external words through the actual clear/allocations/stores. -/
theorem fresh_suffix_ready (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower message empty : BitVec 64) (words : MessageWords) (suffixWords : SuffixWords)
    (messageLocal : source.locals.lookup (ofString "msg") = some (.val (.word message)))
    (emptyGlobal : source.globals.lookup (ofString "evm_empty") = some (.val (.word empty)))
    (frameMapped : ∀ offset, offset + 8 ≤ 280 → offset % 8 = 0 →
      source.memaddrs (WitnessRadix.byteAddress (Arenas.rounded .down scratch 280#64) offset))
    (mapped : ∀ cell ∈ suffixCells message suffixWords, source.memaddrs cell.1)
    (stored : ∀ cell ∈ suffixCells message suffixWords, source.memory cell.1 = .word cell.2)
    (separate : ∀ cell ∈ suffixCells message suffixWords, ∀ offset < size,
      cell.1 ≠ WitnessRadix.byteAddress (Arenas.rounded .down scratch 280#64) offset) :
    SuffixReady (fresh source scratch lower words) (Arenas.rounded .down scratch 280#64) message suffixWords empty := by
  refine ⟨fresh_frame_local source scratch lower words, fresh_message_local source scratch lower message words messageLocal,
    fresh_empty_global source scratch lower empty words emptyGlobal, mapped, ?_, frameMapped⟩
  intro cell member
  rw [fresh_memory_away source scratch lower words cell.1 (separate cell member)]
  exact stored cell member

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.fresh_memory_away
#print axioms InitECandidate.Solver.GasBudget.FrameNew.fresh_frame_local
#print axioms InitECandidate.Solver.GasBudget.FrameNew.fresh_message_local
#print axioms InitECandidate.Solver.GasBudget.FrameNew.fresh_empty_global
#print axioms InitECandidate.Solver.GasBudget.FrameNew.fresh_suffix_ready
