import InitECandidate.Solver.GasBudget.FrameNewEntry
import InitECandidate.Solver.GasBudget.MessageFieldFrame
import InitECandidate.Solver.MutableTable.TableState
import InitECandidate.Solver.MutableTable.MemoryRegionWord

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix MutableTable NaturalLayout

/-- Derive all frame input mapping/count/separation facts from the owned
root message and actual live warm-table headers. The original non-creation
root message starts with empty code, so no code-buffer mapping oracle is needed.
Arena cursor/code/global reachability remains explicit. -/
theorem empty_message_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower empty codePointer gas reservoir : BitVec 64) (start cursor floor storageFloor : Nat)
    (account storage : Plan) (accountSlots storageSlots : List Nat)
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (codes : Code source)
    (memoryCode : source.code.lookup (ofString "frame_mem_alloc") = some (Arenas.formals, Arenas.body .up, .one))
    (jumpCode : source.code.lookup (ofString "compute_jumpdests") = some (JumpDest.formals, JumpDest.body, .one))
    (logCode : source.code.lookup (ofString "lst_new_scratch") = some (ScratchList.formals, ScratchList.body, .one))
    (tableCode : source.code.lookup (ofString "htab_new_scratch") = some (ScratchTable.formals, ScratchTable.body, .one))
    (countCode : source.code.lookup (ofString "htab_count") = some (TableCount.formals, TableCount.body, .one))
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (lowerGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word lower)))
    (emptyGlobal : source.globals.lookup (ofString "evm_empty") = some (.val (.word empty)))
    (scratchAligned : scratch.toNat % 8 = 0) (lowerAligned : lower.toNat % 8 = 0)
    (lowerBound : 2701131776 ≤ lower.toNat) (scratchBound : scratch.toNat ≤ 33806089496)
    (room : lower.toNat + 2664 ≤ scratch.toNat)
    (region : MemoryRegion.Valid ⟨start, 176⟩) (persistent : scratch.toNat ≤ start)
    (accountTable : TableState source .account account accountSlots cursor floor)
    (storageTable : TableState source .storage storage storageSlots cursor storageFloor)
    (accountLater : start + 176 ≤ account.base .header) (storageLater : start + 176 ≤ storage.base .header)
    (codeCell : source.memory (BitVec.ofNat 64 start + 112#64) = .word codePointer)
    (lengthCell : source.memory (BitVec.ofNat 64 start + 120#64) = .word 0#64)
    (gasCell : source.memory (BitVec.ofNat 64 start + 40#64) = .word gas)
    (reservoirCell : source.memory (BitVec.ofNat 64 start + 48#64) = .word reservoir)
    (accountCell : source.memory (BitVec.ofNat 64 start + 152#64) = .word (cell account .header 0))
    (storageCell : source.memory (BitVec.ofNat 64 start + 160#64) = .word (cell storage .header 0)) :
    Entry source scratch lower (BitVec.ofNat 64 start) empty ⟨codePointer, 0#64, gas, reservoir⟩
      (cell account .header 0) (cell storage .header 0) (BitVec.ofNat 64 accountSlots.length) (BitVec.ofNat 64 storageSlots.length) := by
  have geo := construction_geometry scratch lower 8 scratchAligned lowerAligned (by decide) room
  have frameEnd : (framePointer scratch).toNat + 280 ≤ scratch.toNat := by have number := geo.1; omega
  have messageMapped (offset : Nat) (inside : offset + 8 ≤ 176) (aligned : offset % 8 = 0) :
      source.memaddrs (BitVec.ofNat 64 start + BitVec.ofNat 64 offset) := by
    rw [domain]
    exact MemoryRegion.word_mapped ⟨start, 176⟩ region offset inside aligned
  have messageProtected (offset : Nat) (inside : offset ≤ 176) :
      SuffixProtected (memoryPointer lower) (framePointer scratch) (BitVec.ofNat 64 start + BitVec.ofNat 64 offset) := by
    right
    rw [MessageField.field_number start offset region inside]
    omega
  have headerMapped (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) : source.memaddrs (cell plan .header 0 + 24#64) := by
    rw [constant_cell, domain]
    exact NaturalLayout.mapped kind plan valid .header 24 (by change 24 < 72; decide) (by decide)
  have headerProtected (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (later : start + 176 ≤ plan.base .header) :
      SuffixProtected (memoryPointer lower) (framePointer scratch) (cell plan .header 0 + 24#64) := by
    right
    rw [constant_cell, NaturalLayout.number kind plan valid .header 24 (by change 24 < 72; decide)]
    omega
  have accountCount : source.memory (cell account .header 0 + 24#64) = .word (BitVec.ofNat 64 accountSlots.length) := by
    rw [constant_cell]
    exact accountTable.header 24 _ (by simp [MemoryModel.headerEntries])
  have storageCount : source.memory (cell storage .header 0 + 24#64) = .word (BitVec.ofNat 64 storageSlots.length) := by
    rw [constant_cell]
    exact storageTable.header 24 _ (by simp [MemoryModel.headerEntries])
  refine ⟨codes, memoryCode, jumpCode, logCode, tableCode, countCode, scratchGlobal, lowerGlobal, emptyGlobal,
    scratchAligned, lowerAligned, by change (0#64 : BitVec 64).toNat + 63 < 2 ^ 64; decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [JumpDest.bitmapBytes] using room
  · intro query above below aligned
    rw [domain]
    exact BackingLayout.ordinary_mapped query (by omega) (by omega) aligned
  · intro offset member
    simp only [messageOffsets, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> exact messageMapped _ (by decide) (by decide)
  · intro offset member
    simp only [messageOffsets, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact codeCell
    · exact lengthCell
    · exact gasCell
    · exact reservoirCell
  · intro offset member
    simp only [messageOffsets, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> exact messageProtected _ (by decide)
  · intro entry member
    simp only [suffixCells, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact messageMapped 112 (by decide) (by decide)
    · exact messageMapped 120 (by decide) (by decide)
    · exact messageMapped 152 (by decide) (by decide)
    · exact messageMapped 160 (by decide) (by decide)
    · exact headerMapped .account account accountTable.valid
    · exact headerMapped .storage storage storageTable.valid
  · intro entry member
    simp only [suffixCells, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact codeCell
    · exact lengthCell
    · exact accountCell
    · exact storageCell
    · exact accountCount
    · exact storageCount
  · intro entry member
    simp only [suffixCells, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact messageProtected 112 (by decide)
    · exact messageProtected 120 (by decide)
    · exact messageProtected 152 (by decide)
    · exact messageProtected 160 (by decide)
    · exact headerProtected .account account accountTable.valid accountLater
    · exact headerProtected .storage storage storageTable.valid storageLater
  · intro offset impossible
    exact False.elim (Nat.not_lt_zero offset impossible)

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.empty_message_entry
