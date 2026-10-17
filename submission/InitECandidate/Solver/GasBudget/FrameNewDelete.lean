import InitECandidate.Solver.GasBudget.FrameNewSuffixData
import InitECandidate.Solver.ScratchTable.Call

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Execute the real three stores following the delete-table call. -/
theorem delete_stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame message table : BitVec 64) (words : SuffixWords) (empty : BitVec 64)
    (ready : SuffixReady source frame message words empty)
    (tableLocal : source.locals.lookup (ofString "del") = some (.val (.word table)))
    (separate : ∀ readOffset ∈ ([152, 160] : List Nat), ∀ writeOffset ∈ ([136, 168, 176] : List Nat),
      message + BitVec.ofNat 64 readOffset ≠ frame + BitVec.ofNat 64 writeOffset) :
    evaluateHOLFiniteState source deleteContinuation =
      evaluateHOLFiniteState {source with memory := (WitnessRadix.WordWrites.write source.memory
        (FieldStores.writes frame (deleteFields table words.addresses words.keys)))} countProgram := by
  have reads : ∀ field ∈ deleteFields table words.addresses words.keys,
      field.value.Ready source "msg" message := by
    intro field member
    simp only [deleteFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact tableLocal
    · exact ready.copied 152 words.addresses (by simp [suffixCells])
    · exact ready.copied 160 words.keys (by simp [suffixCells])
  have mapped : ∀ field ∈ deleteFields table words.addresses words.keys,
      source.memaddrs (frame + BitVec.ofNat 64 field.offset) := by
    intro field member
    simp only [deleteFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact ready.frameMapped _ (by dsimp <;> decide) (by dsimp <;> decide)
  have guarded : ∀ reader ∈ deleteFields table words.addresses words.keys,
      ∀ writer ∈ deleteFields table words.addresses words.keys,
        reader.value.Avoid message (frame + BitVec.ofNat 64 writer.offset) := by
    intro reader member writer writerIn
    have writeIn : writer.offset ∈ ([136, 168, 176] : List Nat) := by
      simp only [deleteFields, List.mem_cons, List.not_mem_nil, or_false] at writerIn
      rcases writerIn with rfl | rfl | rfl <;> simp
    simp only [deleteFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · trivial
    · exact separate 152 (by simp) writer.offset writeIn
    · exact separate 160 (by simp) writer.offset writeIn
  exact FieldStores.execute source "e" "msg" frame message (deleteFields table words.addresses words.keys)
    ready.frameLocal reads mapped guarded countProgram

set_option maxHeartbeats 1000000 in
/-- Actual delete-table allocation through frame return. The two input table
counts are read from protected prior memory; the new delete table is empty.
All real callees and stores execute. Cost14 source clocks, including callers. -/
theorem delete_suffix_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower frame message : BitVec 64) (words : SuffixWords) (empty : BitVec 64)
    (ready : SuffixReady source frame message words empty)
    (known : source.code.lookup (ofString "htab_new_scratch") = some (ScratchTable.formals, ScratchTable.body, .one))
    (scratchCode : source.code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (WitnessRadix.Zero.formals, WitnessRadix.Zero.body, .one))
    (countCode : source.code.lookup (ofString "htab_count") = some (TableCount.formals, TableCount.body, .one))
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (lowerGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word lower)))
    (scratchAligned : scratch.toNat % 8 = 0) (lowerAligned : lower.toNat % 8 = 0)
    (room : lower.toNat + 272 ≤ scratch.toNat) (frameAbove : scratch.toNat ≤ frame.toNat)
    (frameFits : frame.toNat + 280 < 2 ^ 64)
    (inputsProtected : ∀ cell ∈ suffixCells message words, SuffixProtected lower frame cell.1)
    (mapped : ∀ offset, offset + 8 ≤ 72 → offset % 8 = 0 →
      source.memaddrs (ScratchTable.cursor scratch 72 + BitVec.ofNat 64 offset))
    (usedMapped : source.memaddrs (ScratchTable.cursor scratch 208))
    (enough : 14 ≤ source.clock) :
    ∃ target : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source (.decCall (ofString "del") .one (ofString "htab_new_scratch")
        [.const 20#64, .const 4#64] deleteContinuation) =
        (some (.returned (.val (.word frame))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with
        globals := source.globals.update (ofString "scratch_ptr", .val (.word (ScratchTable.cursor scratch 272)))
        memory := target.memory
        clock := source.clock - 14} ∧
      ∀ query, SuffixSafe lower frame query → target.memory query = source.memory query := by
  obtain ⟨tableMemory, tableFrame, tableRun⟩ := ScratchTable.call_execute source "del"
    [.const 20#64, .const 4#64] deleteContinuation scratch lower rfl known scratchCode zeroCode
    scratchGlobal lowerGlobal scratchAligned lowerAligned room mapped usedMapped (by omega)
  let allocated := WitnessRadix.QueryBranch.bind {source with
    globals := source.globals.update (ofString "scratch_ptr", .val (.word (ScratchTable.cursor scratch 272)))
    memory := tableMemory
    clock := source.clock - 12} "del" (ScratchTable.cursor scratch 72)
  let stored := {allocated with memory := (WitnessRadix.WordWrites.write tableMemory
    (FieldStores.writes frame (deleteFields (ScratchTable.cursor scratch 72) words.addresses words.keys)))}
  have inputAway (cell : BitVec 64 × BitVec 64) (member : cell ∈ suffixCells message words)
      (offset : Nat) (inside : offset < 280) : cell.1 ≠ frame + BitVec.ofNat 64 offset :=
    suffix_protected_away lower frame cell.1 offset (inputsProtected cell member) (by omega) frameFits inside
  have allocatedReady : SuffixReady allocated frame message words empty := by
    have changed := (ready.memory tableMemory (by
      intro cell member
      exact tableFrame cell.1 (suffix_protected_outside lower frame scratch cell.1 (inputsProtected cell member) frameAbove))).scratch
      (ScratchTable.cursor scratch 272)
    exact (changed.clock (source.clock - 12)).bound "del" (ScratchTable.cursor scratch 72) (by decide) (by decide)
  have storedReady : SuffixReady stored frame message words empty := by
    apply allocatedReady.stored
    intro cell member
    simp only [FieldStores.writes, deleteFields, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨inputAway cell member 136 (by decide), inputAway cell member 168 (by decide), inputAway cell member 176 (by decide)⟩
  have storesRun := delete_stores_execute allocated frame message (ScratchTable.cursor scratch 72) words empty
    allocatedReady (bind_lookup_same _ _ _) (by
      intro readOffset readIn writeOffset writeIn
      have protectedRead : SuffixProtected lower frame (message + BitVec.ofNat 64 readOffset) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at readIn
        rcases readIn with rfl | rfl
        · exact inputsProtected (message + 152#64, words.addresses) (by simp [suffixCells])
        · exact inputsProtected (message + 160#64, words.keys) (by simp [suffixCells])
      apply suffix_protected_away lower frame _ writeOffset protectedRead (by omega) frameFits
      simp only [List.mem_cons, List.not_mem_nil, or_false] at writeIn
      rcases writeIn with rfl | rfl | rfl <;> decide)
  change evaluateHOLFiniteState allocated deleteContinuation = evaluateHOLFiniteState stored countProgram at storesRun
  have countsRun := counts_execute stored frame message words.addresses words.keys words.addressCount words.keyCount empty
    storedReady.frameLocal storedReady.messageLocal storedReady.emptyGlobal countCode
    (by
      intro offset member
      apply storedReady.frameMapped
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl <;> decide)
    (storedReady.readsMapped (message + 152#64, words.addresses) (by simp [suffixCells]))
    (storedReady.readsStored (message + 152#64, words.addresses) (by simp [suffixCells]))
    (storedReady.readsMapped (message + 160#64, words.keys) (by simp [suffixCells]))
    (storedReady.readsStored (message + 160#64, words.keys) (by simp [suffixCells]))
    (storedReady.readsMapped (words.addresses + 24#64, words.addressCount) (by simp [suffixCells]))
    (storedReady.readsStored (words.addresses + 24#64, words.addressCount) (by simp [suffixCells]))
    (storedReady.readsMapped (words.keys + 24#64, words.keyCount) (by simp [suffixCells]))
    (storedReady.readsStored (words.keys + 24#64, words.keyCount) (by simp [suffixCells]))
    (inputAway (message + 160#64, words.keys) (by simp [suffixCells]) 264 (by decide))
    (inputAway (words.keys + 24#64, words.keyCount) (by simp [suffixCells]) 264 (by decide))
    (by change 2 ≤ source.clock - 12; omega)
  rw [countsRun] at storesRun
  change evaluateHOLFiniteState source _ =
    (let output := evaluateHOLFiniteState allocated deleteContinuation
     (output.1, restore source "del" output.2)) at tableRun
  rw [storesRun] at tableRun
  let target := restore source "del" (restore stored "acc_n"
    (emptyLocalsHOLFinite (countedFinal stored frame words.addressCount words.keyCount empty)))
  refine ⟨target, tableRun, ?_, ?_⟩
  · have clocks : source.clock - 12 - 1 - 1 = source.clock - 14 := by omega
    simp only [target, restore, emptyLocalsHOLFinite, countedFinal, countedFirst,
      WitnessRadix.QueryBranch.bind, setVarHOLFinite, stored, allocated, clocks]
  · intro query safe
    change (countedFinal stored frame words.addressCount words.keyCount empty).memory query = source.memory query
    rw [count_memory_away]
    · change WitnessRadix.WordWrites.write tableMemory _ query = source.memory query
      rw [WitnessRadix.WordWrites.write_away]
      · exact tableFrame query (suffix_safe_outside lower frame scratch query safe frameAbove)
      · simp only [FieldStores.writes, deleteFields, List.map_cons, List.map_nil,
          List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨safe.2 136 (by simp [suffixStoreOffsets]), safe.2 168 (by simp [suffixStoreOffsets]), safe.2 176 (by simp [suffixStoreOffsets])⟩
    · intro offset member
      apply safe.2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [suffixStoreOffsets]

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.delete_stores_execute
#print axioms InitECandidate.Solver.GasBudget.FrameNew.delete_suffix_execute
