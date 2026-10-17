import InitECandidate.Solver.GasBudget.FrameNewDelete
import InitECandidate.Solver.GasBudget.FrameNewSuffixLayout

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Three actual log/status/message stores, including EV_RUNNING at104. -/
theorem log_stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame message logs : BitVec 64) (words : SuffixWords) (empty : BitVec 64)
    (ready : SuffixReady source frame message words empty)
    (logsLocal : source.locals.lookup (ofString "logs") = some (.val (.word logs)))
    (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (FieldStores.program "e" "msg" (logFields 0#64 0#64) continuation) =
      evaluateHOLFiniteState {source with memory := (WitnessRadix.WordWrites.write source.memory
        (FieldStores.writes frame (logFields logs message)))} continuation := by
  have reads : ∀ field ∈ logFields logs message, field.value.Ready source "msg" message := by
    intro field member
    simp only [logFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact logsLocal
    · trivial
    · exact ready.messageLocal
  have mapped : ∀ field ∈ logFields logs message, source.memaddrs (frame + BitVec.ofNat 64 field.offset) := by
    intro field member
    simp only [logFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact ready.frameMapped _ (by dsimp <;> decide) (by dsimp <;> decide)
  have guarded : ∀ reader ∈ logFields logs message, ∀ writer ∈ logFields logs message,
      reader.value.Avoid message (frame + BitVec.ofNat 64 writer.offset) := by
    intro reader member writer _
    simp only [logFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> trivial
  exact FieldStores.execute source "e" "msg" frame message (logFields logs message) ready.frameLocal reads mapped guarded continuation

set_option maxHeartbeats 1000000 in
/-- Original empty log-list and delete-table constructors through frame return.
Their actual calls plus both access counts consume17source clocks. -/
theorem logs_suffix_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower frame message : BitVec 64) (words : SuffixWords) (empty : BitVec 64)
    (ready : SuffixReady source frame message words empty)
    (logCode : source.code.lookup (ofString "lst_new_scratch") = some (ScratchList.formals, ScratchList.body, .one))
    (tableCode : source.code.lookup (ofString "htab_new_scratch") = some (ScratchTable.formals, ScratchTable.body, .one))
    (scratchCode : source.code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (WitnessRadix.Zero.formals, WitnessRadix.Zero.body, .one))
    (countCode : source.code.lookup (ofString "htab_count") = some (TableCount.formals, TableCount.body, .one))
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (lowerGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word lower)))
    (scratchAligned : scratch.toNat % 8 = 0) (lowerAligned : lower.toNat % 8 = 0)
    (room : lower.toNat + 328 ≤ scratch.toNat) (frameAbove : scratch.toNat ≤ frame.toNat)
    (frameFits : frame.toNat + 280 < 2 ^ 64)
    (inputsProtected : ∀ cell ∈ suffixCells message words, SuffixProtected lower frame cell.1)
    (logMapped : ∀ offset ∈ ([0, 8, 16] : List Nat), source.memaddrs (ScratchList.header scratch + BitVec.ofNat 64 offset))
    (tableMapped : ∀ offset, offset + 8 ≤ 72 → offset % 8 = 0 →
      source.memaddrs (ScratchTable.cursor (ScratchList.buffer scratch 32#64) 72 + BitVec.ofNat 64 offset))
    (usedMapped : source.memaddrs (ScratchTable.cursor (ScratchList.buffer scratch 32#64) 208))
    (enough : 17 ≤ source.clock) :
    ∃ target : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source (.decCall (ofString "logs") .one (ofString "lst_new_scratch")
        [.const 8#64, .const 4#64] logContinuation) =
        (some (.returned (.val (.word frame))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with
        globals := source.globals.update (ofString "scratch_ptr", .val (.word (ScratchTable.cursor (ScratchList.buffer scratch 32#64) 272)))
        memory := target.memory
        clock := source.clock - 17} ∧
      ∀ query, SuffixSafe lower frame query → target.memory query = source.memory query := by
  have geometry := log_geometry scratch lower scratchAligned room
  have amount : 8#64 * 4#64 = 32#64 := by decide
  obtain ⟨logMemory, logFrame, logRun⟩ := ScratchList.call_execute source "logs"
    [.const 8#64, .const 4#64] logContinuation scratch lower 8#64 4#64 rfl logCode scratchCode
    scratchGlobal lowerGlobal lowerAligned (by omega) (by rw [amount]; change lower.toNat + 32 ≤ (ScratchList.header scratch).toNat; rw [geometry.2.2.1]; omega) logMapped (by omega)
  rw [amount] at logRun
  let buffer := ScratchList.buffer scratch 32#64
  let allocated := WitnessRadix.QueryBranch.bind {Arenas.post source .down (ScratchList.header scratch) 32#64 with
    memory := logMemory
    clock := source.clock - 3} "logs" (ScratchList.header scratch)
  let stored := {allocated with memory := (WitnessRadix.WordWrites.write logMemory
    (FieldStores.writes frame (logFields (ScratchList.header scratch) message)))}
  have allocatedReady : SuffixReady allocated frame message words empty := by
    have changed := (ready.memory logMemory (by
      intro cell member
      exact logFrame cell.1 (suffix_protected_outside lower frame scratch cell.1 (inputsProtected cell member) frameAbove))).scratch buffer
    exact (changed.clock (source.clock - 3)).bound "logs" (ScratchList.header scratch) (by decide) (by decide)
  have storedReady : SuffixReady stored frame message words empty := by
    apply allocatedReady.stored
    intro cell member
    simp only [FieldStores.writes, logFields, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    have away (offset : Nat) (inside : offset < 280) : cell.1 ≠ frame + BitVec.ofNat 64 offset :=
      suffix_protected_away lower frame cell.1 offset (inputsProtected cell member) (by omega) frameFits inside
    exact ⟨away 88 (by decide), away 104 (by decide), away 112 (by decide)⟩
  have storesRun := log_stores_execute allocated frame message (ScratchList.header scratch) words empty
    allocatedReady (bind_lookup_same _ _ _)
    (.decCall (ofString "del") .one (ofString "htab_new_scratch") [.const 20#64, .const 4#64] deleteContinuation)
  change evaluateHOLFiniteState allocated logContinuation = evaluateHOLFiniteState stored _ at storesRun
  have storedScratch : stored.globals.lookup (ofString "scratch_ptr") = some (.val (.word buffer)) := by
    simp [stored, allocated, Arenas.post, Arenas.pointerName, WitnessRadix.QueryBranch.bind,
      setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, buffer, ScratchList.buffer]
  have storedLower : stored.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word lower)) := by
    simpa [stored, allocated, Arenas.post, Arenas.pointerName, WitnessRadix.QueryBranch.bind,
      setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using lowerGlobal
  obtain ⟨deleted, deleteRun, deleteFrame, deleteKept⟩ := delete_suffix_execute stored buffer lower frame message words empty
    storedReady tableCode scratchCode zeroCode countCode storedScratch storedLower
    geometry.2.2.2.2.1 lowerAligned geometry.2.2.2.2.2
    (by change (ScratchList.buffer scratch 32#64).toNat ≤ frame.toNat; rw [geometry.2.2.2.1]; omega)
    frameFits inputsProtected tableMapped usedMapped (by change 14 ≤ source.clock - 3; omega)
  rw [deleteRun] at storesRun
  change evaluateHOLFiniteState source _ =
    (let output := evaluateHOLFiniteState allocated logContinuation
     (output.1, restore source "logs" output.2)) at logRun
  rw [storesRun] at logRun
  let target := restore source "logs" deleted
  refine ⟨target, logRun, ?_, ?_⟩
  · change emptyLocalsHOLFinite deleted = _
    rw [deleteFrame]
    have overwrite : (source.globals.update (ofString "scratch_ptr", .val (.word buffer))).update
        (ofString "scratch_ptr", .val (.word (ScratchTable.cursor buffer 272))) =
        source.globals.update (ofString "scratch_ptr", .val (.word (ScratchTable.cursor buffer 272))) := by
      apply HolFiniteMapExact.ext
      funext query
      by_cases same : ofString "scratch_ptr" = query <;> simp [HolFiniteMapExact.update, FUPDATE, same]
    have clocks : source.clock - 3 - 14 = source.clock - 17 := by omega
    change emptyLocalsHOLFinite {source with
      globals := (source.globals.update (ofString "scratch_ptr", .val (.word buffer))).update
        (ofString "scratch_ptr", .val (.word (ScratchTable.cursor buffer 272)))
      memory := deleted.memory
      clock := source.clock - 3 - 14} = emptyLocalsHOLFinite {source with
      globals := source.globals.update (ofString "scratch_ptr", .val (.word (ScratchTable.cursor buffer 272)))
      memory := deleted.memory
      clock := source.clock - 17}
    rw [overwrite, clocks]
  · intro query safe
    change deleted.memory query = source.memory query
    rw [deleteKept query safe]
    change WitnessRadix.WordWrites.write logMemory _ query = source.memory query
    rw [WitnessRadix.WordWrites.write_away]
    · exact logFrame query (suffix_safe_outside lower frame scratch query safe frameAbove)
    · simp only [FieldStores.writes, logFields, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨safe.2 88 (by simp [suffixStoreOffsets]), safe.2 104 (by simp [suffixStoreOffsets]), safe.2 112 (by simp [suffixStoreOffsets])⟩

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.log_stores_execute
#print axioms InitECandidate.Solver.GasBudget.FrameNew.logs_suffix_execute
