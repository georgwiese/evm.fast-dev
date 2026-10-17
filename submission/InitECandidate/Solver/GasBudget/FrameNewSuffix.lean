import InitECandidate.Solver.GasBudget.FrameNewLogs

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

set_option maxHeartbeats 1000000 in
/-- All remaining original frame_new instructions: actual bitmap scan, empty
log/delete constructors, access-set count reads and final return. The initialized
regular ledger survives. Entry ownership/code/room/clock premises remain explicit;
these source-clock units do not count all straight-line or target work. -/
theorem suffix_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower frame message : BitVec 64) (words : SuffixWords) (empty : BitVec 64)
    (ready : SuffixReady source frame message words empty)
    (jumpCode : source.code.lookup (ofString "compute_jumpdests") = some (JumpDest.formals, JumpDest.body, .one))
    (logCode : source.code.lookup (ofString "lst_new_scratch") = some (ScratchList.formals, ScratchList.body, .one))
    (tableCode : source.code.lookup (ofString "htab_new_scratch") = some (ScratchTable.formals, ScratchTable.body, .one))
    (scratchCode : source.code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (WitnessRadix.Zero.formals, WitnessRadix.Zero.body, .one))
    (countCode : source.code.lookup (ofString "htab_count") = some (TableCount.formals, TableCount.body, .one))
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (lowerGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word lower)))
    (scratchAligned : scratch.toNat % 8 = 0) (lowerAligned : lower.toNat % 8 = 0)
    (lengthFits : words.length.toNat + 63 < 2 ^ 64)
    (room : lower.toNat + JumpDest.bitmapBytes words.length.toNat + 328 ≤ scratch.toNat)
    (frameAbove : scratch.toNat ≤ frame.toNat) (frameFits : frame.toNat + 280 < 2 ^ 64)
    (inputsProtected : ∀ cell ∈ suffixCells message words, SuffixProtected lower frame cell.1)
    (codeMapped : ∀ offset < words.length.toNat,
      source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress words.code offset)))
    (bitmapMapped : ∀ offset, offset + 8 ≤ JumpDest.bitmapBytes words.length.toNat → offset % 8 = 0 →
      source.memaddrs (WitnessRadix.byteAddress (Arenas.rounded .down scratch (JumpDest.bytesWord words.length)) offset))
    (logMapped : ∀ offset ∈ ([0, 8, 16] : List Nat),
      source.memaddrs (ScratchList.header (Arenas.rounded .down scratch (JumpDest.bytesWord words.length)) + BitVec.ofNat 64 offset))
    (tableMapped : ∀ offset, offset + 8 ≤ 72 → offset % 8 = 0 →
      source.memaddrs (ScratchTable.cursor (ScratchList.buffer
        (Arenas.rounded .down scratch (JumpDest.bytesWord words.length)) 32#64) 72 + BitVec.ofNat 64 offset))
    (usedMapped : source.memaddrs (ScratchTable.cursor (ScratchList.buffer
      (Arenas.rounded .down scratch (JumpDest.bytesWord words.length)) 32#64) 208))
    (enough : words.length.toNat + WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 20 ≤ source.clock) :
    ∃ (target : PanSemStateFiniteExact 64 Guest.HostMemory) (spent : Nat),
      spent ≤ words.length.toNat ∧
      evaluateHOLFiniteState source afterGas = (some (.returned (.val (.word frame))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with
        globals := source.globals.update (ofString "scratch_ptr", .val (.word
          (ScratchTable.cursor (ScratchList.buffer (Arenas.rounded .down scratch (JumpDest.bytesWord words.length)) 32#64) 272)))
        memory := target.memory
        clock := source.clock - (WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 20 + spent)} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      ∀ query, SuffixSafe lower frame query → target.memory query = source.memory query := by
  let bitmap := Arenas.rounded .down scratch (JumpDest.bytesWord words.length)
  let price := WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat)
  have geometry := bitmap_geometry scratch lower words.length scratchAligned lengthFits room
  have codeRead := FieldStores.Value.read source "msg" message (.copied 112 words.code)
    (ready.copied 112 words.code (by simp [suffixCells]))
  have lengthRead := FieldStores.Value.read source "msg" message (.copied 120 words.length)
    (ready.copied 120 words.length (by simp [suffixCells]))
  simp only [FieldStores.Value.expression, FieldStores.Value.word, eval] at codeRead lengthRead
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [messageLoad 112, messageLoad 120] = some (JumpDest.values words.code words.length) := by
    simp only [evalListHOLFinite, evalListHOLExact, messageLoad, codeRead, lengthRead, JumpDest.values]
  obtain ⟨bitmapMemory, spent, spentBound, bitmapFrame, bitmapRun⟩ := JumpDest.call_execute source "jd"
    [messageLoad 112, messageLoad 120] jumpContinuation scratch lower words.code words.length args
    jumpCode scratchCode zeroCode scratchGlobal lowerGlobal lowerAligned lengthFits (by omega)
    codeMapped bitmapMapped (by omega)
  let allocated := WitnessRadix.QueryBranch.bind {Arenas.post source .down scratch (JumpDest.bytesWord words.length) with
    memory := bitmapMemory
    clock := source.clock - (price + 3 + spent)} "jd" bitmap
  let stored := {allocated with memory := (WitnessRadix.WordWrites.write bitmapMemory (FieldStores.writes frame (jumpFields bitmap)))}
  have allocatedReady : SuffixReady allocated frame message words empty := by
    have changed := (ready.memory bitmapMemory (by
      intro cell member
      exact bitmapFrame cell.1 (suffix_protected_outside lower frame scratch cell.1 (inputsProtected cell member) frameAbove))).scratch bitmap
    exact (changed.clock (source.clock - (price + 3 + spent))).bound "jd" bitmap (by decide) (by decide)
  have storedReady : SuffixReady stored frame message words empty := by
    apply allocatedReady.stored
    intro cell member
    simpa [FieldStores.writes, jumpFields] using
      suffix_protected_away lower frame cell.1 80 (inputsProtected cell member) (by omega) frameFits (by decide)
  have storesRun := FieldStores.execute allocated "e" "msg" frame message (jumpFields bitmap)
    allocatedReady.frameLocal
    (by intro field member; simp only [jumpFields, List.mem_cons, List.not_mem_nil, or_false] at member; subst field; exact bind_lookup_same _ _ _)
    (by intro field member; simp only [jumpFields, List.mem_cons, List.not_mem_nil, or_false] at member; subst field; exact allocatedReady.frameMapped 80 (by decide) (by decide))
    (by intro reader member writer _; simp only [jumpFields, List.mem_cons, List.not_mem_nil, or_false] at member; subst reader; trivial)
    (.decCall (ofString "logs") .one (ofString "lst_new_scratch") [.const 8#64, .const 4#64] logContinuation)
  change evaluateHOLFiniteState allocated jumpContinuation = evaluateHOLFiniteState stored _ at storesRun
  have storedScratch : stored.globals.lookup (ofString "scratch_ptr") = some (.val (.word bitmap)) := by
    simp [stored, allocated, Arenas.post, Arenas.pointerName, WitnessRadix.QueryBranch.bind,
      setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, bitmap]
  have storedLower : stored.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word lower)) := by
    simpa [stored, allocated, Arenas.post, Arenas.pointerName, WitnessRadix.QueryBranch.bind,
      setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using lowerGlobal
  obtain ⟨logged, logsRun, logsFrame, logsKept⟩ := logs_suffix_execute stored bitmap lower frame message words empty
    storedReady logCode tableCode scratchCode zeroCode countCode storedScratch storedLower
    geometry.2.2.1 lowerAligned geometry.2.2.2 (by change bitmap.toNat ≤ frame.toNat; dsimp [bitmap]; rw [geometry.2.1]; omega)
    frameFits inputsProtected logMapped tableMapped usedMapped
    (by change 17 ≤ source.clock - (price + 3 + spent); dsimp [price]; omega)
  rw [logsRun] at storesRun
  change evaluateHOLFiniteState source suffixProgram =
    (let output := evaluateHOLFiniteState allocated jumpContinuation
     (output.1, restore source "jd" output.2)) at bitmapRun
  rw [storesRun] at bitmapRun
  let target := restore source "jd" logged
  have kept (query : BitVec 64) (safe : SuffixSafe lower frame query) : target.memory query = source.memory query := by
    change logged.memory query = source.memory query
    rw [logsKept query safe]
    change WitnessRadix.WordWrites.write bitmapMemory _ query = source.memory query
    rw [WitnessRadix.WordWrites.write_away]
    · exact bitmapFrame query (suffix_safe_outside lower frame scratch query safe frameAbove)
    · simpa [FieldStores.writes, jumpFields] using safe.2 80 (by simp [suffixStoreOffsets])
  refine ⟨target, spent, spentBound, ?_, ?_, ?_, kept⟩
  · rw [actual_suffix]
    exact bitmapRun
  · change emptyLocalsHOLFinite logged = _
    rw [logsFrame]
    let lastCursor := ScratchTable.cursor (ScratchList.buffer bitmap 32#64) 272
    have overwrite : (source.globals.update (ofString "scratch_ptr", .val (.word bitmap))).update
        (ofString "scratch_ptr", .val (.word lastCursor)) =
        source.globals.update (ofString "scratch_ptr", .val (.word lastCursor)) := by
      apply HolFiniteMapExact.ext
      funext query
      by_cases same : ofString "scratch_ptr" = query <;> simp [HolFiniteMapExact.update, FUPDATE, same]
    have clocks : source.clock - (price + 3 + spent) - 17 = source.clock - (price + 20 + spent) := by omega
    change emptyLocalsHOLFinite {source with
      globals := (source.globals.update (ofString "scratch_ptr", .val (.word bitmap))).update
        (ofString "scratch_ptr", .val (.word lastCursor))
      memory := logged.memory
      clock := source.clock - (price + 3 + spent) - 17} = emptyLocalsHOLFinite {source with
      globals := source.globals.update (ofString "scratch_ptr", .val (.word lastCursor))
      memory := logged.memory
      clock := source.clock - (price + 20 + spent)}
    rw [overwrite, clocks]
  · have preserved (offset : Nat) (member : offset ∈ ([64, 184, 192] : List Nat)) :=
      kept (frame + BitVec.ofNat 64 offset) (suffix_regular_safe lower frame offset member frameFits)
    simp only [regularBudget, wordAt, preserved 64 (by simp), preserved 184 (by simp), preserved 192 (by simp)]

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.suffix_execute
