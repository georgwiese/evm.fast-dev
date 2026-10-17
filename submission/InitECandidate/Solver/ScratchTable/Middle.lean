import InitECandidate.Solver.ScratchTable.Initial

namespace InitECandidate.Solver.ScratchTable
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual keys/value/used-array allocations and their two header stores. -/
theorem middle_executes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch memory : BitVec 64)
    (code : source.code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one))
    (memoryGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word 4#64)))
    (scratchAligned : scratch.toNat % 8 = 0) (memoryAligned : memory.toNat % 8 = 0)
    (room : memory.toNat + 272 ≤ scratch.toNat)
    (mapped : ∀ offset, offset + 8 ≤ 72 → offset % 8 = 0 →
      source.memaddrs (cursor scratch 72 + BitVec.ofNat 64 offset))
    (enough : 4 ≤ source.clock) :
    ∃ restoreStack, Arenas.Prefix.Executes .down (initialState source scratch) middleActions
      (preClearState source scratch) restoreStack := by
  have initialLocals := initial_locals source scratch capLocal
  have keysLocals := initialLocals.allocated "keys" (cursor scratch 168) (by decide) (by decide) (by decide)
  have keysStoredLocals := keysLocals.stored (pointerFields 32 "keys" (cursor scratch 168))
  have valsLocals := keysStoredLocals.allocated "vals" (cursor scratch 200) (by decide) (by decide) (by decide)
  have valsStoredLocals := valsLocals.stored (pointerFields 40 "vals" (cursor scratch 200))
  have initialScratch : (initialState source scratch).globals.lookup (ofString "scratch_ptr") = some (.val (.word (cursor scratch 72))) :=
    expected_scratch source "t" (cursor scratch 72)
  have initialMemory : (initialState source scratch).globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)) :=
    expected_memory source "t" (cursor scratch 72) memory memoryGlobal
  have keysMemory : (keysStored source scratch).globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)) :=
    expected_memory (initialState source scratch) "keys" (cursor scratch 168) memory initialMemory
  have valsMemory : (valsStored source scratch).globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)) :=
    expected_memory (keysStored source scratch) "vals" (cursor scratch 200) memory keysMemory
  have number72 := Arenas.cursor_number scratch 72 (by omega)
  have number168 := Arenas.cursor_number scratch 168 (by omega)
  have number200 := Arenas.cursor_number scratch 200 (by omega)
  have roundKeys : Arenas.rounded .down (cursor scratch 72) 96#64 = cursor scratch 168 := by
    simpa only [cursor] using Arenas.rounded_decrement scratch 72 96 96 scratchAligned
      (by decide) (by decide) (by decide) (by decide) (by omega)
  have roundVals : Arenas.rounded .down (cursor scratch 168) 32#64 = cursor scratch 200 := by
    simpa only [cursor] using Arenas.rounded_decrement scratch 168 32 32 scratchAligned
      (by decide) (by decide) (by decide) (by decide) (by omega)
  have roundUsed : Arenas.rounded .down (cursor scratch 200) 4#64 = cursor scratch 208 := by
    simpa only [cursor] using Arenas.rounded_decrement scratch 200 4 8 scratchAligned
      (by decide) (by decide) (by decide) (by decide) (by omega)
  have allocKeys : Arenas.Prefix.Executes .down (initialState source scratch)
      [.allocate "keys" (WitnessRadix.TableNew.capacityTimes (localVar "stride"))] (keysState source scratch)
      (fun post => restore (initialState source scratch) "keys" post) := by
    apply Arenas.Prefix.allocate_expected _ _ "keys" _ [] id (cursor scratch 72) memory 96#64 (cursor scratch 168)
      (keys_amount _ _ initialLocals) code initialScratch initialMemory memoryAligned
      (by change memory.toNat + 96 ≤ (scratch - BitVec.ofNat 64 72).toNat; rw [number72]; omega) roundKeys
      (by change 1 ≤ source.clock - 1; omega)
    exact .done _
  have storeKeys := pointer_executes (keysState source scratch) scratch 32 "keys" (cursor scratch 168)
    keysLocals.table (bind_lookup_same _ _ _) (mapped 32 (by decide) (by decide))
  have allocVals : Arenas.Prefix.Executes .down (keysStored source scratch)
      [.allocate "vals" (WitnessRadix.TableNew.capacityTimes (.const 8#64))] (valsState source scratch)
      (fun post => restore (keysStored source scratch) "vals" post) := by
    apply Arenas.Prefix.allocate_expected _ _ "vals" _ [] id (cursor scratch 168) memory 32#64 (cursor scratch 200)
      (words_amount _ _ keysStoredLocals) code (expected_scratch _ "keys" _) keysMemory memoryAligned
      (by change memory.toNat + 32 ≤ (scratch - BitVec.ofNat 64 168).toNat; rw [number168]; omega) roundVals
      (by change 1 ≤ source.clock - 1 - 1; omega)
    exact .done _
  have storeVals := pointer_executes (valsState source scratch) scratch 40 "vals" (cursor scratch 200)
    valsLocals.table (bind_lookup_same _ _ _) (mapped 40 (by decide) (by decide))
  have allocUsed : Arenas.Prefix.Executes .down (valsStored source scratch)
      [.allocate "used" (localVar "cap")] (preClearState source scratch)
      (fun post => restore (valsStored source scratch) "used" post) := by
    apply Arenas.Prefix.allocate_expected _ _ "used" _ [] id (cursor scratch 200) memory 4#64 (cursor scratch 208)
      (capacity_read _ _ valsStoredLocals) code (expected_scratch _ "vals" _) valsMemory memoryAligned
      (by change memory.toNat + 4 ≤ (scratch - BitVec.ofNat 64 200).toNat; rw [number200]; omega) roundUsed
      (by change 1 ≤ source.clock - 1 - 1 - 1; omega)
    exact .done _
  exact ⟨_, allocKeys.append (storeKeys.append (allocVals.append (storeVals.append allocUsed)))⟩

theorem preclear_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64)
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word 4#64))) :
    Locals (preClearState source scratch) scratch := by
  have initial := initial_locals source scratch capLocal
  have keys := initial.allocated "keys" (cursor scratch 168) (by decide) (by decide) (by decide)
  have vals := (keys.stored (pointerFields 32 "keys" (cursor scratch 168))).allocated "vals" (cursor scratch 200)
    (by decide) (by decide) (by decide)
  exact (vals.stored (pointerFields 40 "vals" (cursor scratch 200))).allocated "used" (cursor scratch 208)
    (by decide) (by decide) (by decide)

end InitECandidate.Solver.ScratchTable

#print axioms InitECandidate.Solver.ScratchTable.middle_executes
#print axioms InitECandidate.Solver.ScratchTable.preclear_locals
