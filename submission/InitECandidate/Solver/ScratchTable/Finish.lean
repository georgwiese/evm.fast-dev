import InitECandidate.Solver.ScratchTable.Middle

namespace InitECandidate.Solver.ScratchTable
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual four-byte used-array clear and final order-array allocations/stores. -/
theorem finish_executes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch memory : BitVec 64)
    (code : source.code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (WitnessRadix.Zero.formals, WitnessRadix.Zero.body, .one))
    (memoryGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word 4#64)))
    (scratchAligned : scratch.toNat % 8 = 0) (memoryAligned : memory.toNat % 8 = 0)
    (room : memory.toNat + 272 ≤ scratch.toNat)
    (mapped : ∀ offset, offset + 8 ≤ 72 → offset % 8 = 0 →
      source.memaddrs (cursor scratch 72 + BitVec.ofNat 64 offset))
    (usedMapped : source.memaddrs (cursor scratch 208))
    (enough : 11 ≤ source.clock) :
    ∃ restoreStack, Arenas.Prefix.Executes .down (preClearState source scratch) finishActions
      (finalState source scratch) restoreStack := by
  classical
  have beforeLocals := preclear_locals source scratch capLocal
  have afterLocals : Locals (clearState source scratch) scratch :=
    ⟨beforeLocals.table, beforeLocals.capacity, beforeLocals.stride⟩
  have usedLocals := afterLocals.stored (pointerFields 48 "used" (cursor scratch 208))
  have orderLocals := usedLocals.allocated "order" (cursor scratch 240) (by decide) (by decide) (by decide)
  have orderStoredLocals := orderLocals.stored (pointerFields 56 "order" (cursor scratch 240))
  have positionLocals := orderStoredLocals.allocated "order_pos" (cursor scratch 272) (by decide) (by decide) (by decide)
  have number208 := Arenas.cursor_number scratch 208 (by omega)
  have number240 := Arenas.cursor_number scratch 240 (by omega)
  have usedAligned : (cursor scratch 208).toNat % 8 = 0 := by change (scratch - BitVec.ofNat 64 208).toNat % 8 = 0; rw [number208]; omega
  have usedFits : (cursor scratch 208).toNat + 32 < 2 ^ 64 := by
    change (scratch - BitVec.ofNat 64 208).toNat + 32 < 2 ^ 64
    rw [number208]
    have bound := scratch.isLt
    omega
  have usedLocal : (preClearState source scratch).locals.lookup (ofString "used") = some (.val (.word (cursor scratch 208))) := bind_lookup_same _ _ _
  have args : evalListHOLFinite (preClearState source scratch)
      (h := fun address => Classical.propDecidable ((preClearState source scratch).memaddrs address))
      [localVar "used", localVar "cap"] = some (WitnessRadix.Zero.values (cursor scratch 208) 4) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, usedLocal,
      beforeLocals.capacity, WitnessRadix.Zero.values]
  have clearRun := WitnessRadix.Zero.call_small (preClearState source scratch) [localVar "used", localVar "cap"]
    (cursor scratch 208) 4 args zeroCode (by decide) usedAligned usedFits usedMapped
    (by change 5 ≤ source.clock - 1 - 1 - 1 - 1; omega)
  change evaluateHOLFiniteState (preClearState source scratch) clearCall = (none, clearState source scratch) at clearRun
  have clearing : Arenas.Prefix.Executes .down (preClearState source scratch) [.command clearCall] (clearState source scratch) id :=
    .command clearRun (by change (preClearState source scratch).clock - 5 ≤ _; omega) (.done _)
  have storeUsed := pointer_executes (clearState source scratch) scratch 48 "used" (cursor scratch 208)
    afterLocals.table usedLocal (mapped 48 (by decide) (by decide))
  have initialMemory : (initialState source scratch).globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)) :=
    expected_memory source "t" (cursor scratch 72) memory memoryGlobal
  have keysMemory : (keysStored source scratch).globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)) :=
    expected_memory (initialState source scratch) "keys" (cursor scratch 168) memory initialMemory
  have valsMemory : (valsStored source scratch).globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)) :=
    expected_memory (keysStored source scratch) "vals" (cursor scratch 200) memory keysMemory
  have usedMemory : (usedStored source scratch).globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)) :=
    expected_memory (valsStored source scratch) "used" (cursor scratch 208) memory valsMemory
  have orderMemory : (orderStored source scratch).globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)) :=
    expected_memory (usedStored source scratch) "order" (cursor scratch 240) memory usedMemory
  have roundOrder : Arenas.rounded .down (cursor scratch 208) 32#64 = cursor scratch 240 := by
    simpa only [cursor] using Arenas.rounded_decrement scratch 208 32 32 scratchAligned
      (by decide) (by decide) (by decide) (by decide) (by omega)
  have roundPosition : Arenas.rounded .down (cursor scratch 240) 32#64 = cursor scratch 272 := by
    simpa only [cursor] using Arenas.rounded_decrement scratch 240 32 32 scratchAligned
      (by decide) (by decide) (by decide) (by decide) (by omega)
  have allocOrder : Arenas.Prefix.Executes .down (usedStored source scratch)
      [.allocate "order" (WitnessRadix.TableNew.capacityTimes (.const 8#64))] (orderState source scratch)
      (fun post => restore (usedStored source scratch) "order" post) := by
    apply Arenas.Prefix.allocate_expected _ _ "order" _ [] id (cursor scratch 208) memory 32#64 (cursor scratch 240)
      (words_amount _ _ usedLocals) code (expected_scratch _ "used" _) usedMemory memoryAligned
      (by change memory.toNat + 32 ≤ (scratch - BitVec.ofNat 64 208).toNat; rw [number208]; omega) roundOrder
      (by change 1 ≤ source.clock - 1 - 1 - 1 - 1 - 5; omega)
    exact .done _
  have storeOrder := pointer_executes (orderState source scratch) scratch 56 "order" (cursor scratch 240)
    orderLocals.table (bind_lookup_same _ _ _) (mapped 56 (by decide) (by decide))
  have allocPosition : Arenas.Prefix.Executes .down (orderStored source scratch)
      [.allocate "order_pos" (WitnessRadix.TableNew.capacityTimes (.const 8#64))] (positionState source scratch)
      (fun post => restore (orderStored source scratch) "order_pos" post) := by
    apply Arenas.Prefix.allocate_expected _ _ "order_pos" _ [] id (cursor scratch 240) memory 32#64 (cursor scratch 272)
      (words_amount _ _ orderStoredLocals) code (expected_scratch _ "order" _) orderMemory memoryAligned
      (by change memory.toNat + 32 ≤ (scratch - BitVec.ofNat 64 240).toNat; rw [number240]; omega) roundPosition
      (by change 1 ≤ source.clock - 1 - 1 - 1 - 1 - 5 - 1; omega)
    exact .done _
  have storePosition := pointer_executes (positionState source scratch) scratch 64 "order_pos" (cursor scratch 272)
    positionLocals.table (bind_lookup_same _ _ _) (mapped 64 (by decide) (by decide))
  exact ⟨_, clearing.append (storeUsed.append (allocOrder.append (storeOrder.append (allocPosition.append storePosition))))⟩

end InitECandidate.Solver.ScratchTable

#print axioms InitECandidate.Solver.ScratchTable.finish_executes
