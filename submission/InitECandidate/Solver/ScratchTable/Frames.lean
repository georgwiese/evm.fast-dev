import InitECandidate.Solver.ScratchTable.Finish

namespace InitECandidate.Solver.ScratchTable
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem final_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64)
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word 4#64))) :
    Locals (finalState source scratch) scratch := by
  have before := preclear_locals source scratch capLocal
  have after : Locals (clearState source scratch) scratch := ⟨before.table, before.capacity, before.stride⟩
  have used := after.stored (pointerFields 48 "used" (cursor scratch 208))
  have order := used.allocated "order" (cursor scratch 240) (by decide) (by decide) (by decide)
  have position := (order.stored (pointerFields 56 "order" (cursor scratch 240))).allocated "order_pos" (cursor scratch 272)
    (by decide) (by decide) (by decide)
  exact position.stored (pointerFields 64 "order_pos" (cursor scratch 272))

theorem final_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :
    emptyLocalsHOLFinite (finalState source scratch) = emptyLocalsHOLFinite {source with
      globals := source.globals.update (ofString "scratch_ptr", .val (.word (cursor scratch 272)))
      memory := (finalState source scratch).memory
      clock := source.clock - 11} := by
  have globals : (finalState source scratch).globals =
      source.globals.update (ofString "scratch_ptr", .val (.word (cursor scratch 272))) := by
    apply HolFiniteMapExact.ext
    funext query
    by_cases same : ofString "scratch_ptr" = query <;>
      simp [finalState, positionState, orderStored, orderState, usedStored, clearState, preClearState,
        valsStored, valsState, keysStored, keysState, initialState, strideState, tableState, stored,
        Arenas.Prefix.expectedState, WitnessRadix.QueryBranch.bind, setVarHOLFinite,
        HolFiniteMapExact.update, FUPDATE, same]
  have clocks : (finalState source scratch).clock = source.clock - 11 := by
    change source.clock - 1 - 1 - 1 - 1 - 5 - 1 - 1 = source.clock - 11
    omega
  have actual : emptyLocalsHOLFinite (finalState source scratch) = emptyLocalsHOLFinite {source with
      globals := (finalState source scratch).globals
      memory := (finalState source scratch).memory
      clock := (finalState source scratch).clock} := rfl
  rw [globals, clocks] at actual
  exact actual

theorem pointer_memory_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch query : BitVec 64)
    (offset : Nat) (name : String) (pointer : BitVec 64)
    (away : query ≠ cursor scratch 72 + BitVec.ofNat 64 offset) :
    (stored source scratch (pointerFields offset name pointer)).memory query = source.memory query := by
  apply WitnessRadix.WordWrites.write_away
  simpa only [FieldStores.writes, pointerFields, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false, not_false_eq_true] using away

/-- All real header writes and the four byte clears stay below the incoming
scratch cursor. The complete allocated table/backing plan consumes272bytes. -/
theorem final_memory_outside (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch query : BitVec 64)
    (aligned : scratch.toNat % 8 = 0) (room : 272 ≤ scratch.toNat)
    (outsideArena : query.toNat < (cursor scratch 272).toNat ∨ scratch.toNat ≤ query.toNat) :
    (finalState source scratch).memory query = source.memory query := by
  have tableNumber := Arenas.cursor_number scratch 72 (by omega)
  have usedNumber := Arenas.cursor_number scratch 208 (by omega)
  have tableValue : (cursor scratch 72).toNat = scratch.toNat - 72 := tableNumber
  have lastValue : (cursor scratch 272).toNat = scratch.toNat - 272 := Arenas.cursor_number scratch 272 room
  have headerAway : ∀ offset < 72, query ≠ cursor scratch 72 + BitVec.ofNat 64 offset := by
    intro offset inside equal
    have number := WitnessRadix.byteAddress_toNat (cursor scratch 72) offset
      (by change (scratch - BitVec.ofNat 64 72).toNat + offset < 2 ^ 64; rw [tableNumber]; have bound := scratch.isLt; omega)
    change (cursor scratch 72 + BitVec.ofNat 64 offset).toNat = (cursor scratch 72).toNat + offset at number
    have same := congrArg BitVec.toNat equal
    change (scratch - BitVec.ofNat 64 72).toNat = scratch.toNat - 72 at tableNumber
    rcases outsideArena with below | above <;> omega
  have initialAway : (initialState source scratch).memory query = source.memory query := by
    change WitnessRadix.WordWrites.write source.memory (FieldStores.writes (cursor scratch 72) headerFields) query = _
    apply WitnessRadix.WordWrites.write_away
    simp only [FieldStores.writes, headerFields, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    exact ⟨headerAway 0 (by decide), headerAway 8 (by decide), headerAway 16 (by decide), headerAway 24 (by decide)⟩
  have keysAway := pointer_memory_away (keysState source scratch) scratch query 32 "keys" (cursor scratch 168) (headerAway 32 (by decide))
  have valsAway := pointer_memory_away (valsState source scratch) scratch query 40 "vals" (cursor scratch 200) (headerAway 40 (by decide))
  have beforeAway : (preClearState source scratch).memory query = source.memory query := valsAway.trans (keysAway.trans initialAway)
  have usedAligned : (cursor scratch 208).toNat % 8 = 0 := by change (scratch - BitVec.ofNat 64 208).toNat % 8 = 0; rw [usedNumber]; omega
  have usedFits : (cursor scratch 208).toNat + 32 < 2 ^ 64 := by
    change (scratch - BitVec.ofNat 64 208).toNat + 32 < 2 ^ 64
    rw [usedNumber]
    have bound := scratch.isLt
    omega
  have usedAway : query ≠ cursor scratch 208 := by
    intro equal
    have same := congrArg BitVec.toNat equal
    change query.toNat = (scratch - BitVec.ofNat 64 208).toNat at same
    rcases outsideArena with below | above <;> omega
  have clearAway := WitnessRadix.Zero.small_memory_away (preClearState source scratch).memory source.be
    (cursor scratch 208) query 4 (by decide) usedAligned usedFits usedAway
  have usedStoreAway := pointer_memory_away (clearState source scratch) scratch query 48 "used" (cursor scratch 208) (headerAway 48 (by decide))
  have orderAway := pointer_memory_away (orderState source scratch) scratch query 56 "order" (cursor scratch 240) (headerAway 56 (by decide))
  have positionAway := pointer_memory_away (positionState source scratch) scratch query 64 "order_pos" (cursor scratch 272) (headerAway 64 (by decide))
  exact positionAway.trans (orderAway.trans (usedStoreAway.trans (clearAway.trans beforeAway)))

theorem final_memory_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch query : BitVec 64)
    (aligned : scratch.toNat % 8 = 0) (room : 272 ≤ scratch.toNat) (above : scratch.toNat ≤ query.toNat) :
    (finalState source scratch).memory query = source.memory query :=
  final_memory_outside source scratch query aligned room (Or.inr above)

end InitECandidate.Solver.ScratchTable

#print axioms InitECandidate.Solver.ScratchTable.final_locals
#print axioms InitECandidate.Solver.ScratchTable.final_frame
#print axioms InitECandidate.Solver.ScratchTable.pointer_memory_away
#print axioms InitECandidate.Solver.ScratchTable.final_memory_away

#print axioms InitECandidate.Solver.ScratchTable.final_memory_outside
