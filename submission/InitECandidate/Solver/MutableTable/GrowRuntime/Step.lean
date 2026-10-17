import InitECandidate.Solver.MutableTable.GrowRuntime.Frames
import InitECandidate.Solver.WitnessRadix.Bindings

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- One complete actual rehash body: old order read, raw-insertion ABI,
index increment and restoration of the scoped slot local. No insertion
execution or post-state representation is assumed. -/
theorem step_execute (source snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start capacity : Nat) (newValid : Valid kind (relocated kind (old.base .header) start capacity))
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (oldSlots : List Nat) (oldRoom : oldSlots.length ≤ old.capacity) (oldOccupied : MemoryModel.Occupied snapshot kind old oldSlots)
    (frame : OldArrays source snapshot kind old) (cursor : Fin oldSlots.length)
    (locals : LoopLocals source kind old oldSlots.length cursor.val)
    (slots : List Nat) (room : slots.length < capacity)
    (header : MemoryModel.Header source.memory kind (relocated kind (old.base .header) start capacity) (BitVec.ofNat 64 slots.length))
    (occupied : MemoryModel.Occupied source kind (relocated kind (old.base .header) start capacity) slots)
    (bits : Nat) (small : bits < 64) (power : capacity = 2 ^ bits)
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw") = some (TableCall.formals, Insert.body, .one))
    (enough : slots.length + KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 2 ≤ source.clock) :
    ∃ paid memory nextSlot, paid ≤ slots.length + KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 2 ∧
      evaluateHOLFiniteState source Grow.loopBody =
        (none, WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - paid} "k" (BitVec.ofNat 64 (cursor.val + 1))) ∧
      MemoryModel.Header memory kind (relocated kind (old.base .header) start capacity) (BitVec.ofNat 64 (slots ++ [nextSlot]).length) ∧
      MemoryModel.Occupied {source with memory := memory, clock := source.clock - paid} kind (relocated kind (old.base .header) start capacity) (slots ++ [nextSlot]) ∧
      OldArrays {source with memory := memory, clock := source.clock - paid} snapshot kind old := by
  let plan := relocated kind (old.base .header) start capacity
  let oldSlot := BitVec.ofNat 64 (oldSlots.get cursor)
  let query := cell old .keys 0 + oldSlot * BitVec.ofNat 64 (NaturalLayout.stride kind)
  have oldInside := oldOccupied.inside (oldSlots.get cursor) (List.get_mem oldSlots cursor)
  have slotNat : oldSlot.toNat = oldSlots.get cursor := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans oldInside (capacity_small kind old oldValid))]
  have vectorInside : oldSlot.toNat < old.capacity := by rw [slotNat]; exact oldInside
  have cursorSmall : cursor.val < 2 ^ 64 := by
    have high := cursor.isLt
    have capHigh := capacity_small kind old oldValid
    omega
  have orderMapped : source.memaddrs (cell old .order 0 + BitVec.ofNat 64 cursor.val * 8#64) := by
    rw [domain, scaled_cell, BitVec.toNat_ofNat, Nat.mod_eq_of_lt cursorSmall]
    exact mapped kind old oldValid .order _ (word_offset_inside kind old .order cursor.val (Or.inr (Or.inl rfl)) (by have := cursor.isLt; omega)) (by omega)
  have orderRead := index_read source kind old oldSlots.length cursor.val locals oldSlot orderMapped
    (old_order_cell source snapshot kind old oldValid oldSlots oldRoom oldOccupied frame cursor)
  let entry := WitnessRadix.QueryBranch.bind source "i" oldSlot
  have entryLocals := LoopLocals.bind_i source kind old _ _ locals oldSlot
  have valuesMapped : entry.memaddrs (cell old .values 0 + oldSlot * 8#64) := by
    change source.memaddrs (cell old .values 0 + oldSlot * 8#64)
    rw [domain, scaled_cell]
    exact mapped kind old oldValid .values _ (word_offset_inside kind old .values oldSlot.toNat (Or.inl rfl) vectorInside) (by omega)
  cases valueRead : source.memory (cell old .values 0 + oldSlot * 8#64) with
  | word value =>
    have args := insert_arguments entry kind old oldSlots.length cursor.val entryLocals oldSlot value (bind_lookup_same _ _ _) valuesMapped valueRead
    have queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64 := slot_fits kind old oldValid 0#64 oldSlot vectorInside
    have queryMapped : ∀ offset < KeyHash.keySize kind, entry.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)) := by
      intro offset inside
      change source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset))
      rw [domain]
      exact slot_mapped kind old oldValid 0#64 oldSlot vectorInside offset inside
    have entryOccupied := MemoryModel.Occupied.of_fields source entry kind plan slots occupied rfl rfl rfl
    obtain ⟨paid, index, bounded, inside, fresh, actual, nextHeader, nextOccupied⟩ := MemoryModel.insertion_call entry kind plan newValid domain little slots room header entryOccupied
      query value bits small power queryFits queryMapped hashCode copyCode insertCode [localVar "t", Grow.keyAddress, Grow.valueRead] args enough
    let memory := MemoryModel.insertedMemory source.memory source.be kind plan query index (BitVec.ofNat 64 slots.length) value
    let post := {entry with memory := memory, clock := source.clock - paid}
    have kLocal : post.locals.lookup (ofString "k") = some (.val (.word (BitVec.ofNat 64 cursor.val))) := entryLocals.indexLocal
    have incrementRead : eval post (.op .add [localVar "k", .const 1#64]) = some (.val (.word (BitVec.ofNat 64 (cursor.val + 1)))) := by
      simp [eval, localVar, evalHOLExact, evalListHOLExact, toExact, kLocal,
        valueIsWord, valueWord, wordOpHOL, wordOp, ← BitVec.ofNat_add]
    have incrementRun := StateSteps.assign_execute post "k" _ (BitVec.ofNat 64 cursor.val) (BitVec.ofNat 64 (cursor.val + 1)) entryLocals.indexLocal incrementRead
    have inner : evaluateHOLFiniteState entry (.seq Grow.insertCall Grow.increment) =
        (none, WitnessRadix.QueryBranch.bind post "k" (BitVec.ofNat 64 (cursor.val + 1))) := by
      rw [StateSteps.next_sequence entry post Grow.insertCall Grow.increment actual (by change source.clock - paid ≤ source.clock; omega)]
      exact incrementRun
    have run := Input.ScalarScope.declare_execute source _ "i" Grow.indexRead oldSlot (.seq Grow.insertCall Grow.increment) none orderRead inner
    have restored : restore source "i" (WitnessRadix.QueryBranch.bind post "k" (BitVec.ofNat 64 (cursor.val + 1))) =
        WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - paid} "k" (BitVec.ofNat 64 (cursor.val + 1)) := by
      rw [restore_bind_other source post "i" "k" _ (by decide)]
      change WitnessRadix.QueryBranch.bind (restore {source with memory := memory, clock := source.clock - paid} "i"
        (WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - paid} "i" oldSlot)) "k" _ = _
      rw [restore_bound]
    have countInside : (BitVec.ofNat 64 slots.length).toNat < capacity := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans room (capacity_small kind plan newValid))]
      exact room
    have kept := inserted_old_arrays source snapshot kind old oldValid start capacity newValid earlier frame query index _ value inside countInside
    refine ⟨paid, memory, index.toNat, bounded, ?_, nextHeader, ?_, ?_⟩
    · simpa only [Grow.loopBody, restored] using run
    · exact MemoryModel.Occupied.of_fields _ _ kind plan _ nextOccupied rfl rfl rfl
    · exact OldArrays.of_memory _ _ snapshot kind old rfl kept

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.step_execute
