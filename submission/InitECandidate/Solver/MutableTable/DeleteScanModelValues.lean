import InitECandidate.Solver.MutableTable.DeleteScanLoopValues

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual original deletion scan starts from the physical table model.
It hashes at most D-1 occupied successors, followed by one empty iteration,
without a hash-distribution or self-lookup correctness assumption. -/
theorem scan_from_occupied_values (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < plan.capacity) (occupied : MemoryModel.Occupied source kind plan slots) (deleted : Fin slots.length)
    (bits : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (locals : ScanLocals source kind plan (slots.get deleted) (slots.get deleted))
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (property : BitVec 64 → Prop) (values : Get.OccupiedValuesHave source (cell plan .values 0) (BitVec.ofNat 64 plan.capacity) slots property)
    (enough : scanPrice kind * (slots.length - 1) + 1 ≤ source.clock) :
    ∃ stop paid memory target nextEntries nextHole,
      1 ≤ stop ∧ stop ≤ slots.length ∧ paid ≤ scanPrice kind * (slots.length - 1) + 1 ∧
      evaluateHOLFiniteState source loop = (none, target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - paid} ∧
      ScanLocals target kind plan nextHole (Probe.slot plan.capacity (slots.get deleted) stop) ∧
      Pending target kind plan slots.length deleted nextEntries nextHole ∧
      MemoryModel.Header memory kind plan (BitVec.ofNat 64 slots.length) ∧
      (∀ query < plan.capacity, Find.usedByte {source with memory := memory} (parameters kind plan 0#64) (BitVec.ofNat 64 query) =
        Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 query)) ∧
      (∀ name : String, ofString "i" ≠ ofString name → ofString "j" ≠ ofString name →
        target.locals.lookup (ofString name) = source.locals.lookup (ofString name)) ∧
      TableFootprint.Frame source.memory memory kind plan ∧ PendingValues {source with memory:=memory} plan deleted nextEntries property := by
  obtain ⟨stop, positive, bounded, empty, prefixUsed⟩ := deletion_first_empty source kind plan slots room occupied deleted
  have startInside := occupied.inside _ (List.get_mem slots deleted)
  have endIndex : 0 + (stop - 1) + 1 = stop := by omega
  have budget : scanPrice kind * (stop - 1) + 1 ≤ scanPrice kind * (slots.length - 1) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 1
  have scanLocals : ScanLocals source kind plan (slots.get deleted) (Probe.slot plan.capacity (slots.get deleted) 0) := by
    simpa only [Probe.slot, Nat.add_zero, Nat.mod_eq_of_lt startInside] using locals
  obtain ⟨paid, memory, target, nextEntries, nextHole, paidBound, actual, frame, finalLocals, finalPending, frontier, finalHeader, stable, other, footprint, finalValues⟩ :=
    scan_loop_values kind plan valid bits (slots.get deleted) small power startInside slots.length deleted (stop - 1) source domain little 0 _ _
      (by omega) (initial_pending source kind plan slots room occupied deleted) (frontier_initial _ _ startInside) scanLocals
      (by intro rank lower upper; exact prefixUsed rank (by omega)) (by simpa only [endIndex] using empty)
      header hashCode copyCode property (PendingValues.initial source kind plan valid slots occupied deleted property values) (Nat.le_trans budget enough)
  exact ⟨stop, paid, memory, target, nextEntries, nextHole, positive, bounded, Nat.le_trans paidBound budget, actual, frame,
    by simpa only [endIndex] using finalLocals, finalPending, finalHeader, stable, other, footprint, finalValues⟩

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.scan_from_occupied_values
