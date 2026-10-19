import InitECandidate.Solver.MutableTable.DeleteScanModelValues

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual original deletion scan starts from the physical table model.
It hashes at most D-1 occupied successors, followed by one empty iteration,
without a hash-distribution or self-lookup correctness assumption. -/
theorem scan_from_occupied (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < plan.capacity) (occupied : MemoryModel.Occupied source kind plan slots) (deleted : Fin slots.length)
    (bits : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (locals : ScanLocals source kind plan (slots.get deleted) (slots.get deleted))
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
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
      TableFootprint.Frame source.memory memory kind plan := by
  obtain ⟨stop,paid,memory,target,nextEntries,nextHole,positive,stopBound,bounded,run,frame,nextLocals,nextPending,nextHeader,stable,other,footprint,nextValues⟩ :=
    scan_from_occupied_values source kind plan valid domain little slots room occupied deleted bits small power locals header hashCode copyCode (fun _=>True) (fun _ _ _ _ _=>True.intro) enough
  exact ⟨stop,paid,memory,target,nextEntries,nextHole,positive,stopBound,bounded,run,frame,nextLocals,nextPending,nextHeader,stable,other,footprint⟩

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.scan_from_occupied
