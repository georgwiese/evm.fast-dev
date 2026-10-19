import InitECandidate.Solver.MutableTable.DeleteScanLoopValues

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete original deletion scan through an unchanged used-byte prefix.
Each occupied iteration pays for the actual hash, optional copy and while;
the final empty iteration pays one while clock. The physical model, header,
nonlocal state and all locals other than i/j are preserved as specified. -/
theorem scan_loop (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (bits start : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits) (startInside : start < plan.capacity)
    (count : Nat) (deleted : Fin count)
    (remaining : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (cursor : Nat) (entries : Fin count → Nat) (hole : Nat)
    (stopInside : cursor + remaining + 1 < plan.capacity)
    (pending : Pending source kind plan count deleted entries hole)
    (frontier : Frontier plan.capacity start cursor hole)
    (locals : ScanLocals source kind plan hole (Probe.slot plan.capacity start cursor))
    (occupied : ∀ rank, cursor < rank → rank < cursor + remaining + 1 →
      Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 (Probe.slot plan.capacity start rank)) = some 1)
    (empty : Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 (Probe.slot plan.capacity start (cursor + remaining + 1))) = some 0)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 count))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : scanPrice kind * remaining + 1 ≤ source.clock) :
    ∃ paid memory target nextEntries nextHole, paid ≤ scanPrice kind * remaining + 1 ∧
      evaluateHOLFiniteState source loop = (none, target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - paid} ∧
      ScanLocals target kind plan nextHole (Probe.slot plan.capacity start (cursor + remaining + 1)) ∧
      Pending target kind plan count deleted nextEntries nextHole ∧
      Frontier plan.capacity start (cursor + remaining + 1) nextHole ∧
      MemoryModel.Header memory kind plan (BitVec.ofNat 64 count) ∧
      (∀ query < plan.capacity, Find.usedByte {source with memory := memory} (parameters kind plan 0#64) (BitVec.ofNat 64 query) =
        Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 query)) ∧
      (∀ name : String, ofString "i" ≠ ofString name → ofString "j" ≠ ofString name →
        target.locals.lookup (ofString name) = source.locals.lookup (ofString name)) ∧
      TableFootprint.Frame source.memory memory kind plan := by
  obtain ⟨paid,memory,target,nextEntries,nextHole,bounded,run,frame,nextLocals,nextPending,nextFrontier,nextHeader,stable,other,footprint,nextValues⟩ :=
    scan_loop_values kind plan valid bits start small power startInside count deleted remaining source domain little cursor entries hole stopInside pending frontier locals occupied empty header hashCode copyCode (fun _=>True) (fun _ _ _ _=>True.intro) enough
  exact ⟨paid,memory,target,nextEntries,nextHole,bounded,run,frame,nextLocals,nextPending,nextFrontier,nextHeader,stable,other,footprint⟩

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.scan_loop
