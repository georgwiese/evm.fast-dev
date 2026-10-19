import InitECandidate.Solver.MutableTable.DeleteScanStepValues

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- One occupied iteration of the literal original deletion body, before
the enclosing while-clock. The next-slot/hole distinction follows from the
finite masked frontier; it is not an assumed dictionary correctness fact. -/
theorem scan_step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (pending : Pending source kind plan count deleted entries hole)
    (bits start cursor : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (startInside : start < plan.capacity) (nextInside : cursor + 1 < plan.capacity)
    (frontier : Frontier plan.capacity start cursor hole)
    (locals : ScanLocals source kind plan hole (Probe.slot plan.capacity start cursor))
    (used : Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 (Probe.slot plan.capacity start (cursor + 1))) = some 1)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 count))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ≤ source.clock) :
    ∃ paid memory nextEntries nextHole,
      paid ≤ KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ∧
      evaluateHOLFiniteState source loopBody = (none,
        WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - paid}
          "j" (BitVec.ofNat 64 (Probe.slot plan.capacity start (cursor + 1)))) "i" (BitVec.ofNat 64 nextHole)) ∧
      Pending (WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - paid}
          "j" (BitVec.ofNat 64 (Probe.slot plan.capacity start (cursor + 1)))) "i" (BitVec.ofNat 64 nextHole)) kind plan count deleted nextEntries nextHole ∧
      Frontier plan.capacity start (cursor + 1) nextHole ∧
      MemoryModel.Header memory kind plan (BitVec.ofNat 64 count) ∧
      (∀ query < plan.capacity, Find.usedByte {source with memory := memory} (parameters kind plan 0#64) (BitVec.ofNat 64 query) =
        Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 query)) ∧
      TableFootprint.Frame source.memory memory kind plan := by
  obtain ⟨paid,memory,nextEntries,nextHole,bounded,run,nextPending,nextFrontier,nextHeader,stable,footprint,nextValues⟩ :=
    scan_step_values source kind plan valid domain little count deleted entries hole pending bits start cursor small power startInside nextInside frontier locals used header hashCode copyCode (fun _=>True) (fun _ _ _ _=>True.intro) enough
  exact ⟨paid,memory,nextEntries,nextHole,bounded,run,nextPending,nextFrontier,nextHeader,stable,footprint⟩

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.scan_step
