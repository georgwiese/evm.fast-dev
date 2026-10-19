import InitECandidate.Solver.MutableTable.DeleteScanFinishValues

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The entire original present-deletion scan and final mutation. The
physical table supplies scan progress; the actual final stores establish a
new physical table with one fewer entry. -/
theorem scan_finish (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < plan.capacity) (occupied : MemoryModel.Occupied source kind plan slots) (deleted : Fin slots.length)
    (bits : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (locals : ScanLocals source kind plan (slots.get deleted) (slots.get deleted))
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (deletedLocal : source.locals.lookup (ofString "deleted_pos") = some (.val (.word (BitVec.ofNat 64 deleted.val))))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : scanPrice kind * (slots.length - 1) + 1 ≤ source.clock) :
    ∃ paid memory target next, paid ≤ scanPrice kind * (slots.length - 1) + 1 ∧
      evaluateHOLFiniteState source (.seq loop afterLoop) = (some (.returned (.val (.word 1#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - paid} ∧
      next.length = slots.length - 1 ∧ MemoryModel.Header memory kind plan (BitVec.ofNat 64 next.length) ∧
      MemoryModel.Occupied target kind plan next ∧ TableFootprint.Frame source.memory memory kind plan := by
  obtain ⟨paid,memory,target,next,bounded,run,frame,length,nextHeader,nextOccupied,footprint,nextValues⟩ :=
    scan_finish_values source kind plan valid domain little slots room occupied deleted bits small power locals header tableLocal deletedLocal hashCode copyCode (fun _=>True) (fun _ _ _ _ _=>True.intro) enough
  exact ⟨paid,memory,target,next,bounded,run,frame,length,nextHeader,nextOccupied,footprint⟩

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.scan_finish
