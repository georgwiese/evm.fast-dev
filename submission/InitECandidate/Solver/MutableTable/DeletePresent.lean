import InitECandidate.Solver.MutableTable.DeletePresentValues

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

/-- The whole actual present-deletion suffix: seven header declarations,
real inverse-position read, deleted_pos/j setup, scan, final mutation and
all nine declaration restorations. -/
theorem present_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < plan.capacity) (occupied : MemoryModel.Occupied source kind plan slots) (deleted : Fin slots.length)
    (bits : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (slots.get deleted)))))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 plan.capacity))))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : scanPrice kind * (slots.length - 1) + 1 ≤ source.clock) :
    ∃ paid memory target next, paid ≤ scanPrice kind * (slots.length - 1) + 1 ∧
      evaluateHOLFiniteState source (program headerActions afterHeaders) = (some (.returned (.val (.word 1#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - paid} ∧
      next.length = slots.length - 1 ∧ MemoryModel.Header memory kind plan (BitVec.ofNat 64 next.length) ∧
      MemoryModel.Occupied target kind plan next ∧ TableFootprint.Frame source.memory memory kind plan := by
  obtain ⟨paid,memory,target,next,bounded,run,frame,length,nextHeader,nextOccupied,footprint,nextValues⟩ :=
    present_execute_values source kind plan valid domain little slots room occupied deleted bits small power header tableLocal indexLocal capLocal hashCode copyCode (fun _=>True) (fun _ _ _ _ _=>True.intro) enough
  exact ⟨paid,memory,target,next,bounded,run,frame,length,nextHeader,nextOccupied,footprint⟩

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.present_execute
