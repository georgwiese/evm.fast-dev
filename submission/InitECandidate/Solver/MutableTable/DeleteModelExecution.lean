import InitECandidate.Solver.MutableTable.DeleteModelExecutionValues

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Entire unchanged htab_del body: actual lookup, absent/present choice,
all original headers and scans, final stores, scopes and physical result. -/
theorem model_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < plan.capacity) (occupied : MemoryModel.Occupied source kind plan slots)
    (bits : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length)) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (memeqCode : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (enough : modelPrice kind slots.length ≤ source.clock) :
    ∃ paid memory target next flag, paid ≤ modelPrice kind slots.length ∧
      evaluateHOLFiniteState source body = (some (.returned (.val (.word flag))), target) ∧
      ModelPost source kind plan slots paid memory target next flag := by
  obtain ⟨paid,memory,target,next,flag,bounded,run,post,nextValues⟩ :=
    model_execute_values source kind plan valid domain little slots room occupied bits small power header query queryFits queryMapped tableLocal keyLocal hashCode copyCode memeqCode findCode (fun _=>True) (fun _ _ _ _ _=>True.intro) enough
  exact ⟨paid,memory,target,next,flag,bounded,run,post⟩

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.model_execute
