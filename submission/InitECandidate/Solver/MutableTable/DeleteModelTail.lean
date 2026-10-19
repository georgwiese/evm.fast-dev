import InitECandidate.Solver.MutableTable.DeleteModelTailValues

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

/-- Actual cap read, absent return or complete present-deletion suffix.
The present ordinal is obtained from the real physical occupied list. -/
theorem model_tail (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < plan.capacity) (occupied : MemoryModel.Occupied source kind plan slots)
    (bits : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length)) (index : BitVec 64)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (presentMember : index ≠ BitVec.ofNat 64 plan.capacity → index.toNat ∈ slots)
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : tailPrice kind slots.length ≤ source.clock) :
    ∃ paid memory target next flag, paid ≤ tailPrice kind slots.length ∧
      evaluateHOLFiniteState source afterIndex = (some (.returned (.val (.word flag))), target) ∧
      ModelPost source kind plan slots paid memory target next flag := by
  obtain ⟨paid,memory,target,next,flag,bounded,run,post,nextValues⟩ :=
    model_tail_values source kind plan valid domain little slots room occupied bits small power header index tableLocal indexLocal presentMember hashCode copyCode (fun _=>True) (fun _ _ _ _ _=>True.intro) enough
  exact ⟨paid,memory,target,next,flag,bounded,run,post⟩

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.model_tail
