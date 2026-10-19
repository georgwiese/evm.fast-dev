import InitECandidate.Solver.MutableTable.DeleteModelCallValues

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

/-- Real ignored-result deletion caller, as used by the unchanged guest.
The original physical table survives with zero or one fewer entries and no
change to its layout, heap cursor, globals or other nonlocal fields. -/
theorem model_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < plan.capacity) (occupied : MemoryModel.Occupied source kind plan slots)
    (bits : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length)) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (memeqCode : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, body, .one))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word (cell plan .header 0)), .val (.word query)])
    (enough : modelPrice kind slots.length + 1 ≤ source.clock) :
    ∃ paid memory next flag, paid ≤ modelPrice kind slots.length + 1 ∧
      evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_del") arguments) = (none, modelCallState source paid memory) ∧
      ModelPost source kind plan slots paid memory (modelCallState source paid memory) next flag ∧
      (2 * slots.length ≤ plan.capacity → 2 * next.length ≤ plan.capacity) := by
  obtain ⟨paid,memory,next,flag,bounded,run,post,half,nextValues⟩ :=
    model_call_values source kind plan valid domain little slots room occupied bits small power header query queryFits queryMapped hashCode copyCode memeqCode findCode deleteCode arguments args (fun _=>True) (fun _ _ _ _ _=>True.intro) enough
  exact ⟨paid,memory,next,flag,bounded,run,post,half⟩

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.model_call
