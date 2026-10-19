import InitECandidate.Solver.MutableTable.DeleteAfterHashValues

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original post-hash decision and optional complete movement, with
both declaration scopes restored. The hole either stays or becomes this
scan slot; the used-byte set and physical header remain unchanged. -/
theorem after_hash_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (pending : Pending source kind plan count deleted entries hole) (moved : Fin count) (active : moved ≠ deleted)
    (locals : Move.Locals source kind plan hole (entries moved)) (value hash : BitVec 64)
    (valueCell : source.memory (cell plan .values (8 * entries moved)) = .word value)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 count))
    (hashLocal : source.locals.lookup (ofString "h") = some (.val (.word hash)))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 plan.capacity))))
    (code : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ≤ source.clock) :
    ∃ paid memory nextEntries nextHole, paid ≤ MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ∧
      evaluateHOLFiniteState source afterHash = (none, WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - paid} "i" (BitVec.ofNat 64 nextHole)) ∧
      (nextHole = hole ∨ nextHole = entries moved) ∧
      Pending (WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - paid} "i" (BitVec.ofNat 64 nextHole)) kind plan count deleted nextEntries nextHole ∧
      MemoryModel.Header memory kind plan (BitVec.ofNat 64 count) ∧
      (∀ query < plan.capacity, Find.usedByte {source with memory := memory} (parameters kind plan 0#64) (BitVec.ofNat 64 query) =
        Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 query)) ∧
      TableFootprint.Frame source.memory memory kind plan := by
  obtain ⟨paid,memory,nextEntries,nextHole,bounded,run,choice,nextPending,nextHeader,stable,footprint,nextValues⟩ :=
    after_hash_execute_values source kind plan valid domain count deleted entries hole pending moved active locals value hash valueCell header hashLocal capLocal code (fun _=>True) (fun _ _ _ _=>True.intro) enough
  exact ⟨paid,memory,nextEntries,nextHole,bounded,run,choice,nextPending,nextHeader,stable,footprint⟩

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.after_hash_execute
