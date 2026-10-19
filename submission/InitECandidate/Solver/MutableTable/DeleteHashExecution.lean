import InitECandidate.Solver.MutableTable.DeleteHashValues

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual original hash caller and its complete optional movement
continuation. Scoped hash/home/movable bindings restore, while the hole is
unchanged or becomes the current scan slot. All old used bytes remain intact. -/
theorem hash_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (pending : Pending source kind plan count deleted entries hole) (moved : Fin count) (active : moved ≠ deleted)
    (locals : Move.Locals source kind plan hole (entries moved)) (value : BitVec 64)
    (valueCell : source.memory (cell plan .values (8 * entries moved)) = .word value)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 count))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 plan.capacity))))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ≤ source.clock) :
    ∃ paid memory nextEntries nextHole, paid ≤ KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ∧
      evaluateHOLFiniteState source hashCall = (none, WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - paid} "i" (BitVec.ofNat 64 nextHole)) ∧
      (nextHole = hole ∨ nextHole = entries moved) ∧
      Pending (WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - paid} "i" (BitVec.ofNat 64 nextHole)) kind plan count deleted nextEntries nextHole ∧
      MemoryModel.Header memory kind plan (BitVec.ofNat 64 count) ∧
      (∀ query < plan.capacity, Find.usedByte {source with memory := memory} (parameters kind plan 0#64) (BitVec.ofNat 64 query) =
        Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 query)) ∧
      TableFootprint.Frame source.memory memory kind plan := by
  obtain ⟨paid,memory,nextEntries,nextHole,bounded,run,choice,nextPending,nextHeader,stable,footprint,nextValues⟩ :=
    hash_execute_values source kind plan valid domain little count deleted entries hole pending moved active locals value valueCell header capLocal hashCode copyCode (fun _=>True) (fun _ _ _ _=>True.intro) enough
  exact ⟨paid,memory,nextEntries,nextHole,bounded,run,choice,nextPending,nextHeader,stable,footprint⟩

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.hash_execute
