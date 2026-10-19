import InitECandidate.Solver.MutableTable.SetGrowValues
import InitECandidate.Solver.MutableTable.SetGrowGuard
import InitECandidate.Solver.MutableTable.GrowRuntime.Call

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual absent-key growing setter suffix: derive the original guard,
execute growth, insert into its returned physical table, then return. Entry
allocation/query/code reachability remains explicit; neither mutation result
nor its execution is an input hypothesis. -/
theorem after_grow (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start : Nat) (newValid : Valid kind (relocated kind (old.base .header) start (2 * old.capacity)))
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (header : MemoryModel.Header source.memory kind old (BitVec.ofNat 64 slots.length)) (occupied : MemoryModel.Occupied source kind old slots)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))))
    (query value : BitVec 64) (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (valueLocal : source.locals.lookup (ofString "value") = some (.val (.word value)))
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (threshold : old.capacity < 2 * slots.length + 2)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (bits : Nat) (power : old.capacity = 2 ^ bits) (minimum : 2 ≤ bits)
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw") = some (TableCall.formals, Insert.body, .one))
    (growCode : source.code.lookup (ofString "htab_grow") = some (Grow.formals, Grow.body, .one))
    (enough : afterGrowPrice kind old.capacity slots.length ≤ source.clock) :
    ∃ paid memory target next, paid ≤ afterGrowPrice kind old.capacity slots.length ∧
      evaluateHOLFiniteState source afterPresent = (some (.returned (.val (.word 0#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite (GrowRuntime.callState source kind old start memory paid) ∧
      next.length = slots.length + 1 ∧
      MemoryModel.Header memory kind (relocated kind (old.base .header) start (2 * old.capacity)) (BitVec.ofNat 64 next.length) ∧
      MemoryModel.Occupied target kind (relocated kind (old.base .header) start (2 * old.capacity)) next ∧
      TableFootprint.Frame source.memory memory kind (relocated kind (old.base .header) start (2 * old.capacity)) := by
  obtain ⟨paid, memory, target, next, bounded, run, fields, length, nextHeader, nextOccupied, footprint, _⟩ :=
    after_grow_values source kind old oldValid start newValid earlier domain little slots header occupied
      (fun _=>True) (fun _ _ _ _ _=>True.intro) tableLocal query value keyLocal valueLocal queryFits queryMapped
      True.intro threshold heap bits power minimum allocCode zeroCode hashCode copyCode insertCode growCode enough
  exact ⟨paid, memory, target, next, bounded, run, fields, length, nextHeader, nextOccupied, footprint⟩

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.after_grow
