import InitECandidate.Solver.MutableTable.GrowRuntime.CallValues
import InitECandidate.Solver.MutableTable.GrowRuntime.Execution
import InitECandidate.Solver.MutableTable.GrowRuntime.Environment
import InitECandidate.Solver.MutableTable.MemoryModelBounds

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual ignored-result growth caller. The physical model derives the old
item-count bound; actual owned extents and the old power derive the signed
loop range, new probe power and clearing shape. Header/array allocation room
and full code/clock reachability remain explicit caller obligations. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start : Nat) (newValid : Valid kind (relocated kind (old.base .header) start (2 * old.capacity)))
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (header : MemoryModel.Header source.memory kind old (BitVec.ofNat 64 slots.length)) (occupied : MemoryModel.Occupied source kind old slots)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (bits : Nat) (power : old.capacity = 2 ^ bits) (minimum : 2 ≤ bits)
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw") = some (TableCall.formals, Insert.body, .one))
    (growCode : source.code.lookup (ofString "htab_grow") = some (Grow.formals, Grow.body, .one))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (Grow.values (cell old .header 0)))
    (enough : price kind (2 * old.capacity) slots.length + 1 ≤ source.clock) :
    ∃ paid memory next, paid ≤ price kind (2 * old.capacity) slots.length + 1 ∧
      evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_grow") arguments) =
        (none, callState source kind old start memory paid) ∧ next.length = slots.length ∧
      MemoryModel.Header memory kind (relocated kind (old.base .header) start (2 * old.capacity)) (BitVec.ofNat 64 next.length) ∧
      MemoryModel.Occupied (callState source kind old start memory paid) kind (relocated kind (old.base .header) start (2 * old.capacity)) next ∧
      OldArrays (callState source kind old start memory paid) source kind old ∧
      TableFootprint.Frame source.memory memory kind (relocated kind (old.base .header) start (2 * old.capacity)) := by
  obtain ⟨paid, memory, next, bounded, run, length, nextHeader, nextOccupied, arrays, footprint, _⟩ :=
    call_execute_values source kind old oldValid start newValid earlier domain little slots header occupied
      (fun _=>True) (fun _ _ _ _ _=>True.intro) heap bits power minimum allocCode zeroCode hashCode copyCode insertCode growCode arguments args enough
  exact ⟨paid, memory, next, bounded, run, length, nextHeader, nextOccupied, arrays, footprint⟩

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.call_execute
