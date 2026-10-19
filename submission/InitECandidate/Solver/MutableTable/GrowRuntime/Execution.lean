import InitECandidate.Solver.MutableTable.GrowRuntime.ExecutionValues
import InitECandidate.Solver.MutableTable.GrowRuntime.Setup
import InitECandidate.Solver.MutableTable.GrowRuntime.Loop
import InitECandidate.Solver.MutableTable.GrowRuntime.Footprint

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete original growth body. It doubles and relocates the arrays,
clears the new occupancy, reinserts every old dense-order item, returns and
restores all declaration scopes. The physical model and complete nonlocal
frame are derived from actual execution. Global heap reachability is still
an entry obligation, and these are source clocks rather than target steps. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start : Nat) (newValid : Valid kind (relocated kind (old.base .header) start (2 * old.capacity)))
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false) (multiple : (2 * old.capacity) % 8 = 0)
    (slots : List Nat) (room : slots.length ≤ old.capacity)
    (header : MemoryModel.Header source.memory kind old (BitVec.ofNat 64 slots.length)) (occupied : MemoryModel.Occupied source kind old slots)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (bits : Nat) (small : bits < 64) (power : 2 * old.capacity = 2 ^ bits)
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw") = some (TableCall.formals, Insert.body, .one))
    (enough : price kind (2 * old.capacity) slots.length ≤ source.clock) :
    ∃ paid memory target next, paid ≤ price kind (2 * old.capacity) slots.length ∧
      evaluateHOLFiniteState source Grow.body = (some (.returned (.val (.word 0#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with
        globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (relocatedEnd kind start (2 * old.capacity)))))
        memory := memory, clock := source.clock - paid} ∧
      next.length = slots.length ∧
      MemoryModel.Header memory kind (relocated kind (old.base .header) start (2 * old.capacity)) (BitVec.ofNat 64 next.length) ∧
      MemoryModel.Occupied target kind (relocated kind (old.base .header) start (2 * old.capacity)) next ∧ OldArrays target source kind old ∧
      TableFootprint.Frame source.memory memory kind (relocated kind (old.base .header) start (2 * old.capacity)) := by
  obtain ⟨paid, memory, target, next, bounded, run, fields, length, nextHeader, nextOccupied, arrays, footprint, _⟩ :=
    execute_values source kind old oldValid start newValid earlier domain little multiple slots room header occupied
      (fun _=>True) (fun _ _ _ _ _=>True.intro) tableLocal heap bits small power allocCode zeroCode hashCode copyCode insertCode enough
  exact ⟨paid, memory, target, next, bounded, run, fields, length, nextHeader, nextOccupied, arrays, footprint⟩

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.execute
