import InitECandidate.Solver.MutableTable.GrowRuntime.LoopValues

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole original signed rehash loop. Each iteration derives its old-row
read and new-table mutation from actual execution. The price sums increasing
occupied counts rather than multiplying every probe by the final count. -/
theorem loop_execute (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start capacity : Nat) (newValid : Valid kind (relocated kind (old.base .header) start capacity))
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (oldSlots : List Nat) (oldRoom : oldSlots.length ≤ old.capacity) (newRoom : oldSlots.length < capacity)
    (oldOccupied : MemoryModel.Occupied snapshot kind old oldSlots) (bits : Nat) (small : bits < 64) (power : capacity = 2 ^ bits)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (cursor remaining : Nat) (count : cursor + remaining = oldSlots.length)
    (locals : LoopLocals source kind old oldSlots.length cursor)
    (slots : List Nat) (length : slots.length = cursor)
    (header : MemoryModel.Header source.memory kind (relocated kind (old.base .header) start capacity) (BitVec.ofNat 64 slots.length))
    (occupied : MemoryModel.Occupied source kind (relocated kind (old.base .header) start capacity) slots)
    (frame : OldArrays source snapshot kind old)
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw") = some (TableCall.formals, Insert.body, .one))
    (enough : loopPrice kind cursor remaining ≤ source.clock) :
    ∃ paid memory target next, paid ≤ loopPrice kind cursor remaining ∧
      evaluateHOLFiniteState source Grow.loop = (none, target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - paid} ∧
      next.length = oldSlots.length ∧
      MemoryModel.Header memory kind (relocated kind (old.base .header) start capacity) (BitVec.ofNat 64 next.length) ∧
      MemoryModel.Occupied target kind (relocated kind (old.base .header) start capacity) next ∧ OldArrays target snapshot kind old ∧
      TableFootprint.Frame source.memory memory kind (relocated kind (old.base .header) start capacity) := by
  obtain ⟨paid, memory, target, next, bounded, run, fields, length, nextHeader, nextOccupied, arrays, footprint, _⟩ :=
    loop_execute_values snapshot kind old oldValid start capacity newValid earlier oldSlots oldRoom newRoom oldOccupied
      bits small power source domain little cursor remaining count locals slots length header occupied frame
      (fun _=>True) (fun _ _ _ _ _=>True.intro) (fun _ _ _ _ _=>True.intro) hashCode copyCode insertCode enough
  exact ⟨paid, memory, target, next, bounded, run, fields, length, nextHeader, nextOccupied, arrays, footprint⟩

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.loop_execute
