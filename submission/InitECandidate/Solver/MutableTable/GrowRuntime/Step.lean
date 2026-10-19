import InitECandidate.Solver.MutableTable.GrowRuntime.StepValues
import InitECandidate.Solver.MutableTable.GrowRuntime.Frames
import InitECandidate.Solver.WitnessRadix.Bindings
import InitECandidate.Solver.MutableTable.TableFootprint

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- One complete actual rehash body: old order read, raw-insertion ABI,
index increment and restoration of the scoped slot local. No insertion
execution or post-state representation is assumed. -/
theorem step_execute (source snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start capacity : Nat) (newValid : Valid kind (relocated kind (old.base .header) start capacity))
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (oldSlots : List Nat) (oldRoom : oldSlots.length ≤ old.capacity) (oldOccupied : MemoryModel.Occupied snapshot kind old oldSlots)
    (frame : OldArrays source snapshot kind old) (cursor : Fin oldSlots.length)
    (locals : LoopLocals source kind old oldSlots.length cursor.val)
    (slots : List Nat) (room : slots.length < capacity)
    (header : MemoryModel.Header source.memory kind (relocated kind (old.base .header) start capacity) (BitVec.ofNat 64 slots.length))
    (occupied : MemoryModel.Occupied source kind (relocated kind (old.base .header) start capacity) slots)
    (bits : Nat) (small : bits < 64) (power : capacity = 2 ^ bits)
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw") = some (TableCall.formals, Insert.body, .one))
    (enough : slots.length + KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 2 ≤ source.clock) :
    ∃ paid memory nextSlot, paid ≤ slots.length + KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 2 ∧
      evaluateHOLFiniteState source Grow.loopBody =
        (none, WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - paid} "k" (BitVec.ofNat 64 (cursor.val + 1))) ∧
      MemoryModel.Header memory kind (relocated kind (old.base .header) start capacity) (BitVec.ofNat 64 (slots ++ [nextSlot]).length) ∧
      MemoryModel.Occupied {source with memory := memory, clock := source.clock - paid} kind (relocated kind (old.base .header) start capacity) (slots ++ [nextSlot]) ∧
      OldArrays {source with memory := memory, clock := source.clock - paid} snapshot kind old ∧
      TableFootprint.Frame source.memory memory kind (relocated kind (old.base .header) start capacity) := by
  obtain ⟨paid, memory, nextSlot, bounded, run, nextHeader, nextOccupied, arrays, footprint, _⟩ :=
    step_execute_values source snapshot kind old oldValid start capacity newValid earlier domain little oldSlots oldRoom oldOccupied
      frame cursor locals slots room header occupied (fun _=>True) (fun _ _ _ _ _=>True.intro) (fun _ _ _ _ _=>True.intro)
      bits small power hashCode copyCode insertCode enough
  exact ⟨paid, memory, nextSlot, bounded, run, nextHeader, nextOccupied, arrays, footprint⟩

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.step_execute
