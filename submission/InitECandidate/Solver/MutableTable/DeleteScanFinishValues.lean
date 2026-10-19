import InitECandidate.Solver.MutableTable.DeleteFinishExecution
import InitECandidate.Solver.MutableTable.DeleteScanModelValues
import InitECandidate.Solver.MutableTable.DeleteFinishValues

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The entire original present-deletion scan and final mutation. The
physical table supplies scan progress; the actual final stores establish a
new physical table with one fewer entry. -/
theorem scan_finish_values (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < plan.capacity) (occupied : MemoryModel.Occupied source kind plan slots) (deleted : Fin slots.length)
    (bits : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (locals : ScanLocals source kind plan (slots.get deleted) (slots.get deleted))
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (deletedLocal : source.locals.lookup (ofString "deleted_pos") = some (.val (.word (BitVec.ofNat 64 deleted.val))))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (property : BitVec 64 → Prop) (values : Get.OccupiedValuesHave source (cell plan .values 0) (BitVec.ofNat 64 plan.capacity) slots property)
    (enough : scanPrice kind * (slots.length - 1) + 1 ≤ source.clock) :
    ∃ paid memory target next, paid ≤ scanPrice kind * (slots.length - 1) + 1 ∧
      evaluateHOLFiniteState source (.seq loop afterLoop) = (some (.returned (.val (.word 1#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - paid} ∧
      next.length = slots.length - 1 ∧ MemoryModel.Header memory kind plan (BitVec.ofNat 64 next.length) ∧
      MemoryModel.Occupied target kind plan next ∧ TableFootprint.Frame source.memory memory kind plan ∧
      Get.OccupiedValuesHave target (cell plan .values 0) (BitVec.ofNat 64 plan.capacity) next property := by
  obtain ⟨stop, paid, scanMemory, scanned, entries, hole, stopPositive, stopBound, bounded, scanRun, scanFrame, scanLocals, pending, scanHeader, stable, other, scanFootprint, scanValues⟩ :=
    scan_from_occupied_values source kind plan valid domain little slots room occupied deleted bits small power locals header hashCode copyCode property values enough
  have memoryEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) scanFrame
  have domainEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) scanFrame
  have endianEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) scanFrame
  have clockEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.clock) scanFrame
  change scanned.memory = scanMemory at memoryEq
  change scanned.memaddrs = source.memaddrs at domainEq
  change scanned.be = source.be at endianEq
  change scanned.clock = source.clock - paid at clockEq
  have actualHeader : MemoryModel.Header scanned.memory kind plan (BitVec.ofNat 64 slots.length) := by rw [memoryEq]; exact scanHeader
  obtain ⟨target, finishRun, finishFrame, finishHeader, finishOccupied⟩ := Finish.execute scanned kind plan valid (domainEq.trans domain) (endianEq.trans little)
    slots.length deleted entries hole _ pending scanLocals ((other "t" (by decide) (by decide)).trans tableLocal)
    ((other "deleted_pos" (by decide) (by decide)).trans deletedLocal) actualHeader
  let finalMemory := Finish.memory scanned.memory plan deleted entries hole
  have replaceMemory := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with memory := finalMemory}) scanFrame
  change emptyLocalsHOLFinite {scanned with memory := finalMemory} = emptyLocalsHOLFinite {source with memory := finalMemory, clock := source.clock - paid} at replaceMemory
  have finishedFrame : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := finalMemory, clock := source.clock - paid} := finishFrame.trans replaceMemory
  have finalMemoryEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) finishedFrame
  change target.memory = finalMemory at finalMemoryEq
  refine ⟨paid, finalMemory, target, finalSlots entries deleted, bounded, ?_, finishedFrame, final_length _ _, ?_, finishOccupied, ?_,?_⟩
  · rw [StateSteps.next_sequence source scanned loop afterLoop scanRun (by omega), finishRun]
  · rw [final_length, ← finalMemoryEq]
    exact finishHeader
  · apply TableFootprint.Frame.trans source.memory scanned.memory finalMemory kind plan
    · rw [memoryEq]
      exact scanFootprint
    · exact Finish.footprint scanned.memory kind plan valid slots.length deleted entries hole pending.room pending.holeInside pending.inside

  · have actualValues : PendingValues scanned plan deleted entries property :=
      scanValues.of_memory {source with memory:=scanMemory} scanned plan deleted entries property memoryEq
    have finishedValues := actualValues.finished scanned kind plan valid slots.length deleted entries hole pending property
    exact finishedValues.of_agreement _ target _ _ _ _ (by intro slot inside member; rw [finalMemoryEq])

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.scan_finish_values
