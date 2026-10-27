import InitECandidate.Solver.WitnessRadix.AllocationCall
import InitECandidate.Solver.Input.VarList.AllocatedTail

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def allocationEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input) :=
  bind (WitnessRadix.PersistentAlloc.post {source with clock:=source.clock-1} plan.array (BitVec.ofNat 64 (16*plan.count))) "arr" plan.array

/-- Actual record-array allocator call and the entire allocated tail. The real
heap global advances, caller arr scope restores, records initialize, and every
outcome preserves copied bytes and all memory outside this allocation.
Semantic allocator room is separate from ordinary backing geometry. -/
theorem allocation_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (first total : BitVec 64) (heap : Blob.HeapInput source input plan.inputPointer) (domain : source.memaddrs=InitE.ordinaryDomain)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (plan.inputPointer+BitVec.ofNat 64 plan.start))))
    (f : source.locals.lookup (ofString "first")=some (.val (.word first)))
    (n : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (c : source.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 plan.count))))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word plan.array)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (room : plan.array.toNat + 16 * plan.count ≤ 2952790016)
    (enough : plan.count+2≤source.clock) :
    ∃ result target paid,
      evaluateHOLFiniteState source allocationCall=(result,target) ∧ paid≤plan.count+2 ∧ target.clock=source.clock-paid ∧
      WitnessRadix.BackingLayout.control target=WitnessRadix.BackingLayout.control
        (WitnessRadix.PersistentAlloc.post source plan.array (BitVec.ofNat 64 (16*plan.count))) ∧
      Blob.HeapInput target input plan.inputPointer ∧ ArrayFrame source target input plan ∧
      ((result=some (.returned (pairValue plan.array plan.count)) ∧ paid=plan.count+1 ∧ Complete target input plan total ∧
          ∀ position,position<plan.count→Offsets.ValidAt first total (currentWord input plan.start) position) ∨
        result=some (.exception (ofString "SszErr") (.val (.word 23#64)))) := by
  classical
  let amount:=BitVec.ofNat 64 (16*plan.count)
  have amountNat : amount.toNat=16*plan.count := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have h:=plan.arrayRoom; omega)]
  have read : eval source allocationExpression=some (.val (.word amount)) := by
    have actual:=allocation_read source (BitVec.ofNat 64 plan.count) c
    simpa only [←BitVec.ofNat_mul,Nat.mul_comm plan.count 16] using actual
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [allocationExpression]=
      some (WitnessRadix.PersistentAlloc.values amount) := by
    simp only [eval] at read
    simp [evalListHOLFinite,evalListHOLExact,read,WitnessRadix.PersistentAlloc.values]
  let entry:=allocationEntry source input plan
  have called : evaluateHOLFiniteState source allocationCall=
      (let output:=evaluateHOLFiniteState entry allocatedTail; (output.1,restore source "arr" output.2)) :=
    WitnessRadix.PersistentAlloc.call_execute source "arr" [allocationExpression] allocatedTail plan.array amount args allocCode heapGlobal
      (by rw [amountNat]; exact room) (by omega)
  have entryHeap : Blob.HeapInput entry input plan.inputPointer := Blob.HeapInput.of_fields source entry input plan.inputPointer rfl rfl rfl heap
  have ep : entry.locals.lookup (ofString "p")=some (.val (.word (plan.inputPointer+BitVec.ofNat 64 plan.start))) :=
    (bind_lookup_other (WitnessRadix.PersistentAlloc.post {source with clock:=source.clock-1} plan.array amount) "arr" "p" plan.array (by decide)).trans p
  have ef : entry.locals.lookup (ofString "first")=some (.val (.word (first))) :=
    (bind_lookup_other (WitnessRadix.PersistentAlloc.post {source with clock:=source.clock-1} plan.array amount) "arr" "first" plan.array (by decide)).trans f
  have en : entry.locals.lookup (ofString "len")=some (.val (.word (total))) :=
    (bind_lookup_other (WitnessRadix.PersistentAlloc.post {source with clock:=source.clock-1} plan.array amount) "arr" "len" plan.array (by decide)).trans n
  have ec : entry.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 plan.count))) :=
    (bind_lookup_other (WitnessRadix.PersistentAlloc.post {source with clock:=source.clock-1} plan.array amount) "arr" "count" plan.array (by decide)).trans c
  obtain ⟨result,target,paid,run,bound,clock,control,heapAfter,arrayFrame,outcome⟩:=allocated_execute entry input plan first total entryHeap domain
    (bind_lookup_same _ _ _) ep ef en ec failCode exceptionShape (by change plan.count+1≤source.clock-1; omega)
  rw [run] at called
  let final:=restore source "arr" target
  have finalHeap : Blob.HeapInput final input plan.inputPointer := Blob.HeapInput.restore source target input plan.inputPointer "arr" heapAfter
  have finalFrame : ArrayFrame source final input plan := by intro query outside; exact arrayFrame query outside
  have finalControl : WitnessRadix.BackingLayout.control final=WitnessRadix.BackingLayout.control (WitnessRadix.PersistentAlloc.post source plan.array amount) := by
    exact control
  have finalClock : final.clock=source.clock-(paid+1) := by
    change target.clock=source.clock-(paid+1)
    change target.clock=source.clock-1-paid at clock
    omega
  refine ⟨result,final,paid+1,called,by omega,finalClock,finalControl,finalHeap,finalFrame,?_⟩
  rcases outcome with normal|fault
  · exact Or.inl ⟨normal.1,by omega,normal.2.2.1,normal.2.2.2⟩
  · exact Or.inr fault

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.allocation_execute
