import InitECandidate.Solver.Mpt.CompactToNibblesNormalEntry
import InitECandidate.Solver.Mpt.CompactToNibblesFlags
import InitECandidate.Solver.Mpt.CompactToNibblesAfterNormal
import InitECandidate.Solver.WitnessRadix.AllocationCallNormal
import InitECandidate.Solver.WitnessRadix.AllocationCost

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete normal original225 derives its own nonempty input, allocation
room, genuine output pointer/length/leaf flag, exact heap/metadata update and
preservation of every older memory region. The entry heap is the real current
cursor; no successful future allocation is assumed. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer heap : BitVec 64) (length : Nat)
    (bounded : length≤1024)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    1≤length ∧ AllocatedBytes.Arena heap (2*length) ∧ ∃ nibbles : Nat,∃ leaf : BitVec 64,
      nibbles≤2*length ∧ (leaf=0#64 ∨ leaf=1#64) ∧ value=output heap nibbles leaf ∧
      KeyToNibbles.writeMetadata target=KeyToNibbles.writeMetadata (PersistentAlloc.post source heap (BitVec.ofNat 64 (2*length))) ∧
      ∀ query : BitVec 64,query.toNat<heap.toNat ∨ heap.toNat+2*length≤query.toNat→target.memory query=source.memory query := by
  obtain ⟨positive,byte,restoreStack,inner,setup,allocation,endpoint,clock⟩:=normal_allocation_entry source target pointer length pointerCell lengthCell installed value normal
  let byteState:=QueryBranch.bind source "c0" (BitVec.ofNat 64 byte.toNat)
  let current:=prepared byteState (BitVec.ofNat 64 byte.toNat)
  let request:=BitVec.ofNat 64 (2*length)
  have currentPointer : current.locals.lookup (ofString "p")=some (.val (.word pointer)):=
    (prepared_other byteState _ "p" (by decide) (by decide) (by decide)).trans ((bind_lookup_other source "c0" "p" _ (by decide)).trans pointerCell)
  have currentLength : current.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))):=
    (prepared_other byteState _ "n" (by decide) (by decide) (by decide)).trans ((bind_lookup_other source "c0" "n" _ (by decide)).trans lengthCell)
  have flags:=prepared_flags byteState (BitVec.ofNat 64 byte.toNat)
  obtain ⟨oddCell,leafCell,oddBinary,leafBinary⟩:=flags
  have args : evalListHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) [amount]=some (PersistentAlloc.values request):=by
    simp [amount,PersistentAlloc.values,request,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,currentLength,panOpHOL,valueIsWord,valueWord,BitVec.ofNat_mul]
  have amountNumber : request.toNat=2*length:=by
    change (BitVec.ofNat 64 (2*length)).toNat=2*length
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [allocation_shape] at allocation
  obtain ⟨room,funded,last,afterRun,innerEq⟩:=PersistentAlloc.call_normal current inner "out" [amount] afterAllocation heap request args
    (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed) heapCell (by have upper:=heapArena.upper; omega) value allocation
  rw [amountNumber] at room
  have freshArena : AllocatedBytes.Arena heap (2*length):=⟨heapArena.lower,room⟩
  let allocated:=PersistentAlloc.post {current with clock:=current.clock-1} heap request
  let ready:=QueryBranch.bind allocated "out" heap
  have readyPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)):=
    (bind_lookup_other allocated "out" "p" heap (by decide)).trans currentPointer
  have readyLength : ready.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))):=
    (bind_lookup_other allocated "out" "n" heap (by decide)).trans currentLength
  have readyOdd : ready.locals.lookup (ofString "odd")=some (.val (.word ((BitVec.ofNat 64 byte.toNat>>>4)&&&1#64))):=
    (bind_lookup_other allocated "out" "odd" heap (by decide)).trans oddCell
  have readyLeaf : ready.locals.lookup (ofString "is_leaf")=some (.val (.word ((BitVec.ofNat 64 byte.toNat>>>4>>>1)&&&1#64))):=
    (bind_lookup_other allocated "out" "is_leaf" heap (by decide)).trans leafCell
  obtain ⟨nibbles,extent,valueEq,afterFields,memory⟩:=after_allocation_normal ready last pointer heap _ _ length positive freshArena aligned readyPointer readyLength
    (bind_lookup_same _ _ _) readyOdd readyLeaf installed value afterRun
  have restored:=ProgramPrefix.restoration_frame setup inner
  have restoredFields:=congrArg KeyToNibbles.writeMetadata restored
  change KeyToNibbles.writeMetadata (restoreStack inner)=KeyToNibbles.writeMetadata inner at restoredFields
  have restoredMemory:=congrArg PanSemStateFiniteExact.memory restored
  change (restoreStack inner).memory=inner.memory at restoredMemory
  have finalFields : KeyToNibbles.writeMetadata target=KeyToNibbles.writeMetadata last:=by
    rw [endpoint]
    change KeyToNibbles.writeMetadata (restoreStack inner)=KeyToNibbles.writeMetadata last
    rw [restoredFields,innerEq]
    rfl
  have finalMemory : target.memory=last.memory:=by
    rw [endpoint]
    change (restoreStack inner).memory=last.memory
    rw [restoredMemory,innerEq]
    rfl
  refine ⟨positive,freshArena,nibbles,_,extent,leafBinary,valueEq,finalFields.trans afterFields,?_⟩
  intro query outside
  rw [finalMemory]
  exact memory query outside

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.body_normal
