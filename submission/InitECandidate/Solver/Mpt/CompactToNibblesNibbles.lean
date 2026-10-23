import InitECandidate.Solver.Mpt.CompactToNibblesAfterNibbles
import InitECandidate.Solver.Mpt.CompactToNibblesNormal

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine original225 compact decode derives all stored path bytes'
nibble range from its real first-byte read and converter execution. The
input may be any mapped compact bytes; input-graph acyclicity and future
constructor success are not assumptions. -/
theorem body_nibbles (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer heap : BitVec 64) (length : Nat)
    (bounded : length≤1024) (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (inputArena : AllocatedBytes.Arena pointer length)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    1≤length ∧ AllocatedBytes.Arena heap (2*length) ∧ ∃ nibbles : Nat,∃ leaf : BitVec 64,
      nibbles≤2*length ∧ (leaf=0#64 ∨ leaf=1#64) ∧ value=output heap nibbles leaf ∧ KeyToNibbles.NibblePrefix target heap nibbles := by
  obtain ⟨positive,byte,restoreStack,inner,setup,allocation,endpoint,clock⟩:=normal_allocation_entry source target pointer length pointerCell lengthCell installed value normal
  let byteState:=bind source "c0" (BitVec.ofNat 64 byte.toNat)
  let current:=prepared byteState (BitVec.ofNat 64 byte.toNat)
  let request:=BitVec.ofNat 64 (2*length)
  have currentPointer : current.locals.lookup (ofString "p")=some (.val (.word pointer)):=
    (prepared_other byteState _ "p" (by decide) (by decide) (by decide)).trans ((bind_lookup_other source "c0" "p" _ (by decide)).trans pointerCell)
  have currentLength : current.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))):=
    (prepared_other byteState _ "n" (by decide) (by decide) (by decide)).trans ((bind_lookup_other source "c0" "n" _ (by decide)).trans lengthCell)
  have currentByte : current.locals.lookup (ofString "c0")=some (.val (.word (BitVec.ofNat 64 byte.toNat))):=
    (prepared_other byteState _ "c0" (by decide) (by decide) (by decide)).trans (bind_lookup_same _ _ _)
  obtain ⟨oddCell,leafCell,oddBinary,leafBinary⟩:=prepared_flags byteState (BitVec.ofNat 64 byte.toNat)
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
  let ready:=bind allocated "out" heap
  have readyPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)):=
    (bind_lookup_other allocated "out" "p" heap (by decide)).trans currentPointer
  have readyLength : ready.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))):=
    (bind_lookup_other allocated "out" "n" heap (by decide)).trans currentLength
  have readyOdd : ready.locals.lookup (ofString "odd")=some (.val (.word ((BitVec.ofNat 64 byte.toNat>>>4)&&&1#64))):=
    (bind_lookup_other allocated "out" "odd" heap (by decide)).trans oddCell
  have readyLeaf : ready.locals.lookup (ofString "is_leaf")=some (.val (.word ((BitVec.ofNat 64 byte.toNat>>>4>>>1)&&&1#64))):=
    (bind_lookup_other allocated "out" "is_leaf" heap (by decide)).trans leafCell
  have readyByte : ready.locals.lookup (ofString "c0")=some (.val (.word (BitVec.ofNat 64 byte.toNat))):=
    (bind_lookup_other allocated "out" "c0" heap (by decide)).trans currentByte
  obtain ⟨nibbles,extent,answer,nibblesValid⟩:=after_allocation_nibbles ready last pointer heap _ _ byte.toBitVec length positive bounded domain little freshArena inputArena
    readyPointer readyLength (bind_lookup_same _ _ _) readyOdd readyLeaf (by simpa only [UInt8.toNat_toBitVec] using readyByte) installed value afterRun
  have restored:=ProgramPrefix.restoration_frame setup inner
  have targetFields : emptyLocalsHOLFinite target=emptyLocalsHOLFinite last:=by
    rw [endpoint]
    change emptyLocalsHOLFinite (restoreStack inner)=emptyLocalsHOLFinite last
    exact restored.trans (by rw [innerEq]; rfl)
  have samePrefix:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>KeyToNibbles.NibblePrefix state heap nibbles) targetFields
  change KeyToNibbles.NibblePrefix target heap nibbles=KeyToNibbles.NibblePrefix last heap nibbles at samePrefix
  refine ⟨positive,freshArena,nibbles,_,extent,leafBinary,answer,?_⟩
  rw [samePrefix]
  exact nibblesValid

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.body_nibbles
