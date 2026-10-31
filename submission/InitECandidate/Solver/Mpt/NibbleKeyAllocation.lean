import InitECandidate.Solver.Mpt.NibbleKeyProgram
import InitECandidate.Solver.WitnessRadix.AllocationNoWrapTrace

namespace InitECandidate.Solver.Mpt.NibbleKey
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (length : Nat):=
  bind (PersistentAlloc.post {source with clock:=source.clock-1} heap (BitVec.ofNat 64 (2*length))) "nb2" heap

/-- The actual normal unsecured branch derives its fresh two-times-length
allocation and the genuine converter continuation, including final scope restoration. -/
theorem normal_allocation_room (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (m heap : BitVec 64) (length : Nat)
    (small : length≤32) (installed : Input.OriginalCode.Installed source.code)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 length))))
    (mapped : source.memaddrs (m+8#64)) (cell : source.memory (m+8#64)=.word 0#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    heap.toNat+2*length≤2952790016 ∧ ∃ inner,
      evaluateHOLFiniteState (allocated source heap length) tail=(some (.returned value),inner) ∧
      target=restore source "nb2" inner := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [amount]=
      some (PersistentAlloc.values (BitVec.ofNat 64 (2*length))):=by
    simp [amount,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,lengthCell,panOpHOL,
      valueIsWord,valueWord,BitVec.ofNat_mul]
  have number : (BitVec.ofNat 64 (2*length)).toNat=2*length:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [unsecured_run source m mCell mapped cell,unsecured_shape] at normal
  obtain ⟨room,funded,inner,continued,endpoint⟩:=PersistentAlloc.call_normal_no_wrap source target "nb2" [amount] tail heap
    (BitVec.ofNat 64 (2*length)) args (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed)
    heapCell (by rw [number]; have upper:=frontier.upper; omega) value normal
  rw [number] at room
  exact ⟨room,inner,continued,endpoint⟩

theorem normal_allocation (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (m heap : BitVec 64) (length : Nat)
    (small : length≤32) (installed : Input.OriginalCode.Installed source.code)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 length))))
    (mapped : source.memaddrs (m+8#64)) (cell : source.memory (m+8#64)=.word 0#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    AllocatedBytes.Arena heap (2*length) ∧ ∃ inner,
      evaluateHOLFiniteState (allocated source heap length) tail=(some (.returned value),inner) ∧
      target=restore source "nb2" inner := by
  obtain ⟨room,inner,continued,endpoint⟩:=normal_allocation_room source target m heap length small installed
    mCell lengthCell mapped cell heapCell frontier value normal
  exact ⟨⟨frontier.lower,by omega⟩,inner,continued,endpoint⟩

theorem allocated_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key heap : BitVec 64) (length : Nat)
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 length)))) :
    (allocated source heap length).locals.lookup (ofString "key")=some (.val (.word key)) ∧
      (allocated source heap length).locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 length))) ∧
      (allocated source heap length).locals.lookup (ofString "nb2")=some (.val (.word heap)) :=
  ⟨(bind_lookup_other _ "nb2" "key" heap (by decide)).trans keyCell,
    (bind_lookup_other _ "nb2" "klen" heap (by decide)).trans lengthCell,bind_lookup_same _ _ _⟩

theorem allocated_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (length : Nat) :
    (allocated source heap length).clock=source.clock-1 := by
  simp only [allocated,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite]

end InitECandidate.Solver.Mpt.NibbleKey

#print axioms InitECandidate.Solver.Mpt.NibbleKey.normal_allocation
#print axioms InitECandidate.Solver.Mpt.NibbleKey.allocated_locals
#print axioms InitECandidate.Solver.Mpt.NibbleKey.allocated_clock

#print axioms InitECandidate.Solver.Mpt.NibbleKey.normal_allocation_room
