import InitECandidate.Solver.Mpt.NibblesConcatProgram
import InitECandidate.Solver.WitnessRadix.AllocationCallNormal
import InitECandidate.Solver.WitnessRadix.AllocationCost
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.Mpt.NibblesConcat
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap al bl : BitVec 64):=
  QueryBranch.bind (PersistentAlloc.post {source with clock:=source.clock-1} heap (al+bl)) "out" heap

theorem allocated_lookup_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap al bl : BitVec 64) (name : String)
    (different : ofString "out"≠ofString name) :
    (allocated source heap al bl).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  bind_lookup_other (PersistentAlloc.post {source with clock:=source.clock-1} heap (al+bl)) "out" name heap different

/-- A real normal concatenation derives room for its actual unwrapped sum
and the aligned next heap from the original allocator's guards. -/
theorem allocation_entry (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap a al b bl : BitVec 64)
    (sourceA : AllocatedBytes.Arena a al.toNat) (sourceB : AllocatedBytes.Arena b bl.toNat)
    (leftLengthCell : source.locals.lookup (ofString "al")=some (.val (.word al)))
    (rightLengthCell : source.locals.lookup (ofString "bl")=some (.val (.word bl)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    (al+bl).toNat=al.toNat+bl.toNat ∧ AllocatedBytes.Arena heap (al.toNat+bl.toNat) ∧
      AllocatedBytes.Arena (PersistentAlloc.rounded heap (al+bl)) 0 ∧ (PersistentAlloc.rounded heap (al+bl)).toNat%8=0 ∧
      heap.toNat+al.toNat+bl.toNat≤(PersistentAlloc.rounded heap (al+bl)).toNat ∧
      ∃ inner,evaluateHOLFiniteState (allocated source heap al bl) afterAllocation=(some (.returned value),inner) ∧ target=restore source "out" inner := by
  have amount : (al+bl).toNat=al.toNat+bl.toNat:=BitVec.toNat_add_of_lt (by have left:=sourceA.upper; have right:=sourceB.upper; omega)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) allocationArguments=some (PersistentAlloc.values (al+bl)):=by
    simp [allocationArguments,amountExpression,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,leftLengthCell,rightLengthCell,
      valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [body_shapes.1] at normal
  obtain ⟨room,_funded,inner,continued,endpoint⟩:=PersistentAlloc.call_normal source target "out" allocationArguments afterAllocation heap (al+bl) args
    (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed) heapCell (by have upper:=frontier.upper; omega) value normal
  have guards:=PersistentAlloc.guards heap (al+bl) room
  have destination : AllocatedBytes.Arena heap (al.toNat+bl.toNat):=⟨frontier.lower,by rw [amount] at room; exact room⟩
  have nextArena : AllocatedBytes.Arena (PersistentAlloc.rounded heap (al+bl)) 0:=⟨by have lower:=frontier.lower; have grows:=guards.2.2.1; omega,by have upper:=guards.2.2.2.1; omega⟩
  have grows : heap.toNat+al.toNat+bl.toNat≤(PersistentAlloc.rounded heap (al+bl)).toNat:=by have before:=guards.2.2.1; rw [amount] at before; omega
  exact ⟨amount,destination,nextArena,guards.2.2.2.2,grows,inner,continued,endpoint⟩

end InitECandidate.Solver.Mpt.NibblesConcat

#print axioms InitECandidate.Solver.Mpt.NibblesConcat.allocated_lookup_other
#print axioms InitECandidate.Solver.Mpt.NibblesConcat.allocation_entry
