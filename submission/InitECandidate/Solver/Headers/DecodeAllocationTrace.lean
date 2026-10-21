import InitECandidate.Solver.Headers.DecodeCountEntry
import InitECandidate.Solver.WitnessRadix.AllocationTrace

namespace InitECandidate.Solver.Headers.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def allocationEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array count pointer : BitVec 64) :=
  let current:=counted (declared source array count) count
  bind (PersistentAlloc.post {current with clock:=current.clock-1} pointer 248#64) "h" pointer

/-- From the actual RLP slice pair, the unchanged header scope either stops
within two source ticks or reaches field extraction after its real count
check and allocation. Both early failure and exact lexical restoration are
covered; allocation room is derived from its genuine normal execution. -/
theorem allocation_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (array count pointer : BitVec 64)
    (listCell : source.locals.lookup (ofString "lst")=some (Rlp.Slices.result array count))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (bounded : pointer.toNat≤33806089496) (installed : Input.OriginalCode.Installed source.code)
    (shape : source.eshapes.lookup (ofString "HdrErr")=some .one)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterList=(result,post)) :
    source.clock-post.clock≤2 ∨ (count=21#64 ∨ count=23#64) ∧ 1≤source.clock ∧ pointer.toNat+248≤33806089496 ∧ ∃ inner,
      evaluateHOLFiniteState (allocationEntry source array count pointer) afterAllocation=(result,inner) ∧
      post=restoreDeclared source array count (restore (counted (declared source array count) count) "h" inner) := by
  rcases list_count_trace source post array count listCell shape result run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨countValid,middle,remaining,endpoint⟩ := reached
    let current:=counted (declared source array count) count
    have context := (counted_frame source array count).1
    have clockEq := (counted_frame source array count).2
    have globalsEq := congrArg PanSemStateFiniteExact.globals context
    change (counted (declared source array count) count).globals=source.globals at globalsEq
    have codeEq := congrArg PanSemStateFiniteExact.code context
    change (counted (declared source array count) count).code=source.code at codeEq
    have currentInstalled : Input.OriginalCode.Installed current.code := by
      change Input.OriginalCode.Installed (counted (declared source array count) count).code
      rw [codeEq]
      exact installed
    have currentHeap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)) := by
      change (counted (declared source array count) count).globals.lookup _=_
      rw [globalsEq]
      exact heap
    rw [allocation_shape] at remaining
    have args : evalListHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) [.const 248#64]=some (PersistentAlloc.values 248#64) := rfl
    rcases PersistentAlloc.scoped_trace current middle "h" [.const 248#64] afterAllocation pointer 248#64 args currentInstalled currentHeap bounded result remaining with stopped|allocated
    · have finalClock : post.clock=middle.clock := by rw [endpoint]; rfl
      change (counted (declared source array count) count).clock-middle.clock≤2 at stopped
      rw [clockEq] at stopped
      exact Or.inl (by omega)
    · obtain ⟨funded,room,inner,continued,restored⟩ := allocated
      have enough : 1≤source.clock := by
        change 1≤(counted (declared source array count) count).clock at funded
        rwa [clockEq] at funded
      exact Or.inr ⟨countValid,enough,room,inner,continued,by rw [endpoint,restored]⟩

/-- Actual current bindings, heap cursor and unchanged input memory at the
original header field pipeline, including the real21/23 current-header bit. -/
theorem allocation_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array count pointer : BitVec 64) :
    (allocationEntry source array count pointer).locals.lookup (ofString "h")=some (.val (.word pointer)) ∧
    (allocationEntry source array count pointer).locals.lookup (ofString "arr")=some (.val (.word array)) ∧
    (allocationEntry source array count pointer).locals.lookup (ofString "n")=some (.val (.word count)) ∧
    (allocationEntry source array count pointer).locals.lookup (ofString "is_current")=some (.val (.word (if count=23#64 then 1#64 else 0#64))) ∧
    (allocationEntry source array count pointer).globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded pointer 248#64))) ∧
    (allocationEntry source array count pointer).memory=source.memory ∧
    (allocationEntry source array count pointer).clock=source.clock-1 := by
  have cells:=counted_cells source array count
  have context:=(counted_frame source array count).1
  have memory:=congrArg PanSemStateFiniteExact.memory context
  have clock:=(counted_frame source array count).2
  refine ⟨bind_lookup_same _ _ _,?_,?_,?_,?_,?_,?_⟩
  · exact (bind_lookup_other _ "h" "arr" _ (by decide)).trans cells.1
  · exact (bind_lookup_other _ "h" "n" _ (by decide)).trans cells.2.1
  · exact (bind_lookup_other _ "h" "is_current" _ (by decide)).trans cells.2.2
  · change ((counted (declared source array count) count).globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded pointer 248#64)))).lookup (ofString "heap_ptr")=_
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  · exact memory
  · exact congrArg (fun value=>value-1) clock

end InitECandidate.Solver.Headers.Decode

#print axioms InitECandidate.Solver.Headers.Decode.allocation_trace
#print axioms InitECandidate.Solver.Headers.Decode.allocation_fields
