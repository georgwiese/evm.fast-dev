import InitECandidate.Solver.Headers.DecodeCountReturned
import InitECandidate.Solver.WitnessRadix.AllocationCallNormal
import InitECandidate.Solver.Headers.CurrentDecode.Allocation

namespace InitECandidate.Solver.Headers.CurrentDecode
open Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual successful original count/allocation prefix derives room and the exact field continuation. -/
theorem allocation_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (array count pointer : BitVec 64)
    (listCell : source.locals.lookup (ofString "lst")=some (Rlp.Slices.result array count))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (bounded : pointer.toNat≤2952790016) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterList=(some (.returned value),post)) :
    (count=21#64 ∨ count=23#64) ∧ 1≤source.clock ∧ pointer.toNat+248≤2952790016 ∧ ∃ inner,
      evaluateHOLFiniteState (allocationEntry source array count pointer) afterAllocation=(some (.returned value),inner) ∧
      post=restoreDeclared source array count (restore (counted (declared source array count) count) "h" inner) := by
  obtain ⟨countValid,middle,remaining,endpoint⟩ := list_count_returned source post array count listCell value run
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
  obtain ⟨room,funded,inner,continued,restored⟩ := PersistentAlloc.call_normal current middle "h" [.const 248#64] afterAllocation pointer 248#64 args
    (PersistentAlloc.original_code current.code currentInstalled) (Input.Trap.original_code current.code currentInstalled) currentHeap bounded value remaining
  have enough : 1≤source.clock := by
    change 1≤(counted (declared source array count) count).clock at funded
    rwa [clockEq] at funded
  exact ⟨countValid,enough,room,inner,continued,by rw [endpoint,restored]⟩

end InitECandidate.Solver.Headers.CurrentDecode

#print axioms InitECandidate.Solver.Headers.CurrentDecode.allocation_returned
