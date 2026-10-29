import InitECandidate.Solver.WitnessRadix.AllocationChecked
import InitECandidate.Solver.WitnessRadix.AllocationCost
import InitECandidate.Solver.Input.ScopedCallTrace

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

/-- A bounded nonwrapping actual request either stops within the allocator
price or derives persistent room and the exact reached caller. The initial
heap need not already satisfy the persistent cap; a true normal allocation
supplies its checked second guard. No future allocation success is assumed. -/
theorem scoped_trace_no_wrap (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (pointer amount : BitVec 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (values amount))
    (installed : Input.OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (noWrap : pointer.toNat+amount.toNat+7<2^64) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "alloc") arguments continuation)=(result,target)) :
    source.clock-target.clock≤2 ∨
      1≤source.clock ∧ pointer.toNat+amount.toNat≤2952790016 ∧ ∃ inner,
        evaluateHOLFiniteState (bind (post {source with clock:=source.clock-1} pointer amount) name pointer) continuation=(result,inner) ∧
        target=restore source name inner := by
  obtain ⟨callee,called,amountCell⟩:=environment source.code.lookup amount (original_code source.code installed)
  have price:=body_price source.code installed (callEntryStateHOLFinite source callee) rfl
  rcases Input.CallNormal.scoped_trace source target name .one (ofString "alloc") arguments _ body continuation callee .one 1 args called price result run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨parsed,answer,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩:=reached
    obtain ⟨valueEq,room,frame⟩:=post_of_normal_no_wrap (callEntryStateHOLFinite source callee) parsed pointer amount amountCell heap noWrap
      (Input.Trap.original_code source.code installed) answer bodyRun
    rw [valueEq] at continued
    have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
    change {parsed with locals:=source.locals}=post {source with clock:=source.clock-1} pointer amount at callerFrame
    change evaluateHOLFiniteState (bind {parsed with locals:=source.locals} name pointer) continuation=(result,inner) at continued
    rw [callerFrame] at continued
    exact Or.inr ⟨funded,room,inner,continued,endpoint⟩

end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.scoped_trace_no_wrap
