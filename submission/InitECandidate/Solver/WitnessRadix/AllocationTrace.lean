import InitECandidate.Solver.WitnessRadix.AllocationCallNormal
import InitECandidate.Solver.WitnessRadix.AllocationCost
import InitECandidate.Solver.Input.ScopedCallTrace

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

/-- All original allocation outcomes: either stop within the caller/trap
allowance or derive actual room and the exact normal allocation continuation.
No room or later successful allocation is assumed at entry. -/
theorem scoped_trace (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (pointer amount : BitVec 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (values amount))
    (installed : Input.OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (bounded : pointer.toNat≤33806089496) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "alloc") arguments continuation)=(result,target)) :
    source.clock-target.clock≤2 ∨
      1≤source.clock ∧ pointer.toNat+amount.toNat≤33806089496 ∧ ∃ inner,
        evaluateHOLFiniteState (bind (post {source with clock:=source.clock-1} pointer amount) name pointer) continuation=(result,inner) ∧
        target=restore source name inner := by
  obtain ⟨callee,called,amountCell⟩ := environment source.code.lookup amount (original_code source.code installed)
  have price := body_price source.code installed (callEntryStateHOLFinite source callee) rfl
  rcases Input.CallNormal.scoped_trace source target name .one (ofString "alloc") arguments _ body continuation callee .one 1 args called price result run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨parsed,answer,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩ := reached
    obtain ⟨valueEq,room,frame⟩ := post_of_normal (callEntryStateHOLFinite source callee) parsed pointer amount amountCell heap bounded
      (Input.Trap.original_code source.code installed) answer bodyRun
    rw [valueEq] at continued
    have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
    change {parsed with locals:=source.locals}=post {source with clock:=source.clock-1} pointer amount at callerFrame
    change evaluateHOLFiniteState (bind {parsed with locals:=source.locals} name pointer) continuation=(result,inner) at continued
    rw [callerFrame] at continued
    exact Or.inr ⟨funded,room,inner,continued,endpoint⟩

end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.scoped_trace
