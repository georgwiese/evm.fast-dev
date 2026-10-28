import InitECandidate.Solver.WitnessRadix.AllocationNormal
import InitECandidate.Solver.WitnessRadix.AllocationCost
import InitECandidate.Solver.Input.ScopedCallClassified

namespace InitECandidate.Solver.Input.CurrentAlloc
open WitnessRadix.PersistentAlloc
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- All original allocation outcomes: either stop within the caller/trap
allowance or derive actual room and the exact normal allocation continuation.
No room or later successful allocation is assumed at entry. -/
theorem scoped_classified (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (pointer amount : BitVec 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (values amount))
    (installed : Input.OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (bounded : pointer.toNat≤2952790016) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "alloc") arguments continuation)=(result,target)) :
    (source.clock-target.clock≤2 ∧ ∀ value,result≠some (.returned value)) ∨
      1≤source.clock ∧ pointer.toNat+amount.toNat≤2952790016 ∧ ∃ inner,
        evaluateHOLFiniteState (bind (post {source with clock:=source.clock-1} pointer amount) name pointer) continuation=(result,inner) ∧
        target=restore source name inner := by
  obtain ⟨callee,called,amountCell⟩ := environment source.code.lookup amount (original_code source.code installed)
  have price := body_price source.code installed (callEntryStateHOLFinite source callee) rfl
  rcases Input.CallNormal.scoped_classified source target name .one (ofString "alloc") arguments _ body continuation callee .one 1 args called price result run with stopped|reached
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

/-- Compatibility projection retaining the original all-outcome price API. -/
theorem scoped_trace (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (pointer amount : BitVec 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (values amount))
    (installed : Input.OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (bounded : pointer.toNat≤2952790016) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "alloc") arguments continuation)=(result,target)) :
    source.clock-target.clock≤2 ∨
      1≤source.clock ∧ pointer.toNat+amount.toNat≤2952790016 ∧ ∃ inner,
        evaluateHOLFiniteState (bind (post {source with clock:=source.clock-1} pointer amount) name pointer) continuation=(result,inner) ∧
        target=restore source name inner := by
  rcases scoped_classified source target name arguments continuation pointer amount args installed heap bounded result run with stopped|reached
  · exact Or.inl stopped.1
  · exact Or.inr reached

end InitECandidate.Solver.Input.CurrentAlloc

#print axioms InitECandidate.Solver.Input.CurrentAlloc.scoped_trace

#print axioms InitECandidate.Solver.Input.CurrentAlloc.scoped_classified
