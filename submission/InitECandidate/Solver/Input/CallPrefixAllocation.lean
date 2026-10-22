import InitECandidate.Solver.Input.CallPrefixExecution
import InitECandidate.Solver.WitnessRadix.AllocationNormal
import InitECandidate.Solver.WitnessRadix.AllocationEnvironment
import InitECandidate.Solver.WitnessRadix.AllocationCost

namespace InitECandidate.Solver.Input.CallPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Invert an actual reached original allocation action. Its successful
return derives request room and the exact saved-caller update, without a
future allocation-success or mapped-output premise. -/
theorem Reaches.alloc_target {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (name : MlS) (arguments : List (ExpHOL 64)) (pointer amount : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (argsRead : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (PersistentAlloc.values amount))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (bounded : pointer.toNat≤33806089496)
    (reached : Reaches source (.scoped name .one (ofString "alloc") arguments) target) :
    pointer.toNat+amount.toNat≤33806089496 ∧
      target=setVarHOLFinite name (.val (.word pointer)) (PersistentAlloc.post {source with clock:=source.clock-1} pointer amount) := by
  cases reached with
  | «scoped» _ _ _ _ actualValues actualBody callee returnShape returned childTarget args called funded run checked=>
    have sameValues : actualValues=PersistentAlloc.values amount:=Option.some.inj (args.symm.trans argsRead)
    subst actualValues
    obtain ⟨expected,expectedCall,amountCell⟩:=PersistentAlloc.environment source.code.lookup amount (PersistentAlloc.original_code source.code installed)
    have same:=Option.some.inj (called.symm.trans expectedCall)
    have bodyEq:=congrArg Prod.fst same
    have calleeEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
    have shapeEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.2) same
    change actualBody=PersistentAlloc.body at bodyEq
    change callee=expected at calleeEq
    change returnShape=.one at shapeEq
    subst actualBody
    subst callee
    subst returnShape
    obtain ⟨valueEq,room,frame⟩:=PersistentAlloc.post_of_normal (callEntryStateHOLFinite source expected) childTarget pointer amount
      amountCell heapCell bounded (Trap.original_code source.code installed) returned run
    refine ⟨room,?_⟩
    rw [valueEq]
    have updated:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>
      setVarHOLFinite name (.val (.word pointer)) {state with locals:=source.locals}) frame
    simpa only [emptyLocalsHOLFinite,PersistentAlloc.post,callEntryStateHOLFinite] using updated

theorem Execution.alloc_next {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (name : MlS) (arguments : List (ExpHOL 64)) (pointer amount : BitVec 64) (rest : List Action)
    (installed : OriginalCode.Installed source.code)
    (argsRead : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (PersistentAlloc.values amount))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (bounded : pointer.toNat≤33806089496)
    (execution : Execution source (.scoped name .one (ofString "alloc") arguments::rest) target) :
    pointer.toNat+amount.toNat≤33806089496 ∧
      Execution (setVarHOLFinite name (.val (.word pointer)) (PersistentAlloc.post {source with clock:=source.clock-1} pointer amount)) rest target := by
  cases execution with
  | step first next=>
    obtain ⟨room,same⟩:=first.alloc_target name arguments pointer amount installed argsRead heapCell bounded
    rw [same] at next
    exact ⟨room,next⟩

end InitECandidate.Solver.Input.CallPrefix

#print axioms InitECandidate.Solver.Input.CallPrefix.Reaches.alloc_target
#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.alloc_next
