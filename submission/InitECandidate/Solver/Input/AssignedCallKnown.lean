import InitECandidate.Solver.Input.AssignedCallData

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A genuinely continuing assigned call with known current arguments
and code derives its actual callee execution and exact caller restoration. -/
theorem local_known (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name function : MlS)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (argsRead : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some values)
    (expectedCall : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,shape))
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) function arguments)=(none,target)) :
    1≤source.clock ∧ ∃ childTarget returned,
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned returned),childTarget) ∧
      target=setVarHOLFinite name returned {childTarget with locals:=source.locals} := by
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,childTarget,returned,args,called,run,_checked,endpoint⟩:=
    local_data source target name function arguments normal
  have sameValues : actualValues=values:=Option.some.inj (args.symm.trans argsRead)
  subst actualValues
  have same:=Option.some.inj (called.symm.trans expectedCall)
  have bodyEq:=congrArg Prod.fst same
  have mapEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  have shapeEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.2) same
  change actualBody=body at bodyEq
  change actualCallee=callee at mapEq
  change actualShape=shape at shapeEq
  subst actualBody
  subst actualCallee
  subst actualShape
  exact ⟨funded,childTarget,returned,run,endpoint⟩

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.local_known
