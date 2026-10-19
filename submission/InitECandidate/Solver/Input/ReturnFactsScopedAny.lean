import InitECandidate.Solver.Input.ReturnFacts

namespace InitECandidate.Solver.Input.ReturnFacts
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Scoped callees can only return their caller's value through an actual
execution of the continuation. This needs no successful-callee premise. -/
theorem scoped_any (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (property : ValueHOL 64 → Prop)
    (tail : ∀ ready,Returns ready continuation property) :
    Returns source (.decCall (Flapjack.Basis.Pure.MlString.ofString name) shape function arguments continuation) property := by
  intro post value normal
  obtain ⟨positive,values,actualBody,callee,actualShape,target,returned,inner,args,called,bodyRun,checked,continuationRun,restored⟩ :=
    CallNormal.scoped_data source post name shape function arguments continuation value normal
  exact tail (CallNormal.continuationEntry source target name returned) inner value continuationRun

end InitECandidate.Solver.Input.ReturnFacts

#print axioms InitECandidate.Solver.Input.ReturnFacts.scoped_any
