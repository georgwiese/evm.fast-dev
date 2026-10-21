import InitECandidate.Solver.Input.CallResumeFields

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Exact caller restoration from the nonlocal frame, retaining the real
child clock rather than prescribing its return or its execution. -/
theorem continuation_of_erase (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (value : ValueHOL 64) (frame : LocalEffects.erase target=LocalEffects.erase source) :
    continuationEntry source target name value=setVarHOLFinite (ofString name) value {source with clock:=target.clock} := by
  have restored:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals,clock:=target.clock}) frame
  change {target with locals:=source.locals}={source with clock:=target.clock} at restored
  exact congrArg (fun state=>setVarHOLFinite (ofString name) value state) restored

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.continuation_of_erase
