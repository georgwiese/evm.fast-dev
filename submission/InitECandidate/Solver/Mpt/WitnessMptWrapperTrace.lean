import InitECandidate.Solver.Mpt.WitnessCoreEnvironment
import InitECandidate.Solver.Input.CaughtSequenceObserve
import InitECandidate.Solver.Input.ScalarScopeTrace
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.Mpt.WitnessMaterializeMpt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Original239's true declarations/caught-call prefix exposes original238.
Its MptErr release/rethrow and normal return contribute only fixed overhead. -/
theorem child_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (db pointer length : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤1 ∨ ∃ entry target childResult,
      Input.LocalEffects.erase entry=Input.LocalEffects.erase source ∧ entry.clock=source.clock-1 ∧
      entry.locals.lookup (ofString "db")=some (.val (.word db)) ∧ entry.locals.lookup (ofString "p")=some (.val (.word pointer)) ∧
      entry.locals.lookup (ofString "n")=some (.val (.word length)) ∧
      evaluateHOLFiniteState entry WitnessCore.body=(childResult,target) ∧ source.clock-post.clock≤entry.clock-target.clock+2 := by
  rw [wrapper_shape] at run
  obtain ⟨errorPost,errorRun,errorEnd⟩ := Input.ScalarScope.declare_trace source post "e" (.const 0#64) 0#64 afterError outcome rfl run
  let errorSource:=QueryBranch.bind source "e" 0#64
  obtain ⟨readyPost,readyRun,readyEnd⟩ := Input.ScalarScope.declare_trace errorSource errorPost "nd" (.const 0#64) 0#64 afterResult outcome rfl errorRun
  let ready:=QueryBranch.bind errorSource "nd" 0#64
  have endpoint : post=restore source "e" (restore errorSource "nd" readyPost) := by rw [errorEnd,readyEnd]
  have endpointClock:=congrArg PanSemStateFiniteExact.clock endpoint
  change post.clock=readyPost.clock at endpointClock
  have readyClock : ready.clock=source.clock := rfl
  have keep (name : String) (eOther : ofString "e"≠ofString name) (ndOther : ofString "nd"≠ofString name) :
      ready.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    (bind_lookup_other errorSource "nd" name 0#64 ndOther).trans (bind_lookup_other source "e" name 0#64 eOther)
  have readyDb:= (keep "db" (by decide) (by decide)).trans dbCell
  have readyP:= (keep "p" (by decide) (by decide)).trans pCell
  have readyN:= (keep "n" (by decide) (by decide)).trans nCell
  have args : evalListHOLFinite ready (h:=fun address=>Classical.propDecidable (ready.memaddrs address)) childArguments=
      some (WitnessMaterialize.values db pointer length) := by
    simp [childArguments,WitnessMaterialize.values,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,readyDb,readyP,readyN]
  obtain ⟨callee,called,dbEntry,pEntry,nEntry⟩ := WitnessCore.environment ready.code.lookup db pointer length (WitnessCore.original_code source.code installed)
  rcases Input.CallNormal.caught_sequence_observe ready readyPost (some (.local,ofString "nd")) (ofString "_decode_witness_node_body") childArguments _
      WitnessCore.body footer callee .one (ofString "MptErr") (ofString "e") handler 1 0 args called (handler_price source.code installed)
      (Input.ClockCost.returned source.code _) outcome readyRun with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨target,childResult,funded,childRun,allowance⟩ := reached
    let entry:=callEntryStateHOLFinite ready callee
    have entryClock : entry.clock=source.clock-1 := rfl
    change ready.clock-readyPost.clock≤entry.clock-target.clock+2 at allowance
    exact Or.inr ⟨entry,target,childResult,rfl,entryClock,dbEntry,pEntry,nEntry,childRun,by omega⟩

end InitECandidate.Solver.Mpt.WitnessMaterializeMpt

#print axioms InitECandidate.Solver.Mpt.WitnessMaterializeMpt.child_trace
