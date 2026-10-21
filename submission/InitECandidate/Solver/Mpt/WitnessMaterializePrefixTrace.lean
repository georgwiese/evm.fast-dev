import InitECandidate.Solver.Mpt.WitnessCoreEnvironment
import InitECandidate.Solver.Input.CaughtSequenceObserve
import InitECandidate.Solver.Input.ScalarScopeTrace
import InitECandidate.Solver.Input.ScopeClock
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.Mpt.WitnessMaterialize
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Original240's real mark/declaration/caught-call prefix exposes original239
at the actual unchanged memory/globals. Both successful and error outcomes
keep their genuine release/handler overhead; no child bound is assumed. -/
theorem child_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (db pointer length cursor : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (cursorCell : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤2 ∨ ∃ entry target childResult,
      Input.LocalEffects.erase entry=Input.LocalEffects.erase source ∧ entry.clock=source.clock-2 ∧
      entry.locals.lookup (ofString "db")=some (.val (.word db)) ∧ entry.locals.lookup (ofString "p")=some (.val (.word pointer)) ∧
      entry.locals.lookup (ofString "n")=some (.val (.word length)) ∧ entry.locals.lookup (ofString "mark")=some (.val (.word cursor)) ∧
      evaluateHOLFiniteState entry WitnessMaterializeMpt.body=(childResult,target) ∧
      source.clock-post.clock≤entry.clock-target.clock+4 := by
  by_cases zero : source.clock=0
  · exact Or.inl (by omega)
  · have markRun:=Arenas.mark_call source .down "mark" cursor afterMark (Arenas.Scratch.mark_code source.code installed) cursorCell (by omega)
    change evaluateHOLFiniteState source (.decCall (ofString "mark") .one (ofString "scratch_mark") [] afterMark)=_ at markRun
    rw [wrapper_shape,markRun] at run
    let marked:=QueryBranch.bind {source with clock:=source.clock-1} "mark" cursor
    let markedPost:=(evaluateHOLFiniteState marked afterMark).2
    have firstEq:=congrArg Prod.fst run
    change (evaluateHOLFiniteState marked afterMark).1=outcome at firstEq
    have markedRun : evaluateHOLFiniteState marked afterMark=(outcome,markedPost) := Prod.ext firstEq rfl
    have lastEq:=congrArg Prod.snd run
    have markEnd : post=restore source "mark" markedPost := lastEq.symm
    obtain ⟨errorPost,errorRun,errorEnd⟩ := Input.ScalarScope.declare_trace marked markedPost "e" (.const 0#64) 0#64 afterError outcome rfl markedRun
    let errorSource:=QueryBranch.bind marked "e" 0#64
    obtain ⟨readyPost,readyRun,readyEnd⟩ := Input.ScalarScope.declare_trace errorSource errorPost "nd" (.const 0#64) 0#64 afterResult outcome rfl errorRun
    let ready:=QueryBranch.bind errorSource "nd" 0#64
    have endpoint : post=restore source "mark" (restore marked "e" (restore errorSource "nd" readyPost)) := by rw [markEnd,errorEnd,readyEnd]
    have endpointClock:=congrArg PanSemStateFiniteExact.clock endpoint
    change post.clock=readyPost.clock at endpointClock
    have readyClock : ready.clock=source.clock-1 := rfl
    have readyForward:=evaluateHOLFiniteState_clock_le ready afterResult
    rw [readyRun] at readyForward
    change readyPost.clock≤ready.clock at readyForward
    have keep (name : String) (markOther : ofString "mark"≠ofString name) (eOther : ofString "e"≠ofString name) (ndOther : ofString "nd"≠ofString name) :
        ready.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
      (bind_lookup_other errorSource "nd" name 0#64 ndOther).trans ((bind_lookup_other marked "e" name 0#64 eOther).trans
        (bind_lookup_other {source with clock:=source.clock-1} "mark" name cursor markOther))
    have readyDb:= (keep "db" (by decide) (by decide) (by decide)).trans dbCell
    have readyP:= (keep "p" (by decide) (by decide) (by decide)).trans pCell
    have readyN:= (keep "n" (by decide) (by decide) (by decide)).trans nCell
    have readyMark : ready.locals.lookup (ofString "mark")=some (.val (.word cursor)) :=
      (bind_lookup_other errorSource "nd" "mark" 0#64 (by decide)).trans ((bind_lookup_other marked "e" "mark" 0#64 (by decide)).trans (bind_lookup_same _ _ _))
    have args : evalListHOLFinite ready (h:=fun address=>Classical.propDecidable (ready.memaddrs address)) childArguments=
        some (WitnessMaterializeMpt.values db pointer length cursor) := by
      simp [childArguments,WitnessMaterializeMpt.values,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,readyDb,readyP,readyN,readyMark]
    obtain ⟨callee,called,dbEntry,pEntry,nEntry,markEntry⟩ := WitnessMaterializeMpt.environment ready.code.lookup db pointer length cursor (WitnessMaterializeMpt.original_code source.code installed)
    rcases Input.CallNormal.caught_sequence_observe ready readyPost (some (.local,ofString "nd")) (ofString "_decode_witness_node_mpt") childArguments _
        WitnessMaterializeMpt.body footer callee .one (ofString "RlpErr") (ofString "e") handler 1 1 args called (handler_price source.code installed)
        (footer_price source.code installed) outcome readyRun with stopped|reached
    · exact Or.inl (by omega)
    · obtain ⟨target,childResult,funded,childRun,allowance⟩ := reached
      let entry:=callEntryStateHOLFinite ready callee
      have entryClock : entry.clock=source.clock-2 := by change source.clock-1-1=source.clock-2; omega
      change ready.clock-readyPost.clock≤entry.clock-target.clock+3 at allowance
      exact Or.inr ⟨entry,target,childResult,rfl,entryClock,dbEntry,pEntry,nEntry,markEntry,childRun,by omega⟩

end InitECandidate.Solver.Mpt.WitnessMaterialize

#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.child_trace
