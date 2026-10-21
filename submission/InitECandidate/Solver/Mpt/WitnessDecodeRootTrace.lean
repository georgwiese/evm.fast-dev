import InitECandidate.Solver.Mpt.WitnessDecodeRootEnvironment
import InitECandidate.Solver.MutableTable.MemeqAnyCall
import InitECandidate.Solver.Input.ScopedCallTrace
import InitECandidate.Solver.Input.CallResumeFields
import InitECandidate.Solver.Input.ScopeClock
import InitECandidate.Solver.Input.PureDecisionTrace

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Every real original root decode either stops within its comparison
allowance or reaches its genuine table lookup. No operand readability or
successful comparison/lookup is assumed. -/
theorem lookup_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (db root emptyRoot : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (emptyCell : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤129 ∨ ∃ current inner,
      Input.LocalEffects.erase current=Input.LocalEffects.erase source ∧ current.clock≤source.clock ∧ source.clock-current.clock≤129 ∧
      current.locals.lookup (ofString "db")=some (.val (.word db)) ∧ current.locals.lookup (ofString "root_hash")=some (.val (.word root)) ∧
      evaluateHOLFiniteState current lookupCall=(outcome,inner) ∧ post=QueryBranch.restore source "is_empty" inner := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) compareArguments=
      some (MutableTable.MemeqByteRuntime.values root emptyRoot 32) := by
    simp [compareArguments,QueryBranch.localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,rootCell,emptyCell,
      MutableTable.MemeqByteRuntime.values]
  obtain ⟨callee,called,aCell,bCell,nCell⟩ := MutableTable.MemeqByteRuntime.environment source.code.lookup root emptyRoot 32
    (MutableTable.MemeqAny.original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have price:=MutableTable.MemeqAny.body_cost entry nCell
  rw [shapes.1] at run
  rcases Input.CallNormal.scoped_trace source post "is_empty" .one (ofString "memeq") compareArguments _ Memeq32.body afterCompare callee .one 128
      args called price outcome run with stopped|resumed
  · exact Or.inl stopped
  · obtain ⟨target,returned,inner,funded,bodyRun,checked,forward,spent,continued,endpoint⟩ := resumed
    have pure:=MutableTable.MemeqAny.readonly source.code entry rfl
    rw [bodyRun] at pure
    have targetPure : Input.LocalEffects.erase target=Input.LocalEffects.erase source := pure
    let current:=Input.CallNormal.continuationEntry source target "is_empty" returned
    have currentPure : Input.LocalEffects.erase current=Input.LocalEffects.erase source :=
      (Input.CallNormal.continuation_erase source target "is_empty" returned).trans targetPure
    have currentClock : current.clock=target.clock := rfl
    have endpointClock : post.clock=inner.clock := (congrArg PanSemStateFiniteExact.clock endpoint).trans
      (QueryBranch.restore_clock source inner "is_empty")
    have guardDecision : Input.PureDecision emptyGuard := .ite _ (.returned _) .skip
    rw [shapes.2.1] at continued
    rcases guardDecision.trace current inner lookupCall outcome continued with stopped|lookupRun
    · exact Or.inl (by omega)
    · exact Or.inr ⟨current,inner,currentPure,by omega,by omega,
        (Input.CallNormal.continuation_lookup_other source target "is_empty" "db" returned (by decide)).trans dbCell,
        (Input.CallNormal.continuation_lookup_other source target "is_empty" "root_hash" returned (by decide)).trans rootCell,lookupRun,endpoint⟩

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.lookup_trace
