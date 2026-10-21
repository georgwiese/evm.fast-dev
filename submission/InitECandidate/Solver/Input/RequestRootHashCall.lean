import InitECandidate.Solver.Input.RequestRootHashBody

namespace InitECandidate.Solver.Input.RequestRootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Actual unchanged request-root caller, with its own caller tick and all
observed non-timeout failures at the real two-word ABI. -/
theorem call_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (out ch stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (workspace : SszHash.Workspace source stp accel chunk zeros) (input : HashInput.Frame origin source lower upper)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)))
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : PayloadHash.FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values data.si out))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "htr_new_payload_request") arguments)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤bodyPrice data+1 := by
  obtain ⟨callee,called,siLocal,outLocal⟩ := environment source.code.lookup data.si out (original_code source.code workspace.sha.installed)
  have ready : Entry.Ready data origin (callEntryStateHOLFinite source callee) lower upper out ch stp accel chunk zeros :=
    ⟨SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace,siLocal,outLocal,heap,⟨input.words⟩⟩
  exact ClockCost.call_current_terminating source post destination (ofString "htr_new_payload_request") arguments (values data.si out) body callee .one (bodyPrice data) args called
    (fun observed target evaluated notTimeout=>body_cost data origin (callEntryStateHOLFinite source callee) target lower upper budget out ch stp accel chunk zeros image layout ready geometry outputGeometry separation small before observed evaluated notTimeout)
    result run notTimeout

theorem call_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (out ch stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (workspace : SszHash.Workspace source stp accel chunk zeros) (input : HashInput.Frame origin source lower upper)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)))
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : PayloadHash.FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values data.si out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_new_payload_request") arguments)=(none,post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)) ∧ HashInput.Frame origin post lower upper := by
  obtain ⟨callee,called,siLocal,outLocal⟩ := environment source.code.lookup data.si out (original_code source.code workspace.sha.installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ := CallNormal.ignored_data source post (ofString "htr_new_payload_request") arguments run
  have valuesEq : actualValues=values data.si out := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq : (actualBody,actualCallee,actualShape)=(body,callee,.one) := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have ready : Entry.Ready data origin (callEntryStateHOLFinite source callee) lower upper out ch stp accel chunk zeros :=
    ⟨SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace,siLocal,outLocal,heap,⟨input.words⟩⟩
  have restored := body_normal data origin (callEntryStateHOLFinite source callee) target lower upper budget out ch stp accel chunk zeros image layout ready geometry outputGeometry separation small before returned bodyRun
  rw [endpoint]
  exact ⟨restored.1,⟨restored.2.words⟩⟩

end InitECandidate.Solver.Input.RequestRootHash
#print axioms InitECandidate.Solver.Input.RequestRootHash.call_cost
#print axioms InitECandidate.Solver.Input.RequestRootHash.call_normal
