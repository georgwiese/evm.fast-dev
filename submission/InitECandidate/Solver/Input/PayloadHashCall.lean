import InitECandidate.Solver.Input.PayloadHashGlobals

namespace InitECandidate.Solver.Input.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def values (payload out : BitVec 64) : List (ValueHOL 64) := [.val (.word payload),.val (.word out)]
def rawLocals (payload out : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "out" then some (.val (.word out)) else if name=ofString "pl" then some (.val (.word payload)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (payload out : BitVec 64)
    (code : codeFn (ofString "htr_payload")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "htr_payload") (values payload out)=some (body,callee,.one) ∧
      callee.lookup (ofString "pl")=some (.val (.word payload)) ∧ callee.lookup (ofString "out")=some (.val (.word out)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values payload out).length ∧
      ((formals.zip (values payload out)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "htr_payload") (values payload out)=some (body,rawLocals payload out,.one) := by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [rawLocals,show ofString "pl"≠ofString "out" from by decide],by rw [locals]; simp [rawLocals]⟩

/-- Actual original payload caller, including its caller tick and every
observed non-timeout failure. No digest-value or score-ceiling premise. -/
theorem call_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (out cursor stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (workspace : SszHash.Workspace source stp accel chunk zeros) (input : HashInput.Frame origin source lower upper)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (geometry : data.RuntimeGeometry budget cursor) (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤cursor.toNat)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values data.payload out))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "htr_payload") arguments)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤bodyPrice data+1 := by
  obtain ⟨callee,called,payloadLocal,outLocal⟩ := environment source.code.lookup data.payload out (original_code source.code workspace.sha.installed)
  have ready : Entry.Ready data origin (callEntryStateHOLFinite source callee) lower upper out cursor stp accel chunk zeros :=
    ⟨SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace,payloadLocal,outLocal,heap,⟨input.words⟩⟩
  exact ClockCost.call_current_terminating source post destination (ofString "htr_payload") arguments (values data.payload out) body callee .one (bodyPrice data) args called
    (fun observed target evaluated notTimeout=>body_cost data origin (callEntryStateHOLFinite source callee) target lower upper budget out cursor stp accel chunk zeros image layout ready geometry separation small before observed evaluated notTimeout)
    result run notTimeout

/-- Same real normal ignored caller restores its entry heap and retains all
input/decoded word agreement needed by later newpayload phases. -/
theorem call_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (out cursor stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (workspace : SszHash.Workspace source stp accel chunk zeros) (input : HashInput.Frame origin source lower upper)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (geometry : data.RuntimeGeometry budget cursor) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤cursor.toNat)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values data.payload out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_payload") arguments)=(none,post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) ∧ HashInput.Frame origin post lower upper := by
  obtain ⟨callee,called,payloadLocal,outLocal⟩ := environment source.code.lookup data.payload out (original_code source.code workspace.sha.installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ := CallNormal.ignored_data source post (ofString "htr_payload") arguments run
  have valuesEq : actualValues=values data.payload out := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq : (actualBody,actualCallee,actualShape)=(body,callee,.one) := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have ready : Entry.Ready data origin (callEntryStateHOLFinite source callee) lower upper out cursor stp accel chunk zeros :=
    ⟨SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace,payloadLocal,outLocal,heap,⟨input.words⟩⟩
  have restored := body_normal data origin (callEntryStateHOLFinite source callee) target lower upper budget out cursor stp accel chunk zeros image layout ready geometry outputGeometry separation small before returned bodyRun
  rw [endpoint]
  exact ⟨restored.1,⟨restored.2.words⟩⟩

end InitECandidate.Solver.Input.PayloadHash
#print axioms InitECandidate.Solver.Input.PayloadHash.environment
#print axioms InitECandidate.Solver.Input.PayloadHash.call_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.call_normal
