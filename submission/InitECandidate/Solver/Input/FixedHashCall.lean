import InitECandidate.Solver.Input.FixedHashBody

namespace InitECandidate.Solver.Input.FixedHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def values (p out : BitVec 64) : List (ValueHOL 64) := [.val (.word p),.val (.word out)]
def rawLocals (inputName : String) (p out : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "out" then some (.val (.word out)) else if name=ofString inputName then some (.val (.word p)) else none

theorem environment (kind : Kind) (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (p out : BitVec 64)
    (code : codeFn kind.name=some (kind.formals,kind.body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn kind.name (values p out)=some (kind.body,callee,.one) ∧
      callee.lookup (ofString kind.inputName)=some (.val (.word p)) ∧ callee.lookup (ofString "out")=some (.val (.word out)) := by
  have different : ofString kind.inputName≠ofString "out" := by cases kind <;> decide
  have valid : (kind.formals.map Prod.fst).Nodup ∧ kind.formals.length=(values p out).length ∧
      ((kind.formals.zip (values p out)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by cases kind <;> decide,rfl,?_⟩
    simp [Kind.formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn kind.name (values p out)=some (kind.body,rawLocals kind.inputName p out,.one) := by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [rawLocals,different],by rw [locals]; simp [rawLocals]⟩

/-- Original fixed-record caller, specialized only by its genuine record
kind, with the actual caller tick and all non-timeout failure prefixes. -/
theorem call_cost (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p ch out stp accel chunk zeros : BitVec 64)
    (workspace : SszHash.Workspace source stp accel chunk zeros)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)))
    (inputArena : AllocatedBytes.Arena p kind.length) (arena : AllocatedBytes.Arena ch (32*kind.count+1120)) (aligned : ch.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p out))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) kind.name arguments)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤kind.price+1 := by
  obtain ⟨callee,called,pLocal,outLocal⟩ := environment kind source.code.lookup p out (original_code kind source.code workspace.sha.installed)
  exact ClockCost.call_current_terminating source post destination kind.name arguments (values p out) kind.body callee .one kind.price args called
    (fun result target actual notTimeout=>(body_summary kind (callEntryStateHOLFinite source callee) target p ch out stp accel chunk zeros
      (SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace) pLocal outLocal heap inputArena arena aligned outArena result actual notTimeout).1)
    result run notTimeout

/-- A genuine normal fixed-record caller restores its entry heap; its
callee return and original ABI follow from that same invocation. -/
theorem ignored_return_heap (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p ch out stp accel chunk zeros : BitVec 64)
    (workspace : SszHash.Workspace source stp accel chunk zeros)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)))
    (inputArena : AllocatedBytes.Arena p kind.length) (arena : AllocatedBytes.Arena ch (32*kind.count+1120)) (aligned : ch.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) kind.name arguments)=(none,post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)) := by
  obtain ⟨callee,called,pLocal,outLocal⟩ := environment kind source.code.lookup p out (original_code kind source.code workspace.sha.installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ := CallNormal.ignored_data source post kind.name arguments run
  have valuesEq : actualValues=values p out := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq : (actualBody,actualCallee,actualShape)=(kind.body,callee,.one) := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have restored := (body_summary kind (callEntryStateHOLFinite source callee) target p ch out stp accel chunk zeros
    (SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace) pLocal outLocal heap inputArena arena aligned outArena (some (.returned returned)) bodyRun (by simp)).2 returned rfl
  rw [endpoint]
  exact restored

end InitECandidate.Solver.Input.FixedHash

#print axioms InitECandidate.Solver.Input.FixedHash.environment
#print axioms InitECandidate.Solver.Input.FixedHash.call_cost
#print axioms InitECandidate.Solver.Input.FixedHash.ignored_return_heap
