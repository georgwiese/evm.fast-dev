import InitECandidate.Solver.Input.RequestListHashBody

namespace InitECandidate.Solver.Input.RequestListHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def values (kind : Kind) (p : BitVec 64) (n : Nat) (out : BitVec 64) : List (ValueHOL 64) :=
  [.val (.word (BitVec.ofNat 64 kind.tag)),.val (.word p),.val (.word (BitVec.ofNat 64 n)),.val (.word (BitVec.ofNat 64 kind.record.length)),.val (.word out)]
def rawLocals (kind : Kind) (p : BitVec 64) (n : Nat) (out : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "out" then some (.val (.word out)) else if name=ofString "sz" then some (.val (.word (BitVec.ofNat 64 kind.record.length)))
  else if name=ofString "n" then some (.val (.word (BitVec.ofNat 64 n))) else if name=ofString "p" then some (.val (.word p))
  else if name=ofString "kind" then some (.val (.word (BitVec.ofNat 64 kind.tag))) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (kind : Kind) (p : BitVec 64) (n : Nat) (out : BitVec 64)
    (code : codeFn (ofString "htr_request_list")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "htr_request_list") (values kind p n out)=some (body,callee,.one) ∧
      callee.lookup (ofString "kind")=some (.val (.word (BitVec.ofNat 64 kind.tag))) ∧
      callee.lookup (ofString "p")=some (.val (.word p)) ∧ callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))) ∧
      callee.lookup (ofString "sz")=some (.val (.word (BitVec.ofNat 64 kind.record.length))) ∧ callee.lookup (ofString "out")=some (.val (.word out)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values kind p n out).length ∧
      ((formals.zip (values kind p n out)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "htr_request_list") (values kind p n out)=some (body,rawLocals kind p n out,.one) := by
    simp only [lookupCodeHOLExact,code,valid,and_self,ite_true]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_,?_,?_⟩
  all_goals rw [locals]
  all_goals simp [rawLocals,
    show ofString "kind"≠ofString "out" from by decide,show ofString "kind"≠ofString "sz" from by decide,show ofString "kind"≠ofString "n" from by decide,show ofString "kind"≠ofString "p" from by decide,
    show ofString "p"≠ofString "out" from by decide,show ofString "p"≠ofString "sz" from by decide,show ofString "p"≠ofString "n" from by decide,
    show ofString "n"≠ofString "out" from by decide,show ofString "n"≠ofString "sz" from by decide,show ofString "sz"≠ofString "out" from by decide]

/-- Genuine original five-word request-list caller, charged by the actual
kind's record cost/count, retaining every observed non-timeout failure. -/
theorem call_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out stp accel chunk zeros : BitVec 64) (n : Nat)
    (bounded : n≤134217728) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)))
    (inputArena : AllocatedBytes.Arena p (n*kind.record.length)) (arena : AllocatedBytes.Arena roots (96*n+1312)) (aligned : roots.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values kind p n out))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "htr_request_list") arguments)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤price kind n+1 := by
  obtain ⟨callee,called,kindLocal,pLocal,nLocal,sizeLocal,outLocal⟩ := environment source.code.lookup kind p n out (original_code source.code workspace.sha.installed)
  exact ClockCost.call_current_terminating source post destination (ofString "htr_request_list") arguments (values kind p n out) body callee .one (price kind n) args called
    (fun result target actual notTimeout=>(body_summary (callEntryStateHOLFinite source callee) target kind p roots out stp accel chunk zeros n bounded
      (SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace) kindLocal pLocal nLocal sizeLocal outLocal heap inputArena arena aligned outArena result actual notTimeout).1)
    result run notTimeout

/-- Actual normal request-list callers restore the real entry heap. -/
theorem ignored_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out stp accel chunk zeros : BitVec 64) (n : Nat)
    (bounded : n≤134217728) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)))
    (inputArena : AllocatedBytes.Arena p (n*kind.record.length)) (arena : AllocatedBytes.Arena roots (96*n+1312)) (aligned : roots.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values kind p n out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_request_list") arguments)=(none,post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)) := by
  obtain ⟨callee,called,kindLocal,pLocal,nLocal,sizeLocal,outLocal⟩ := environment source.code.lookup kind p n out (original_code source.code workspace.sha.installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (ofString "htr_request_list") arguments run
  have valuesEq : actualValues=values kind p n out := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq : (actualBody,actualCallee,actualShape)=(body,callee,.one) := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have restored := (body_summary (callEntryStateHOLFinite source callee) target kind p roots out stp accel chunk zeros n bounded
    (SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace) kindLocal pLocal nLocal sizeLocal outLocal heap inputArena arena aligned outArena (some (.returned returned)) bodyRun (by simp)).2 returned rfl
  rw [endpoint]
  exact restored

end InitECandidate.Solver.Input.RequestListHash

#print axioms InitECandidate.Solver.Input.RequestListHash.environment
#print axioms InitECandidate.Solver.Input.RequestListHash.call_cost
#print axioms InitECandidate.Solver.Input.RequestListHash.ignored_return_heap
