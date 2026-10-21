import InitECandidate.Solver.Input.BytesListBodyCost
import InitECandidate.Solver.Input.ClockCostTerminatingCall
import InitECandidate.Solver.Input.BytesListHeap

namespace InitECandidate.Solver.Input.BytesListHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def values (p : BitVec 64) (n : Nat) (out : BitVec 64) : List (ValueHOL 64) := [.val (.word p),.val (.word (BitVec.ofNat 64 n)),.val (.word 1#64),.val (.word out)]
def rawLocals (p : BitVec 64) (n : Nat) (out : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "out" then some (.val (.word out)) else if name=ofString "limit_chunks" then some (.val (.word 1#64))
  else if name=ofString "n" then some (.val (.word (BitVec.ofNat 64 n))) else if name=ofString "p" then some (.val (.word p)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (p : BitVec 64) (n : Nat) (out : BitVec 64)
    (code : codeFn (ofString "htr_bytes_list")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "htr_bytes_list") (values p n out)=some (body,callee,.one) ∧
      callee.lookup (ofString "p")=some (.val (.word p)) ∧ callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))) ∧ callee.lookup (ofString "limit_chunks")=some (.val (.word 1#64)) ∧ callee.lookup (ofString "out")=some (.val (.word out)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values p n out).length ∧
      ((formals.zip (values p n out)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "htr_bytes_list") (values p n out)=some (body,rawLocals p n out,.one) := by
    simp only [lookupCodeHOLExact,code,valid,and_self,ite_true]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [rawLocals,show ofString "p"≠ofString "out" from by decide,show ofString "p"≠ofString "n" from by decide,show ofString "p"≠ofString "limit_chunks" from by decide],
    by rw [locals]; simp [rawLocals,show ofString "n"≠ofString "out" from by decide,show ofString "n"≠ofString "limit_chunks" from by decide],by rw [locals]; simp [rawLocals,show ofString "limit_chunks"≠ofString "out" from by decide,show ofString "limit_chunks"≠ofString "n" from by decide],by rw [locals]; simp [rawLocals]⟩

/-- Actual payload extra-data caller, including its literal limit of one chunk. -/
theorem call_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out stp accel chunk zeros : BitVec 64) (n : Nat)
    (short : n≤32) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p n) (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p n out))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "htr_bytes_list") arguments)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤n/8+115*PackBytes.chunks n+149 := by
  obtain ⟨callee,called,pLocal,nLocal,limitLocal,outLocal⟩ := environment source.code.lookup p n out (original_code source.code workspace.sha.installed)
  have bounded := ClockCost.call_current_terminating source post destination (ofString "htr_bytes_list") arguments (values p n out) body callee .one (n/8+115*PackBytes.chunks n+148) args called
    (fun result target actual notTimeout=>body_cost (callEntryStateHOLFinite source callee) target p cursor out stp accel chunk zeros n short
      (SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace) pLocal nLocal limitLocal outLocal heap inputArena arena aligned outArena result actual notTimeout)
    result run notTimeout
  omega

/-- A real normal original byte-list hash caller restores its entry heap;
its callee return and exact arguments are derived from that same call. -/
theorem ignored_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out stp accel chunk zeros : BitVec 64) (n : Nat)
    (short : n≤32) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p n out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_bytes_list") arguments)=(none,post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  obtain ⟨callee,called,pLocal,nLocal,limitLocal,outLocal⟩ := environment source.code.lookup p n out (original_code source.code workspace.sha.installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (ofString "htr_bytes_list") arguments run
  have valuesEq : actualValues=values p n out := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq : (actualBody,actualCallee,actualShape)=(body,callee,.one) := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have restored := body_return_heap (callEntryStateHOLFinite source callee) target p cursor out stp accel chunk zeros n short
    (SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace) pLocal nLocal limitLocal outLocal heap arena aligned returned bodyRun
  rw [endpoint]
  exact restored

end InitECandidate.Solver.Input.BytesListHash

#print axioms InitECandidate.Solver.Input.BytesListHash.environment
#print axioms InitECandidate.Solver.Input.BytesListHash.call_cost
#print axioms InitECandidate.Solver.Input.BytesListHash.ignored_return_heap
