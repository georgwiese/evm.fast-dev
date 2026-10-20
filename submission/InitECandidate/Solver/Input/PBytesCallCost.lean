import InitECandidate.Solver.Input.PBytesBodyCost
import InitECandidate.Solver.Input.PBytesHeap

namespace InitECandidate.Solver.Input.PBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def values (p : BitVec 64) (n : Nat) (out : BitVec 64) : List (ValueHOL 64) := [.val (.word p),.val (.word (BitVec.ofNat 64 n)),.val (.word out)]
def rawLocals (p : BitVec 64) (n : Nat) (out : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "out" then some (.val (.word out)) else if name=ofString "n" then some (.val (.word (BitVec.ofNat 64 n)))
  else if name=ofString "p" then some (.val (.word p)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (p : BitVec 64) (n : Nat) (out : BitVec 64)
    (code : codeFn (ofString "htr_pbytes")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "htr_pbytes") (values p n out)=some (body,callee,.one) ∧
      callee.lookup (ofString "p")=some (.val (.word p)) ∧ callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))) ∧ callee.lookup (ofString "out")=some (.val (.word out)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values p n out).length ∧
      ((formals.zip (values p n out)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "htr_pbytes") (values p n out)=some (body,rawLocals p n out,.one) := by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [rawLocals,show ofString "p"≠ofString "out" from by decide,show ofString "p"≠ofString "n" from by decide],
    by rw [locals]; simp [rawLocals,show ofString "n"≠ofString "out" from by decide],by rw [locals]; simp [rawLocals]⟩

/-- Genuine original progressive-byte-hash caller at its actual byte length,
current initialized workspace and physical input/temporary/output arenas. -/
theorem call_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out stp accel chunk zeros : BitVec 64) (n : Nat)
    (small : n≤134217728) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p n) (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p n out))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "htr_pbytes") arguments)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤n/8+115*PackBytes.chunks n+24283 := by
  obtain ⟨callee,called,pLocal,nLocal,outLocal⟩ := environment source.code.lookup p n out (original_code source.code workspace.sha.installed)
  exact ClockCost.call_current_terminating source post destination (ofString "htr_pbytes") arguments (values p n out) body callee .one (n/8+115*PackBytes.chunks n+24282) args called
    (fun result target actual notTimeout=>body_cost (callEntryStateHOLFinite source callee) target p cursor out stp accel chunk zeros n small
      (SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace) pLocal nLocal outLocal heap inputArena arena aligned outArena result actual notTimeout)
    result run notTimeout

/-- A real normal original progressive-byte caller restores its entry heap;
its callee return and exact arguments are derived from that same call. -/
theorem ignored_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out stp accel chunk zeros : BitVec 64) (n : Nat)
    (small : n≤134217728) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p n out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_pbytes") arguments)=(none,post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  obtain ⟨callee,called,pLocal,nLocal,outLocal⟩ := environment source.code.lookup p n out (original_code source.code workspace.sha.installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (ofString "htr_pbytes") arguments run
  have valuesEq : actualValues=values p n out := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq : (actualBody,actualCallee,actualShape)=(body,callee,.one) := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have restored := body_return_heap (callEntryStateHOLFinite source callee) target p cursor out stp accel chunk zeros n small
    (SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace) pLocal nLocal outLocal heap arena aligned outArena returned bodyRun
  rw [endpoint]
  exact restored

end InitECandidate.Solver.Input.PBytes

#print axioms InitECandidate.Solver.Input.PBytes.environment
#print axioms InitECandidate.Solver.Input.PBytes.call_cost
#print axioms InitECandidate.Solver.Input.PBytes.ignored_return_heap
