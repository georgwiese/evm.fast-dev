import InitECandidate.Solver.Input.PContainerBodyCost
import InitECandidate.Solver.Input.PContainerHeap

namespace InitECandidate.Solver.Input.PContainer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def values (ch : BitVec 64) (n : Nat) (out : BitVec 64) : List (ValueHOL 64) := [.val (.word ch),.val (.word (BitVec.ofNat 64 n)),.val (.word out)]
def rawLocals (ch : BitVec 64) (n : Nat) (out : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "out" then some (.val (.word out)) else if name=ofString "n" then some (.val (.word (BitVec.ofNat 64 n)))
  else if name=ofString "ch" then some (.val (.word ch)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (ch : BitVec 64) (n : Nat) (out : BitVec 64)
    (code : codeFn (ofString "htr_pcontainer")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "htr_pcontainer") (values ch n out)=some (body,callee,.one) ∧
      callee.lookup (ofString "ch")=some (.val (.word ch)) ∧ callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))) ∧ callee.lookup (ofString "out")=some (.val (.word out)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values ch n out).length ∧
      ((formals.zip (values ch n out)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "htr_pcontainer") (values ch n out)=some (body,rawLocals ch n out,.one) := by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [rawLocals,show ofString "ch"≠ofString "out" from by decide,show ofString "ch"≠ofString "n" from by decide],
    by rw [locals]; simp [rawLocals,show ofString "n"≠ofString "out" from by decide],by rw [locals]; simp [rawLocals]⟩

/-- Actual original container caller at the validated field count. -/
theorem call_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch cursor out stp accel chunk zeros : BitVec 64) (n : Nat)
    (short : n<32) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena ch (32*n)) (arena : AllocatedBytes.Arena cursor (896+64*n)) (aligned : cursor.toNat%8=0)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values ch n out))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "htr_pcontainer") arguments)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤116*n+24206 := by
  obtain ⟨callee,called,chLocal,nLocal,outLocal⟩ := environment source.code.lookup ch n out (original_code source.code workspace.sha.installed)
  have bounded := ClockCost.call_current_terminating source post destination (ofString "htr_pcontainer") arguments (values ch n out) body callee .one (116*n+24205) args called
    (fun result target actual notTimeout=>body_cost (callEntryStateHOLFinite source callee) target ch cursor out stp accel chunk zeros n short
      (SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace) chLocal nLocal outLocal heap inputArena arena aligned result actual notTimeout)
    result run notTimeout
  omega

/-- A real normal original container caller restores its entry heap;
its callee return and exact arguments are derived from that same call. -/
theorem ignored_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch cursor out stp accel chunk zeros : BitVec 64) (n : Nat)
    (short : n<32) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena ch (32*n)) (arena : AllocatedBytes.Arena cursor (896+64*n)) (aligned : cursor.toNat%8=0)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values ch n out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_pcontainer") arguments)=(none,post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  obtain ⟨callee,called,chLocal,nLocal,outLocal⟩ := environment source.code.lookup ch n out (original_code source.code workspace.sha.installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (ofString "htr_pcontainer") arguments run
  have valuesEq : actualValues=values ch n out := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq : (actualBody,actualCallee,actualShape)=(body,callee,.one) := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have restored := body_return_heap (callEntryStateHOLFinite source callee) target ch cursor out stp accel chunk zeros n short
    (SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace) chLocal nLocal outLocal heap inputArena arena aligned returned bodyRun
  rw [endpoint]
  exact restored

end InitECandidate.Solver.Input.PContainer

#print axioms InitECandidate.Solver.Input.PContainer.environment
#print axioms InitECandidate.Solver.Input.PContainer.call_cost
#print axioms InitECandidate.Solver.Input.PContainer.ignored_return_heap
