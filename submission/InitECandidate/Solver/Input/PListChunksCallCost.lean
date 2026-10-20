import InitECandidate.Solver.Input.PListChunksCost
import InitECandidate.Solver.Input.PListChunksHeap

namespace InitECandidate.Solver.Input.PListChunks
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def values (roots : BitVec 64) (n : Nat) (len out : BitVec 64) : List (ValueHOL 64) := [.val (.word roots),.val (.word (BitVec.ofNat 64 n)),.val (.word len),.val (.word out)]
def rawLocals (roots : BitVec 64) (n : Nat) (len out : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "out" then some (.val (.word out)) else if name=ofString "len" then some (.val (.word len))
  else if name=ofString "n" then some (.val (.word (BitVec.ofNat 64 n))) else if name=ofString "roots" then some (.val (.word roots)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (roots : BitVec 64) (n : Nat) (len out : BitVec 64)
    (code : codeFn (ofString "htr_plist_chunks")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "htr_plist_chunks") (values roots n len out)=some (body,callee,.one) ∧
      callee.lookup (ofString "roots")=some (.val (.word roots)) ∧ callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))) ∧
      callee.lookup (ofString "len")=some (.val (.word len)) ∧ callee.lookup (ofString "out")=some (.val (.word out)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values roots n len out).length ∧
      ((formals.zip (values roots n len out)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "htr_plist_chunks") (values roots n len out)=some (body,rawLocals roots n len out,.one) := by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_,?_⟩
  all_goals rw [locals]
  all_goals simp [rawLocals,show ofString "roots"≠ofString "out" from by decide,show ofString "roots"≠ofString "len" from by decide,show ofString "roots"≠ofString "n" from by decide,
    show ofString "n"≠ofString "out" from by decide,show ofString "n"≠ofString "len" from by decide,show ofString "len"≠ofString "out" from by decide]

/-- Actual original list-chunk caller includes the progressive tree, actual
length mix and genuine caller tick. No successful outcome is assumed. -/
theorem call_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (roots cursor out len stp accel chunk zeros : BitVec 64) (n : Nat)
    (bounded : n≤134217728) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena roots (32*n)) (temporaryArena : AllocatedBytes.Arena cursor (832+64*n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values roots n len out))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "htr_plist_chunks") arguments)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤115*n+24207 := by
  obtain ⟨callee,called,rootsLocal,nLocal,lenLocal,outLocal⟩ := environment source.code.lookup roots n len out (original_code source.code workspace.sha.installed)
  exact ClockCost.call_current_terminating source post destination (ofString "htr_plist_chunks") arguments (values roots n len out) body callee .one (115*n+24206) args called
    (fun result target actual notTimeout=>body_cost (callEntryStateHOLFinite source callee) target roots cursor out len stp accel chunk zeros n bounded
      (SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace) rootsLocal nLocal outLocal lenLocal heap inputArena temporaryArena aligned outArena result actual notTimeout)
    result run notTimeout

/-- A real normal original list-chunk call restores its current heap cursor,
using only its actual callee return and present physical input/workspace. -/
theorem ignored_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (roots cursor out len stp accel chunk zeros : BitVec 64) (n : Nat)
    (bounded : n≤134217728) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena roots (32*n)) (temporaryArena : AllocatedBytes.Arena cursor (832+64*n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values roots n len out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_plist_chunks") arguments)=(none,post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  obtain ⟨callee,called,rootsLocal,nLocal,lenLocal,outLocal⟩ := environment source.code.lookup roots n len out (original_code source.code workspace.sha.installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (ofString "htr_plist_chunks") arguments run
  have valuesEq : actualValues=values roots n len out := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq : (actualBody,actualCallee,actualShape)=(body,callee,.one) := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have returnedHeap := body_return_heap (callEntryStateHOLFinite source callee) target roots cursor out stp accel chunk zeros n bounded
    (SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace) rootsLocal nLocal outLocal heap inputArena temporaryArena aligned outArena returned bodyRun
  rw [endpoint]
  exact returnedHeap

end InitECandidate.Solver.Input.PListChunks

#print axioms InitECandidate.Solver.Input.PListChunks.environment
#print axioms InitECandidate.Solver.Input.PListChunks.call_cost
#print axioms InitECandidate.Solver.Input.PListChunks.ignored_return_heap
