import InitECandidate.Solver.Input.MerkleBodyCost
import InitECandidate.Solver.Input.ClockCostTerminatingCall

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def values (p n limit out : BitVec 64) : List (ValueHOL 64) := [.val (.word p),.val (.word n),.val (.word limit),.val (.word out)]
def rawLocals (p n limit out : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "out" then some (.val (.word out)) else if name=ofString "limit" then some (.val (.word limit))
  else if name=ofString "n" then some (.val (.word n)) else if name=ofString "p" then some (.val (.word p)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (p n limit out : BitVec 64)
    (code : codeFn (ofString "merkleize")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "merkleize") (values p n limit out)=some (body,callee,.one) ∧
      callee.lookup (ofString "p")=some (.val (.word p)) ∧ callee.lookup (ofString "n")=some (.val (.word n)) ∧
      callee.lookup (ofString "limit")=some (.val (.word limit)) ∧ callee.lookup (ofString "out")=some (.val (.word out)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values p n limit out).length ∧
      ((formals.zip (values p n limit out)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "merkleize") (values p n limit out)=some (body,rawLocals p n limit out,.one) := by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_,?_⟩
  all_goals rw [locals]
  all_goals simp [rawLocals,show ofString "p"≠ofString "out" from by decide,show ofString "p"≠ofString "limit" from by decide,
    show ofString "p"≠ofString "n" from by decide,show ofString "n"≠ofString "out" from by decide,
    show ofString "n"≠ofString "limit" from by decide,show ofString "limit"≠ofString "out" from by decide]

/-- Actual four-word original caller, with current mapped geometry and
workspace. The source-clock allowance includes the genuine caller tick. -/
theorem call_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (p n limit cursor out zeros stp accel : BitVec 64) (depth : Nat)
    (small : depth<64) (countBound : n.toNat≤2^depth) (limitBound : limit.toNat≤2^depth)
    (workspace : ShaPair.Workspace source stp accel)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (table : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)))
    (inputArena : AllocatedBytes.Arena p (32*n.toNat))
    (bufferArena : AllocatedBytes.Arena cursor (32*max 1 (2*n.toNat))) (aligned : cursor.toNat%8=0)
    (outputArena : AllocatedBytes.Arena out 32) (tableArena : AllocatedBytes.Arena zeros 2048)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p n limit out))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "merkleize") arguments)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤115*n.toNat+55*depth+14 := by
  obtain ⟨callee,called,pLocal,nLocal,limitLocal,outLocal⟩ := environment source.code.lookup p n limit out (original_code source.code workspace.installed)
  have price := ClockCost.call_current_terminating source post destination (ofString "merkleize") arguments (values p n limit out) body callee .one
    (115*n.toNat+55*depth+13) args called
    (fun result target actual notTimeout=>body_cost (callEntryStateHOLFinite source callee) target p n limit cursor out zeros stp accel depth small countBound limitBound
      (ShaPair.Workspace.at_callee source callee stp accel workspace) pLocal nLocal limitLocal outLocal heap table inputArena bufferArena aligned outputArena tableArena result actual notTimeout)
    result run notTimeout
  exact price

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.environment
#print axioms InitECandidate.Solver.Input.Merkle.call_cost
