import InitECandidate.Solver.Input.ShaPairCost

namespace InitECandidate.Solver.Input.ShaPair
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix ShaFixedCost

def values (a b out : BitVec 64) : List (ValueHOL 64) := [.val (.word a),.val (.word b),.val (.word out)]
def rawLocals (a b out : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "out" then some (.val (.word out))
  else if name=ofString "input_b" then some (.val (.word b))
  else if name=ofString "input_a" then some (.val (.word a)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (a b out : BitVec 64)
    (code : codeFn (ofString "sha256_pair")=some (pairFormals,pairBody,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "sha256_pair") (values a b out)=some (pairBody,callee,.one) ∧
      callee.lookup (ofString "input_a")=some (.val (.word a)) ∧ callee.lookup (ofString "input_b")=some (.val (.word b)) := by
  have valid : (pairFormals.map Prod.fst).Nodup ∧ pairFormals.length=(values a b out).length ∧
      ((pairFormals.zip (values a b out)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [pairFormals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "sha256_pair") (values a b out)=some (pairBody,rawLocals a b out,.one) := by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  · rw [locals]
    simp [rawLocals,show ofString "input_a"≠ofString "out" from by decide,show ofString "input_a"≠ofString "input_b" from by decide]
  · rw [locals]
    simp [rawLocals,show ofString "input_b"≠ofString "out" from by decide]

/-- Genuine original pair call, with its actual three-word ABI and no
successful-return premise. Only current mapped inputs/workspace are needed. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b out stp accel : BitVec 64)
    (installed : OriginalCode.Installed source.code) (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values a b out))
    (state : source.globals.lookup (ofString "sha_st")=some (.val (.word stp)))
    (accelerator : source.globals.lookup (ofString "sha_accel")=some (.val (.word accel)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (aArena : AllocatedBytes.Arena a 32) (bArena : AllocatedBytes.Arena b 32)
    (workspaceArena : AllocatedBytes.Arena accel 96) (aligned : accel.toNat%8=0) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "sha256_pair") arguments)).2.clock≤53 := by
  obtain ⟨callee,called,inputA,inputB⟩ := environment source.code.lookup a b out (pair_code source.code installed)
  have actual : Ready (callEntryStateHOLFinite source callee) a b stp accel := ⟨installed,domain,inputA,inputB,state,accelerator⟩
  have cost := body_cost _ a b stp accel actual aArena bArena workspaceArena aligned
  exact ClockCost.call_current source destination (ofString "sha256_pair") arguments (values a b out) pairBody callee .one 52 args called cost

end InitECandidate.Solver.Input.ShaPair

#print axioms InitECandidate.Solver.Input.ShaPair.environment
#print axioms InitECandidate.Solver.Input.ShaPair.call_cost
