import InitECandidate.Solver.Input.U64Hash

namespace InitECandidate.Solver.Input.U64Hash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def values (p out : BitVec 64) : List (ValueHOL 64) := [.val (.word p),.val (.word out)]
def rawLocals (p out : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "out" then some (.val (.word out)) else if name=ofString "p" then some (.val (.word p)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (p out : BitVec 64)
    (code : codeFn (ofString "htr_u64_at")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "htr_u64_at") (values p out)=some (body,callee,.one) ∧
      callee.lookup (ofString "p")=some (.val (.word p)) ∧ callee.lookup (ofString "out")=some (.val (.word out)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values p out).length ∧
      ((formals.zip (values p out)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "htr_u64_at") (values p out)=some (body,rawLocals p out,.one) := by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [rawLocals,show ofString "p"≠ofString "out" from by decide],by rw [locals]; simp [rawLocals]⟩

/-- Genuine original scalar hash caller costs at most5 source ticks for
all outcomes, at current physically mapped input/output operands. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p out : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (inputArena : AllocatedBytes.Arena p 8) (outArena : AllocatedBytes.Arena out 32) (aligned : out.toNat%8=0)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p out)) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "htr_u64_at") arguments)).2.clock≤5 := by
  obtain ⟨callee,called,pLocal,outLocal⟩ := environment source.code.lookup p out (original_code source.code installed)
  have price := body_cost (callEntryStateHOLFinite source callee) p out installed domain pLocal outLocal inputArena outArena aligned
  exact ClockCost.call_current source destination (ofString "htr_u64_at") arguments (values p out) body callee .one 4 args called price

end InitECandidate.Solver.Input.U64Hash

#print axioms InitECandidate.Solver.Input.U64Hash.environment
#print axioms InitECandidate.Solver.Input.U64Hash.call_cost
