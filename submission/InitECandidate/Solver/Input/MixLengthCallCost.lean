import InitECandidate.Solver.Input.MixLengthCost

namespace InitECandidate.Solver.Input.MixLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def values (root len out : BitVec 64) : List (ValueHOL 64) := [.val (.word root),.val (.word len),.val (.word out)]
def rawLocals (root len out : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "out" then some (.val (.word out)) else if name=ofString "len" then some (.val (.word len))
  else if name=ofString "root" then some (.val (.word root)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (root len out : BitVec 64)
    (code : codeFn (ofString "mix_in_length")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "mix_in_length") (values root len out)=some (body,callee,.one) ∧
      callee.lookup (ofString "root")=some (.val (.word root)) ∧ callee.lookup (ofString "out")=some (.val (.word out)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values root len out).length ∧
      ((formals.zip (values root len out)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "mix_in_length") (values root len out)=some (body,rawLocals root len out,.one) := by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [rawLocals,show ofString "root"≠ofString "out" from by decide,show ofString "root"≠ofString "len" from by decide],by rw [locals]; simp [rawLocals]⟩

/-- Actual original length-mixing caller costs59 source ticks, including
all zero/write/hash paths and every possible caller/callee outcome. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root len out chunk stp accel : BitVec 64)
    (workspace : ShaPair.Workspace source stp accel)
    (chunkLocal : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (rootArena : AllocatedBytes.Arena root 32) (chunkArena : AllocatedBytes.Arena chunk 32) (aligned : chunk.toNat%8=0)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values root len out)) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "mix_in_length") arguments)).2.clock≤59 := by
  obtain ⟨callee,called,rootLocal,outLocal⟩ := environment source.code.lookup root len out (original_code source.code workspace.installed)
  have actual : Ready (callEntryStateHOLFinite source callee) root out chunk stp accel := ⟨rootLocal,outLocal,chunkLocal,ShaPair.Workspace.at_callee source callee stp accel workspace⟩
  have price := body_cost (callEntryStateHOLFinite source callee) root out chunk stp accel actual rootArena chunkArena aligned
  exact ClockCost.call_current source destination (ofString "mix_in_length") arguments (values root len out) body callee .one 58 args called price

end InitECandidate.Solver.Input.MixLength

#print axioms InitECandidate.Solver.Input.MixLength.environment
#print axioms InitECandidate.Solver.Input.MixLength.call_cost
