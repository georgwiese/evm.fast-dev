import InitECandidate.Solver.Input.ShaFinishMemory

namespace InitECandidate.Solver.Input.ShaFixedCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def finishValues (pointer out : BitVec 64) : List (ValueHOL 64) := [.val (.word pointer),.val (.word out)]
def finishLocals (pointer out : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "out" then some (.val (.word out)) else if name=ofString "stp" then some (.val (.word pointer)) else none

theorem finish_environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (pointer out : BitVec 64)
    (code : codeFn (ofString "sha256_finish")=some (finishFormals,finishBody,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "sha256_finish") (finishValues pointer out)=some (finishBody,callee,.one) ∧
      callee.lookup (ofString "out")=some (.val (.word out)) := by
  have valid : (finishFormals.map Prod.fst).Nodup ∧ finishFormals.length=(finishValues pointer out).length ∧
      ((finishFormals.zip (finishValues pointer out)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [finishFormals,finishValues,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "sha256_finish") (finishValues pointer out)=some (finishBody,finishLocals pointer out,.one) := by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [finishLocals]⟩

/-- Actual original normal finish caller preserves every word outside its
real output32, with no condition on input SHA state or digest contents. -/
theorem finish_call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer out query : BitVec 64) (arguments : List (ExpHOL 64))
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (finishValues pointer out))
    (away : CopyGeneral.Away out query 32)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256_finish") arguments)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨callee,called,outLocal⟩ := finish_environment source.code.lookup pointer out (finish_code source.code installed)
  exact MemoryAt.call_normal source post (ofString "sha256_finish") arguments (finishValues pointer out) finishBody callee .one query args called
    (fun target value evaluated=>finish_memory (callEntryStateHOLFinite source callee) target out query installed outLocal away value evaluated) run

end InitECandidate.Solver.Input.ShaFixedCost

#print axioms InitECandidate.Solver.Input.ShaFixedCost.finish_environment
#print axioms InitECandidate.Solver.Input.ShaFixedCost.finish_call_memory
