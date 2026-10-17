import InitECandidate.Solver.Input.CallNormal

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def continuationEntry {F : Type} (source target : PanSemStateFiniteExact 64 F) (name : String) (value : ValueHOL 64) :=
  setVarHOLFinite (ofString name) value {target with locals:=source.locals}

/-- Actual scoped-call return, installing arbitrary (including tuple) values,
resuming the real continuation and restoring the saved caller binding. -/
theorem return_execute {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (returned : ValueHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,returnShape))
    (enough : 1≤source.clock)
    (bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned returned),target))
    (shapePass : (shapeEqHOL (shapeOfHOLExact returned) shape && shapeEqHOL (shapeOfHOLExact returned) returnShape)=true) :
    evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation)=
      (let output:=evaluateHOLFiniteState (continuationEntry source target name returned) continuation;
        (output.1,restore source name output.2)) := by
  classical
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  simp only [args,called,if_neg (show source.clock≠0 from by omega)]
  rw [bodyRun]
  simp only [shapePass,↓reduceIte]
  rfl

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.return_execute
