import InitECandidate.Solver.Input.CallResume
import InitECandidate.Solver.WitnessRadix.CodeEnvironment
import Guest.Model

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def unaryLocals (parameter : String) (value : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString parameter then some (.val (.word value)) else none

theorem unary_environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (fn : MlS) (parameter : String) (body : ProgHOL 64) (value : BitVec 64)
    (lookup : codeFn fn=some ([(ofString parameter,.one)],body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn fn [.val (.word value)]=some (body,callee,.one) ∧
      callee.lookup (ofString parameter)=some (.val (.word value)) := by
  have valid : (([(ofString parameter,.one)] : List (MlS×ShapeHOL)).map Prod.fst).Nodup ∧
      ([(ofString parameter,.one)] : List (MlS×ShapeHOL)).length=([.val (.word value)] : List (ValueHOL 64)).length ∧
      ((([(ofString parameter,.one)] : List (MlS×ShapeHOL)).zip [.val (.word value)]).all
        (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn fn [.val (.word value)]=some (body,unaryLocals parameter value,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn fn _ body _ .one raw
  refine ⟨callee,called,?_⟩
  rw [locals]
  simp [unaryLocals]

/-- Scalar call resumption when the real body changes only locals and clock.
The continuation entry is an exact canonical caller state, not an assumed run. -/
theorem pure_return_execute (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (fn : MlS)
    (expressions : List (ExpHOL 64)) (values : List (ValueHOL 64)) (body continuation : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (word : BitVec 64) (paid : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some values)
    (lookup : lookupCodeHOLFinite source.code.lookup fn values=some (body,callee,.one)) (enough : 1≤source.clock)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned (.val (.word word))),target))
    (frame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-1-paid}) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one fn expressions continuation)=
      let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-1-paid} name word) continuation
      (output.1,restore source name output.2) := by
  have actual:=return_execute source target name .one fn expressions values body continuation callee .one (.val (.word word)) args lookup enough run
    (by simp [shapeOfHOLExact,shapeEqHOL])
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
  have nextEq : continuationEntry source target name (.val (.word word))=bind {source with clock:=source.clock-1-paid} name word := by
    change setVarHOLFinite (ofString name) (.val (.word word)) {target with locals:=source.locals}=_
    exact congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>setVarHOLFinite (ofString name) (.val (.word word)) state) callerFrame
  rw [nextEq] at actual
  exact actual

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.pure_return_execute
#print axioms InitECandidate.Solver.Input.CallNormal.unary_environment
