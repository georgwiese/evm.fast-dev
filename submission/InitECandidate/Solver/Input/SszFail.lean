import Guest.SoftwareAst
import InitECandidate.Solver.WitnessRadix.CodeEnvironment
import InitECandidate.Solver.WitnessRadix.StateSteps
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace InitECandidate.Solver.Input.SszFail
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_ssz_fail with
  | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "code",.one)]
def values (code : BitVec 64) : List (ValueHOL 64) := [.val (.word code)]
def rawLocals (code : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "code" then some (.val (.word code)) else none

theorem body_shape : body=.seq (.raise (ofString "SszErr") (localVar "code")) (.return (.const 0#64)) := by
  simp only [body,Guest.Software.guestFn_ssz_fail,progToHOL,expToHOL,shapeToHOL,localVar]

theorem execute {F : Type} (source : PanSemStateFiniteExact 64 F) (code : BitVec 64)
    (codeLocal : source.locals.lookup (ofString "code")=some (.val (.word code)))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) :
    evaluateHOLFiniteState source body=
      (some (.exception (ofString "SszErr") (.val (.word code))),emptyLocalsHOLFinite source) := by
  classical
  have raised : evaluateHOLFiniteState source (.raise (ofString "SszErr") (localVar "code"))=
      (some (.exception (ofString "SszErr") (.val (.word code))),emptyLocalsHOLFinite source) := by
    simp [evaluateHOLFiniteState_raise,exceptionShape,evalHOLExact,localVar,toExact,codeLocal,
      shapeOfHOLExact,sizeOfShapeWithContextHOL]
  rw [body_shape,WitnessRadix.StateSteps.stopped_sequence source (emptyLocalsHOLFinite source) _ _ _ raised (Nat.le_refl _)]

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (code : BitVec 64)
    (lookup : codeFn (ofString "ssz_fail")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "ssz_fail") (values code)=some (body,callee,.one) ∧
      callee.lookup (ofString "code")=some (.val (.word code)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values code).length ∧
      ((formals.zip (values code)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "ssz_fail") (values code)=some (body,rawLocals code,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_⟩
  rw [locals]
  simp [rawLocals]

/-- Real decoder-failure call raises SszErr and cannot resume its continuation.
The exception shape and actual code lookup are explicit reachable premises. -/
theorem call_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (code : BitVec 64)
    (lookup : source.code.lookup (ofString "ssz_fail")=some (formals,body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "ssz_fail") [.const code])=
      (some (.exception (ofString "SszErr") (.val (.word code))),emptyLocalsHOLFinite {source with clock:=source.clock-1}) := by
  classical
  obtain ⟨callee,called,localCode⟩:=environment source.code.lookup code lookup
  let entry:=callEntryStateHOLFinite source callee
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [.const code]=some (values code) := rfl
  have bodyRun:=execute entry code localCode exceptionShape
  have run:=evaluateHOLFiniteState_call_exception_no_handler source none (ofString "ssz_fail") [.const code]
    (values code) body callee .one (ofString "SszErr") (.val (.word code)) (emptyLocalsHOLFinite entry)
    args called (by omega) bodyRun
  exact run

end InitECandidate.Solver.Input.SszFail

#print axioms InitECandidate.Solver.Input.SszFail.body_shape
#print axioms InitECandidate.Solver.Input.SszFail.execute
#print axioms InitECandidate.Solver.Input.SszFail.environment
#print axioms InitECandidate.Solver.Input.SszFail.call_execute
