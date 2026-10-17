import InitECandidate.Solver.Input.SszFail

namespace InitECandidate.Solver.Input.Offsets
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_ssz_check_offsets with
  | .function fn=>progToHOL fn.body | _=>.skip
def loop : ProgHOL 64 := match body with
  | .seq _ (.dec _ _ _ (.seq loop _))=>loop | _=>.skip
def loopBody : ProgHOL 64 := match loop with | .while _ code=>code | _=>.skip
def lastTest : ExpHOL 64 := .cmp .notEqual (.load .one (localVar "offs")) (localVar "fixed")
def lastGuard : ProgHOL 64 := .ite lastTest (.call (some (none,none)) (ofString "ssz_fail") [.const 12#64]) .skip
def returnZero : ProgHOL 64 := .return (.const 0#64)
def tailCode : ProgHOL 64 := .seq lastGuard returnZero

theorem body_shape : body=.seq (.ite (.cmp .equal (localVar "n") (.const 0#64)) returnZero .skip)
    (.dec (ofString "i") .one (.const 0#64) (.seq loop tailCode)) := by
  simp only [body,loop,Guest.guestFn_ssz_check_offsets,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    localVar,tailCode,lastGuard,lastTest,returnZero,Option.map_none]

theorem last_test_read {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer first fixed : BitVec 64)
    (pointerLocal : source.locals.lookup (ofString "offs")=some (.val (.word pointer)))
    (fixedLocal : source.locals.lookup (ofString "fixed")=some (.val (.word fixed)))
    (mapped : source.memaddrs pointer) (cell : source.memory pointer=.word first) :
    eval source lastTest=some (.val (.word (if first=fixed then 0#64 else 1#64))) := by
  classical
  simp [eval,lastTest,localVar,evalHOLExact,toExact,pointerLocal,fixedLocal,
    isWfShapeExactHOL,memLoadHOLExact,mapped,cell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

/-- The literal final equality guard returns zero exactly when the first
container offset equals its fixed-part size; mismatch raises real SszErr. -/
theorem tail_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer first fixed : BitVec 64)
    (pointerLocal : source.locals.lookup (ofString "offs")=some (.val (.word pointer)))
    (fixedLocal : source.locals.lookup (ofString "fixed")=some (.val (.word fixed)))
    (mapped : source.memaddrs pointer) (cell : source.memory pointer=.word first)
    (lookup : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source tailCode=
      if first=fixed then (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite source)
      else (some (.exception (ofString "SszErr") (.val (.word 12#64))),emptyLocalsHOLFinite {source with clock:=source.clock-1}) := by
  classical
  have test:=last_test_read source pointer first fixed pointerLocal fixedLocal mapped cell
  simp only [eval] at test
  by_cases same : first=fixed
  · simp only [if_pos same] at test ⊢
    have guarded : evaluateHOLFiniteState source lastGuard=(none,source) := by
      rw [lastGuard,evaluateHOLFiniteState_ite,test]
      simp
    rw [tailCode,WitnessRadix.StateSteps.next_sequence source source _ _ guarded (Nat.le_refl _)]
    simp [returnZero,evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  · simp only [if_neg same] at test ⊢
    have failRun:=SszFail.call_execute source 12#64 lookup exceptionShape enough
    have guarded : evaluateHOLFiniteState source lastGuard=
        (some (.exception (ofString "SszErr") (.val (.word 12#64))),emptyLocalsHOLFinite {source with clock:=source.clock-1}) := by
      rw [lastGuard,evaluateHOLFiniteState_ite,test]
      simpa using failRun
    rw [tailCode,WitnessRadix.StateSteps.stopped_sequence source _ _ _ _ guarded (by change source.clock-1≤source.clock; omega)]

end InitECandidate.Solver.Input.Offsets

#print axioms InitECandidate.Solver.Input.Offsets.body_shape
#print axioms InitECandidate.Solver.Input.Offsets.last_test_read
#print axioms InitECandidate.Solver.Input.Offsets.tail_execute
