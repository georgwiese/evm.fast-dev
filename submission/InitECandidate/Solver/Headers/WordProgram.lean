import InitECandidate.Solver.Headers.FieldChecks
import InitECandidate.Solver.Input.CounterExpressionLoopCost
import InitECandidate.Solver.Input.ClockCostGuardReached

namespace InitECandidate.Solver.Headers.WordField
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_hdr_word_field with | .function fn=>progToHOL fn.body | _=>.skip
def afterField : ProgHOL 64 := match body with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterGuard : ProgHOL 64 := match afterField with | .seq _ rest=>rest | _=>.skip
def arguments : List (ExpHOL 64) := [localVar "arr",localVar "i",.const 0#64]
def guardTest : ExpHOL 64 := .cmp .lower (.const 8#64) (.rfield 1 (localVar "f"))
def loop : ProgHOL 64 := match afterGuard with | .dec _ _ _ (.dec _ _ _ (.seq first _))=>first | _=>.skip
def accumulate : ProgHOL 64 := .assign .local (ofString "v") (.op .or
  [.shift .lsl (localVar "v") (.const 8#64),.loadByte (.op .add [.rfield 0 (localVar "f"),localVar "j"])])
def increment : ProgHOL 64 := .assign .local (ofString "j") (.op .add [localVar "j",.const 1#64])
def loopBody : ProgHOL 64 := .seq accumulate increment
def condition : ExpHOL 64 := .cmp .lower (localVar "j") (.rfield 1 (localVar "f"))

theorem body_shape : body=.decCall (ofString "f") (.comb [.one,.one]) (ofString "hdr_uint_field") arguments afterField := by
  simp only [body,afterField,arguments,localVar,Guest.Software.guestFn_hdr_word_field,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
theorem field_shape : afterField=.seq (.ite guardTest (.raise (ofString "HdrErr") (.const 4#64)) .skip) afterGuard := by
  simp only [afterField,afterGuard,body,guardTest,localVar,Guest.Software.guestFn_hdr_word_field,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
theorem after_guard_shape : afterGuard=.dec (ofString "v") .one (.const 0#64)
    (.dec (ofString "j") .one (.const 0#64) (.seq loop (.return (localVar "v")))) := by
  simp only [afterGuard,afterField,body,loop,localVar,Guest.Software.guestFn_hdr_word_field,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
theorem loop_shape : loop=.while condition loopBody := by
  simp only [loop,afterGuard,afterField,body,condition,loopBody,accumulate,increment,localVar,
    Guest.Software.guestFn_hdr_word_field,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

set_option maxRecDepth 100000 in
/-- Literal original word-field decoder204. -/
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "hdr_word_field")=some (Field.Kind.raw.formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 204 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_hdr_word_field) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Field.Kind.formals,body,
    Guest.Software.guestFn_hdr_word_field,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem loop_body_price (code) : Input.ClockCost.Bound code loopBody 0 :=
  Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.assign code _ _) (Input.ClockCost.assign code _ _)
theorem loop_body_snapshot : Input.LocalPrefix (ofString "f") loopBody :=
  .seq (.assign _ _ (by decide)) (.assign _ _ (by decide))
theorem loop_body_advance : Input.CounterFlow.Advances (ofString "j") 1 loopBody :=
  Input.CounterFlow.sequence (ofString "j") accumulate increment 0 1
    (Input.CounterFlow.preserved _ _ (.assign _ _ (by decide))) (Input.CounterFlow.increment _)

end InitECandidate.Solver.Headers.WordField

#print axioms InitECandidate.Solver.Headers.WordField.body_shape
#print axioms InitECandidate.Solver.Headers.WordField.field_shape
#print axioms InitECandidate.Solver.Headers.WordField.after_guard_shape
#print axioms InitECandidate.Solver.Headers.WordField.loop_shape
#print axioms InitECandidate.Solver.Headers.WordField.original_code
#print axioms InitECandidate.Solver.Headers.WordField.loop_body_price
#print axioms InitECandidate.Solver.Headers.WordField.loop_body_snapshot
#print axioms InitECandidate.Solver.Headers.WordField.loop_body_advance
