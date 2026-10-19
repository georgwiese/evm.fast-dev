import InitECandidate.Solver.Rlp.Fail
import InitECandidate.Solver.Input.CounterLoopCost
import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Rlp.ReadLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_rlp_read_length with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "p",.one),(ofString "n",.one)]
def front : ProgHOL 64 := match body with | .seq first _ => first | _ => .skip
def guardTest : ExpHOL 64 := match front with | .ite test _ _ => test | _ => .const 0#64
def failure : ProgHOL 64 := .call (some (none,none)) (ofString "rlp_fail") [.const 2#64]
def afterGuard : ProgHOL 64 := match body with | .seq _ rest => rest | _ => .skip
def loop : ProgHOL 64 := match afterGuard with | .dec _ _ _ (.dec _ _ _ (.seq first _)) => first | _ => .skip
def accumulate : ProgHOL 64 := .assign .local (ofString "v") (.op .or
  [.shift .lsl (localVar "v") (.const 8#64),.loadByte (.op .add [localVar "p",localVar "i"])])
def increment : ProgHOL 64 := .assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def loopBody : ProgHOL 64 := .seq accumulate increment
def condition : ExpHOL 64 := .cmp .lower (localVar "i") (localVar "n")

theorem body_shape : body=.seq (.ite guardTest failure .skip) afterGuard := by
  simp only [body,front,guardTest,failure,afterGuard,Guest.guestFn_rlp_read_length,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none]

theorem after_guard_shape : afterGuard=.dec (ofString "v") .one (.const 0#64)
    (.dec (ofString "i") .one (.const 0#64) (.seq loop (.return (localVar "v")))) := by
  simp only [afterGuard,loop,body,Guest.guestFn_rlp_read_length,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]

theorem loop_shape : loop=.while condition loopBody := by
  simp only [loop,afterGuard,body,Guest.guestFn_rlp_read_length,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    condition,loopBody,accumulate,increment,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "rlp_read_length")=some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 94 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_rlp_read_length) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,
    Guest.guestFn_rlp_read_length,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem loop_body_price (code) : Input.ClockCost.Bound code loopBody 0 :=
  Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.assign code _ _) (Input.ClockCost.assign code _ _)

theorem loop_body_limit : Input.LocalPrefix (ofString "n") loopBody :=
  .seq (.assign _ _ (by decide)) (.assign _ _ (by decide))

theorem loop_body_advance : Input.CounterFlow.Advances (ofString "i") 1 loopBody :=
  Input.CounterFlow.sequence (ofString "i") accumulate increment 0 1
    (Input.CounterFlow.preserved _ _ (.assign _ _ (by decide))) (Input.CounterFlow.increment _)

end InitECandidate.Solver.Rlp.ReadLength

#print axioms InitECandidate.Solver.Rlp.ReadLength.body_shape
#print axioms InitECandidate.Solver.Rlp.ReadLength.after_guard_shape
#print axioms InitECandidate.Solver.Rlp.ReadLength.loop_shape
#print axioms InitECandidate.Solver.Rlp.ReadLength.original_code
#print axioms InitECandidate.Solver.Rlp.ReadLength.loop_body_price
#print axioms InitECandidate.Solver.Rlp.ReadLength.loop_body_limit
#print axioms InitECandidate.Solver.Rlp.ReadLength.loop_body_advance
