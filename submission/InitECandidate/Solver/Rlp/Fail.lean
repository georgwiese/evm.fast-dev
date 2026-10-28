import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.NoReturnScoped
import InitECandidate.Solver.Input.NoNamedException
import InitECandidate.Solver.Input.ClockCostCall
import InitECandidate.Solver.Input.IgnoredCallData

namespace InitECandidate.Solver.Rlp.Fail
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_rlp_fail with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "code", .one)]
theorem body_shape : body = .seq (.raise (ofString "RlpErr") (localVar "code")) (.return (.const 0#64)) := by
  simp only [body, Guest.Software.guestFn_rlp_fail, progToHOL, expToHOL, localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "rlp_fail") = some (formals, body, .one) := by
  have checked := Input.OriginalCode.indexed code installed 93 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_rlp_fail) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, body, formals,
    Guest.Software.guestFn_rlp_fail, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

theorem never_returns : Input.NoReturn.Never body := by
  rw [body_shape]
  exact Input.NoReturn.raised_sequence _ _ _

theorem readonly (code) : Input.LocalEffects.Preserves code body := by
  rw [body_shape]
  exact Input.LocalEffects.sequence code _ _ (Input.LocalEffects.raised code _ _) (Input.LocalEffects.returned code _)

theorem price (code) : Input.ClockCost.Bound code body 0 := by
  rw [body_shape]
  exact Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.raised code _ _) (Input.ClockCost.returned code _)

theorem no_other_exception (code) (forbidden : MlS) (other : ofString "RlpErr" ≠ forbidden) :
    Input.NoNamedException.Safe code forbidden body := by
  rw [body_shape]
  exact Input.NoNamedException.sequence code forbidden _ _
    (Input.NoNamedException.raised_other code forbidden _ _ other)
    (Input.NoNamedException.of_all code forbidden _ (Input.NoException.returned code _))

theorem call_not_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : Input.OriginalCode.Installed source.code) (arguments : List (ExpHOL 64))
    (run : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "rlp_fail") arguments) = (none, post)) : False := by
  obtain ⟨positive, values, actual, callee, shape, target, returned, args, called, bodyRun, checked, postEq, fields⟩ :=
    Input.CallNormal.ignored_data source post (ofString "rlp_fail") arguments run
  have bodyEq := Input.LocalEffects.lookup_body source.code (ofString "rlp_fail") formals body .one
    (original_code source.code installed) values actual callee shape called
  rw [bodyEq] at bodyRun
  exact never_returns (callEntryStateHOLFinite source callee) returned (congrArg Prod.fst bodyRun)

theorem call_price (code) (installed : Input.OriginalCode.Installed code) (arguments : List (ExpHOL 64)) :
    Input.ClockCost.Bound code (.call (some (none, none)) (ofString "rlp_fail") arguments) 1 :=
  Input.ClockCost.call_body code (some none) (ofString "rlp_fail") arguments formals body .one 0
    (original_code code installed) (price code)

end InitECandidate.Solver.Rlp.Fail

#print axioms InitECandidate.Solver.Rlp.Fail.body_shape
#print axioms InitECandidate.Solver.Rlp.Fail.original_code
#print axioms InitECandidate.Solver.Rlp.Fail.never_returns
#print axioms InitECandidate.Solver.Rlp.Fail.readonly
#print axioms InitECandidate.Solver.Rlp.Fail.price
#print axioms InitECandidate.Solver.Rlp.Fail.no_other_exception
#print axioms InitECandidate.Solver.Rlp.Fail.call_not_normal
#print axioms InitECandidate.Solver.Rlp.Fail.call_price
