import InitECandidate.Solver.MutableTable.GetNormalCall
import InitECandidate.Solver.MutableTable.GetNoException
import InitECandidate.Solver.MutableTable.FamilySet
import InitECandidate.Solver.MutableTable.FamilyControl
import InitECandidate.Solver.MutableTable.FamilyFloorFrame
import InitECandidate.Solver.Input.GlobalFieldRead

namespace InitECandidate.Solver.GasBudget.AccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

def body : ProgHOL 64 := match Guest.guestFn_get_account_optional with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "addr", .one)]
def tableField (offset : BitVec 64) : ExpHOL 64 := .load .one (addConst (.var .global (ofString "ts")) offset)
def setArguments : List (ExpHOL 64) := [tableField 8#64, localVar "addr", .const 1#64]
def setCall : ProgHOL 64 := .call (some (none, none)) (ofString "htab_set") setArguments
def getArguments : List (ExpHOL 64) := [tableField 16#64, localVar "addr"]
def afterSet : ProgHOL 64 := match body with | .seq _ rest => rest | _ => .skip
def afterGet : ProgHOL 64 := match afterSet with | .decCall _ _ _ _ rest => rest | _ => .skip
def afterMiss : ProgHOL 64 := match afterGet with | .seq _ rest => rest | _ => .skip

theorem body_shape : body = .seq setCall afterSet := by
  simp only [body, Guest.guestFn_get_account_optional, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    setCall, setArguments, afterSet, tableField, localVar, addConst, Option.map_none]
theorem getter_shape : afterSet = .decCall (ofString "w") Get.pairShape (ofString "htab_get") getArguments afterGet := by
  simp only [body, Guest.guestFn_get_account_optional, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    afterSet, afterGet, getArguments, tableField, localVar, addConst, Get.pairShape, Option.map_none]
theorem cache_shape : afterGet = .seq
    (.ite (.cmp .notEqual (.rfield 0 (localVar "w")) (.const 0#64)) (.return (.rfield 1 (localVar "w"))) .skip) afterMiss := by
  simp only [body, Guest.guestFn_get_account_optional, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    afterSet, afterGet, afterMiss, localVar, Option.map_none]
theorem miss_shape : afterMiss = .decCall (ofString "a") .one (ofString "get_pre_state_account_optional")
    [localVar "addr"] (.return (localVar "a")) := by
  simp only [body, Guest.guestFn_get_account_optional, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    afterSet, afterGet, afterMiss, localVar, Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "get_account_optional") = some (formals, body, .one) := by
  have checked := Input.OriginalCode.indexed code installed 342 (OriginalCodeEnvironment.originalEntry Guest.guestFn_get_account_optional) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, body, formals,
    Guest.guestFn_get_account_optional, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

end InitECandidate.Solver.GasBudget.AccountOptional

#print axioms InitECandidate.Solver.GasBudget.AccountOptional.body_shape
#print axioms InitECandidate.Solver.GasBudget.AccountOptional.getter_shape
#print axioms InitECandidate.Solver.GasBudget.AccountOptional.cache_shape
#print axioms InitECandidate.Solver.GasBudget.AccountOptional.miss_shape
#print axioms InitECandidate.Solver.GasBudget.AccountOptional.original_code
