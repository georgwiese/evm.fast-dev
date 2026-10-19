import InitECandidate.Solver.GasBudget.AccountOptionalProgram

namespace InitECandidate.Solver.GasBudget.AccountCache
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

inductive Kind where | transaction | preState
def Kind.original : Kind → Decl (BitVec 64)
  | .transaction => Guest.guestFn_get_account_optional
  | .preState => Guest.guestFn_get_pre_state_account_optional
def Kind.readerGlobal : Kind → String | .transaction => "ts" | .preState => "bs"
def Kind.name : Kind → MlS | .transaction => ofString "get_account_optional" | .preState => ofString "get_pre_state_account_optional"
def Kind.body (kind : Kind) : ProgHOL 64 := match kind.original with | .function fn => progToHOL fn.body | _ => .skip
abbrev formals := AccountOptional.formals
abbrev setArguments := AccountOptional.setArguments
abbrev setCall := AccountOptional.setCall
def Kind.getArguments (kind : Kind) : List (ExpHOL 64) :=
  [.load .one (addConst (.var .global (ofString kind.readerGlobal)) 16#64), localVar "addr"]
def Kind.afterSet (kind : Kind) : ProgHOL 64 := match kind.body with | .seq _ rest => rest | _ => .skip
def Kind.afterGet (kind : Kind) : ProgHOL 64 := match kind.afterSet with | .decCall _ _ _ _ rest => rest | _ => .skip
def Kind.afterMiss (kind : Kind) : ProgHOL 64 := match kind.afterGet with | .seq _ rest => rest | _ => .skip

theorem Kind.body_shape (kind : Kind) : kind.body = .seq setCall kind.afterSet := by
  cases kind <;> simp only [Kind.body, Kind.original, Kind.afterSet, Guest.guestFn_get_account_optional,
    Guest.guestFn_get_pre_state_account_optional, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    setCall, setArguments, AccountOptional.setCall, AccountOptional.setArguments, AccountOptional.tableField,
    localVar, addConst, Option.map_none]
theorem Kind.getter_shape (kind : Kind) : kind.afterSet = .decCall (ofString "w") Get.pairShape (ofString "htab_get") kind.getArguments kind.afterGet := by
  cases kind <;> simp only [Kind.body, Kind.original, Kind.readerGlobal, Kind.afterSet, Kind.afterGet, Kind.getArguments,
    Guest.guestFn_get_account_optional, Guest.guestFn_get_pre_state_account_optional, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, localVar, addConst, Get.pairShape, Option.map_none]
theorem Kind.cache_shape (kind : Kind) : kind.afterGet = .seq
    (.ite (.cmp .notEqual (.rfield 0 (localVar "w")) (.const 0#64)) (.return (.rfield 1 (localVar "w"))) .skip) kind.afterMiss := by
  cases kind <;> simp only [Kind.body, Kind.original, Kind.afterSet, Kind.afterGet, Kind.afterMiss,
    Guest.guestFn_get_account_optional, Guest.guestFn_get_pre_state_account_optional, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, localVar, Option.map_none]

theorem pre_state_miss_shape : Kind.preState.afterMiss = .seq
    (.call (some (none, none)) (ofString "record_pre_state_read") [localVar "addr"])
    (.decCall (ofString "a") .one (ofString "ws_get_account_optional") [localVar "addr"] (.return (localVar "a"))) := by
  simp only [Kind.body, Kind.original, Kind.afterSet, Kind.afterGet, Kind.afterMiss,
    Guest.guestFn_get_pre_state_account_optional, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, localVar, Option.map_none]

set_option maxRecDepth 100000 in
theorem Kind.original_code (kind : Kind) (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup kind.name = some (formals, kind.body, .one) := by
  cases kind with
  | transaction => exact AccountOptional.original_code code installed
  | preState =>
    have checked := Input.OriginalCode.indexed code installed 340
      (OriginalCodeEnvironment.originalEntry Guest.guestFn_get_pre_state_account_optional) (by rfl)
    simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Kind.body, Kind.original, Kind.name,
      formals, AccountOptional.formals, Guest.guestFn_get_pre_state_account_optional, shapeToHOL, paramToHOL,
      List.map_cons, List.map_nil] using checked

end InitECandidate.Solver.GasBudget.AccountCache

#print axioms InitECandidate.Solver.GasBudget.AccountCache.Kind.body_shape
#print axioms InitECandidate.Solver.GasBudget.AccountCache.Kind.getter_shape
#print axioms InitECandidate.Solver.GasBudget.AccountCache.Kind.cache_shape
#print axioms InitECandidate.Solver.GasBudget.AccountCache.pre_state_miss_shape
#print axioms InitECandidate.Solver.GasBudget.AccountCache.Kind.original_code
