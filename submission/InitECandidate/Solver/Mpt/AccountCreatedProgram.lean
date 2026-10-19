import InitECandidate.Solver.GasBudget.JournalZoneSetValues
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.Mpt.AccountCreated
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

def body : ProgHOL 64 := match Guest.guestFn_mark_account_created with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "addr",.one)]
def table : ExpHOL 64 := .load .one (.op .add [.var .global (ofString "ts"),.const 56#64])
def mutation : ProgHOL 64 := .call (some (none,none)) (ofString "htab_set") [table,localVar "addr",.const 1#64]

theorem body_shape : body = .seq mutation (.return (.const 0#64)) := by
  simp only [body,table,mutation,localVar,Guest.guestFn_mark_account_created,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "mark_account_created") = some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 361 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_mark_account_created) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,Guest.guestFn_mark_account_created,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem set_price (population : Nat) : Set.noGrowthPrice .account population + 1 = 9 * population + 12 := by
  simp [Set.noGrowthPrice,Insert.findPrice,Insert.rawPrice,Find.generalProbePrice,KeyHash.keySize,KeyHash.hashPrice,MemeqByteRuntime.price]
  omega

end InitECandidate.Solver.Mpt.AccountCreated

#print axioms InitECandidate.Solver.Mpt.AccountCreated.body_shape
#print axioms InitECandidate.Solver.Mpt.AccountCreated.original_code
#print axioms InitECandidate.Solver.Mpt.AccountCreated.set_price
