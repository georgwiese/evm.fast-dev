import InitECandidate.Solver.Mpt.AccountBalanceSetProgram

namespace InitECandidate.Solver.Mpt.AccountNonceIncrement
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_increment_nonce with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "addr",.one)]
def copyCall : ProgHOL 64 := AccountBalanceSet.copyCall
def nonceStore : ProgHOL 64 := .store (.op .add [localVar "a",.const 0#64])
  (.op .add [.load .one (.op .add [localVar "a",.const 0#64]),.const 1#64])
def commitCall : ProgHOL 64 := AccountBalanceSet.commitCall
def afterCopy : ProgHOL 64 := .seq nonceStore (.seq commitCall (.return (.const 0#64)))
def afterGet : ProgHOL 64 := .seq copyCall afterCopy

theorem body_shape : body = .decCall (ofString "a") .one (ofString "get_account") [localVar "addr"] afterGet := by
  simp only [body,afterGet,afterCopy,copyCall,nonceStore,commitCall,AccountBalanceSet.copyCall,AccountBalanceSet.commitCall,localVar,Guest.guestFn_increment_nonce,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "increment_nonce") = some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 366 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_increment_nonce) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,Guest.guestFn_increment_nonce,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Mpt.AccountNonceIncrement

#print axioms InitECandidate.Solver.Mpt.AccountNonceIncrement.body_shape
#print axioms InitECandidate.Solver.Mpt.AccountNonceIncrement.original_code
