import InitECandidate.Solver.Mpt.AccountBalanceStoreCommit
import InitECandidate.Solver.Mpt.AccountBalanceSetPrice

namespace InitECandidate.Solver.Mpt.AccountEtherCreate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable GasBudget

def body : ProgHOL 64 := match Guest.guestFn_create_ether with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := AccountBalanceSet.formals
def copyCall : ProgHOL 64 := AccountBalanceSet.copyCall
def addArguments : List (ExpHOL 64) := [.load Input.RlpWrite.U256Value.tupleShape (.op .add [localVar "a",.const 8#64]),localVar "amount"]
def afterCopy : ProgHOL 64 := .decCall (ofString "nb") Input.RlpWrite.U256Value.tupleShape (ofString "u256_add") addArguments (AccountBalanceSet.afterBalance (localVar "nb"))
def afterGet : ProgHOL 64 := .seq copyCall afterCopy

theorem body_shape : body = .decCall (ofString "a") .one (ofString "get_account") [localVar "addr"] afterGet := by
  simp only [body,afterGet,afterCopy,copyCall,addArguments,AccountBalanceSet.copyCall,AccountBalanceSet.afterBalance,AccountBalanceSet.storeBalance,AccountBalanceSet.commitCall,
    Input.RlpWrite.U256Value.tupleShape,localVar,Guest.guestFn_create_ether,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "create_ether") = some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 364 (OriginalCodeEnvironment.originalEntry Guest.guestFn_create_ether) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,AccountBalanceSet.formals,Input.RlpWrite.U256Value.tupleShape,Guest.guestFn_create_ether,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

def suffixPrice (markers outers accounts : Nat) (destroyed found : Bool) (iterations : Nat) : Nat :=
  AccountBalanceSet.suffixPrice markers outers accounts destroyed found iterations + 1

theorem suffix_price_mono (markers outers accounts bound : Nat) (markersBound : markers ≤ bound) (outersBound : outers ≤ bound) (accountsBound : accounts ≤ bound)
    (destroyed found : Bool) (iterations : Nat) :
    suffixPrice markers outers accounts destroyed found iterations ≤ suffixPrice bound bound bound destroyed found iterations :=
  Nat.add_le_add_right (AccountBalanceSet.suffix_price_mono markers outers accounts bound markersBound outersBound accountsBound destroyed found iterations) 1

def wholePrice (population : Nat) (destroyed found : Bool) (iterations : Nat) : Nat :=
  43 * population + 31152 + suffixPrice (population + 3) (population + 3) (population + 3) destroyed found iterations

end InitECandidate.Solver.Mpt.AccountEtherCreate

#print axioms InitECandidate.Solver.Mpt.AccountEtherCreate.body_shape
#print axioms InitECandidate.Solver.Mpt.AccountEtherCreate.original_code
#print axioms InitECandidate.Solver.Mpt.AccountEtherCreate.suffix_price_mono
