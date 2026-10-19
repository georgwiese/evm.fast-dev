import InitECandidate.Solver.Input.RlpWrite.U256Value
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.Mpt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

namespace AccountNew
def body : ProgHOL 64 := match Guest.guestFn_acct_new with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "nonce",.one),(ofString "balance",Input.RlpWrite.U256Value.tupleShape),(ofString "code_hash",.one)]
def address (offset : Nat) : ExpHOL 64 := .op .add [localVar "a",.const (BitVec.ofNat 64 offset)]
def rootStore : ProgHOL 64 := .store (address 40) (.var .global (ofString "empty_trie_root"))
def hashStore : ProgHOL 64 := .store (address 48) (localVar "code_hash")
def afterRoot : ProgHOL 64 := .seq hashStore (.return (localVar "a"))
def afterBalance : ProgHOL 64 := .seq rootStore afterRoot
def afterNonce : ProgHOL 64 := .seq (.store (address 8) (localVar "balance")) afterBalance
def tail : ProgHOL 64 := .seq (.store (address 0) (localVar "nonce")) afterNonce

theorem body_shape : body=.decCall (ofString "a") .one (ofString "alloc") [.const 56#64] tail := by
  simp only [body,Guest.guestFn_acct_new,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    tail,afterNonce,afterBalance,afterRoot,rootStore,hashStore,address,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) : code.lookup (ofString "acct_new")=some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 329 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_acct_new) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,Guest.guestFn_acct_new,
    Input.RlpWrite.U256Value.tupleShape,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked
end AccountNew

namespace AccountEmpty
def body : ProgHOL 64 := match Guest.guestFn_acct_empty with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := []
def arguments : List (ExpHOL 64) := [.const 0#64,.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64],.var .global (ofString "empty_code_hash")]
theorem body_shape : body=.decCall (ofString "a") .one (ofString "acct_new") arguments (.return (localVar "a")) := by
  simp only [body,Guest.guestFn_acct_empty,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,arguments,localVar]
set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) : code.lookup (ofString "acct_empty")=some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 330 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_acct_empty) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,Guest.guestFn_acct_empty,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked
end AccountEmpty

namespace AccountCopy
def body : ProgHOL 64 := match Guest.guestFn_acct_copy with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "a",.one)]
def copyCall : ProgHOL 64 := .call (some (none,none)) (ofString "memcpy") [localVar "b",localVar "a",.const 56#64]
def tail : ProgHOL 64 := .seq copyCall (.return (localVar "b"))
theorem body_shape : body=.decCall (ofString "b") .one (ofString "alloc") [.const 56#64] tail := by
  simp only [body,Guest.guestFn_acct_copy,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,tail,copyCall,localVar]
set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) : code.lookup (ofString "acct_copy")=some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 331 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_acct_copy) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,Guest.guestFn_acct_copy,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked
end AccountCopy
end InitECandidate.Solver.Mpt

#print axioms InitECandidate.Solver.Mpt.AccountNew.body_shape
#print axioms InitECandidate.Solver.Mpt.AccountNew.original_code
#print axioms InitECandidate.Solver.Mpt.AccountEmpty.body_shape
#print axioms InitECandidate.Solver.Mpt.AccountEmpty.original_code
#print axioms InitECandidate.Solver.Mpt.AccountCopy.body_shape
#print axioms InitECandidate.Solver.Mpt.AccountCopy.original_code
