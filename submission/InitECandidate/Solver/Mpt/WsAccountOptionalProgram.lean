import InitECandidate.Solver.Mpt.AccountDecodeCall
import InitECandidate.Solver.Mpt.TrieWalkProgram

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_ws_get_account_optional with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS × ShapeHOL) := [(ofString "addr",.one)]
private def callRest : ProgHOL 64 → ProgHOL 64 | .decCall _ _ _ _ rest=>rest | _=>.skip
private def seqRest : ProgHOL 64 → ProgHOL 64 | .seq _ rest=>rest | _=>.skip
def afterLeaf := callRest body
def afterGuard := seqRest afterLeaf
def afterAlloc := callRest afterGuard
def field (index : Nat) : ExpHOL 64 := .rfield index (localVar "leaf")
def decodeArguments : List (ExpHOL 64) := [field 1,field 2,localVar "a"]
def decode : ProgHOL 64 := .call (some (none,none)) (ofString "decode_account_from_leaf") decodeArguments

theorem body_shape : body=.decCall (ofString "leaf") TrieWalk.resultShape (ofString "ws_account_leaf") [localVar "addr"] afterLeaf := by
  simp only [body,afterLeaf,callRest,TrieWalk.resultShape,Guest.guestFn_ws_get_account_optional,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]
theorem after_leaf_shape : afterLeaf=.seq (.ite (.cmp .equal (field 0) (.const 0#64)) (.return (.const 1#64)) .skip) afterGuard := by
  simp only [afterLeaf,afterGuard,body,callRest,seqRest,field,Guest.guestFn_ws_get_account_optional,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]
theorem after_guard_shape : afterGuard=.decCall (ofString "a") .one (ofString "alloc") [.const 56#64] afterAlloc := by
  simp only [afterLeaf,afterGuard,afterAlloc,body,callRest,seqRest,Guest.guestFn_ws_get_account_optional,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
theorem after_alloc_shape : afterAlloc=.seq decode (.return (localVar "a")) := by
  simp only [afterLeaf,afterGuard,afterAlloc,body,callRest,seqRest,decode,decodeArguments,field,Guest.guestFn_ws_get_account_optional,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "ws_get_account_optional")=some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 334 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_ws_get_account_optional) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,Guest.guestFn_ws_get_account_optional,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.body_shape
#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.after_leaf_shape
#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.after_guard_shape
#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.after_alloc_shape
#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.original_code
