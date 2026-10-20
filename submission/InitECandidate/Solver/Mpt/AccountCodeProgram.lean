import InitECandidate.Solver.Mpt.AccountCommitProgram
import InitECandidate.Solver.Input.DecCallFallthroughReturn

namespace InitECandidate.Solver.Mpt.AccountCode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable GasBudget

def body : ProgHOL 64 := match Guest.guestFn_set_code with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "addr",.one),(ofString "code",.one),(ofString "code_len",.one)]
def copyCall : ProgHOL 64 := .call (some (some (.local,ofString "a"),none)) (ofString "acct_copy") [localVar "a"]
def commitCall : ProgHOL 64 := .call (some (none,none)) (ofString "modify_state_commit") [localVar "addr",localVar "a"]
def hashStore : ProgHOL 64 := .store (.op .add [localVar "a",.const 48#64]) (localVar "h")
def afterCopy : ProgHOL 64 := .seq hashStore (.seq commitCall (.return (.const 0#64)))
def afterGet : ProgHOL 64 := .seq copyCall afterCopy
def afterBranch : ProgHOL 64 := .decCall (ofString "a") .one (ofString "get_account") [localVar "addr"] afterGet
def sliceStores : ProgHOL 64 := .seq (.store (localVar "sl") (localVar "code"))
  (.store (.op .add [localVar "sl",.const 8#64]) (localVar "code_len"))
def codeSetCall : ProgHOL 64 := .call (some (none,none)) (ofString "jset")
  [.load .one (.op .add [.var .global (ofString "ts"),.const 48#64]),localVar "h",localVar "sl"]
def nonemptyBranch : ProgHOL 64 := .decCall (ofString "sl") .one (ofString "alloc") [.const 16#64]
  (.seq (.store (localVar "sl") (localVar "code"))
    (.seq (.store (.op .add [localVar "sl",.const 8#64]) (localVar "code_len")) codeSetCall))
def afterCompare : ProgHOL 64 := .seq (.ite (.cmp .equal (localVar "eq") (.const 0#64)) nonemptyBranch .skip) afterBranch
def afterHash : ProgHOL 64 := .decCall (ofString "eq") .one (ofString "memeq")
  [localVar "h",.var .global (ofString "empty_code_hash"),.const 32#64] afterCompare
def hashCall : ProgHOL 64 := .call (some (none,none)) (ofString "keccak256") [localVar "code",localVar "code_len",localVar "h"]
def afterAllocation : ProgHOL 64 := .seq hashCall afterHash

theorem nonempty_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    evaluateHOLFiniteState source nonemptyBranch = evaluateHOLFiniteState source
      (.decCall (ofString "sl") .one (ofString "alloc") [.const 16#64] (.seq sliceStores codeSetCall)) := by
  apply Input.CallNormal.continuation_congr
  intro state
  exact (MemeqByteRuntime.sequence_assoc state (.store (localVar "sl") (localVar "code"))
    (.store (.op .add [localVar "sl",.const 8#64]) (localVar "code_len")) codeSetCall).symm

theorem body_shape : body = .decCall (ofString "h") .one (ofString "alloc") [.const 32#64] afterAllocation := by
  simp only [body,afterAllocation,hashCall,afterHash,afterCompare,nonemptyBranch,codeSetCall,afterBranch,afterGet,copyCall,afterCopy,hashStore,commitCall,
    localVar,Guest.guestFn_set_code,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "set_code") = some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 367 (OriginalCodeEnvironment.originalEntry Guest.guestFn_set_code) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,Guest.guestFn_set_code,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Mpt.AccountCode

#print axioms InitECandidate.Solver.Mpt.AccountCode.body_shape
#print axioms InitECandidate.Solver.Mpt.AccountCode.original_code
#print axioms InitECandidate.Solver.Mpt.AccountCode.nonempty_execute
