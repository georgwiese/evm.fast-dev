import InitECandidate.Solver.Mpt.TrieLookupCall
import InitECandidate.Solver.Mpt.TrieWalkGraphHash
import InitECandidate.Solver.Input.HeapScopeCost
import InitECandidate.Solver.WitnessRadix.Keccak256EntryFields

namespace InitECandidate.Solver.Mpt.WsAccountLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_ws_account_leaf with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "addr",.one)]
def hashArguments : List (ExpHOL 64) := [localVar "addr",.const 20#64,localVar "h"]
def hash : ProgHOL 64 := .call (some (none,none)) (ofString "keccak256") hashArguments
def lookupArguments : List (ExpHOL 64) := [.load .one (.op .add [.var .global (ofString "ws"),.const 24#64]),localVar "h"]
def finish : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) (.return (localVar "r"))
def lookup : ProgHOL 64 := .decCall (ofString "r") TrieWalk.resultShape (ofString "trie_lookup") lookupArguments finish
def afterAlloc : ProgHOL 64 := .seq hash lookup
def afterMark : ProgHOL 64 := .decCall (ofString "h") .one (ofString "alloc") [.const 32#64] afterAlloc

theorem body_shape : body=.decCall (ofString "mark") .one (ofString "heap_mark") [] afterMark := by
  simp only [body,afterMark,afterAlloc,hash,hashArguments,lookup,lookupArguments,finish,TrieWalk.resultShape,
    Guest.guestFn_ws_account_leaf,progToHOL,expToHOL,shapeToHOL,localVar,List.map_cons,List.map_nil,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "ws_account_leaf")=some (formals,body,TrieWalk.resultShape) := by
  have checked := Input.OriginalCode.indexed code installed 333 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_ws_account_leaf) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,TrieWalk.resultShape,
    Guest.guestFn_ws_account_leaf,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem hash_original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "keccak256")=some (WitnessRadix.Keccak256.formals,WitnessRadix.Keccak256.body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 92 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_keccak256) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,WitnessRadix.Keccak256.body,WitnessRadix.Keccak256.formals,
    Guest.guestFn_keccak256,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem hash_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (addr h : BitVec 64)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word addr)))
    (outputCell : source.locals.lookup (ofString "h")=some (.val (.word h))) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) hashArguments=some (WitnessRadix.Keccak256.values addr h 20) := by
  simp [hashArguments,WitnessRadix.Keccak256.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressCell,outputCell]

theorem lookup_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root h : BitVec 64)
    (worldState : source.globals.lookup (ofString "ws")=some (.val (.word ws)))
    (rootMapped : source.memaddrs (ws+24#64)) (rootStored : source.memory (ws+24#64)=.word root)
    (outputCell : source.locals.lookup (ofString "h")=some (.val (.word h))) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) lookupArguments=some (TrieLookup.values root h) := by
  simp [lookupArguments,TrieLookup.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,worldState,rootMapped,rootStored,
    outputCell,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact]

theorem finish_cost (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code finish 1 :=
  Input.ClockCost.sequence code _ _ 1 0 (Input.HeapScope.release_call_cost code installed (some none) _) (Input.ClockCost.returned code _)

end InitECandidate.Solver.Mpt.WsAccountLeaf

#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.body_shape
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.original_code
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.hash_original_code
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.hash_arguments
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.lookup_arguments
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.finish_cost
