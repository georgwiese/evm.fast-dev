import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.PanState

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_decode_witness_to_mpt with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "db",.one),(ofString "root_hash",.one)]
def afterCompare : ProgHOL 64 := match body with | .decCall _ _ _ _ rest=>rest | _=>.skip
def lookupCall : ProgHOL 64 := match afterCompare with | .seq _ rest=>rest | _=>.skip
def afterLookup : ProgHOL 64 := match lookupCall with | .decCall _ _ _ _ rest=>rest | _=>.skip
def compareArguments : List (ExpHOL 64) := [localVar "root_hash",.var .global (ofString "empty_trie_root"),.const 32#64]
def lookupArguments : List (ExpHOL 64) := [localVar "db",localVar "root_hash"]
def emptyGuard : ProgHOL 64 := .ite (.cmp .notEqual (localVar "is_empty") (.const 0#64)) (.return (.const 0#64)) .skip

set_option maxRecDepth 100000

/-- Literal current239 through its empty-root comparison and real lookup. -/
theorem shapes : body=.decCall (ofString "is_empty") .one (ofString "memeq") compareArguments afterCompare ∧
    afterCompare=.seq emptyGuard lookupCall ∧
    lookupCall=.decCall (ofString "r") (.comb [.one,.one,.one]) (ofString "nodedb_lookup") lookupArguments afterLookup := by
  simp only [body,Guest.Software.guestFn_decode_witness_to_mpt,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    afterCompare,lookupCall,afterLookup,compareArguments,lookupArguments,emptyGuard,localVar]
  trivial

theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "decode_witness_to_mpt")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 239 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_decode_witness_to_mpt) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.Software.guestFn_decode_witness_to_mpt,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.shapes
#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.original_code
