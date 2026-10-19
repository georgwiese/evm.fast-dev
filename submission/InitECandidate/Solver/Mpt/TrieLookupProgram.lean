import InitECandidate.Solver.Mpt.KeyToNibblesCall
import InitECandidate.Solver.Mpt.TrieWalkCall
import InitECandidate.Solver.Mpt.TrieWalkGraphProtection

namespace InitECandidate.Solver.Mpt.TrieLookup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_trie_lookup with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "root", .one), (ofString "key_hash32", .one)]
def prepareArguments : List (ExpHOL 64) := [localVar "key_hash32", .const 32#64, .var .global (ofString "mpt_nib_scratch")]
def forwardArguments : List (ExpHOL 64) := [localVar "root", .var .global (ofString "mpt_nib_scratch"), .const 64#64]
def prepare : ProgHOL 64 := .call (some (none, none)) (ofString "key_to_nibbles") prepareArguments
def forward : ProgHOL 64 := .call none (ofString "trie_walk") forwardArguments

theorem body_shape : body = .seq prepare forward := by
  simp only [body, prepare, forward, prepareArguments, forwardArguments, localVar, Guest.guestFn_trie_lookup,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "trie_lookup") = some (formals, body, TrieWalk.resultShape) := by
  have checked := Input.OriginalCode.indexed code installed 243 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_trie_lookup) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, body, formals, TrieWalk.resultShape,
    Guest.guestFn_trie_lookup, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

theorem prepare_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key out : BitVec 64)
    (keyCell : source.locals.lookup (ofString "key_hash32") = some (.val (.word key)))
    (scratch : source.globals.lookup (ofString "mpt_nib_scratch") = some (.val (.word out))) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) prepareArguments = some (KeyToNibbles.values key out) := by
  simp [prepareArguments, KeyToNibbles.values, evalListHOLFinite, evalListHOLExact, evalHOLExact, localVar, toExact, keyCell, scratch]

theorem forward_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root out : BitVec 64)
    (rootCell : source.locals.lookup (ofString "root") = some (.val (.word root)))
    (scratch : source.globals.lookup (ofString "mpt_nib_scratch") = some (.val (.word out))) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) forwardArguments = some (TrieWalk.values root out 64) := by
  simp [forwardArguments, TrieWalk.values, evalListHOLFinite, evalListHOLExact, evalHOLExact, localVar, toExact, rootCell, scratch]

end InitECandidate.Solver.Mpt.TrieLookup

#print axioms InitECandidate.Solver.Mpt.TrieLookup.body_shape
#print axioms InitECandidate.Solver.Mpt.TrieLookup.original_code
#print axioms InitECandidate.Solver.Mpt.TrieLookup.prepare_arguments
#print axioms InitECandidate.Solver.Mpt.TrieLookup.forward_arguments
