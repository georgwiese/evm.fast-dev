import InitECandidate.Solver.Mpt.Fail
import InitECandidate.Solver.MutableTable.QueryNoException

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_trie_walk with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "node", .one), (ofString "nibs", .one), (ofString "nlen", .one)]
def resultShape : ShapeHOL := .comb [.one, .one, .one]
def nodeField (offset : BitVec 64) : ExpHOL 64 := .load .one (addConst (localVar "node") offset)
def afterPos : ProgHOL 64 := match body with | .dec _ _ _ rest => rest | _ => .skip
def loop : ProgHOL 64 := match afterPos with | .seq first _ => first | _ => .skip
def afterLoop : ProgHOL 64 := match afterPos with | .seq _ rest => rest | _ => .skip
def loopBody : ProgHOL 64 := match loop with | .while _ rest => rest | _ => .skip
def afterK : ProgHOL 64 := match loopBody with | .dec _ _ _ rest => rest | _ => .skip
def hashGuard : ProgHOL 64 := match afterK with | .seq first _ => first | _ => .skip
def afterHash : ProgHOL 64 := match afterK with | .seq _ rest => rest | _ => .skip
def leafGuard : ProgHOL 64 := match afterHash with | .seq first _ => first | _ => .skip
def nodeStep : ProgHOL 64 := match afterHash with | .seq _ rest => rest | _ => .skip
def leaf : ProgHOL 64 := match leafGuard with | .ite _ yes _ => yes | _ => .skip
def extension : ProgHOL 64 := match nodeStep with | .ite _ yes _ => yes | _ => .skip
def branch : ProgHOL 64 := match nodeStep with | .ite _ _ no => no | _ => .skip
def condition : ExpHOL 64 := .cmp .notEqual (localVar "node") (.const 0#64)
def absent : ProgHOL 64 := .return (.rstruct [.const 0#64, .const 0#64, .const 0#64])

set_option maxRecDepth 10000

theorem body_shape : body = .dec (ofString "pos") .one (.const 0#64) (.seq loop afterLoop) := by
  simp only [body, Guest.guestFn_trie_walk, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    loop, afterPos, afterLoop]
theorem loop_shape : loop = .while condition loopBody := by
  simp only [loop, afterPos, body, Guest.guestFn_trie_walk, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    loopBody, condition, localVar]
theorem loop_body_shape : loopBody = .dec (ofString "k") .one (nodeField 0#64) afterK := by
  simp only [loopBody, loop, afterPos, body, Guest.guestFn_trie_walk, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, afterK, nodeField, localVar, addConst]
theorem hash_shape : afterK = .seq hashGuard afterHash := by
  simp only [afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, hashGuard, afterHash]
theorem hash_guard_shape : hashGuard = .ite (.cmp .equal (localVar "k") (.const 0#64))
    (.call (some (none, none)) (ofString "mpt_fail") [.const 2#64]) .skip := by
  simp only [hashGuard, afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, localVar, Option.map_none]
theorem leaf_shape : afterHash = .seq leafGuard nodeStep := by
  simp only [afterHash, afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, leafGuard, nodeStep]
theorem leaf_guard_shape : leafGuard = .ite (.cmp .equal (localVar "k") (.const 1#64)) leaf .skip := by
  simp only [leafGuard, afterHash, afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, leaf, localVar]
theorem node_step_shape : nodeStep = .ite (.cmp .equal (localVar "k") (.const 2#64)) extension branch := by
  simp only [nodeStep, afterHash, afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, extension, branch, localVar]
theorem after_loop_shape : afterLoop = absent := by
  simp only [afterLoop, afterPos, body, Guest.guestFn_trie_walk, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, absent]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "trie_walk") = some (formals, body, resultShape) := by
  have checked := Input.OriginalCode.indexed code installed 242 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_trie_walk) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, body, formals, resultShape,
    Guest.guestFn_trie_walk, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.body_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.loop_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.loop_body_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.hash_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.hash_guard_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.leaf_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.leaf_guard_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.node_step_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.after_loop_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.original_code
