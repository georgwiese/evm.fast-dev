import InitECandidate.Solver.Mpt.TrieWalkProgram

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def branchGuard : ProgHOL 64 := match branch with | .seq first _ => first | _ => .skip
def branchAdvance : ProgHOL 64 := match branch with | .seq _ rest => rest | _ => .skip
def branchTerminal : ProgHOL 64 := match branchGuard with | .ite _ yes _ => yes | _ => .skip
def branchNode : ProgHOL 64 := match branchAdvance with | .seq first _ => first | _ => .skip
def branchPosition : ProgHOL 64 := .assign .local (ofString "pos") (addConst (localVar "pos") 1#64)
def afterSize : ProgHOL 64 := match extension with | .dec _ _ _ rest => rest | _ => .skip
def extentGuard : ProgHOL 64 := match afterSize with | .seq first _ => first | _ => .skip
def extensionCompare : ProgHOL 64 := match afterSize with | .seq _ rest => rest | _ => .skip
def afterCompare : ProgHOL 64 := match extensionCompare with | .decCall _ _ _ _ rest => rest | _ => .skip
def comparisonGuard : ProgHOL 64 := match afterCompare with | .seq first _ => first | _ => .skip
def extensionAdvance : ProgHOL 64 := match afterCompare with | .seq _ rest => rest | _ => .skip
def remaining : ExpHOL 64 := .op .sub [localVar "nlen", localVar "pos"]
def pathAtPosition : ExpHOL 64 := .op .add [localVar "nibs", localVar "pos"]
def compareArguments : List (ExpHOL 64) := [nodeField 32#64, pathAtPosition, localVar "sl"]

set_option maxRecDepth 10000

theorem branch_shape : branch = .seq branchGuard branchAdvance := by
  simp only [branch, nodeStep, afterHash, afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, branchGuard, branchAdvance]
theorem branch_guard_shape : branchGuard = .ite (.cmp .equal (localVar "pos") (localVar "nlen")) branchTerminal .skip := by
  simp only [branchGuard, branch, nodeStep, afterHash, afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, branchTerminal, localVar]
theorem branch_advance_shape : branchAdvance = .seq branchNode branchPosition := by
  simp only [branchAdvance, branchNode, branch, nodeStep, afterHash, afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, branchPosition, addConst, localVar]
theorem extension_shape : extension = .dec (ofString "sl") .one (nodeField 40#64) (.seq extentGuard extensionCompare) := by
  simp only [extension, nodeStep, afterHash, afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, afterSize, extentGuard, extensionCompare, nodeField, localVar, addConst]
theorem extent_guard_shape : extentGuard = .ite (.cmp .lower remaining (localVar "sl")) absent .skip := by
  simp only [extentGuard, afterSize, extension, nodeStep, afterHash, afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, remaining, localVar, absent]
theorem compare_shape : extensionCompare = .decCall (ofString "eq2") .one (ofString "memeq") compareArguments afterCompare := by
  simp only [extensionCompare, afterSize, extension, nodeStep, afterHash, afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, compareArguments, nodeField, addConst, pathAtPosition, localVar, afterCompare]
theorem after_compare_shape : afterCompare = .seq comparisonGuard extensionAdvance := by
  simp only [afterCompare, extensionCompare, afterSize, extension, nodeStep, afterHash, afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, comparisonGuard, extensionAdvance]
theorem comparison_guard_shape : comparisonGuard = .ite (.cmp .equal (localVar "eq2") (.const 0#64)) absent .skip := by
  simp only [comparisonGuard, afterCompare, extensionCompare, afterSize, extension, nodeStep, afterHash, afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, localVar, absent]
theorem extension_advance_shape : extensionAdvance = .seq
    (.assign .local (ofString "pos") (.op .add [localVar "pos", localVar "sl"]))
    (.assign .local (ofString "node") (nodeField 48#64)) := by
  simp only [extensionAdvance, afterCompare, extensionCompare, afterSize, extension, nodeStep, afterHash, afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, nodeField, addConst, localVar]

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.branch_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.branch_guard_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.branch_advance_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.extension_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.extent_guard_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.compare_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.after_compare_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.comparison_guard_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.extension_advance_shape
