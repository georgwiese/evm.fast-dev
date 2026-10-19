import InitECandidate.Solver.Mpt.TrieWalkMemory
import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

def leafAfterSize : ProgHOL 64 := match leaf with | .dec _ _ _ rest => rest | _ => .skip
def leafLengthGuard : ProgHOL 64 := match leafAfterSize with | .seq first _ => first | _ => .skip
def leafCompare : ProgHOL 64 := match leafLengthGuard with | .ite _ yes _ => yes | _ => .skip
def leafMatch : ProgHOL 64 := match leafCompare with | .decCall _ _ _ _ rest => rest | _ => .skip
def leafArguments : List (ExpHOL 64) := [nodeField 32#64, pathAtPosition, localVar "rl"]

set_option maxRecDepth 10000
theorem leaf_body_shape : leaf = .dec (ofString "rl") .one (nodeField 40#64) (.seq leafLengthGuard absent) := by
  simp only [leaf, leafGuard, afterHash, afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, leafAfterSize, leafLengthGuard, nodeField, addConst, localVar, absent]
theorem leaf_length_shape : leafLengthGuard = .ite (.cmp .equal (localVar "rl") remaining) leafCompare .skip := by
  simp only [leafLengthGuard, leafAfterSize, leaf, leafGuard, afterHash, afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, localVar, remaining, leafCompare]
theorem leaf_compare_shape : leafCompare = .decCall (ofString "eq") .one (ofString "memeq") leafArguments leafMatch := by
  simp only [leafCompare, leafLengthGuard, leafAfterSize, leaf, leafGuard, afterHash, afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, localVar, leafArguments, nodeField, addConst, pathAtPosition, leafMatch]
theorem leaf_match_quiet (code) : Input.QuietClock.Preserves code leafMatch := by
  simp only [leafMatch, leafCompare, leafLengthGuard, leafAfterSize, leaf, leafGuard, afterHash, afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil]
  exact Input.QuietClock.conditional code _ _ _ (Input.QuietClock.returned code _) (Input.QuietClock.skip code)

theorem leaf_arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node nibs position size path : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsCell : source.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position)))
    (sizeCell : source.locals.lookup (ofString "rl") = some (.val (.word size)))
    (mapped : source.memaddrs (node + 32#64)) (stored : source.memory (node + 32#64) = .word path) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) leafArguments =
      some (MemeqByteRuntime.values path (nibs + position) size.toNat) := by
  classical
  have pathRead := node_field_read source node 32#64 path nodeCell mapped stored
  change evalListHOLExact source.toExact leafArguments = _
  simp only [leafArguments, evalListHOLExact]
  simp only [eval] at pathRead
  rw [pathRead]
  simp [pathAtPosition, localVar, evalHOLExact, evalListHOLExact, toExact, nibsCell, posCell, sizeCell,
    valueIsWord, valueWord, wordOpHOL, wordOp, MemeqByteRuntime.values]

theorem Graph.leaf_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (node nibs position : BitVec 64) (limit : Nat)
    (key : KeyView source.memory source.memaddrs source.be nibs limit)
    (member : graph.valid node) (active : node ≠ 0#64) (tag : wordAt source.memory node = 1#64)
    (bounded : position.toNat ≤ limit)
    (nodeCell : source.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsCell : source.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position)))
    (limitCell : source.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))))
    (code : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one)) :
    source.clock - (evaluateHOLFiniteState source leaf).2.clock ≤ 15 := by
  let path := graph.path node member active (Or.inl tag)
  have sizeRead := node_field_read source node 40#64 path.size nodeCell path.sizeMapped path.sizeStored
  rw [leaf_body_shape]
  apply Input.ClockCost.declared_current source "rl" (nodeField 40#64) path.size _ 15 sizeRead
  let entered := bind source "rl" path.size
  change entered.clock - (evaluateHOLFiniteState entered (.seq leafLengthGuard absent)).2.clock ≤ 15
  have currentNode : entered.locals.lookup (ofString "node") = some (.val (.word node)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans nodeCell
  have currentNibs : entered.locals.lookup (ofString "nibs") = some (.val (.word nibs)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans nibsCell
  have currentPos : entered.locals.lookup (ofString "pos") = some (.val (.word position)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans posCell
  have currentLimit : entered.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans limitCell
  have currentSize : entered.locals.lookup (ofString "rl") = some (.val (.word path.size)) := bind_lookup_same _ _ _
  have guardCost : entered.clock - (evaluateHOLFiniteState entered leafLengthGuard).2.clock ≤ 15 := by
    by_cases same : path.size = BitVec.ofNat 64 limit - position
    · have actual : evaluateHOLFiniteState entered leafLengthGuard = evaluateHOLFiniteState entered leafCompare := by
        simp [leaf_length_shape, evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact,
          remaining, localVar, currentPos, currentLimit, currentSize, valueIsWord, valueWord, wordOpHOL, wordOp,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, same]
      have limitNumber : (BitVec.ofNat 64 limit).toNat = limit := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have small := key.small; omega)]
      have order : position ≤ BitVec.ofNat 64 limit := by
        change position.toNat ≤ (BitVec.ofNat 64 limit).toNat
        rwa [limitNumber]
      have sizeNumber : path.size.toNat = limit - position.toNat := by
        rw [same, BitVec.toNat_sub_of_le order, limitNumber]
      have sizeSmall : path.size.toNat ≤ 64 := by have small := key.small; omega
      have within : path.size.toNat ≤ limit - position.toNat := by omega
      have clipped : min path.size.toNat 64 = path.size.toNat := min_eq_left sizeSmall
      have aFits := path.fits
      have leftMapped := path.mapped
      rw [clipped] at aFits leftMapped
      have bFits := KeyView.window_fits source.memory source.memaddrs source.be nibs position limit path.size.toNat key bounded within
      have rightMapped := KeyView.window_mapped source.memory source.memaddrs source.be nibs position limit path.size.toNat key bounded within
      have args := leaf_arguments_read entered node nibs position path.size path.pointer currentNode currentNibs currentPos currentSize path.pointerMapped path.pointerStored
      rw [actual, leaf_compare_shape]
      have cost := MemeqSmall.call_cost entered path.pointer (nibs + position) path.size.toNat sizeSmall aFits bFits leftMapped rightMapped code
        (ofString "eq") leafArguments leafMatch args (Input.ClockCost.of_quiet _ _ (leaf_match_quiet _))
      have price := MemeqSmall.price_le_fourteen path.size.toNat sizeSmall
      omega
    · have actual : evaluateHOLFiniteState entered leafLengthGuard = (none, entered) := by
        simp [leaf_length_shape, evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact,
          remaining, localVar, currentPos, currentLimit, currentSize, valueIsWord, valueWord, wordOpHOL, wordOp,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, same, evaluateHOLFiniteState_skip]
      rw [actual]
      simp
  have cost := Input.ClockCost.sequence_current entered leafLengthGuard absent 15 0 guardCost
    (Input.ClockCost.returned entered.code _)
  exact cost

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.leaf_body_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.leaf_length_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.leaf_compare_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.leaf_match_quiet
#print axioms InitECandidate.Solver.Mpt.TrieWalk.leaf_arguments_read
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.leaf_cost
