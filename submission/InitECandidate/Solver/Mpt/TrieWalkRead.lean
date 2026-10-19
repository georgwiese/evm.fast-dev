import InitECandidate.Solver.Mpt.TrieWalkStepProgram
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Call

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

theorem node_field_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node offset word : BitVec 64)
    (cell : source.locals.lookup (ofString "node") = some (.val (.word node)))
    (mapped : source.memaddrs (node + offset)) (stored : source.memory (node + offset) = .word word) :
    eval source (nodeField offset) = some (.val (.word word)) := by
  simp [eval, nodeField, addConst, localVar, evalHOLExact, evalListHOLExact, toExact, cell,
    valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact, isWfShapeExactHOL, mapped, stored]

/-- Original extension comparison operands are read from the current node
and current key position; no callee or later state is supplied. -/
theorem compare_arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node nibs position size path : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsCell : source.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position)))
    (sizeCell : source.locals.lookup (ofString "sl") = some (.val (.word size)))
    (mapped : source.memaddrs (node + 32#64)) (stored : source.memory (node + 32#64) = .word path) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) compareArguments =
      some (MemeqByteRuntime.values path (nibs + position) size.toNat) := by
  classical
  have pathRead := node_field_read source node 32#64 path nodeCell mapped stored
  change evalListHOLExact source.toExact compareArguments = _
  simp only [compareArguments, evalListHOLExact]
  simp only [eval] at pathRead
  rw [pathRead]
  simp [pathAtPosition, localVar, evalHOLExact, evalListHOLExact, toExact, nibsCell, posCell, sizeCell,
    valueIsWord, valueWord, wordOpHOL, wordOp, MemeqByteRuntime.values]

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.node_field_read
#print axioms InitECandidate.Solver.Mpt.TrieWalk.compare_arguments_read
