import InitECandidate.Solver.WitnessRadix.PopProgram

namespace InitECandidate.Solver.WitnessRadix.PopProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem pending_read {F : Type} (source : PanSemStateFiniteExact 64 F)
    (name : String) (base depth value : BitVec 64)
    (baseLocal : source.locals.lookup (ofString name) = some (.val (.word base)))
    (depthLocal : source.locals.lookup (ofString "depth") = some (.val (.word depth)))
    (mapped : source.memaddrs (base + depth * 8#64))
    (stored : source.memory (base + depth * 8#64) = .word value) :
    eval source (pendingExpression name) = some (.val (.word value)) := by
  classical
  simp [eval, pendingExpression, localVar, evalHOLExact, evalListHOLExact, toExact,
    baseLocal, depthLocal, isWfShapeExactHOL, memLoadHOLExact, mapped, stored,
    valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]

theorem decrement_read {F : Type} (source : PanSemStateFiniteExact 64 F) (depth : BitVec 64)
    (depthLocal : source.locals.lookup (ofString "depth") = some (.val (.word depth))) :
    eval source (.op .sub [localVar "depth", .const 1#64]) = some (.val (.word (depth - 1#64))) := by
  classical
  simp [eval, localVar, evalHOLExact, evalListHOLExact, toExact, depthLocal,
    valueIsWord, valueWord, wordOpHOL, wordOp]

theorem parent_bit_read {F : Type} (source : PanSemStateFiniteExact 64 F) (parent bit : BitVec 64)
    (parentLocal : source.locals.lookup (ofString "parent") = some (.val (.word parent)))
    (mapped : source.memaddrs parent) (stored : source.memory parent = .word bit) :
    eval source bitExpression = some (.val (.word (bit + 1#64))) := by
  classical
  simp [eval, bitExpression, localVar, addConst, evalHOLExact, evalListHOLExact, toExact,
    parentLocal, isWfShapeExactHOL, memLoadHOLExact, mapped, stored,
    valueIsWord, valueWord, wordOpHOL, wordOp]

theorem parent_dest_read {F : Type} (source : PanSemStateFiniteExact 64 F) (parent : BitVec 64)
    (parentLocal : source.locals.lookup (ofString "parent") = some (.val (.word parent))) :
    eval source destExpression = some (.val (.word (parent + 16#64))) := by
  classical
  simp [eval, destExpression, localVar, addConst, evalHOLExact, evalListHOLExact, toExact,
    parentLocal, valueIsWord, valueWord, wordOpHOL, wordOp]

end InitECandidate.Solver.WitnessRadix.PopProgram

#print axioms InitECandidate.Solver.WitnessRadix.PopProgram.pending_read
