import InitECandidate.Solver.GasBudget.Frame

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem global_field_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (pointer offset value : BitVec 64)
    (global : source.globals.lookup (ofString name) = some (.val (.word pointer)))
    (mapped : source.memaddrs (pointer + offset)) (stored : source.memory (pointer + offset) = .word value) :
    eval source (.load .one (addConst (.var .global (ofString name)) offset)) = some (.val (.word value)) := by
  simp [eval, addConst, evalHOLExact, evalListHOLExact, toExact, global, valueIsWord, valueWord, wordOpHOL, wordOp,
    memLoadHOLExact, isWfShapeExactHOL, mapped, stored]

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.global_field_read
