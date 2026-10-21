import InitECandidate.Solver.MutableTable.NodeDbTail32

namespace InitECandidate.Solver.MutableTable.NodeDb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original witness suffix ignores the second getter field on an
absent flag, and reads exactly the real record on a present flag. -/
theorem flag_tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (flag record : BitVec 64) (slices : BitVec 64→Slice)
    (rCell : source.locals.lookup (ofString "r")=some (Get.pair flag record)) (binary : flag=0#64 ∨ flag=1#64)
    (reads : flag=1#64→source.memaddrs record ∧ source.memaddrs (record+8#64) ∧
      source.memory record=.word (slices record).1 ∧ source.memory (record+8#64)=.word (slices record).2) :
    evaluateHOLFiniteState source afterGet=(some (.returned (output ((if flag=0#64 then none else some record).map slices))),emptyLocalsHOLFinite source) := by
  classical
  rcases binary with rfl|rfl
  · have stopped : evaluateHOLFiniteState source (.ite condition absent .skip)=
        (some (.returned (output none)),emptyLocalsHOLFinite source) := by
      simp [condition,evaluateHOLFiniteState_ite,evalHOLExact,toExact,localVar,rCell,Get.pair,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,absent,triple,output,evaluateHOLFiniteState_return,evalListHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    rw [afterGet,StateSteps.stopped_sequence source (emptyLocalsHOLFinite source) _ _ _ stopped (Nat.le_refl _)]
    simp
  · have data:=reads rfl
    have actual:=tail32_execute source (some record) slices rCell (by
      intro selected same
      have equal : record=selected := Option.some.inj same
      rw [← equal]
      exact data)
    simpa using actual

end InitECandidate.Solver.MutableTable.NodeDb

#print axioms InitECandidate.Solver.MutableTable.NodeDb.flag_tail_execute
