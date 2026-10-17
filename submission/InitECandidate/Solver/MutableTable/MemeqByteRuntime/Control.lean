import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Bodies

namespace InitECandidate.Solver.MutableTable.MemeqByteRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- Actual while/continuation composition through a successful body step. -/
theorem loop_continue {F : Type} (source next : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (body tail : ProgHOL 64)
    (test : eval source condition = some (.val (.word 1#64))) (positive : source.clock ≠ 0)
    (run : evaluateHOLFiniteState (decClockHOLFinite source) body = (none, next))
    (clock : next.clock ≤ source.clock - 1) :
    evaluateHOLFiniteState source (.seq (.while condition body) tail) =
      evaluateHOLFiniteState next (.seq (.while condition body) tail) := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
  simp only [eval, evalHOLFinite] at test ⊢
  rw [test]
  simp only [if_pos (show (1#64 : BitVec 64) ≠ 0 from by decide), if_neg positive, run]
  rw [WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite source) next none clock]
  exact (evaluateHOLFiniteState_seq_line780 next (.while condition body) tail).symm

/-- An actual mismatch return exits both the byte loop and its suffix. -/
theorem loop_return {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (body tail : ProgHOL 64) (word : BitVec 64)
    (test : eval source condition = some (.val (.word 1#64))) (positive : source.clock ≠ 0)
    (run : evaluateHOLFiniteState (decClockHOLFinite source) body = (some (.returned (.val (.word word))), target))
    (clock : target.clock ≤ source.clock - 1) :
    evaluateHOLFiniteState source (.seq (.while condition body) tail) = (some (.returned (.val (.word word))), target) := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
  simp only [eval, evalHOLFinite] at test ⊢
  rw [test]
  simp only [if_pos (show (1#64 : BitVec 64) ≠ 0 from by decide), if_neg positive, run]
  rw [WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite source) target _ clock]

/-- A false actual test enters the tail with no loop-clock cost. -/
theorem loop_stop {F : Type} (source : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (body tail : ProgHOL 64)
    (test : eval source condition = some (.val (.word 0#64))) :
    evaluateHOLFiniteState source (.seq (.while condition body) tail) = evaluateHOLFiniteState source tail := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_total]
  simp only [eval, evalHOLFinite] at test ⊢
  rw [test]
  simp

end InitECandidate.Solver.MutableTable.MemeqByteRuntime

#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.loop_continue
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.loop_return
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.loop_stop
