import InitECandidate.Solver.WitnessRadix.TerminalFinish
import InitECandidate.Solver.WitnessRadix.TerminalReads

namespace InitECandidate.Solver.WitnessRadix.TerminalProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem main_body_finish {F : Type} (source : PanSemStateFiniteExact 64 F)
    (destination ordinal : BitVec 64)
    (test : eval source terminalTest = some (.val (.word 1#64)))
    (readOrdinal : eval source ordinalExpression = some (.val (.word ordinal)))
    (destLocal : source.locals.lookup (ofString "dest") = some (.val (.word destination)))
    (depth : source.locals.lookup (ofString "depth") = some (.val (.word 0#64)))
    (mapped : source.memaddrs destination) :
    ∃ target : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState source BuildEntry.mainBody = (some (.returned (.val (.word 0#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite
        { source with memory := StoreWord.put source.memory destination (ordinal * 2#64 + 1#64) } := by
  classical
  obtain ⟨target, terminalRun, frame⟩ := terminal_finish source destination ordinal readOrdinal destLocal depth mapped
  have clockEq : target.clock = source.clock := congrArg (fun state => state.clock) frame
  have chosen : evaluateHOLFiniteState source (.ite terminalTest terminalCode .skip) =
      (some (.returned (.val (.word 0#64))), target) := by
    simp only [eval] at test
    rw [evaluateHOLFiniteState_ite, test]
    simpa using terminalRun
  refine ⟨target, ?_, frame⟩
  rw [main_body_shape]
  exact StateSteps.stopped_sequence source target _ _ _ chosen (by omega)

/-- The final outer-loop iteration pays exactly one clock and returns after
the leaf store. All private-memory and clock changes are explicit. -/
theorem main_loop_finish {F : Type} (source : PanSemStateFiniteExact 64 F)
    (destination ordinal : BitVec 64)
    (test : eval (decClockHOLFinite source) terminalTest = some (.val (.word 1#64)))
    (readOrdinal : eval (decClockHOLFinite source) ordinalExpression = some (.val (.word ordinal)))
    (destLocal : source.locals.lookup (ofString "dest") = some (.val (.word destination)))
    (depth : source.locals.lookup (ofString "depth") = some (.val (.word 0#64)))
    (mapped : source.memaddrs destination) (enough : 1 ≤ source.clock) :
    ∃ target : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState source BuildEntry.mainLoop = (some (.returned (.val (.word 0#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite { source with
        memory := StoreWord.put source.memory destination (ordinal * 2#64 + 1#64)
        clock := source.clock - 1 } := by
  classical
  obtain ⟨target, bodyRun, frame⟩ := main_body_finish (decClockHOLFinite source) destination ordinal
    test readOrdinal destLocal depth mapped
  have clockEq : target.clock = (decClockHOLFinite source).clock := congrArg (fun state => state.clock) frame
  have positive : source.clock ≠ 0 := by omega
  refine ⟨target, ?_, frame⟩
  rw [main_loop_shape, evaluateHOLFiniteState_while_total]
  simp only [evalHOLFinite, evalHOLExact]
  rw [if_pos (by decide)]
  simp only [if_neg positive, bodyRun]
  rw [StateSteps.fixed_clock (decClockHOLFinite source) target _ (by omega)]

end InitECandidate.Solver.WitnessRadix.TerminalProgram

#print axioms InitECandidate.Solver.WitnessRadix.TerminalProgram.main_loop_finish
