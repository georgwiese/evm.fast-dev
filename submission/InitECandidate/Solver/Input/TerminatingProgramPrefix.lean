import InitECandidate.Solver.WitnessRadix.ProgramPrefix
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Funding for an actual lexical allocation/declaration/command prefix is
forced by the enclosing non-timeout run. The restoration stack is justified
by the actual checked prefix, and changes only local bindings. -/
theorem terminating_program_prefix {F : Type} (source post entered : PanSemStateFiniteExact 64 F)
    (actions : List WitnessRadix.ProgramPrefix.Action) (continuation : ProgHOL 64)
    (restoreStack : PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F) (padding : Nat)
    (setup : WitnessRadix.ProgramPrefix.Executes {source with clock := source.clock + padding} actions entered restoreStack)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (WitnessRadix.ProgramPrefix.program actions continuation) = (result,post))
    (notTimeout : result ≠ some .timeOut) : padding ≤ entered.clock := by
  have whole := panPropsEvaluateAddClockEq (WitnessRadix.ProgramPrefix.program actions continuation) source result post padding ⟨run,notTimeout⟩
  rw [WitnessRadix.ProgramPrefix.execute setup continuation] at whole
  have nextClock := evaluateHOLFiniteState_clock_le entered continuation
  have restoration := congrArg (fun state : PanSemStateFiniteExact 64 F => state.clock)
    (WitnessRadix.ProgramPrefix.restoration_frame setup (evaluateHOLFiniteState entered continuation).2)
  have endClock := congrArg (fun output => output.2.clock) whole
  change (restoreStack (evaluateHOLFiniteState entered continuation).2).clock = (evaluateHOLFiniteState entered continuation).2.clock at restoration
  change (restoreStack (evaluateHOLFiniteState entered continuation).2).clock = post.clock + padding at endClock
  omega

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.terminating_program_prefix
