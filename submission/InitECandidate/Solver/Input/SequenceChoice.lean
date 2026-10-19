import InitECandidate.Solver.Input.SequenceStopped
import InitECandidate.Solver.Input.NoFallthrough

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Select a stopping branch or the unchanged current suffix from its
actual guard evaluation. All clocks and outcomes are included. -/
theorem sequence_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (guard first second : ProgHOL 64)
    (selected : Prop) [Decidable selected]
    (read : evaluateHOLFiniteState source guard=if selected then evaluateHOLFiniteState source first else (none,source))
    (stops : NoFallthrough first) :
    evaluateHOLFiniteState source (.seq guard second)=
      if selected then evaluateHOLFiniteState source first else evaluateHOLFiniteState source second := by
  by_cases chosen : selected
  · have stopped : (evaluateHOLFiniteState source guard).1≠none := by rw [read,if_pos chosen]; exact stops source
    rw [sequence_stopped source guard second stopped,read,if_pos chosen,if_pos chosen]
  · rw [evaluateHOLFiniteState_seq_line780,read,if_neg chosen,if_neg chosen]

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.sequence_choice
