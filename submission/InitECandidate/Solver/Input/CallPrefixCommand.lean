import InitECandidate.Solver.Input.CallPrefixExecution

namespace InitECandidate.Solver.Input.CallPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem Execution.command_next {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (command : ProgHOL 64) (rest : List Action)
    (execution : Execution source (.command command::rest) target) :
    ∃ middle,evaluateHOLFiniteState source command=(none,middle) ∧ Execution middle rest target := by
  cases execution with
  | step first next=>
    cases first with
    | command _ _ run=>exact ⟨_,run,next⟩

theorem Execution.command_known {source target expected : PanSemStateFiniteExact 64 Guest.HostMemory}
    (command : ProgHOL 64) (rest : List Action)
    (execution : Execution source (.command command::rest) target)
    (known : evaluateHOLFiniteState source command=(none,expected)) : Execution expected rest target := by
  obtain ⟨middle,actual,next⟩:=execution.command_next command rest
  have same : middle=expected:=congrArg Prod.snd (actual.symm.trans known)
  rw [same] at next
  exact next

end InitECandidate.Solver.Input.CallPrefix

#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.command_next
#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.command_known
