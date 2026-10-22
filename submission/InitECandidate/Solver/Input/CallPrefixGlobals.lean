import InitECandidate.Solver.Input.CallPrefixExecution
import InitECandidate.Solver.Input.GlobalEffects

namespace InitECandidate.Solver.Input.CallPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem Execution.globals {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {actions : List Action}
    (execution : Execution source actions target) (key : MlS)
    (preserved : GlobalEffects.Preserves key source.code (program actions .skip)) :
    target.globals.lookup key=source.globals.lookup key := by
  have actual:=congrArg (fun state=>state.globals.lookup key) execution.skip_erase
  have known:=congrArg Prod.snd (preserved source rfl)
  exact actual.symm.trans known

theorem Reaches.globals {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {action : Action}
    (reached : Reaches source action target) (key : MlS)
    (preserved : GlobalEffects.Preserves key source.code (program [action] .skip)) :
    target.globals.lookup key=source.globals.lookup key :=
  (Execution.step reached (.done target)).globals key preserved

end InitECandidate.Solver.Input.CallPrefix

#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.globals
#print axioms InitECandidate.Solver.Input.CallPrefix.Reaches.globals
