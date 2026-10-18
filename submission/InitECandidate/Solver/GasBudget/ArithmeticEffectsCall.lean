import InitECandidate.Solver.GasBudget.ArithmeticEffects
import InitECandidate.Solver.GasBudget.Frame

namespace InitECandidate.Solver.GasBudget.ArithmeticEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Input.LocalEffects

theorem original_call_preserves (kind : Kind) (code) (environment : Environment code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    Preserves code (.call (callInfo destination) kind.name arguments) :=
  call_body code destination kind.name arguments kind.signature.1 kind.body kind.signature.2.2
    (environment kind) (original_preserves kind code environment)

/-- Genuine original arithmetic calls preserve the physical gas budget and
used field for all arguments/clocks/outcomes, including tail and local-result
calls. Environment is an explicit original-code-map entry obligation. No
iteration-count or runtime-price theorem is asserted here. -/
theorem call_frame (kind : Kind) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : Environment source.code) (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.call (callInfo destination) kind.name arguments) = (result, target)) :
    target = {source with locals := target.locals, clock := target.clock} ∧
      target.memory = source.memory ∧ target.globals = source.globals ∧
      (∀ frame, regularBudget target.memory frame = regularBudget source.memory frame) ∧
      (∀ frame, target.memory (frame + 184#64) = source.memory (frame + 184#64)) := by
  have frame := original_call_preserves kind source.code environment destination arguments source rfl
  rw [run] at frame
  have canonical := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    {state with locals := target.locals, clock := target.clock}) frame
  change target = {source with locals := target.locals, clock := target.clock} at canonical
  have memoryEq := memory_of_erase source target frame
  have globalsEq := congrArg PanSemStateFiniteExact.globals frame
  refine ⟨canonical, memoryEq, globalsEq, ?_, ?_⟩
  · intro frame
    rw [memoryEq]
  · intro frame
    rw [memoryEq]

end InitECandidate.Solver.GasBudget.ArithmeticEffects

#print axioms InitECandidate.Solver.GasBudget.ArithmeticEffects.original_call_preserves
#print axioms InitECandidate.Solver.GasBudget.ArithmeticEffects.call_frame
