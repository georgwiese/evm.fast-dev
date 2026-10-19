import InitECandidate.Solver.Input.HeapScope
import InitECandidate.Solver.Input.ClockCostCall
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.Input.HeapScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

set_option maxRecDepth 100000 in
theorem mark_original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "heap_mark")=some ([],markBody,.one) := by
  have checked := OriginalCode.indexed code installed 3 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_heap_mark) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,markBody,
    Guest.guestFn_heap_mark,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem release_original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "heap_release")=some (releaseFormals,releaseBody,.one) := by
  have checked := OriginalCode.indexed code installed 4 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_heap_release) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,releaseBody,releaseFormals,
    Guest.guestFn_heap_release,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem mark_body_cost (code) : ClockCost.Bound code markBody 0 := by
  rw [mark_shape]
  exact ClockCost.returned code heapVar

theorem release_body_cost (code) : ClockCost.Bound code releaseBody 0 := by
  have assignClock : QuietClock.Preserves code (.assign .global (ofString "heap_ptr") (localVar "m")) := by
    intro source installed
    rw [evaluateHOLFiniteState_assign]
    repeat first | rfl | split
  rw [release_shape]
  exact ClockCost.sequence code _ _ 0 0 (ClockCost.of_quiet code _ assignClock) (ClockCost.returned code _)

/-- All actual release outcomes cost at most one caller clock, even with
malformed arguments or an absent heap global. -/
theorem release_call_cost (code) (installed : OriginalCode.Installed code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (LocalEffects.callInfo destination) (ofString "heap_release") arguments) 1 :=
  ClockCost.call_body code destination (ofString "heap_release") arguments releaseFormals releaseBody .one 0
    (release_original_code code installed) (release_body_cost code)

end InitECandidate.Solver.Input.HeapScope

#print axioms InitECandidate.Solver.Input.HeapScope.mark_original_code
#print axioms InitECandidate.Solver.Input.HeapScope.release_original_code
#print axioms InitECandidate.Solver.Input.HeapScope.mark_body_cost
#print axioms InitECandidate.Solver.Input.HeapScope.release_body_cost
#print axioms InitECandidate.Solver.Input.HeapScope.release_call_cost
