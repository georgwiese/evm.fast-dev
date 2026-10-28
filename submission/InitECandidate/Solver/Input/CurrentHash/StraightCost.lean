import InitECandidate.Solver.Input.CurrentHash.Code
import InitECandidate.Solver.Input.StraightBody
import InitECandidate.Solver.Input.ClockCostCall

namespace InitECandidate.Solver.Input.CurrentHash.StraightCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Any actually checked straight-line routine has zero source body ticks.
This keeps the large static target-instruction cost separate. -/
theorem body (code) (routine : Code.Routine) (supported : StraightBody.accepts (Code.body routine) = true) :
    ClockCost.Bound code (Code.body routine) 0 :=
  ClockCost.of_quiet code _ (StraightBody.effects (ofString "heap_ptr") code _ supported).1

theorem call (code) (installed : OriginalCode.Installed code) (routine : Code.Routine)
    (supported : StraightBody.accepts (Code.body routine) = true)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (LocalEffects.callInfo destination) (Code.name routine) arguments) 1 :=
  ClockCost.call_body code destination (Code.name routine) arguments
    (Code.formals routine) (Code.body routine) (Code.shape routine) 0
    (Code.installed code installed routine) (body code routine supported)

/-- Current heap marks, maximum and fixed-width integer stores have only
this straight-line syntax, with no successful memory-read/store premise. -/
theorem basic_supported (routine : Code.Routine)
    (member : routine ∈ [.heap_mark, .max, .st_le32]) :
    StraightBody.accepts (Code.body routine) = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals
    simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL, funDeclToHOL, Guest.Software.guestFn_heap_mark, Guest.Software.guestFn_max,
      Guest.Software.guestFn_st_le32, Guest.Software.guestFn_st_le64, progToHOL, expToHOL,
      shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
    rfl

theorem basic_call (code) (installed : OriginalCode.Installed code) (routine : Code.Routine)
    (member : routine ∈ [.heap_mark, .max, .st_le32])
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (LocalEffects.callInfo destination) (Code.name routine) arguments) 1 :=
  call code installed routine (basic_supported routine member) destination arguments

/-- The actual64-bit integer store is two32-bit store calls followed by a
literal return. Each called body is straight-line, on all outcomes. -/
theorem le64_body (code) (installed : OriginalCode.Installed code) :
    ClockCost.Bound code (Code.body .st_le64) 2 := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_st_le64, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  refine ClockCost.sequence code _ _ 1 1 ?_ ?_
  · exact basic_call code installed .st_le32 (by simp) (some none) _
  · exact ClockCost.sequence code _ _ 1 0
      (basic_call code installed .st_le32 (by simp) (some none) _) (ClockCost.returned code _)

theorem le64_call (code) (installed : OriginalCode.Installed code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (LocalEffects.callInfo destination) (Code.name .st_le64) arguments) 3 :=
  ClockCost.call_body code destination (Code.name .st_le64) arguments
    (Code.formals .st_le64) (Code.body .st_le64) (Code.shape .st_le64) 2
    (Code.installed code installed .st_le64) (le64_body code installed)

end InitECandidate.Solver.Input.CurrentHash.StraightCost

#print axioms InitECandidate.Solver.Input.CurrentHash.StraightCost.body
#print axioms InitECandidate.Solver.Input.CurrentHash.StraightCost.call
#print axioms InitECandidate.Solver.Input.CurrentHash.StraightCost.basic_supported
#print axioms InitECandidate.Solver.Input.CurrentHash.StraightCost.basic_call

#print axioms InitECandidate.Solver.Input.CurrentHash.StraightCost.le64_body
#print axioms InitECandidate.Solver.Input.CurrentHash.StraightCost.le64_call
