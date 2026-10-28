import InitECandidate.Solver.Input.CurrentHash.Code
import InitECandidate.Solver.WitnessRadix.AllocationCost
import InitECandidate.Solver.Input.QuietClockEffects

namespace InitECandidate.Solver.Input.CurrentHash.AllocatorCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Actual persistent allocation, including failed guards and their stopping
trap path. No incoming cursor value or future allocation room is assumed. -/
theorem alloc_call (code) (installed : OriginalCode.Installed code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (LocalEffects.callInfo destination) (ofString "alloc") arguments) 2 :=
  ClockCost.call_body code destination (ofString "alloc") arguments PersistentAlloc.formals PersistentAlloc.body .one 1
    (PersistentAlloc.original_code code installed) (PersistentAlloc.body_price code installed)

/-- Heap release changes a global, but has no source call/loop work. -/
theorem release_body (code) : ClockCost.Bound code (Code.body .heap_release) 0 := by
  apply ClockCost.of_quiet
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_heap_release, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact QuietClock.sequence code _ _ (QuietClock.assign_kind code .global _ _) (QuietClock.returned code _)

theorem release_call (code) (installed : OriginalCode.Installed code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (LocalEffects.callInfo destination) (Code.name .heap_release) arguments) 1 :=
  ClockCost.call_body code destination (Code.name .heap_release) arguments
    (Code.formals .heap_release) (Code.body .heap_release) (Code.shape .heap_release) 0
    (Code.installed code installed .heap_release) (release_body code)

end InitECandidate.Solver.Input.CurrentHash.AllocatorCost

#print axioms InitECandidate.Solver.Input.CurrentHash.AllocatorCost.alloc_call
#print axioms InitECandidate.Solver.Input.CurrentHash.AllocatorCost.release_body
#print axioms InitECandidate.Solver.Input.CurrentHash.AllocatorCost.release_call
