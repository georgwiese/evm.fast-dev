import InitECandidate.Solver.Input.CurrentHash.FixedMemoryCost
import InitECandidate.Solver.Input.CurrentHash.StraightCost
import InitECandidate.Solver.Input.CurrentHash.Sha256Pair

namespace InitECandidate.Solver.Input.CurrentHash.FixedHashCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual fixed length-mixing body, including all failed reads/stores
and exhausted-clock paths. No workspace entry or future success is assumed. -/
theorem mix_body (code) (installed : OriginalCode.Installed code) :
    ClockCost.Bound code (Code.body .mix_in_length) 46 := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_mix_in_length, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  refine ClockCost.sequence code _ _ 42 4 ?_ ?_
  · exact FixedMemoryCost.zero code installed (some none) _ 32 (by decide)
  · refine ClockCost.sequence code _ _ 3 1 (StraightCost.le64_call code installed (some none) _) ?_
    exact ClockCost.sequence code _ _ 1 0 (Sha256Pair.call_cost code installed (some none) _) (ClockCost.returned code _)

theorem mix_call (code) (installed : OriginalCode.Installed code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (LocalEffects.callInfo destination) (Code.name .mix_in_length) arguments) 47 :=
  ClockCost.call_body code destination (Code.name .mix_in_length) arguments
    (Code.formals .mix_in_length) (Code.body .mix_in_length) (Code.shape .mix_in_length) 46
    (Code.installed code installed .mix_in_length) (mix_body code installed)

/-- The actual scalar root body copies just eight bytes after clearing its
32-byte output. Its price depends only on those literal lengths. -/
theorem u64_body (code) (installed : OriginalCode.Installed code) :
    ClockCost.Bound code (Code.body .htr_u64_at) 53 := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_htr_u64_at, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  refine ClockCost.sequence code _ _ 42 11 ?_ ?_
  · exact FixedMemoryCost.zero code installed (some none) _ 32 (by decide)
  · exact ClockCost.sequence code _ _ 11 0
      (FixedMemoryCost.copy code installed (some none) _ _ 8 (by decide)) (ClockCost.returned code _)

theorem u64_call (code) (installed : OriginalCode.Installed code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (LocalEffects.callInfo destination) (Code.name .htr_u64_at) arguments) 54 :=
  ClockCost.call_body code destination (Code.name .htr_u64_at) arguments
    (Code.formals .htr_u64_at) (Code.body .htr_u64_at) (Code.shape .htr_u64_at) 53
    (Code.installed code installed .htr_u64_at) (u64_body code installed)

end InitECandidate.Solver.Input.CurrentHash.FixedHashCost

#print axioms InitECandidate.Solver.Input.CurrentHash.FixedHashCost.mix_body
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedHashCost.mix_call
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedHashCost.u64_body
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedHashCost.u64_call
