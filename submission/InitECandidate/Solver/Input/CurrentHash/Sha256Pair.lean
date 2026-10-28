import InitECandidate.Solver.Input.CurrentHash.Base
import InitECandidate.Solver.Input.StraightBody
import InitECandidate.Solver.Input.ClockCostCall

namespace InitECandidate.Solver.Input.CurrentHash.Sha256Pair
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

-- Kernel-reduced syntax check of the actual expanded software SHA pair.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem supported : StraightBody.accepts (Code.body .sha256_pair) = true := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_sha256_pair, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  rfl

theorem any_key (selected : MlS) (code) : GlobalEffects.Preserves selected code (Code.body .sha256_pair) :=
  (StraightBody.effects selected code (Code.body .sha256_pair) supported).2

/-- Existing arena callers retain their original interface. The stronger
syntax theorem actually preserves every global for every actual outcome. -/
theorem preserves (cursor : Cursor) (code) (_installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .sha256_pair) := any_key (key cursor) code

/-- The expanded body spends no source call/loop ticks. Its many straight-line
target instructions still require a separate static compilation cost. -/
theorem clock (code) : QuietClock.Preserves code (Code.body .sha256_pair) :=
  (StraightBody.effects (key .scratch) code (Code.body .sha256_pair) supported).1

theorem body_cost (code) : ClockCost.Bound code (Code.body .sha256_pair) 0 :=
  ClockCost.of_quiet code (Code.body .sha256_pair) (clock code)

/-- Every real tail/ignored/local-result pair call spends at most its single
caller tick, including malformed arguments, memory errors and clock exhaustion. -/
theorem call_cost (code) (installed : OriginalCode.Installed code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (LocalEffects.callInfo destination) (Code.name .sha256_pair) arguments) 1 :=
  ClockCost.call_body code destination (Code.name .sha256_pair) arguments
    (Code.formals .sha256_pair) (Code.body .sha256_pair) (Code.shape .sha256_pair) 0
    (Code.installed code installed .sha256_pair) (body_cost code)

end InitECandidate.Solver.Input.CurrentHash.Sha256Pair

#print axioms InitECandidate.Solver.Input.CurrentHash.Sha256Pair.supported
#print axioms InitECandidate.Solver.Input.CurrentHash.Sha256Pair.any_key
#print axioms InitECandidate.Solver.Input.CurrentHash.Sha256Pair.preserves
#print axioms InitECandidate.Solver.Input.CurrentHash.Sha256Pair.clock
#print axioms InitECandidate.Solver.Input.CurrentHash.Sha256Pair.body_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.Sha256Pair.call_cost
