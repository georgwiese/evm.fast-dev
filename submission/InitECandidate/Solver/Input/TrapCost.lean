import InitECandidate.Solver.Input.TrapNoReturn
import InitECandidate.Solver.Input.QuietClockEffects
import InitECandidate.Solver.Input.ClockCostCall
import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.OriginalCode

namespace InitECandidate.Solver.Input.Trap
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "trap_with")=some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 0 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_trap_with) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,
    Guest.Software.guestFn_trap_with,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- The real trap's shared-memory and FFI effects do not spend source
call/loop clocks. They are retained in the semantics, not erased. -/
theorem body_price (code) : ClockCost.Bound code body 0 := by
  apply ClockCost.of_quiet
  simp only [body,Guest.Software.guestFn_trap_with,progToHOL]
  repeat first
    | apply QuietClock.sequence
    | exact QuietClock.shared_store code _ _ _
    | exact QuietClock.external code _ _ _ _ _
    | exact QuietClock.raised code _ _

theorem call_price (code) (installed : OriginalCode.Installed code) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (some (none,none)) (ofString "trap_with") arguments) 1 :=
  ClockCost.call_body code (some none) (ofString "trap_with") arguments formals body .one 0 (original_code code installed) (body_price code)

end InitECandidate.Solver.Input.Trap

#print axioms InitECandidate.Solver.Input.Trap.original_code
#print axioms InitECandidate.Solver.Input.Trap.body_price
#print axioms InitECandidate.Solver.Input.Trap.call_price
