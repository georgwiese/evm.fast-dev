import InitECandidate.Solver.Headers.FieldSyntax
import InitECandidate.Solver.Input.QuietClock
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Headers.Field
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem after_item_quiet (code) (kind : Kind) : Input.QuietClock.Preserves code kind.afterItem := by
  cases kind <;> simp only [Kind.afterItem,Kind.body,Kind.declaration,
    Guest.Software.guestFn_hdr_uint_field,Guest.Software.guestFn_hdr_bytes_field,Guest.Software.guestFn_hdr_raw_field,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  all_goals repeat first
    | apply Input.QuietClock.sequence
    | apply Input.QuietClock.conditional
    | exact Input.QuietClock.skip code
    | exact Input.QuietClock.raised code _ _
    | exact Input.QuietClock.returned code _

/-- Every actual field-helper tail only reads memory and checks/returns
values, including on HdrErr and malformed-expression paths. -/
theorem after_item_readonly (code) (kind : Kind) : Input.LocalEffects.Preserves code kind.afterItem := by
  cases kind <;> simp only [Kind.afterItem,Kind.body,Kind.declaration,
    Guest.Software.guestFn_hdr_uint_field,Guest.Software.guestFn_hdr_bytes_field,Guest.Software.guestFn_hdr_raw_field,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  all_goals repeat first
    | apply Input.LocalEffects.sequence
    | apply Input.LocalEffects.conditional
    | exact Input.LocalEffects.skip code
    | exact Input.LocalEffects.raised code _ _
    | exact Input.LocalEffects.returned code _

end InitECandidate.Solver.Headers.Field

#print axioms InitECandidate.Solver.Headers.Field.after_item_quiet
#print axioms InitECandidate.Solver.Headers.Field.after_item_readonly
