import InitECandidate.Solver.GasBudget.ArithmeticEffects
import InitECandidate.Solver.Input.QuietClock

namespace InitECandidate.Solver.GasBudget.ArithmeticEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

-- Generated proof data: each true case is checked against the original AST.
def Kind.quiet : Kind → Bool
  | .add_sat => true
  | .bit_length64 => true
  | .bswap64 => true
  | .ceil_log2 => false
  | .digits_len => false
  | .digits_to_u256 => true
  | .div64by32 => false
  | .max => true
  | .min => true
  | .mul64x64 => true
  | .nlz32 => true
  | .sat_word => true
  | .u256_add => true
  | .u256_add_carry => true
  | .u256_and => true
  | .u256_eq => true
  | .u256_fits_word => true
  | .u256_from_word => true
  | .u256_is_zero => true
  | .u256_limb => true
  | .u256_low => true
  | .u256_lt => true
  | .u256_neg => true
  | .u256_not => true
  | .u256_or => true
  | .u256_shl => true
  | .u256_shr => true
  | .u256_slt => true
  | .u256_sub => true
  | .u256_xor => true
  | .u256_abs => false
  | .u256_bit => false
  | .u256_bit_length => false
  | .u256_byte => false
  | .u256_cmp => false
  | .u256_from_be => false
  | .u256_gt => false
  | .u256_mul => false
  | .u256_mul_full => false
  | .u256_sar => false
  | .u256_sgt => false
  | .u256_byte_length => false
  | .u256_exp => false
  | .u256_signextend => false

theorem quiet_preserves (kind : Kind) (code) (checked : kind.quiet = true) : Input.QuietClock.Preserves code kind.body := by
  cases kind with
  | add_sat =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_add_sat, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    apply Input.QuietClock.declared
    apply Input.QuietClock.sequence
    · apply Input.QuietClock.conditional
      · exact Input.QuietClock.returned code _
      · exact Input.QuietClock.skip code
    · exact Input.QuietClock.returned code _
  | bit_length64 =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_bit_length64, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    apply Input.QuietClock.declared
    apply Input.QuietClock.sequence
    · apply Input.QuietClock.conditional
      · apply Input.QuietClock.sequence
        · exact Input.QuietClock.assign code _ _
        · exact Input.QuietClock.assign code _ _
      · exact Input.QuietClock.skip code
    · apply Input.QuietClock.sequence
      · apply Input.QuietClock.conditional
        · apply Input.QuietClock.sequence
          · exact Input.QuietClock.assign code _ _
          · exact Input.QuietClock.assign code _ _
        · exact Input.QuietClock.skip code
      · apply Input.QuietClock.sequence
        · apply Input.QuietClock.conditional
          · apply Input.QuietClock.sequence
            · exact Input.QuietClock.assign code _ _
            · exact Input.QuietClock.assign code _ _
          · exact Input.QuietClock.skip code
        · apply Input.QuietClock.sequence
          · apply Input.QuietClock.conditional
            · apply Input.QuietClock.sequence
              · exact Input.QuietClock.assign code _ _
              · exact Input.QuietClock.assign code _ _
            · exact Input.QuietClock.skip code
          · apply Input.QuietClock.sequence
            · apply Input.QuietClock.conditional
              · apply Input.QuietClock.sequence
                · exact Input.QuietClock.assign code _ _
                · exact Input.QuietClock.assign code _ _
              · exact Input.QuietClock.skip code
            · apply Input.QuietClock.sequence
              · apply Input.QuietClock.conditional
                · apply Input.QuietClock.sequence
                  · exact Input.QuietClock.assign code _ _
                  · exact Input.QuietClock.assign code _ _
                · exact Input.QuietClock.skip code
              · exact Input.QuietClock.returned code _
  | bswap64 =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_bswap64, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    apply Input.QuietClock.sequence
    · exact Input.QuietClock.assign code _ _
    · apply Input.QuietClock.sequence
      · exact Input.QuietClock.assign code _ _
      · exact Input.QuietClock.returned code _
  | ceil_log2 => cases checked
  | digits_len => cases checked
  | digits_to_u256 =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_digits_to_u256, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    exact Input.QuietClock.returned code _
  | div64by32 => cases checked
  | max =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_max, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    apply Input.QuietClock.sequence
    · apply Input.QuietClock.conditional
      · exact Input.QuietClock.returned code _
      · exact Input.QuietClock.skip code
    · exact Input.QuietClock.returned code _
  | min =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_min, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    apply Input.QuietClock.sequence
    · apply Input.QuietClock.conditional
      · exact Input.QuietClock.returned code _
      · exact Input.QuietClock.skip code
    · exact Input.QuietClock.returned code _
  | mul64x64 =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_mul64x64, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    apply Input.QuietClock.declared
    apply Input.QuietClock.declared
    apply Input.QuietClock.declared
    apply Input.QuietClock.declared
    apply Input.QuietClock.declared
    apply Input.QuietClock.declared
    apply Input.QuietClock.declared
    apply Input.QuietClock.sequence
    · exact Input.QuietClock.primitive code _ _ _
    · apply Input.QuietClock.declared
      apply Input.QuietClock.sequence
      · exact Input.QuietClock.primitive code _ _ _
      · apply Input.QuietClock.declared
        exact Input.QuietClock.returned code _
  | nlz32 =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_nlz32, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    apply Input.QuietClock.declared
    apply Input.QuietClock.sequence
    · apply Input.QuietClock.conditional
      · apply Input.QuietClock.sequence
        · exact Input.QuietClock.assign code _ _
        · exact Input.QuietClock.assign code _ _
      · exact Input.QuietClock.skip code
    · apply Input.QuietClock.sequence
      · apply Input.QuietClock.conditional
        · apply Input.QuietClock.sequence
          · exact Input.QuietClock.assign code _ _
          · exact Input.QuietClock.assign code _ _
        · exact Input.QuietClock.skip code
      · apply Input.QuietClock.sequence
        · apply Input.QuietClock.conditional
          · apply Input.QuietClock.sequence
            · exact Input.QuietClock.assign code _ _
            · exact Input.QuietClock.assign code _ _
          · exact Input.QuietClock.skip code
        · apply Input.QuietClock.sequence
          · apply Input.QuietClock.conditional
            · apply Input.QuietClock.sequence
              · exact Input.QuietClock.assign code _ _
              · exact Input.QuietClock.assign code _ _
            · exact Input.QuietClock.skip code
          · apply Input.QuietClock.sequence
            · apply Input.QuietClock.conditional
              · exact Input.QuietClock.assign code _ _
              · exact Input.QuietClock.skip code
            · exact Input.QuietClock.returned code _
  | sat_word =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_sat_word, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    apply Input.QuietClock.sequence
    · apply Input.QuietClock.conditional
      · exact Input.QuietClock.returned code _
      · exact Input.QuietClock.skip code
    · exact Input.QuietClock.returned code _
  | u256_add =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_add, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    apply Input.QuietClock.declared
    apply Input.QuietClock.sequence
    · exact Input.QuietClock.primitive code _ _ _
    · apply Input.QuietClock.declared
      apply Input.QuietClock.sequence
      · exact Input.QuietClock.primitive code _ _ _
      · apply Input.QuietClock.declared
        apply Input.QuietClock.sequence
        · exact Input.QuietClock.primitive code _ _ _
        · apply Input.QuietClock.declared
          apply Input.QuietClock.sequence
          · exact Input.QuietClock.primitive code _ _ _
          · exact Input.QuietClock.returned code _
  | u256_add_carry =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_add_carry, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    apply Input.QuietClock.declared
    apply Input.QuietClock.sequence
    · exact Input.QuietClock.primitive code _ _ _
    · apply Input.QuietClock.declared
      apply Input.QuietClock.sequence
      · exact Input.QuietClock.primitive code _ _ _
      · apply Input.QuietClock.declared
        apply Input.QuietClock.sequence
        · exact Input.QuietClock.primitive code _ _ _
        · apply Input.QuietClock.declared
          apply Input.QuietClock.sequence
          · exact Input.QuietClock.primitive code _ _ _
          · exact Input.QuietClock.returned code _
  | u256_and =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_and, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    exact Input.QuietClock.returned code _
  | u256_eq =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_eq, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    apply Input.QuietClock.sequence
    · apply Input.QuietClock.conditional
      · exact Input.QuietClock.returned code _
      · exact Input.QuietClock.skip code
    · exact Input.QuietClock.returned code _
  | u256_fits_word =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_fits_word, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    apply Input.QuietClock.sequence
    · apply Input.QuietClock.conditional
      · exact Input.QuietClock.returned code _
      · exact Input.QuietClock.skip code
    · exact Input.QuietClock.returned code _
  | u256_from_word =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_from_word, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    exact Input.QuietClock.returned code _
  | u256_is_zero =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_is_zero, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    apply Input.QuietClock.sequence
    · apply Input.QuietClock.conditional
      · exact Input.QuietClock.returned code _
      · exact Input.QuietClock.skip code
    · exact Input.QuietClock.returned code _
  | u256_limb =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_limb, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    apply Input.QuietClock.sequence
    · apply Input.QuietClock.conditional
      · exact Input.QuietClock.returned code _
      · exact Input.QuietClock.skip code
    · apply Input.QuietClock.sequence
      · apply Input.QuietClock.conditional
        · exact Input.QuietClock.returned code _
        · exact Input.QuietClock.skip code
      · apply Input.QuietClock.sequence
        · apply Input.QuietClock.conditional
          · exact Input.QuietClock.returned code _
          · exact Input.QuietClock.skip code
        · apply Input.QuietClock.sequence
          · apply Input.QuietClock.conditional
            · exact Input.QuietClock.returned code _
            · exact Input.QuietClock.skip code
          · exact Input.QuietClock.returned code _
  | u256_low =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_low, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    exact Input.QuietClock.returned code _
  | u256_lt =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_lt, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    apply Input.QuietClock.sequence
    · apply Input.QuietClock.conditional
      · apply Input.QuietClock.sequence
        · apply Input.QuietClock.conditional
          · exact Input.QuietClock.returned code _
          · exact Input.QuietClock.skip code
        · exact Input.QuietClock.returned code _
      · exact Input.QuietClock.skip code
    · apply Input.QuietClock.sequence
      · apply Input.QuietClock.conditional
        · apply Input.QuietClock.sequence
          · apply Input.QuietClock.conditional
            · exact Input.QuietClock.returned code _
            · exact Input.QuietClock.skip code
          · exact Input.QuietClock.returned code _
        · exact Input.QuietClock.skip code
      · apply Input.QuietClock.sequence
        · apply Input.QuietClock.conditional
          · apply Input.QuietClock.sequence
            · apply Input.QuietClock.conditional
              · exact Input.QuietClock.returned code _
              · exact Input.QuietClock.skip code
            · exact Input.QuietClock.returned code _
          · exact Input.QuietClock.skip code
        · apply Input.QuietClock.sequence
          · apply Input.QuietClock.conditional
            · exact Input.QuietClock.returned code _
            · exact Input.QuietClock.skip code
          · exact Input.QuietClock.returned code _
  | u256_neg =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_neg, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    apply Input.QuietClock.declared
    apply Input.QuietClock.sequence
    · exact Input.QuietClock.primitive code _ _ _
    · apply Input.QuietClock.declared
      apply Input.QuietClock.sequence
      · exact Input.QuietClock.primitive code _ _ _
      · apply Input.QuietClock.declared
        apply Input.QuietClock.sequence
        · exact Input.QuietClock.primitive code _ _ _
        · apply Input.QuietClock.declared
          apply Input.QuietClock.sequence
          · exact Input.QuietClock.primitive code _ _ _
          · exact Input.QuietClock.returned code _
  | u256_not =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_not, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    exact Input.QuietClock.returned code _
  | u256_or =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_or, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    exact Input.QuietClock.returned code _
  | u256_shl =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_shl, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    apply Input.QuietClock.sequence
    · apply Input.QuietClock.conditional
      · exact Input.QuietClock.returned code _
      · exact Input.QuietClock.skip code
    · apply Input.QuietClock.declared
      apply Input.QuietClock.declared
      apply Input.QuietClock.declared
      apply Input.QuietClock.declared
      apply Input.QuietClock.declared
      apply Input.QuietClock.declared
      apply Input.QuietClock.sequence
      · apply Input.QuietClock.conditional
        · apply Input.QuietClock.sequence
          · exact Input.QuietClock.assign code _ _
          · apply Input.QuietClock.sequence
            · exact Input.QuietClock.assign code _ _
            · apply Input.QuietClock.sequence
              · exact Input.QuietClock.assign code _ _
              · exact Input.QuietClock.assign code _ _
        · exact Input.QuietClock.skip code
      · apply Input.QuietClock.sequence
        · apply Input.QuietClock.conditional
          · apply Input.QuietClock.sequence
            · exact Input.QuietClock.assign code _ _
            · apply Input.QuietClock.sequence
              · exact Input.QuietClock.assign code _ _
              · apply Input.QuietClock.sequence
                · exact Input.QuietClock.assign code _ _
                · exact Input.QuietClock.assign code _ _
          · exact Input.QuietClock.skip code
        · apply Input.QuietClock.sequence
          · apply Input.QuietClock.conditional
            · apply Input.QuietClock.sequence
              · exact Input.QuietClock.assign code _ _
              · apply Input.QuietClock.sequence
                · exact Input.QuietClock.assign code _ _
                · apply Input.QuietClock.sequence
                  · exact Input.QuietClock.assign code _ _
                  · exact Input.QuietClock.assign code _ _
            · exact Input.QuietClock.skip code
          · apply Input.QuietClock.sequence
            · apply Input.QuietClock.conditional
              · apply Input.QuietClock.sequence
                · exact Input.QuietClock.assign code _ _
                · apply Input.QuietClock.sequence
                  · exact Input.QuietClock.assign code _ _
                  · apply Input.QuietClock.sequence
                    · exact Input.QuietClock.assign code _ _
                    · exact Input.QuietClock.assign code _ _
              · exact Input.QuietClock.skip code
            · exact Input.QuietClock.returned code _
  | u256_shr =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_shr, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    apply Input.QuietClock.sequence
    · apply Input.QuietClock.conditional
      · exact Input.QuietClock.returned code _
      · exact Input.QuietClock.skip code
    · apply Input.QuietClock.declared
      apply Input.QuietClock.declared
      apply Input.QuietClock.declared
      apply Input.QuietClock.declared
      apply Input.QuietClock.declared
      apply Input.QuietClock.declared
      apply Input.QuietClock.sequence
      · apply Input.QuietClock.conditional
        · apply Input.QuietClock.sequence
          · exact Input.QuietClock.assign code _ _
          · apply Input.QuietClock.sequence
            · exact Input.QuietClock.assign code _ _
            · apply Input.QuietClock.sequence
              · exact Input.QuietClock.assign code _ _
              · exact Input.QuietClock.assign code _ _
        · exact Input.QuietClock.skip code
      · apply Input.QuietClock.sequence
        · apply Input.QuietClock.conditional
          · apply Input.QuietClock.sequence
            · exact Input.QuietClock.assign code _ _
            · apply Input.QuietClock.sequence
              · exact Input.QuietClock.assign code _ _
              · apply Input.QuietClock.sequence
                · exact Input.QuietClock.assign code _ _
                · exact Input.QuietClock.assign code _ _
          · exact Input.QuietClock.skip code
        · apply Input.QuietClock.sequence
          · apply Input.QuietClock.conditional
            · apply Input.QuietClock.sequence
              · exact Input.QuietClock.assign code _ _
              · apply Input.QuietClock.sequence
                · exact Input.QuietClock.assign code _ _
                · apply Input.QuietClock.sequence
                  · exact Input.QuietClock.assign code _ _
                  · exact Input.QuietClock.assign code _ _
            · exact Input.QuietClock.skip code
          · apply Input.QuietClock.sequence
            · apply Input.QuietClock.conditional
              · apply Input.QuietClock.sequence
                · exact Input.QuietClock.assign code _ _
                · apply Input.QuietClock.sequence
                  · exact Input.QuietClock.assign code _ _
                  · apply Input.QuietClock.sequence
                    · exact Input.QuietClock.assign code _ _
                    · exact Input.QuietClock.assign code _ _
              · exact Input.QuietClock.skip code
            · exact Input.QuietClock.returned code _
  | u256_slt =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_slt, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    apply Input.QuietClock.sequence
    · apply Input.QuietClock.conditional
      · apply Input.QuietClock.sequence
        · apply Input.QuietClock.conditional
          · exact Input.QuietClock.returned code _
          · exact Input.QuietClock.skip code
        · exact Input.QuietClock.returned code _
      · exact Input.QuietClock.skip code
    · apply Input.QuietClock.sequence
      · apply Input.QuietClock.conditional
        · apply Input.QuietClock.sequence
          · apply Input.QuietClock.conditional
            · exact Input.QuietClock.returned code _
            · exact Input.QuietClock.skip code
          · exact Input.QuietClock.returned code _
        · exact Input.QuietClock.skip code
      · apply Input.QuietClock.sequence
        · apply Input.QuietClock.conditional
          · apply Input.QuietClock.sequence
            · apply Input.QuietClock.conditional
              · exact Input.QuietClock.returned code _
              · exact Input.QuietClock.skip code
            · exact Input.QuietClock.returned code _
          · exact Input.QuietClock.skip code
        · apply Input.QuietClock.sequence
          · apply Input.QuietClock.conditional
            · exact Input.QuietClock.returned code _
            · exact Input.QuietClock.skip code
          · exact Input.QuietClock.returned code _
  | u256_sub =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_sub, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    apply Input.QuietClock.declared
    apply Input.QuietClock.sequence
    · exact Input.QuietClock.primitive code _ _ _
    · apply Input.QuietClock.declared
      apply Input.QuietClock.sequence
      · exact Input.QuietClock.primitive code _ _ _
      · apply Input.QuietClock.declared
        apply Input.QuietClock.sequence
        · exact Input.QuietClock.primitive code _ _ _
        · apply Input.QuietClock.declared
          apply Input.QuietClock.sequence
          · exact Input.QuietClock.primitive code _ _ _
          · exact Input.QuietClock.returned code _
  | u256_xor =>
    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_xor, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
    exact Input.QuietClock.returned code _
  | u256_abs => cases checked
  | u256_bit => cases checked
  | u256_bit_length => cases checked
  | u256_byte => cases checked
  | u256_cmp => cases checked
  | u256_from_be => cases checked
  | u256_gt => cases checked
  | u256_mul => cases checked
  | u256_mul_full => cases checked
  | u256_sar => cases checked
  | u256_sgt => cases checked
  | u256_byte_length => cases checked
  | u256_exp => cases checked
  | u256_signextend => cases checked

/-- Zero source clocks means no charged calls/loops; it does not
mean zero straight-line target work. This covers all actual outcomes. -/
theorem quiet_clock (kind : Kind) (checked : kind.quiet = true)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source kind.body = (outcome, target)) : target.clock = source.clock := by
  have clock := quiet_preserves kind source.code checked source rfl
  simpa only [run] using clock

end InitECandidate.Solver.GasBudget.ArithmeticEffects

#print axioms InitECandidate.Solver.GasBudget.ArithmeticEffects.quiet_preserves
#print axioms InitECandidate.Solver.GasBudget.ArithmeticEffects.quiet_clock
